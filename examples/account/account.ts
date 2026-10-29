// An account, folded from its ledger: each entry changes the state the loop
// builds. The loop carries its invariants, the proof code the verifier reads it
// by; they do nothing when it runs. `account.contract.ts` states the laws.
import { invariant } from "tsverify"

export type Entry =
  | { readonly kind: "opened"; readonly at: string; readonly owner: string }
  | { readonly kind: "deposited"; readonly at: string; readonly id: string; readonly amount: bigint }
  | { readonly kind: "withdrawn"; readonly at: string; readonly id: string; readonly amount: bigint }
  | { readonly kind: "disputed"; readonly at: string; readonly id: string }
  | { readonly kind: "resolved"; readonly at: string; readonly id: string; readonly upheld: boolean }
  | { readonly kind: "frozen"; readonly at: string; readonly reason: string }
  | { readonly kind: "closed"; readonly at: string }

export interface Transaction {
  readonly id: string
  /** Signed: a withdrawal is negative. */
  readonly amount: bigint
  disputed: boolean
  /** A dispute upheld against it: its amount is taken back out of the balance. */
  reversed?: true
}

export interface Account {
  owner: string
  opened: boolean
  balance: bigint
  transactions: Transaction[]
  /** Why it is frozen: the first reason given. */
  frozen: string | null
  closed: boolean
}

/** The `opened` entry `e`, written into the account `a`. */
function openInto(a: Account, e: Extract<Entry, { kind: "opened" }>): void {
  a.opened = true
  a.owner = e.owner
}

/** The account its ledger says. Never stored: always folded again from the entries. */
export function accountOf(entries: readonly Entry[]): Account {
  const a: Account = { owner: "", opened: false, balance: 0n, transactions: [], frozen: null, closed: false }
  for (const e of entries) {
    invariant((i) => a.opened === entries.slice(0, i).some((x) => x.kind === "opened"))
    invariant((i) => a.closed === entries.slice(0, i).some((x) => x.kind === "closed"))
    invariant((i) => a.frozen === null || entries.slice(0, i).some((x) => x.kind === "frozen"))
    invariant((i) => a.transactions.length <= i)
    invariant((i) => a.balance >= 0n || entries.slice(0, i).some((x) => x.kind === "withdrawn" || x.kind === "resolved"))
    switch (e.kind) {
      case "opened":
        openInto(a, e)
        break
      case "deposited":
        a.balance += e.amount
        a.transactions.push({ id: e.id, amount: e.amount, disputed: false })
        break
      case "withdrawn":
        a.balance -= e.amount
        a.transactions.push({ id: e.id, amount: -e.amount, disputed: false })
        break
      case "disputed": {
        const t = a.transactions.find((x) => x.id === e.id)
        if (t) t.disputed = true
        break
      }
      case "resolved": {
        const t = a.transactions.find((x) => x.id === e.id)
        if (t && t.disputed) {
          t.disputed = false
          if (e.upheld) {
            t.reversed = true
            a.balance -= t.amount
          }
        }
        break
      }
      case "frozen":
        a.frozen ??= e.reason
        break
      case "closed":
        a.closed = true
        break
    }
  }
  return a
}

/** Why `account` cannot pay out `amount` now, in words that say what to do instead; `undefined` when it can. */
export function withdrawalRefusalOf(account: Account, amount: bigint): string | undefined {
  if (!account.opened) return "the account is not open: open it first"
  if (account.closed) return "the account is closed: withdraw from another"
  if (account.frozen !== null) return `the account is frozen (${account.frozen}): lift the freeze first`
  if (amount <= 0n) return "the amount is not positive: ask for more than 0"
  if (account.balance < amount) return "the balance is below the amount: ask for less"
  return undefined
}

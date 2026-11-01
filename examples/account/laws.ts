// The laws of a withdrawal, written once and held against both programs that
// make one. They speak of the outcome and of the calls made, never of how the
// program is written.
import type { Outcome } from "@emyann/tsverify"
import { accountOf, type Entry, withdrawalRefusalOf } from "./account.ts"

type Failure = { readonly _tag: string }
export type WithdrawOutcome = Outcome<void, Failure>
export type LedgerCall =
  | { readonly op: "read"; readonly args: readonly [string]; readonly outcome: Outcome<readonly Entry[], Failure> }
  | { readonly op: "append"; readonly args: readonly [string, Entry]; readonly outcome: Outcome<void, Failure> }
type Law = (accountId: string, id: string, amount: bigint, out: WithdrawOutcome, calls: ReadonlyArray<LedgerCall>) => boolean

/** The ledger is read first, and this account's. */
export const readsFirst: Law = (accountId, _id, _amount, _out, calls) => {
  const first = calls.at(0)
  return first !== undefined && first.op === "read" && first.args[0] === accountId
}

/** A read that fails ends the withdrawal with that failure, and nothing else is called. */
export const readFailurePassesThrough: Law = (_accountId, _id, _amount, out, calls) => {
  const first = calls.at(0)
  if (first === undefined || first.outcome._tag !== "Failure") return true
  return calls.length === 1 && out._tag === "Failure" && out.error._tag === first.outcome.error._tag
}

/** A refused withdrawal writes nothing. */
export const refusedWritesNothing: Law = (_accountId, _id, _amount, out, calls) =>
  !(out._tag === "Failure" && out.error._tag === "WithdrawalRefused") || !calls.some((c) => c.op === "append")

/** A paid withdrawal writes exactly one entry, last, to this account: a withdrawal of the amount asked, under its id. */
export const paidWritesOneWithdrawal: Law = (accountId, id, amount, out, calls) => {
  if (out._tag !== "Success") return true
  const last = calls.at(-1)
  return (
    calls.filter((c) => c.op === "append").length === 1 &&
    last !== undefined &&
    last.op === "append" &&
    last.args[0] === accountId &&
    last.args[1].kind === "withdrawn" &&
    last.args[1].id === id &&
    last.args[1].amount === amount
  )
}

/** The withdrawal is refused exactly when the guard, asked of the ledger read, gives words. */
export const refusedExactlyWhenTheGuardSays: Law = (_accountId, _id, amount, out, calls) => {
  const first = calls.at(0)
  if (first === undefined || first.op !== "read" || first.outcome._tag !== "Success") return true
  const refused = withdrawalRefusalOf(accountOf(first.outcome.value), amount) !== undefined
  return refused === (out._tag === "Failure" && out.error._tag === "WithdrawalRefused")
}

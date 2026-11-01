// What an account's ledger makes of it: five laws, proved for ledgers of every
// length through the invariants its loop carries.
import { contract } from "@emyann/tsverify"
import { accountOf, type Entry } from "./account.ts"

const positive = ({ input: [entries] }: { readonly input: readonly [readonly Entry[]] }) =>
  entries.every((e) => (e.kind !== "deposited" && e.kind !== "withdrawn") || e.amount > 0n)

export const folded = contract(accountOf, {
  requires: positive,
  ensures: {
    openedExactlyWhenRecorded: ({ input: [entries], output }) => output.opened === entries.some((e) => e.kind === "opened"),
    closedExactlyWhenRecorded: ({ input: [entries], output }) => output.closed === entries.some((e) => e.kind === "closed"),
    frozenOnlyWhenRecorded: ({ input: [entries], output }) => output.frozen === null || entries.some((e) => e.kind === "frozen"),
    noMoreTransactionsThanEntries: ({ input: [entries], output }) => output.transactions.length <= entries.length,
    noDebtWithoutWithdrawals: ({ input: [entries], output }) =>
      output.balance >= 0n || entries.some((e) => e.kind === "withdrawn" || e.kind === "resolved"),
  },
})

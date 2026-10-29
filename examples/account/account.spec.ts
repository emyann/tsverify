// What an account's ledger makes of it: five laws, proved for ledgers of every
// length through the invariants its loop carries.
import { contract } from "tsverify"
import { accountOf, type Entry } from "./account.ts"

const positive = (entries: readonly Entry[]) => entries.every((e) => (e.kind !== "deposited" && e.kind !== "withdrawn") || e.amount > 0n)

export const folded = contract(accountOf, {
  requires: positive,
  ensures: {
    openedExactlyWhenRecorded: (entries, a) => a.opened === entries.some((e) => e.kind === "opened"),
    closedExactlyWhenRecorded: (entries, a) => a.closed === entries.some((e) => e.kind === "closed"),
    frozenOnlyWhenRecorded: (entries, a) => a.frozen === null || entries.some((e) => e.kind === "frozen"),
    noMoreTransactionsThanEntries: (entries, a) => a.transactions.length <= entries.length,
    noDebtWithoutWithdrawals: (entries, a) => a.balance >= 0n || entries.some((e) => e.kind === "withdrawn" || e.kind === "resolved"),
  },
})

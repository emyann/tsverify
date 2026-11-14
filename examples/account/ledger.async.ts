// The same ledger as plain TypeScript gives it: an interface handed to the program, its failures thrown. A module of its
// own, which the spec and the program both import.
import type { Rejects } from "@emyann/tsverify"
import type { Entry } from "./account.ts"

export class WithdrawalRefused extends Error {
  readonly _tag = "WithdrawalRefused" as const
}

export class LedgerError extends Error {
  readonly _tag = "LedgerError" as const
}

export interface LedgerPort {
  readonly read: (accountId: string) => Rejects<readonly Entry[], LedgerError>
  readonly append: (accountId: string, entry: Entry) => Rejects<void, LedgerError>
}

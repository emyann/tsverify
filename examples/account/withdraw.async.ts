// The same withdrawal as plain TypeScript writes it: async, its ledger given as
// an interface, its refusal thrown. No Effect anywhere; the same pure helpers.
import type { Implementation, Rejects } from "@emyann/tsverify"
import { accountOf, type Entry, withdrawalRefusalOf } from "./account.ts"
import type { AsyncWithdrawSpec } from "./withdraw.contract.ts"

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

export const withdraw: Implementation<AsyncWithdrawSpec> = async (ledger, accountId, id, amount) => {
  const entries = await ledger.read(accountId)
  const refused = withdrawalRefusalOf(accountOf(entries), amount)
  if (refused) throw new WithdrawalRefused(refused)
  await ledger.append(accountId, { kind: "withdrawn", at: new Date().toISOString(), id, amount })
}

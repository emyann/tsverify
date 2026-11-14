// The same withdrawal as plain TypeScript writes it: async, its ledger given as
// an interface, its refusal thrown. No Effect anywhere; the same pure helpers.
import type { Implementation } from "@emyann/tsverify"
import { accountOf, withdrawalRefusalOf } from "./account.ts"
import { WithdrawalRefused } from "./ledger.async.ts"
import type { AsyncWithdrawSpec } from "./withdraw.contract.ts"

export { LedgerError, type LedgerPort, WithdrawalRefused } from "./ledger.async.ts"

export const withdraw: Implementation<AsyncWithdrawSpec> = async (ledger, accountId, id, amount) => {
  const entries = await ledger.read(accountId)
  const refused = withdrawalRefusalOf(accountOf(entries), amount)
  if (refused) throw new WithdrawalRefused(refused)
  await ledger.append(accountId, { kind: "withdrawn", at: new Date().toISOString(), id, amount })
}

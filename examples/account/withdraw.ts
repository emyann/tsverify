// A withdrawal as an Effect 4 program: read the ledger, ask the guard, refuse
// or record one withdrawal. The ledger is a service the program is given.
import { Effect } from "effect"
import type { Implementation } from "@emyann/tsverify"
import { accountOf, withdrawalRefusalOf } from "./account.ts"
import { Ledger, WithdrawalRefused } from "./ledger.ts"
import type { WithdrawSpec } from "./withdraw.contract.ts"

export { Ledger, LedgerError, type LedgerShape, WithdrawalRefused } from "./ledger.ts"

/** Pays out `amount` from the account, recorded as the withdrawal `id`; refused, with nothing written, when the guard says why. */
export const withdraw: Implementation<WithdrawSpec> = Effect.fn("withdraw")(function* (accountId: string, id: string, amount: bigint) {
  const ledger = yield* Ledger
  const entries = yield* ledger.read(accountId)
  const refused = withdrawalRefusalOf(accountOf(entries), amount)
  if (refused) return yield* Effect.fail(new WithdrawalRefused({ message: refused }))
  yield* ledger.append(accountId, { kind: "withdrawn", at: new Date().toISOString(), id, amount })
})

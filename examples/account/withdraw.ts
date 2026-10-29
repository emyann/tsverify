// A withdrawal as an Effect 4 program: read the ledger, ask the guard, refuse
// or record one withdrawal. The ledger is a service the program is given.
import { Context, Effect, Schema } from "effect"
import type { Implementation } from "tsverify"
import { accountOf, type Entry, withdrawalRefusalOf } from "./account.ts"
import type { WithdrawSpec } from "./withdraw.contract.ts"

export class LedgerError extends Schema.TaggedError<LedgerError>()("LedgerError", {
  accountId: Schema.String,
  message: Schema.String,
}) {}

export class WithdrawalRefused extends Schema.TaggedError<WithdrawalRefused>()("WithdrawalRefused", {
  message: Schema.String,
}) {}

export interface LedgerShape {
  readonly read: (accountId: string) => Effect.Effect<readonly Entry[], LedgerError>
  readonly append: (accountId: string, entry: Entry) => Effect.Effect<void, LedgerError>
}

export class Ledger extends Context.Service<Ledger, LedgerShape>()("examples/Ledger") {}

/** Pays out `amount` from the account, recorded as the withdrawal `id`; refused, with nothing written, when the guard says why. */
export const withdraw: Implementation<typeof WithdrawSpec> = Effect.fn("withdraw")(function* (
  accountId: string,
  id: string,
  amount: bigint,
) {
  const ledger = yield* Ledger
  const entries = yield* ledger.read(accountId)
  const refused = withdrawalRefusalOf(accountOf(entries), amount)
  if (refused) return yield* Effect.fail(new WithdrawalRefused({ message: refused }))
  yield* ledger.append(accountId, { kind: "withdrawn", at: new Date().toISOString(), id, amount })
})

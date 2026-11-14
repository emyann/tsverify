// The ledger a withdrawal reads and writes, as an Effect 4 service, and the two ways a withdrawal fails: a module of its
// own, which the specs and the programs both import, so no spec reads the code that implements it.
import { Context, type Effect, Schema } from "effect"
import type { Entry } from "./account.ts"

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

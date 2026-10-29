// One withdrawal, two programs, the same five laws: the specs, written before
// the code. `withdraw.ts` and `withdraw.async.ts` take them as their types.
import type { Effect } from "effect"
import { assume, type Rejects, spec } from "tsverify"
import { spec as effectSpec } from "tsverify/effect"
import { accountOf } from "./account.ts"
import {
  paidWritesOneWithdrawal,
  readFailurePassesThrough,
  readsFirst,
  refusedExactlyWhenTheGuardSays,
  refusedWritesNothing,
} from "./laws.ts"
import type { Ledger, LedgerError, WithdrawalRefused } from "./withdraw.ts"
import type * as Async from "./withdraw.async.ts"

/**
 * The ledger's fold, pure, which the verifier checks from its source, and nothing else: the laws hold whatever account it
 * folds to. Its own laws are proved apart (`account.contract.ts`); read here, each of its loops would be a different unknown
 * in the program and in the law, and the law would not be provable.
 */
export const accountOfIsPure = assume(accountOf, { pure: true })

/**
 * Pays out `amount` from the account, as the withdrawal `id`, through the `Ledger` service: refused when the guard says
 * why, failing as the ledger fails. The calls its laws read are `Ledger`'s, typed from the service.
 */
export const WithdrawSpec = effectSpec<
  (accountId: string, id: string, amount: bigint) => Effect.Effect<void, WithdrawalRefused | LedgerError, Ledger>
>({
  ensures: { readsFirst, readFailurePassesThrough, refusedWritesNothing, paidWritesOneWithdrawal, refusedExactlyWhenTheGuardSays },
})

/** Its async twin, whose ledger is its first argument: the calls its laws read are that argument's. */
export const AsyncWithdrawSpec = spec<
  (ledger: Async.LedgerPort, accountId: string, id: string, amount: bigint) => Rejects<void, Async.WithdrawalRefused | Async.LedgerError>
>({
  ensures: {
    readsFirst: (_, accountId, id, amount, out, calls) => readsFirst(accountId, id, amount, out, calls),
    readFailurePassesThrough: (_, accountId, id, amount, out, calls) => readFailurePassesThrough(accountId, id, amount, out, calls),
    refusedWritesNothing: (_, accountId, id, amount, out, calls) => refusedWritesNothing(accountId, id, amount, out, calls),
    paidWritesOneWithdrawal: (_, accountId, id, amount, out, calls) => paidWritesOneWithdrawal(accountId, id, amount, out, calls),
    refusedExactlyWhenTheGuardSays: (_, accountId, id, amount, out, calls) =>
      refusedExactlyWhenTheGuardSays(accountId, id, amount, out, calls),
  },
})

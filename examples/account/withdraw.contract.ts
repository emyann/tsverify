// One withdrawal, two programs, the same five laws: the specs, written before
// the code. `withdraw.ts` and `withdraw.async.ts` take them as their types.
import type { Effect } from "effect"
import { assume, type Rejects, spec } from "@emyann/tsverify"
import { spec as effectSpec } from "@emyann/tsverify/effect"
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
const withdrawSpec = effectSpec<
  (accountId: string, id: string, amount: bigint) => Effect.Effect<void, WithdrawalRefused | LedgerError, Ledger>
>({
  ensures: { readsFirst, readFailurePassesThrough, refusedWritesNothing, paidWritesOneWithdrawal, refusedExactlyWhenTheGuardSays },
})
export type WithdrawSpec = typeof withdrawSpec

/** Its async twin, whose ledger is its first argument: the calls its laws read are that argument's. */
const asyncWithdrawSpec = spec<
  (ledger: Async.LedgerPort, accountId: string, id: string, amount: bigint) => Rejects<void, Async.WithdrawalRefused | Async.LedgerError>
>({
  ensures: {
    readsFirst: ({ input: [, accountId, id, amount], output, calls }) => readsFirst({ input: [accountId, id, amount], output, calls }),
    readFailurePassesThrough: ({ input: [, accountId, id, amount], output, calls }) =>
      readFailurePassesThrough({ input: [accountId, id, amount], output, calls }),
    refusedWritesNothing: ({ input: [, accountId, id, amount], output, calls }) =>
      refusedWritesNothing({ input: [accountId, id, amount], output, calls }),
    paidWritesOneWithdrawal: ({ input: [, accountId, id, amount], output, calls }) =>
      paidWritesOneWithdrawal({ input: [accountId, id, amount], output, calls }),
    refusedExactlyWhenTheGuardSays: ({ input: [, accountId, id, amount], output, calls }) =>
      refusedExactlyWhenTheGuardSays({ input: [accountId, id, amount], output, calls }),
  },
})
export type AsyncWithdrawSpec = typeof asyncWithdrawSpec

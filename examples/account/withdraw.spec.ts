// One withdrawal, two programs, the same five laws.
import { assume, computation } from "tsverify"
import { computation as effectComputation } from "tsverify/effect"
import { accountOf } from "./account.ts"
import { paidWritesOneWithdrawal, readFailurePassesThrough, readsFirst, refusedExactlyWhenTheGuardSays, refusedWritesNothing } from "./laws.ts"
import { type LedgerShape, withdraw } from "./withdraw.ts"
import { type LedgerError, type LedgerPort, type WithdrawalRefused, withdraw as withdrawAsync } from "./withdraw.async.ts"

/**
 * The ledger's fold, pure, which the verifier checks from its source, and nothing else: the laws hold whatever account it
 * folds to. Its own laws are proved apart (`account.spec.ts`); read here, each of its loops would be a different unknown
 * in the program and in the law, and the law would not be provable.
 */
export const accountOfIsPure = assume(accountOf, { pure: true })

/** The Effect program: `Effect.fn('withdraw')(function* (accountId, id, amount) { ... })`. */
export const effectWithdraw = effectComputation<{ ledger: LedgerShape }>()(withdraw, {
  ensures: { readsFirst, readFailurePassesThrough, refusedWritesNothing, paidWritesOneWithdrawal, refusedExactlyWhenTheGuardSays },
})

/** Its async twin, whose ledger is its first argument. */
export const asyncWithdraw = computation<{ ledger: LedgerPort }, WithdrawalRefused | LedgerError>()(withdrawAsync, {
  ensures: {
    readsFirst: (_, accountId, id, amount, out, calls) => readsFirst(accountId, id, amount, out, calls),
    readFailurePassesThrough: (_, accountId, id, amount, out, calls) => readFailurePassesThrough(accountId, id, amount, out, calls),
    refusedWritesNothing: (_, accountId, id, amount, out, calls) => refusedWritesNothing(accountId, id, amount, out, calls),
    paidWritesOneWithdrawal: (_, accountId, id, amount, out, calls) => paidWritesOneWithdrawal(accountId, id, amount, out, calls),
    refusedExactlyWhenTheGuardSays: (_, accountId, id, amount, out, calls) => refusedExactlyWhenTheGuardSays(accountId, id, amount, out, calls),
  },
})

// The account's other programs, in the other ways Effect is written: a function
// that returns `Effect.gen`, pipelines with `.pipe` and `pipe`, `map`,
// `flatMap`, `catch`, `catchTag` and `sync`. `effects.spec.ts` states their laws.
import { Effect, pipe, Schema } from "effect"
import { type Account, accountOf } from "./account.ts"
import { Ledger } from "./withdraw.ts"

export class DepositRefused extends Schema.TaggedError<DepositRefused>()("DepositRefused", {
  message: Schema.String,
}) {}

/** The balance the ledger folds to. */
export const balanceOf = (accountId: string) =>
  Effect.gen(function* () {
    const ledger = yield* Ledger
    const entries = yield* ledger.read(accountId)
    return accountOf(entries).balance
  })

/** The balance, or 0 when the ledger cannot be read. */
export const balanceOrZero = (accountId: string) => balanceOf(accountId).pipe(Effect.catch(() => Effect.succeed(0n)))

/** Twice the balance. */
export const doubledBalance = (accountId: string) => pipe(balanceOf(accountId), Effect.map((b) => b + b))

/** Why `account` cannot take `amount` now, in words that say what to do instead; `undefined` when it can. */
export function depositRefusalOf(account: Account, amount: bigint): string | undefined {
  if (!account.opened) return "the account is not open: open it first"
  if (account.closed) return "the account is closed: deposit into another"
  if (amount <= 0n) return "the amount is not positive: deposit more than 0"
  return undefined
}

/**
 * Records `amount` as the deposit `id`: refused, with nothing written, when the guard says why, and when the ledger
 * cannot be read (the read's failure is the refusal's reason). A failed write is the ledger's failure.
 */
export const deposit = Effect.fn("deposit")(function* (accountId: string, id: string, amount: bigint) {
  const ledger = yield* Ledger
  const refused = yield* ledger.read(accountId).pipe(
    Effect.map((entries) => depositRefusalOf(accountOf(entries), amount)),
    Effect.catchTag("LedgerError", () => Effect.succeed("the ledger cannot be read now: try again later")),
  )
  if (refused) return yield* Effect.fail(new DepositRefused({ message: refused }))
  yield* Effect.flatMap(
    Effect.sync(() => new Date().toISOString()),
    (at) => ledger.append(accountId, { kind: "deposited", at, id, amount }),
  )
})

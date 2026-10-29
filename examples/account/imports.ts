// The account's programs that take text written elsewhere: code that may throw,
// run under `Effect.try`; a step inside an expression; a loop of steps.
// `imports.contract.ts` states their laws.
import { Effect, Schema } from "effect"
import type { Entry } from "./account.ts"
import { DepositRefused, deposit } from "./effects.ts"
import { Ledger } from "./withdraw.ts"

export class AmountUnreadable extends Schema.TaggedError<AmountUnreadable>()("AmountUnreadable", {
  text: Schema.String,
}) {}

/** The amount a person typed, as a bigint; text that is no integer is `AmountUnreadable`, naming the text. */
export const amountOf = (text: string) => Effect.try({ try: () => BigInt(text), catch: () => new AmountUnreadable({ text }) })

/** Deposits the amount typed, as `deposit` does; text that is no integer is refused before the ledger is read. */
export const depositTyped = Effect.fn("depositTyped")(function* (accountId: string, id: string, text: string) {
  return yield* deposit(accountId, id, yield* amountOf(text))
})

/** The entries an export lists, as JSON, amounts as strings of digits; what `JSON.parse` throws is the failure, as thrown. */
export const exportedEntries = (json: string) =>
  Effect.try({
    try: (): ReadonlyArray<Entry> => JSON.parse(json, (key, value) => (key === "amount" ? BigInt(value) : value)),
    catch: (err) => err,
  })

/**
 * Appends every deposit an export lists to the account's ledger, in order, and says how many it wrote. An export that
 * does not parse fails as it threw, with nothing written; a failed write stops the import there.
 */
export const importDeposits = Effect.fn("importDeposits")(function* (accountId: string, json: string) {
  const ledger = yield* Ledger
  const entries = yield* exportedEntries(json)
  for (const e of entries) if (e.kind === "deposited") yield* ledger.append(accountId, e)
  return entries.filter((e) => e.kind === "deposited").length
})

/** Opens the account for `owner` with its first deposit: the opening, then the deposit, each written once. */
export const openWith = Effect.fn("openWith")(function* (accountId: string, owner: string, id: string, amount: bigint) {
  const ledger = yield* Ledger
  if (amount <= 0n) return yield* Effect.fail(new DepositRefused({ message: "the first deposit is not positive: deposit more than 0" }))
  const at = yield* Effect.sync(() => new Date().toISOString())
  const opening: ReadonlyArray<Entry> = [
    { kind: "opened", at, owner },
    { kind: "deposited", at, id, amount },
  ]
  for (const entry of opening) yield* ledger.append(accountId, entry)
})

// Steps inside expressions: each runs where JavaScript runs it, in its order,
// and only on the paths that reach it (`&&`, `??`, `?:`); a step after `?.` is
// refused. `Effect.try` with an error of type `unknown`: carried, and a law
// that reads it refused. `test/steps.test.ts` asks each, and runs each.
import { Context, Effect } from "effect"
import { computation } from "../src/adapters/effect/contract.ts"

export interface StoreShape {
  readonly get: (key: string) => Effect.Effect<string | undefined>
  readonly put: (key: string, value: string) => Effect.Effect<void>
}
export class Store extends Context.Service<Store, StoreShape>()("fixtures/Store") {}
type Ops = { store: StoreShape }

/** Whether `key` holds something, read only when asked to. */
export const readIf = Effect.fn("readIf")(function* (asked: boolean, key: string) {
  const store = yield* Store
  return asked && (yield* store.get(key)) !== undefined
})
export const readsOnlyWhenAsked = computation<Ops>()(readIf, {
  ensures: {
    readsExactlyWhenAsked: ({ input: [asked, key], calls }) => (calls.length === 1 && calls.at(0)?.args[0] === key) === asked,
    falseWhenNotAsked: ({ input: [asked], output }) => asked || (output._tag === "Success" && output.value === false),
  },
})

/** What `key` holds, or else what `fallback` holds: the second read only when the first finds nothing. */
export const orElse = Effect.fn("orElse")(function* (key: string, fallback: string) {
  const store = yield* Store
  return (yield* store.get(key)) ?? (yield* store.get(fallback))
})
export const fallsBack = computation<Ops>()(orElse, {
  ensures: {
    secondOnlyWhenNothing: ({ input: [key, fallback], calls }) => {
      const first = calls.at(0)
      if (first === undefined || first.op !== "get" || first.args[0] !== key || first.outcome._tag !== "Success") return false
      const found = first.outcome.value !== undefined
      return found ? calls.length === 1 : calls.length === 2 && calls.at(1)?.args[0] === fallback
    },
  },
})

/** Writes `value` under `other` when `toOther`, else under `key`, then reads it back. */
export const putThenGet = Effect.fn("putThenGet")(function* (toOther: boolean, key: string, other: string, value: string) {
  const store = yield* Store
  const at = toOther ? yield* Effect.succeed(other) : key
  yield* store.put(at, value)
  return yield* store.get(at)
})
export const putsWhereAsked = computation<Ops>()(putThenGet, {
  ensures: {
    writesThenReadsTheSameKey: ({ input: [toOther, key, other, value], calls }) => {
      const put = calls.at(0)
      const get = calls.at(1)
      return (
        calls.length === 2 &&
        put !== undefined &&
        put.op === "put" &&
        put.args[0] === (toOther ? other : key) &&
        put.args[1] === value &&
        get !== undefined &&
        get.op === "get" &&
        get.args[0] === put.args[0]
      )
    },
  },
})

/** Copies what `from` holds into `to`, the empty string when nothing: the read runs before the write it is an argument of. */
export const copy = Effect.fn("copy")(function* (from: string, to: string) {
  const store = yield* Store
  return yield* store.put(to, (yield* store.get(from)) ?? "")
})
export const copies = computation<Ops>()(copy, {
  ensures: {
    readsThenWrites: ({ input: [from, to], calls }) => {
      const get = calls.at(0)
      const put = calls.at(1)
      if (get === undefined || get.op !== "get" || get.outcome._tag !== "Success") return false
      return calls.length === 2 && get.args[0] === from && put !== undefined && put.op === "put" && put.args[0] === to && put.args[1] === (get.outcome.value ?? "")
    },
  },
})

/** A step after `?.` runs only when what is before it is present: refused. */
export const afterOptional = Effect.fn("afterOptional")(function* (key: string, keys: ReadonlyArray<string> | undefined) {
  const store = yield* Store
  return keys?.includes((yield* store.get(key)) ?? "")
})
export const optional = computation<Ops>()(afterOptional, { ensures: { calls: ({ calls }) => calls.length <= 1 } })

/** `JSON.parse` under `Effect.try`, what it throws passed along: an error of type `unknown`. */
export const parse = (json: string) => Effect.try({ try: (): number => JSON.parse(json), catch: (err) => err })
export const parsed = computation<Ops>()(parse, {
  ensures: {
    callsNothing: ({ calls }) => calls.length === 0,
    readsTheError: ({ output }) => output._tag === "Success" || output.error !== undefined,
  },
})

/**
 * The same, its error built from what was thrown: the verifier does not read `String(err)`, and takes any error of its
 * type, of which the law is true whatever it is: vacuous.
 */
export const parseTagged = (json: string) =>
  Effect.try({ try: (): number => JSON.parse(json), catch: (err) => ({ _tag: "ParseError" as const, message: String(err) }) })
export const parsedTagged = computation<Ops>()(parseTagged, {
  ensures: { failsAsAParseError: ({ output }) => output._tag === "Success" || output.error._tag === "ParseError" },
})

/** Reads `key` and drops what it found: the read is a call all the same, though nothing reads its value. */
export const readAndDrop = Effect.fn("readAndDrop")(function* (key: string) {
  const store = yield* Store
  const _found = (yield* store.get(key)) ?? ""
  return 0n
})
export const readsWhatItDrops = computation<Ops>()(readAndDrop, {
  ensures: { readsOnce: ({ input: [key], calls }) => calls.length === 1 && calls.at(0)?.args[0] === key },
})

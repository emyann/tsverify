// Defects and the forms around them. A read that may throw, its refusals made its failures and anything else a defect
// (`instanceof` of what was thrown, narrowed to the classes it found); `Effect.exit`, `catchCause`, `failCause`, `orDie`
// and a `throw` in a generator; `mapError`, `andThen`, `as`, `asVoid`, `tap`, `suspend`; and logs, spans and metrics,
// which change nothing a law reads. `test/defects.test.ts` asks each, and runs some.
import { Cause, Context, Data, Effect, Exit, Metric } from "effect"
import { computation } from "../src/adapters/effect/contract.ts"

export class Missing extends Data.TaggedError("Missing")<{ readonly message: string }> {}
export class Conflict extends Data.TaggedError("Conflict")<{ readonly message: string }> {}
export type Refusal = Missing | Conflict
export const isRefusal = (err: unknown): err is Refusal => err instanceof Missing || err instanceof Conflict

/** A read that may throw: a refusal is its failure; anything else it threw, it dies of. */
export const tried = <A>(read: () => A): Effect.Effect<A, Refusal> =>
  Effect.try({ try: read, catch: (err) => err }).pipe(Effect.catch((err) => (isRefusal(err) ? Effect.fail(err) : Effect.die(err))))

type None = Record<never, never>

export const readCount = (read: () => number) => tried(read)
export const refusesOrDies = computation<None>()(readCount, {
  ensures: {
    failsOnlyWithARefusal: ({ output }) => output._tag !== "Failure" || output.error._tag === "Missing" || output.error._tag === "Conflict",
    neverConflicts: ({ output }) => output._tag !== "Failure" || output.error._tag !== "Conflict",
  },
})

/** 1 for a `Missing` thrown, 2 or 3 by the tag of any other refusal, which is never `Missing`; a defect else. */
export const kindOf = (read: () => number) =>
  Effect.try({ try: read, catch: (err) => err }).pipe(
    Effect.as(0),
    Effect.catch((err) =>
      err instanceof Missing ? Effect.succeed(1) : isRefusal(err) ? Effect.succeed(err._tag === "Missing" ? 3 : 2) : Effect.die(err),
    ),
  )
export const tellsTheClassesApart = computation<None>()(kindOf, {
  ensures: {
    neverThree: ({ output }) => output._tag !== "Success" || output.value !== 3,
    neverTwo: ({ output }) => output._tag !== "Success" || output.value !== 2,
  },
})

/** How a read ended, as its `Exit` says: `"read"`, or the tag of its cause's reason. */
export const endOf = (read: () => number) =>
  Effect.gen(function* () {
    const exit = yield* Effect.exit(tried(read))
    if (Exit.isSuccess(exit)) return "read"
    return exit.cause.reasons[0]?._tag ?? "none"
  })
export const exitsSay = computation<None>()(endOf, {
  ensures: {
    alwaysSucceeds: ({ output }) => output._tag === "Success",
    oneReason: ({ output }) => output._tag === "Success" && output.value !== "none" && output.value !== "Interrupt",
    neverDies: ({ output }) => output._tag === "Success" && output.value !== "Die",
  },
})

/** The read, its cause failed again as it is: the same ends. */
export const passed = (read: () => number) => tried(read).pipe(Effect.catchCause((cause) => Effect.failCause(cause)))
export const passesItsCause = computation<None>()(passed, {
  ensures: {
    failsOnlyWithARefusal: ({ output }) => output._tag !== "Failure" || output.error._tag === "Missing" || output.error._tag === "Conflict",
  },
})

/** The read, every failure a defect: through `orDie`, and through `catchCause` and `Cause.squash`. */
export const orDied = (read: () => number) => tried(read).pipe(Effect.orDie)
export const squashed = (read: () => number) => tried(read).pipe(Effect.catchCause((cause) => Effect.die(Cause.squash(cause))))
export const diesOfItsFailures = computation<None>()(orDied, { ensures: { neverFails: ({ output }) => output._tag !== "Failure" } })
export const diesOfItsCause = computation<None>()(squashed, { ensures: { neverFails: ({ output }) => output._tag !== "Failure" } })

/** `n`, or a defect where it is negative: a `throw` in a generator. */
export const nonNegative = Effect.fn("nonNegative")(function* (n: number) {
  if (n < 0) throw "negative"
  return n
})
export const throwsADefect = computation<None>()(nonNegative, {
  ensures: {
    // Proved: a run that dies is judged by no law.
    alwaysSucceeds: ({ output }) => output._tag === "Success",
    notNegative: ({ output }) => output._tag !== "Success" || !(output.value < 0),
  },
})

export interface StoreShape {
  readonly get: (key: string) => Effect.Effect<string, Missing>
  readonly put: (key: string, value: string) => Effect.Effect<void>
}
export class Store extends Context.Service<Store, StoreShape>()("fixtures/defects/Store") {}
type Ops = { store: StoreShape }

/** The length of what `key` holds, written back first; a missing key a conflict. */
export const writtenBack = Effect.fn("writtenBack")(function* (key: string) {
  const store = yield* Store
  return yield* store.get(key).pipe(
    Effect.mapError((e) => new Conflict({ message: e.message })),
    Effect.tap((v) => store.put(key, v)),
    Effect.andThen((v) => Effect.succeed(v.length)),
  )
})
export const combines = computation<Ops>()(writtenBack, {
  ensures: {
    conflictKeepsTheMessage: ({ output, calls }) => {
      const get = calls.at(0)
      return output._tag !== "Failure" || (get?.outcome._tag === "Failure" && output.error.message === get.outcome.error.message)
    },
    writesBackWhatItRead: ({ input: [key], output, calls }) => {
      const [get, put] = [calls.at(0), calls.at(1)]
      if (output._tag !== "Success") return calls.length === 1
      if (get === undefined || get.op !== "get" || get.outcome._tag !== "Success") return false
      return (
        calls.length === 2 &&
        put !== undefined &&
        put.op === "put" &&
        put.args[0] === key &&
        put.args[1] === get.outcome.value &&
        output.value === get.outcome.value.length
      )
    },
  },
})

/** A write, then a value: `andThen` of an Effect and of a value, `as`, `asVoid`, `suspend`. */
export const touched = (key: string) =>
  Effect.suspend(() =>
    Effect.gen(function* () {
      const store = yield* Store
      return yield* store.put(key, "x")
    }),
  ).pipe(Effect.andThen(Effect.succeed(2)), Effect.as(1))
export const voided = (key: string) =>
  Effect.gen(function* () {
    const store = yield* Store
    return yield* store.get(key)
  }).pipe(Effect.andThen(Effect.succeed(5)), Effect.asVoid)
export const touches = computation<Ops>()(touched, {
  ensures: { writesOnceThenOne: ({ input: [key], output, calls }) => calls.length === 1 && calls.at(0)?.args[0] === key && output._tag === "Success" && output.value === 1 },
})
export const voids = computation<Ops>()(voided, {
  ensures: { readsOnceAndNoMore: ({ input: [key], calls }) => calls.length === 1 && calls.at(0)?.op === "get" && calls.at(0)?.args[0] === key },
})

const reads = Metric.counter("reads")
/** What `key` holds, logged, counted and traced. */
export const observed = Effect.fn("observed")(function* (key: string) {
  const store = yield* Store
  yield* Effect.logInfo(`reading ${key}`)
  yield* Metric.update(reads, 1)
  return yield* store.get(key).pipe(Effect.annotateLogs({ key }), Effect.withSpan("get"))
})
export const observes = computation<Ops>()(observed, {
  ensures: { readsOnce: ({ input: [key], calls }) => calls.length === 1 && calls.at(0)?.args[0] === key },
})

const seen = { n: 0 }
/** A log whose argument changes something: refused. */
export const loud = Effect.fn("loud")(function* (key: string) {
  yield* Effect.logInfo(String(seen.n++))
  return key
})
export const logsLoudly = computation<None>()(loud, { ensures: { same: ({ input: [key], output }) => output._tag === "Success" && output.value === key } })

/** Whether `x` is a string or an object: narrowed to `{}`, which a string is too. */
const someThing = (x: unknown): x is {} => typeof x === "string" || typeof x === "object"
/** The kind of what `read` threw, where it is some thing: never read as a record, since it may be a string. */
export const thrownKind = (read: () => number) =>
  Effect.try({ try: read, catch: (err) => err }).pipe(
    Effect.as("none"),
    Effect.catch((err) => Effect.succeed(someThing(err) ? typeof err : "other")),
  )
export const keepsWhatWasThrownOpen = computation<None>()(thrownKind, {
  ensures: { neverAString: ({ output }) => output._tag !== "Success" || output.value !== "string" },
})

/** The length of what a read gave, 0 where it gave nothing: read as `string | undefined`, then as `string`. */
export const lengthOf = (read: () => string | undefined) =>
  Effect.gen(function* () {
    const v = yield* tried(read)
    if (v === undefined) return 0
    return v.length
  })
export const narrowsAGenericValue = computation<None>()(lengthOf, {
  ensures: { notNegative: ({ output }) => output._tag !== "Success" || output.value >= 0 },
})

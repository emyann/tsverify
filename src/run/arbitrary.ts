// The generators of a run, made from the shapes the parent read (`./shape.ts`), in the child alone: the verifier's
// process never imports fast-check. Strings come from the program's own literals, a few per input, so the keys a
// record is given are the ones a lookup asks for; numbers lean on the values that break code (0, -0, NaN, the
// infinities, the edges of the safe integers); collections are no longer than `--bound`.
import * as fc from "fast-check"
import type { Shape } from "./shape.ts"

/** Where a generated function keeps the calls it answered: `[args, result]`, in order. */
export const CALLS: unique symbol = Symbol("tsverify.calls")

/** A generated function: what it answered, by call. */
export type Recorded = ((...args: Array<unknown>) => unknown) & { readonly [CALLS]: Array<[Array<unknown>, unknown]> }

export const isRecorded = (v: unknown): v is Recorded => typeof v === "function" && CALLS in v

/** How many strings of the pool one input's strings are drawn from: a few, so they collide. */
const PER_INPUT = { minLength: 1, maxLength: 4 }

/** The few strings of the pool one input draws its strings from. */
export const stringSetOf = (pool: ReadonlyArray<string>): fc.Arbitrary<ReadonlyArray<string>> =>
  fc.shuffledSubarray([...(pool.length === 0 ? [""] : pool)], PER_INPUT)

/** One input's strings: from its few 9 times in 10, else any short string. */
export const stringsOf = (few: ReadonlyArray<string>): fc.Arbitrary<string> =>
  fc.oneof({ weight: 9, arbitrary: fc.constantFrom(...few) }, { weight: 1, arbitrary: fc.string({ maxLength: 4 }) })

const EDGES = [0, -0, Number.NaN, Number.POSITIVE_INFINITY, Number.NEGATIVE_INFINITY, Number.MAX_SAFE_INTEGER, -Number.MAX_SAFE_INTEGER]

const numbers: fc.Arbitrary<number> = fc.oneof(
  { weight: 3, arbitrary: fc.constantFrom(...EDGES) },
  { weight: 5, arbitrary: fc.integer({ min: -16, max: 16 }) },
  { weight: 2, arbitrary: fc.integer() },
  { weight: 2, arbitrary: fc.integer({ min: -64, max: 64 }).map((n) => n / 4) },
  { weight: 1, arbitrary: fc.double() },
)

const bigints: fc.Arbitrary<bigint> = fc.oneof(
  { weight: 5, arbitrary: fc.bigInt({ min: -16n, max: 16n }) },
  { weight: 1, arbitrary: fc.bigInt() },
)

/** A function of `returns`, the same result for the same arguments, recording each call it answers. */
const functionOf = (returns: fc.Arbitrary<unknown>): fc.Arbitrary<Recorded> =>
  fc.func(returns).map((f) => {
    const calls: Array<[Array<unknown>, unknown]> = []
    const g = (...args: Array<unknown>): unknown => {
      const r = f(...args)
      calls.push([args, r])
      return r
    }
    return Object.assign(g, { [CALLS]: calls })
  })

/** The values of `shape`, strings drawn from `strings`, collections at most `bound` long. */
export const arbitraryOf = (shape: Shape, strings: fc.Arbitrary<string>, bound: number): fc.Arbitrary<unknown> => {
  const of = (s: Shape): fc.Arbitrary<unknown> => arbitraryOf(s, strings, bound)
  switch (shape.kind) {
    case "literal":
      return fc.constant(shape.value)
    case "bigint-literal":
      return fc.constant(BigInt(shape.value))
    case "boolean":
      return fc.boolean()
    case "number":
      return numbers
    case "bigint":
      return bigints
    case "date":
      return fc.date({ noInvalidDate: true })
    case "string":
      return strings
    case "null":
      return fc.constant(null)
    case "undefined":
      return fc.constant(undefined)
    case "union":
      return fc.oneof(...shape.of.map(of))
    case "record": {
      const fields = Object.fromEntries(Object.entries(shape.fields).map(([k, s]) => [k, of(s)]))
      const required = Object.keys(shape.fields).filter((k) => !shape.optional.includes(k))
      return fc.record(fields, { requiredKeys: required, noNullPrototype: true })
    }
    case "array":
      return fc.array(of(shape.of), { maxLength: bound })
    case "tuple": {
      const fixed = fc.tuple(...shape.of.map(of))
      if (shape.rest === undefined) return fixed
      return fc.tuple(fixed, fc.array(of(shape.rest), { maxLength: bound })).map(([head, rest]): Array<unknown> => [...head, ...rest])
    }
    case "dictionary":
      return fc.dictionary(strings, of(shape.of), { maxKeys: bound, noNullPrototype: true })
    case "map":
      return fc.array(fc.tuple(of(shape.key), of(shape.value)), { maxLength: bound }).map((es) => new Map(es))
    case "set":
      return fc.array(of(shape.of), { maxLength: bound }).map((xs) => new Set(xs))
    case "function":
      return functionOf(of(shape.returns))
  }
}

/** One draw of a run: the arguments, and for each law that reads a result, a free result of its shape. */
export interface Drawn {
  readonly args: Array<unknown>
  readonly free: ReadonlyArray<unknown>
}

/**
 * The draws of a run: each input's few strings drawn first, then its arguments and the free results from them, so the
 * keys a record holds are often the names it is asked for.
 */
export const drawsOf = (
  params: ReadonlyArray<Shape>,
  outputs: ReadonlyArray<Shape | undefined>,
  pool: ReadonlyArray<string>,
  bound: number,
): fc.Arbitrary<Drawn> =>
  stringSetOf(pool).chain((few) => {
    const strings = stringsOf(few)
    return fc
      .tuple(
        fc.tuple(...params.map((s) => arbitraryOf(s, strings, bound))),
        fc.tuple(...outputs.map((s) => (s === undefined ? fc.constant(undefined) : arbitraryOf(s, strings, bound)))),
      )
      .map(([args, free]): Drawn => ({ args, free }))
  })

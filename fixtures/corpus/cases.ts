// The corpus: problems published with Z3 (its guide, *Programming Z3*, *SAT/SMT by Example*, the Dafny and Verus
// tutorials, Hacker's Delight), each ported to a function and its laws. Beside each contract, what JavaScript makes of
// each law, from the source and checked by running it: the truth tsverify's verdicts are held to by
// `test/corpus.test.ts`. A law tsverify cannot judge yet carries its gap, so a gap closed is a test to update.

/** Whether a law holds on every input its `requires` allows, as JavaScript runs the function. */
export type Truth = "valid" | "invalid"
/**
 * What tsverify gives today in place of a verdict: refused (not read), or read and not judged, `bounded` or `unknown`,
 * which of the two depending on whether the solver ran out of work, and so held as one.
 */
export type Gap = "refused" | "bounded" | "unknown"

export interface Case {
  /** The page the problem is from. */
  readonly source: string
  /** Each law's truth, and the gap tsverify has on it today, where it has one. */
  readonly laws: Readonly<Record<string, Truth | readonly [Truth, Gap]>>
  /** Inputs the function is run on: a valid law holds on each, and so must every law proved. */
  readonly samples: ReadonlyArray<ReadonlyArray<unknown>>
  /** For an invalid law, an input that breaks it: the source's, where it gives one. */
  readonly witnesses?: Readonly<Record<string, ReadonlyArray<unknown>>>
}

/** Every combination of one value from each axis, in order. */
export const grid = (...axes: ReadonlyArray<ReadonlyArray<unknown>>): ReadonlyArray<ReadonlyArray<unknown>> =>
  axes.reduce<ReadonlyArray<ReadonlyArray<unknown>>>((rows, axis) => rows.flatMap((r) => axis.map((v) => [...r, v])), [[]])

/** Bigints around the places integer code goes wrong: signs, small divisors, a 32-bit edge. */
export const INTS: ReadonlyArray<bigint> = [-2147483648n, -10n, -9n, -4n, -1n, 0n, 1n, 3n, 4n, 9n, 10n, 2147483647n]

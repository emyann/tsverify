// What the verifier may assume of the lodash functions the examples call: a pack,
// as Verus's `vstd` holds the specifications of Rust's standard library. A spec
// brings it in force by importing it. Nothing here is proved: each law is
// trusted, and `test/lodash.test.ts` runs every one against the real lodash.
import { clamp, uniq } from "lodash-es"
import { assume } from "@emyann/tsverify"

/** `uniq` on strings: the same strings, none added, none lost, and never more of them. */
export const uniqOfStrings = assume<[xs: ReadonlyArray<string>], string[]>(uniq, {
  pure: true,
  ensures: {
    emptyExactlyWhenEmpty: ({ input: [xs], output }) => (output.length === 0) === (xs.length === 0),
    noLonger: ({ input: [xs], output }) => output.length <= xs.length,
    keepsEvery: ({ input: [xs], output }) => xs.every((x) => output.includes(x)),
    addsNothing: ({ input: [xs], output }) => output.every((x) => xs.includes(x)),
  },
})

/**
 * `clamp(n, lower, upper)` on numbers. Within the bounds when they are in order and `n` is a number; `n` itself when
 * it fits. Not more: lodash returns `NaN` for `NaN`, and `lower` when the bounds are reversed.
 */
export const clampOfNumbers = assume<[n: number, lower: number, upper: number], number>(clamp, {
  pure: true,
  ensures: {
    within: ({ input: [n, lower, upper], output }) => !(lower <= upper && n === n) || (lower <= output && output <= upper),
    keepsWhatFits: ({ input: [n, lower, upper], output }) => !(lower <= n && n <= upper) || output === n,
  },
})

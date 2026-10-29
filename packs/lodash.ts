// What the verifier may assume of the lodash functions the pilots call: a pack,
// as Verus's `vstd` holds the specifications of Rust's standard library. A spec
// brings it in force by importing it. Nothing here is proved: each law is
// trusted, and `test/lodash.test.ts` runs every one against the real lodash.
import { clamp, uniq } from "lodash-es"
import { assume } from "../src/contract.ts"

/** `uniq` on strings: the same strings, none added, none lost, and never more of them. */
export const uniqOfStrings = assume<[xs: ReadonlyArray<string>], string[]>(uniq, {
  pure: true,
  ensures: {
    emptyExactlyWhenEmpty: (xs, out) => (out.length === 0) === (xs.length === 0),
    noLonger: (xs, out) => out.length <= xs.length,
    keepsEvery: (xs, out) => xs.every((x) => out.includes(x)),
    addsNothing: (xs, out) => out.every((x) => xs.includes(x)),
  },
})

/**
 * `clamp(n, lower, upper)` on numbers. Within the bounds when they are in order and `n` is a number; `n` itself when
 * it fits. Not more: lodash returns `NaN` for `NaN`, and `lower` when the bounds are reversed.
 */
export const clampOfNumbers = assume<[n: number, lower: number, upper: number], number>(clamp, {
  pure: true,
  ensures: {
    within: (n, lower, upper, out) => !(lower <= upper && n === n) || (lower <= out && out <= upper),
    keepsWhatFits: (n, lower, upper, out) => !(lower <= n && n <= upper) || out === n,
  },
})

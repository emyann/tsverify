// Laws that say something of `sign`, and laws that say nothing: each vacuous one
// is proved, and would be proved of any function with this signature.
import { contract } from "@emyann/tsverify"

export function sign(n: bigint): "neg" | "zero" | "pos" {
  return n < 0n ? "neg" : n === 0n ? "zero" : "pos"
}

export const signed = contract(sign, {
  ensures: {
    /** Says something: a result of `zero` anywhere but at 0 would break it. */
    zeroOnlyAtZero: ({ input: [n], output }) => output !== "zero" || n === 0n,
    /** Over the input alone: no result enters it. */
    squareNotNegative: ({ input: [n] }) => n * n >= 0n,
    /** Its condition is never met: `n < n` is false for every `n`. */
    neverAsked: ({ input: [n], output }) => !(n < n) || output === "neg",
  },
})

/** Every input positive: a law that only constrains non-positive inputs says nothing. */
export const positive = contract(sign, {
  requires: ({ input: [n] }) => n > 0n,
  ensures: {
    pos: ({ output }) => output === "pos",
    negativeIsNeg: ({ input: [n], output }) => n >= 0n || output === "neg",
  },
})

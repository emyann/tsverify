// `Math.max`, `Math.min`, `Math.abs`, `Math.trunc`, `Object.is`, and the sign of zero: `NaN` where an argument is,
// `-0` where IEEE 754 gives it, and `Object.is` telling it from `0`. `test/signs.test.ts` asks each, runs each, and
// plants a bug in each.
import { contract } from "../src/contract.ts"

/** `x` kept between `lo` and `hi`. */
export function clamp(x: number, lo: number, hi: number): number {
  return Math.min(Math.max(x, lo), hi)
}
export const clamped = contract(clamp, {
  requires: ({ input: [x, lo, hi] }) => !Number.isNaN(x) && !Number.isNaN(lo) && !Number.isNaN(hi) && lo <= hi,
  ensures: {
    inside: ({ input: [, lo, hi], output }) => lo <= output && output <= hi,
    itselfInside: ({ input: [x, lo, hi], output }) => !(lo <= x && x <= hi) || output === x,
  },
})

/** How far apart two whole numbers are. */
export function distance(a: number, b: number): number {
  return Math.abs(a - b)
}
export const distanceApart = contract(distance, {
  requires: ({ input: [a, b] }) => Number.isSafeInteger(a) && Number.isSafeInteger(b) && Math.abs(a) < 1099511627776 && Math.abs(b) < 1099511627776,
  ensures: {
    notNegative: ({ output }) => output >= 0 && !Object.is(output, -0),
    zeroIffEqual: ({ input: [a, b], output }) => (output === 0) === (a === b),
  },
})

/** Whether two numbers are the same value: `NaN` is itself, `-0` is not `0`. */
export function same(a: number, b: number): boolean {
  return Object.is(a, b)
}
export const sameValue = contract(same, {
  ensures: {
    nanIsItself: ({ input: [a, b], output }) => !(Number.isNaN(a) && Number.isNaN(b)) || output,
    zerosApart: ({ input: [a, b], output }) => !(Object.is(a, 0) && Object.is(b, -0)) || !output,
    likeEqualElsewhere: ({ input: [a, _b], output }) => a === 0 || Number.isNaN(a) || output === (a === _b),
  },
})

/** `-x`, its sign flipped, `0`'s too. */
export function negated(x: number): number {
  return -x
}
export const signFlipped = contract(negated, {
  ensures: { zeroFlips: ({ input: [x], output }) => x !== 0 || Object.is(output, -0) === Object.is(x, 0) },
})

/** The whole part of `x`, toward 0. */
export function wholePart(x: number): number {
  return Math.trunc(x)
}
export const towardZero = contract(wholePart, {
  ensures: {
    noFarther: ({ input: [x], output }) => !Number.isFinite(x) || Math.abs(output) <= Math.abs(x),
    negZeroBetween: ({ input: [x], output }) => !(x > -1 && x < 0) || Object.is(output, -0),
  },
})

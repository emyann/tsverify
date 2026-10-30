// Bitwise operators on `number`, as JavaScript computes them on 32-bit integers: `|`, `&`, `^`, `~`, `<<`, `>>`, `>>>`
// and their compound forms. `test/bitwise.test.ts` asks each, runs each, and plants a bug in each.
import { contract } from "../src/contract.ts"

const isInt32 = (x: number): boolean => x === (x | 0)

/** The middle of two indexes, without the overflow of `(lo + hi) / 2` in 32 bits. */
export function midIndex(lo: number, hi: number): number {
  return (lo + hi) >>> 1
}
export const midBetween = contract(midIndex, {
  requires: (lo, hi) => Number.isInteger(lo) && Number.isInteger(hi) && 0 <= lo && lo <= hi && hi < 2 ** 31,
  ensures: { between: (lo, hi, out) => lo <= out && out <= hi },
})

/** Whether a 32-bit integer is even, by its low bit. */
export function isEven(n: number): boolean {
  return (n & 1) === 0
}
export const evenByLowBit = contract(isEven, {
  requires: (n) => isInt32(n),
  ensures: { halvesBack: (n, out) => out === ((n >> 1) * 2 === n) },
})

/** The `k`th byte of `x`, from the low end. */
export function byteAt(x: number, k: number): number {
  return (x >>> (8 * k)) & 0xff
}
export const aByte = contract(byteAt, {
  requires: (_x, k) => k === 0 || k === 1 || k === 2 || k === 3,
  ensures: { byte: (_x, _k, out) => 0 <= out && out < 256, lowFirst: (x, k, out) => k !== 0 || out === (x & 255) },
})

/** The flag of bit `n`. */
export function flag(n: number): number {
  return 1 << n
}
export const aFlag = contract(flag, {
  requires: (n) => Number.isInteger(n) && 0 <= n && n < 31,
  ensures: { positive: (_n, out) => out > 0, onlyItsBit: (n, out) => out >>> n === 1 },
})

/** `x` as a signed 32-bit integer. */
export function toInt32(x: number): number {
  return x | 0
}
export const int32 = contract(toInt32, {
  ensures: {
    inRange: (_x, out) => -2147483648 <= out && out <= 2147483647,
    wholeKept: (x, out) => !(Number.isInteger(x) && -2147483648 <= x && x <= 2147483647) || out === x,
  },
})

/** `|v|` without a branch, by the sign mask. */
export function abs32(v: number): number {
  const sign = v >> 31
  return (v ^ sign) - sign
}
export const branchless = contract(abs32, {
  requires: (v) => isInt32(v) && v > -2147483648,
  ensures: { isAbs: (v, out) => out === (v < 0 ? -v : v) },
})

/** Two numbers mixed, the result shifted up one: its low bit clear. */
export function mixed(a: number, b: number): number {
  let h = a | 0
  h ^= b
  h <<= 1
  return h
}
export const mixedEven = contract(mixed, {
  ensures: { lowBitClear: (_a, _b, out) => (out & 1) === 0, notOfOnes: (_a, _b, out) => ~out !== 0 },
})

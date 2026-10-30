// Arrays at a computed index, and the whole-number arithmetic that makes the index: a read `xs[i]` (missing outside
// the array), `.at(i)` (negative from the end), a write `b[i] = …` (an obligation that it lands inside), and `+`, `-`
// on `number` (an obligation that it is exact). `test/indexes.test.ts` asks each, runs each, and plants a bug in each.
import { contract, invariant } from "../src/contract.ts"

/** The index of a largest element, the first one; -1 when there is none. */
export function largestAt(xs: ReadonlyArray<bigint>): number {
  if (xs.length === 0) return -1
  let best = 0
  for (let i = 1; i < xs.length; i++) {
    invariant(() => Number.isInteger(best) && 0 <= best && best < i && i <= xs.length)
    invariant(() => xs.every((x, j) => j >= i || x <= (xs[best] ?? x)))
    if ((xs[i] ?? 0n) > (xs[best] ?? 0n)) best = i
  }
  return best
}
export const theLargest = contract(largestAt, {
  ensures: {
    noneWhenEmpty: (xs, out) => xs.length > 0 || out === -1,
    inside: (xs, out) => xs.length === 0 || (Number.isInteger(out) && 0 <= out && out < xs.length),
    noneLarger: (xs, out) => xs.every((x) => x <= (xs[out] ?? x)),
  },
})

/** The elements in the other order, written one by one into a copy. */
export function reversed(xs: ReadonlyArray<bigint>): Array<bigint> {
  const b = [...xs]
  const n = xs.length
  for (let i = 0; i < n; i++) {
    invariant(() => i <= n && b.length === n)
    // Filled from the end: after `i` steps, the last `i` places hold the first `i` elements, mirrored.
    invariant(() => b.every((y, p) => p < n - i || y === xs[n - 1 - p]))
    b[n - 1 - i] = xs[i] ?? 0n
  }
  return b
}
export const reversesIt = contract(reversed, {
  ensures: {
    sameLength: (xs, out) => out.length === xs.length,
    mirrored: (xs, out) => out.every((y, j) => y === xs[xs.length - 1 - j]),
  },
})

/** The element `.at(i)` names: counted from the end when `i` is negative. */
export function nth(xs: ReadonlyArray<string>, i: number): string | undefined {
  return xs.at(i)
}
export const atCounts = contract(nth, {
  ensures: {
    fromTheStart: (xs, i, out) => !(Number.isInteger(i) && 0 <= i && i < xs.length) || out === xs[i],
    fromTheEnd: (xs, i, out) => !(Number.isInteger(i) && -xs.length <= i && i < 0) || out === xs[xs.length + i],
    missingOutside: (xs, i, out) => !(Number.isInteger(i) && (i >= xs.length || i < -xs.length)) || out === undefined,
  },
})

/** One more than `i`: exact for a whole number short of 2^53. */
export function next(i: number): number {
  return i + 1
}
export const nextOfAny = contract(next, { ensures: { larger: (i, out) => out > i } })
export const nextOfWhole = contract(next, {
  requires: (i) => Number.isSafeInteger(i) && i < 9007199254740991,
  ensures: { larger: (i, out) => out > i, whole: (_i, out) => Number.isInteger(out) },
})

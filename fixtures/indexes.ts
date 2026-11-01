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
    noneWhenEmpty: ({ input: [xs], output }) => xs.length > 0 || output === -1,
    inside: ({ input: [xs], output }) => xs.length === 0 || (Number.isInteger(output) && 0 <= output && output < xs.length),
    noneLarger: ({ input: [xs], output }) => xs.every((x) => x <= (xs[output] ?? x)),
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
    sameLength: ({ input: [xs], output }) => output.length === xs.length,
    mirrored: ({ input: [xs], output }) => output.every((y, j) => y === xs[xs.length - 1 - j]),
  },
})

/** The element `.at(i)` names: counted from the end when `i` is negative. */
export function nth(xs: ReadonlyArray<string>, i: number): string | undefined {
  return xs.at(i)
}
export const atCounts = contract(nth, {
  ensures: {
    fromTheStart: ({ input: [xs, i], output }) => !(Number.isInteger(i) && 0 <= i && i < xs.length) || output === xs[i],
    fromTheEnd: ({ input: [xs, i], output }) => !(Number.isInteger(i) && -xs.length <= i && i < 0) || output === xs[xs.length + i],
    missingOutside: ({ input: [xs, i], output }) => !(Number.isInteger(i) && (i >= xs.length || i < -xs.length)) || output === undefined,
  },
})

/** One more than `i`: exact for a whole number short of 2^53. */
export function next(i: number): number {
  return i + 1
}
export const nextOfAny = contract(next, { ensures: { larger: ({ input: [i], output }) => output > i } })
export const nextOfWhole = contract(next, {
  requires: ({ input: [i] }) => Number.isSafeInteger(i) && i < 9007199254740991,
  ensures: { larger: ({ input: [i], output }) => output > i, whole: ({ output }) => Number.isInteger(output) },
})

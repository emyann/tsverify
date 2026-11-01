// Loops, read through their invariants, and the rest of the proof code: an
// assert, a lemma. Each contract here shows one outcome; `test/loops.test.ts`
// asks each.
import { assert, contract, invariant, lemma } from "../src/contract.ts"

const nonNegative = ({ input: [xs] }: { readonly input: readonly [ReadonlyArray<bigint>] }) => xs.every((x) => x >= 0n)

/** A sum, and what it keeps: never negative while every element is not. */
export function sum(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n
  for (const x of xs) {
    invariant(() => total >= 0n)
    total += x
  }
  return total
}
export const sumNonNegative = contract(sum, { requires: nonNegative, ensures: { nonNegative: ({ output }) => output >= 0n } })

/** The same loop with no invariant written: the verifier guesses the law of the elements gone through, `total >= 0n`, and proves it. */
export function sumBare(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n
  for (const x of xs) total += x
  return total
}
export const sumBareNonNegative = contract(sumBare, { requires: nonNegative, ensures: { nonNegative: ({ output }) => output >= 0n } })

/**
 * No invariant written, and the law's guess is wrong: true of the result, not of what the loop has built (0 on entry).
 * It is dropped, and the law is bounded, never proved through it.
 */
export function sumPlusOne(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n
  for (const x of xs) total += x
  total += 1n
  return total
}
export const sumPlusOneAtLeastOne = contract(sumPlusOne, { requires: nonNegative, ensures: { atLeastOne: ({ output }) => output >= 1n } })

/** An invariant an iteration does not keep: the search side finds the input that breaks it. */
export function sumCapped(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n
  for (const x of xs) {
    invariant(() => total < 10n)
    total += x
  }
  return total
}
export const sumCappedNonNegative = contract(sumCapped, { requires: nonNegative, ensures: { nonNegative: ({ output }) => output >= 0n } })

/**
 * The largest element, starting from the first: an invariant written for one law, the other left to a guess. Writing
 * the first does not lose the second.
 */
export function largestOf(xs: ReadonlyArray<bigint>): bigint {
  let best = xs.at(0) ?? 0n
  for (const x of xs) {
    invariant(() => xs.length === 0 || xs.includes(best))
    if (x > best) best = x
  }
  return best
}
export const largestOneOfThem = contract(largestOf, {
  ensures: {
    noneLarger: ({ input: [xs], output }) => xs.every((x) => x <= output),
    oneOfThem: ({ input: [xs], output }) => xs.length === 0 || xs.includes(output),
  },
})

/** An invariant false before the loop. */
export function sumFromNothing(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n
  for (const x of xs) {
    invariant(() => total > 0n)
    total += x
  }
  return total
}
export const sumFromNothingNonNegative = contract(sumFromNothing, { requires: nonNegative, ensures: { nonNegative: ({ output }) => output >= 0n } })

/** The largest element, and an invariant over the elements done: `i` of them. */
export function maxOf(xs: ReadonlyArray<bigint>): bigint {
  let best = 0n
  for (const x of xs) {
    invariant((i) => xs.slice(0, i).every((y) => y <= best))
    if (x > best) best = x
  }
  return best
}
export const maxIsAnUpperBound = contract(maxOf, { ensures: { aboveEvery: ({ input: [xs], output }) => xs.every((x) => x <= output) } })

/** A list built in a loop: never longer than what it was built from. */
export function positives(xs: ReadonlyArray<bigint>): number {
  const out: Array<bigint> = []
  for (const x of xs) {
    invariant((i) => out.length <= i)
    if (x > 0n) out.push(x)
  }
  return out.length
}
export const positivesNoMore = contract(positives, { ensures: { noMore: ({ input: [xs], output }) => output <= xs.length } })

/** An early return, and what the loop knows when it does not return. */
export function firstNegative(xs: ReadonlyArray<bigint>): bigint | undefined {
  for (const x of xs) {
    invariant((i) => xs.slice(0, i).every((y) => y >= 0n))
    if (x < 0n) return x
  }
  return undefined
}
export const firstNegativeIsNegative = contract(firstNegative, {
  ensures: {
    negative: ({ output }) => output === undefined || output < 0n,
    noneWhenNone: ({ input: [xs], output }) => output !== undefined || xs.every((x) => x >= 0n),
  },
})

/**
 * False: `[-1n]` gives `-1n`. What the loop's invariant says at its end holds only if it gets there; read on every path
 * that entered the loop, it once made every element non-negative, and this law proved.
 */
export const neverFindsOne = contract(firstNegative, { ensures: { neverFinds: ({ output }) => output === undefined } })

/** A `while` loop left early by a `return`: the first `k` below `n` whose double passes `limit`, or -1. */
export function firstDoubleAbove(limit: bigint, n: bigint): bigint {
  let k = 0n
  while (k < n) {
    invariant(() => k >= 0n && (k <= n || k === 0n) && (k === 0n || (k - 1n) + (k - 1n) <= limit))
    if (k + k > limit) return k
    k += 1n
  }
  return -1n
}
export const doubleAbove = contract(firstDoubleAbove, {
  ensures: {
    found: ({ input: [limit], output }) => output === -1n || output + output > limit,
    /** False: `limit` 0 and `n` 2 give 1. The same trap as `neverFindsOne`, in a `while` loop. */
    neverFinds: ({ output }) => output === -1n,
  },
})

/** A `while` loop over its own variable. */
export function countTo(n: bigint): bigint {
  let k = 0n
  while (k < n) {
    invariant(() => k >= 0n && (k <= n || k === 0n))
    k += 1n
  }
  return k
}
export const countReaches = contract(countTo, { ensures: { reaches: ({ input: [n], output }) => output === (n > 0n ? n : 0n) } })

/** An assert: proved where the precondition gives it, broken where nothing does. */
export function halve(n: bigint): bigint {
  assert(() => n >= 0n)
  return n
}
export const halveGiven = contract(halve, { requires: ({ input: [n] }) => n >= 0n, ensures: { same: ({ input: [n], output }) => output === n } })
export const halveAnything = contract(halve, { ensures: { same: ({ input: [n], output }) => output === n } })

/** A lemma, proved once, used where a product is. */
export const productNonNegative = lemma((a: bigint, b: bigint) => a * b >= 0n, { requires: (a, b) => a >= 0n && b >= 0n })
export function area(w: bigint, h: bigint): bigint {
  productNonNegative(w, h)
  return w * h
}
export const areaNonNegative = contract(area, { requires: ({ input: [w, h] }) => w >= 0n && h >= 0n, ensures: { nonNegative: ({ output }) => output >= 0n } })
export const areaOfAnything = contract(area, { ensures: { nonNegative: ({ output }) => output >= 0n } })

/** A false lemma: the law that leans on it is not proved, and the lemma's counterexample is given. */
export const everyNumberPositive = lemma((a: bigint) => a > 0n)
export function trusting(a: bigint): bigint {
  everyNumberPositive(a)
  return a
}
export const leansOnAFalseLemma = contract(trusting, { ensures: { positive: ({ output }) => output > 0n } })

// Arrays and sequences: a write read back, two sequences that never meet, binary search and bubble sort.
import { contract, invariant } from "../../src/contract.ts"
import type { Case } from "./cases.ts"

// arr-store (a): a write read back.
export function readBack(a: Array<number>, x: number, y: number): number | undefined {
  const b = [...a]
  b[x] = 3
  return b[y - 2]
}
export const storeThenSelect = contract(readBack, {
  requires: ({ input: [a, x, y] }) => Number.isInteger(x) && 0 <= x && x < a.length && y === x + 2,
  ensures: { readsTheWrite: ({ input: [, x, y], output }) => output === y - x + 1 },
})

// pz3-seq-unit: `s ++ [2]` is never `[1] ++ s`.
export function ends(s: ReadonlyArray<bigint>) {
  return { a: [...s, 2n], b: [1n, ...s] }
}
export const neverEqual = contract(ends, {
  ensures: { differ: ({ output }) => !(output.a.length === output.b.length && output.a.every((e, i) => e === output.b[i])) },
})

// vf-dafny-binary-search: Dafny's binary search, its midpoint on whole numbers, with Dafny's invariants; `sorted` as
// Dafny writes it, every pair in order (Verus's guide shows the adjacent-pairs form failing, wanting induction).
const sorted = (a: ReadonlyArray<bigint>): boolean => a.every((x, j) => a.every((y, k) => j >= k || x <= y))
export function binarySearch(a: ReadonlyArray<bigint>, value: bigint): number {
  let low = 0
  let high = a.length
  while (low < high) {
    // Dafny's `int` says the first two of these by its type.
    invariant(() => Number.isInteger(low) && Number.isInteger(high) && 0 <= low && low <= high && high <= a.length)
    invariant(() => a.every((x, i) => (low <= i && i < high) || x !== value))
    const mid = Math.floor((low + high) / 2)
    const at = a[mid] ?? value
    if (at < value) low = mid + 1
    else if (value < at) high = mid
    else return mid
  }
  return -1
}
export const binarySearchFinds = contract(binarySearch, {
  requires: ({ input: [a] }) => sorted(a),
  ensures: {
    foundIsThere: ({ input: [a, value], output }) => output < 0 || (output < a.length && a[output] === value),
    missingIsAbsent: ({ input: [a, value], output }) => output >= 0 || !a.includes(value),
  },
})

// zg-bubble-sort-bmc: one bubble pass does not sort; a full bubble sort does.
const isSorted = (a: ReadonlyArray<bigint>): boolean => a.every((x, j) => a.every((y, k) => j >= k || x <= y))
export function bubblePass(a: ReadonlyArray<bigint>): Array<bigint> {
  const b = [...a]
  for (let i = 0; i + 1 < b.length; i++) {
    invariant(() => i <= b.length)
    const x = b[i] ?? 0n
    const y = b[i + 1] ?? 0n
    if (x > y) {
      b[i] = y
      b[i + 1] = x
    }
  }
  return b
}
export const onePassSorts = contract(bubblePass, { ensures: { sorted: ({ output }) => isSorted(output) } })
export function bubbleSort(a: ReadonlyArray<bigint>): Array<bigint> {
  const b = [...a]
  for (let n = b.length; n > 1; n--) {
    // What is at `n` and after is in place: no element before it is larger.
    invariant(() => b.every((x, j) => b.every((y, k) => j >= k || k < n || x <= y)))
    for (let i = 0; i + 1 < n; i++) {
      invariant(() => i < n)
      invariant(() => b.every((x, j) => b.every((y, k) => j >= k || k < n || x <= y)))
      // The largest so far has been carried up to `i`.
      invariant(() => b.every((x, j) => j > i || x <= (b[i] ?? x)))
      const x = b[i] ?? 0n
      const y = b[i + 1] ?? 0n
      if (x > y) {
        b[i] = y
        b[i + 1] = x
      }
    }
  }
  return b
}
export const bubbleSortSorts = contract(bubbleSort, {
  ensures: { sorted: ({ output }) => isSorted(output), sameLength: ({ input: [a], output }) => output.length === a.length },
})

const ARRAYS: ReadonlyArray<ReadonlyArray<bigint>> = [[], [1n], [2n, 1n], [3n, 2n, 1n], [1n, 2n, 3n], [2n, 2n, 1n], [5n, -1n, 3n, 0n]]
export const cases: Readonly<Record<string, Case>> = {
  storeThenSelect: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-logical-interface",
    laws: { readsTheWrite: "valid" },
    samples: [[[0, 0, 0, 0], 0, 2], [[0, 0, 0, 0], 3, 5], [[7], 0, 2]],
  },
  neverEqual: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-sequences-and-strings",
    laws: { differ: ["valid", "bounded"] },
    samples: ARRAYS.map((s) => [s]).concat([[[1n, 1n]], [[2n, 2n]]]),
  },
  binarySearchFinds: {
    source: "https://dafny.org/latest/OnlineTutorial/guide",
    laws: { foundIsThere: "valid", missingIsAbsent: "valid" },
    samples: [[[], 1n], [[1n], 1n], [[1n, 3n, 5n], 3n], [[1n, 3n, 5n], 4n], [[1n, 1n, 2n], 1n], [[1n, 2n, 3n, 4n], 4n]],
  },
  onePassSorts: {
    source: "https://github.com/Z3Prover/z3/blob/master/examples/python/bounded%20model%20checking/bubble_sort.py",
    laws: { sorted: "invalid" },
    samples: [],
    witnesses: { sorted: [[3n, 2n, 1n]] },
  },
  bubbleSortSorts: {
    source: "https://github.com/Z3Prover/z3/blob/master/examples/python/bounded%20model%20checking/bubble_sort.py",
    laws: { sorted: "valid", sameLength: "valid" },
    samples: ARRAYS.map((a) => [a]),
  },
}

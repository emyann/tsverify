// Fixed-width code against an unbounded spec: Verus's `loop_triangle`, its u32 sum wrapped, written with `%`.
import { contract, invariant, lemma } from "../../src/contract.ts"
import type { Case } from "./cases.ts"

const U32 = 4294967296n
/** Verus's `triangle_is_monotonic`: a larger n has a larger triangle number. */
export const triangleIsMonotonic = lemma((i: bigint, j: bigint) => i * (i + 1n) <= j * (j + 1n), {
  requires: (i, j) => 0n <= i && i <= j,
})
// vf-verus-loop-triangle: the sum of 1..n in a u32, right while the triangle number fits.
export function loopTriangle(n: bigint): bigint {
  let sum = 0n
  let idx = 0n
  while (idx < n) {
    invariant(() => 0n <= idx && idx <= n && n <= 92681n && sum === (idx * (idx + 1n)) / 2n)
    idx = idx + 1n
    // As Verus's guide does: the new sum fits, since this triangle number is at most the 92681st.
    triangleIsMonotonic(idx, 92681n)
    sum = (sum + idx) % U32
  }
  return sum
}
export const triangleWhileItFits = contract(loopTriangle, {
  requires: ({ input: [n] }) => n >= 0n && n <= 92681n,
  ensures: { isTriangle: ({ input: [n], output }) => output === (n * (n + 1n)) / 2n },
})
export function loopTriangleUnbounded(n: bigint): bigint {
  let sum = 0n
  let idx = 0n
  while (idx < n) {
    idx = idx + 1n
    sum = (sum + idx) % U32
  }
  return sum
}
export const triangleAnyN = contract(loopTriangleUnbounded, {
  requires: ({ input: [n] }) => n >= 0n,
  ensures: { isTriangle: ({ input: [n], output }) => output === (n * (n + 1n)) / 2n },
})

export const cases: Readonly<Record<string, Case>> = {
  triangleWhileItFits: {
    source: "https://verus-lang.github.io/verus/guide/while.html",
    laws: { isTriangle: "valid" },
    samples: [[0n], [1n], [2n], [10n], [1000n], [92681n]],
  },
  triangleAnyN: {
    source: "https://verus-lang.github.io/verus/guide/while.html",
    laws: { isTriangle: ["invalid", "bounded"] },
    samples: [[0n], [1n], [10n]],
    witnesses: { isTriangle: [92682n] },
  },
}

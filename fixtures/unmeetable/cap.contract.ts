// Laws no result can keep at some input: no code could keep them there, and the verdict blames the spec, not the code.
import { contract } from "@emyann/tsverify"

export function cap(n: bigint): bigint {
  return n > 10n ? 10n : n
}

/** Above 10, no result is both at most 10 and at least the input: `cap` keeps the first, and no code could keep both. */
export const capped = contract(cap, {
  ensures: {
    atMostTen: ({ output }) => output <= 10n,
    atLeastTheInput: ({ input: [n], output }) => output >= n,
  },
})

export function uncapped(n: bigint): bigint {
  return n
}

/** Wrong code under a law some result keeps everywhere: an ordinary counterexample. */
export const leftUncapped = contract(uncapped, {
  ensures: { atMostTen: ({ output }) => output <= 10n },
})

export function zero(_n: bigint): bigint {
  return 0n
}

/** One law alone that refuses every result wherever its condition holds. */
export const impossible = contract(zero, {
  ensures: { aboveAndBelow: ({ input: [n], output }) => n <= 0n || (output > n && output < n) },
})

// A function that throws at one input: that input is skipped and counted, never a counterexample.
import { contract } from "@emyann/tsverify"

export function tenOver(x: bigint): bigint {
  return 10n / x
}

export const divided = contract(tenOver, { ensures: { atZero: ({ input: [x], output }) => x !== 0n || output === 1n } })

// A spec and its implementation in one module, the spec not exported: a run reads the spec through the loader.
import { type Implementation, spec } from "@emyann/tsverify"

const halfSpec = spec<(n: bigint) => bigint>({
  ensures: {
    /** Kept: half is never more than the whole, for a whole of 0 or more. */
    notMore: ({ input: [n], output }) => n < 0n || output <= n,
    /** Broken at every odd number. */
    twiceIsWhole: ({ input: [n], output }) => output * 2n === n,
  },
})

export const half: Implementation<typeof halfSpec> = (n) => n / 2n

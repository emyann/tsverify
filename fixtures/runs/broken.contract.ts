// A pure function with one law a run breaks and one it keeps: the broken one comes back from running, before any proof.
import { contract } from "@emyann/tsverify"

/** Ten a piece, nine a piece past ten. */
export function price(qty: number): number {
  return qty > 10 ? qty * 9 : qty * 10
}

export const priced = contract(price, {
  requires: ({ input: [qty] }) => Number.isInteger(qty) && qty >= 0 && qty <= 1000,
  ensures: {
    /** Kept: no count costs less than nothing. */
    notNegative: ({ output }) => output >= 0,
    /** Broken past ten: the price there is nine a piece. */
    tenEach: ({ input: [qty], output }) => output === qty * 10,
  },
})

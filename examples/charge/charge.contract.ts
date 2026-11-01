// What charging an amount against a balance must leave: the spec, written
// before the code. `charge.ts` takes it as its type.
import { spec } from "@emyann/tsverify"

export const chargeSpec = spec<(balance: bigint, amount: bigint) => bigint>({
  requires: ({ input: [balance, amount] }) => balance >= 0n && amount >= 0n,
  ensures: {
    neverNegative: ({ output }) => output >= 0n,
    takesWhatItCan: ({ input: [balance, amount], output }) => (amount > balance ? output === 0n : output === balance - amount),
  },
})
export type ChargeSpec = typeof chargeSpec

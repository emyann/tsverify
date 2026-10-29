// What charging an amount against a balance must leave: the spec, written
// before the code. `charge.ts` takes it as its type.
import { spec } from "tsverify"

export const ChargeSpec = spec<(balance: bigint, amount: bigint) => bigint>({
  requires: (balance, amount) => balance >= 0n && amount >= 0n,
  ensures: {
    neverNegative: (_balance, _amount, left) => left >= 0n,
    takesWhatItCan: (balance, amount, left) => (amount > balance ? left === 0n : left === balance - amount),
  },
})

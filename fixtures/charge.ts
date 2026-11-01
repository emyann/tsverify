// The handoff's scenario A, kept as the bigint case: return 0n when the amount
// exceeds the balance, otherwise the balance less the amount.
import { contract } from "../src/contract.ts"

export type ChargeInput = { readonly balance: bigint; readonly amount: bigint }

export const charge = ({ balance, amount }: ChargeInput): bigint => (amount > balance ? 0n : balance - amount)

/** Wrong on purpose: types as the contract asks and ignores it. */
export const chargeZero = (_: ChargeInput): bigint => 0n

/** Wrong by a sign: may return a negative. */
export const chargeNegative = ({ balance, amount }: ChargeInput): bigint => balance - amount

/** Written differently from the laws (`>=` where they say `>`) and still right. */
export const chargeRewritten = ({ balance, amount }: ChargeInput): bigint => {
  const over = amount >= balance
  if (over) return 0n
  return balance - amount
}

const requires = ({ input: [{ balance, amount }] }: { readonly input: readonly [ChargeInput] }) => balance >= 0n && amount >= 0n
const nonNegative = ({ output }: { readonly output: bigint }) => output >= 0n
const leavesTheRest = ({ input: [{ balance, amount }], output }: { readonly input: readonly [ChargeInput]; readonly output: bigint }) => amount > balance || output + amount === balance
const zeroWhenShort = ({ input: [{ balance, amount }], output }: { readonly input: readonly [ChargeInput]; readonly output: bigint }) => amount <= balance || output === 0n

export const right = contract(charge, { requires, ensures: { nonNegative, leavesTheRest, zeroWhenShort } })
export const zero = contract(chargeZero, { requires, ensures: { nonNegative, leavesTheRest, zeroWhenShort } })
export const negative = contract(chargeNegative, { requires, ensures: { nonNegative, leavesTheRest, zeroWhenShort } })
export const rewritten = contract(chargeRewritten, { requires, ensures: { nonNegative, leavesTheRest, zeroWhenShort } })

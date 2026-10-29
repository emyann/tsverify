// Charges an amount against a balance, written against `ChargeSpec`: the spec is
// a type here, imported as one, and nothing of it runs.
import type { Implementation } from "tsverify"
import type { ChargeSpec } from "./charge.contract.ts"

export const charge: Implementation<ChargeSpec> = (balance, amount) => (amount > balance ? 0n : balance - amount)

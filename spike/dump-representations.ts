// Phase 0, question 1: what does SchemaRepresentation.toRepresentation emit
// for a built-in bigint check, a brand, a struct, a literal and a custom filter?
import { Schema, SchemaRepresentation } from "effect"

const NonNegative = Schema.BigInt.check(Schema.isGreaterThanOrEqualToBigInt(0n)).pipe(Schema.brand("NonNegative"))

const cases = {
  builtin: Schema.BigInt.check(Schema.isGreaterThanOrEqualToBigInt(0n)),
  branded: NonNegative,
  struct: Schema.Struct({ balance: NonNegative, amount: NonNegative }),
  literal: Schema.Literal("issued"),
  custom: Schema.Struct({ charged: Schema.BigInt, remaining: Schema.BigInt }).check(
    Schema.makeFilter(({ charged, remaining }) => charged + remaining >= 0n),
  ),
  group: Schema.BigInt.check(Schema.isGreaterThanOrEqualToBigInt(0n), Schema.isLessThanBigInt(100n)),
}

const replacer = (_: string, v: unknown) => (typeof v === "bigint" ? `${v}n` : typeof v === "function" ? `[function]` : v)
for (const [name, schema] of Object.entries(cases)) {
  console.log(`--- ${name}`)
  console.log(JSON.stringify(SchemaRepresentation.toRepresentation(schema.ast), replacer, 2))
}

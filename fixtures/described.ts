// A law that says what it means, `{ description, condition }`, beside one that does not:
// in a `contract`, in an async `computation` and in an Effect `computation`,
// written in place or as a `const` a name reads. The report prints the sentence
// with the law. A `description` that is not a string written in place is refused.
// `test/described.test.ts` asks each.
import { Context, Effect } from "effect"
import { computation as effectComputation } from "../src/adapters/effect/contract.ts"
import { computation, contract, type Rejects } from "../src/contract.ts"

export const shipping = (total: number): number => (total >= 50 ? 0 : 5)

/** A law kept in a `const`, its sentence with it. */
const smallOrdersPay = {
  description: "A smaller order pays 5",
  condition: ({ input: [total], output }: { readonly input: readonly [number]; readonly output: number }) => (total < 50 ? output === 5 : true),
}

export const shipped = contract(shipping, {
  requires: ({ input: [total] }) => total >= 0,
  ensures: {
    freeFrom50: { description: "An order of 50 or more ships free", condition: ({ input: [total], output }) => (total >= 50 ? output === 0 : true) },
    smallOrdersPay,
    notNegative: ({ output }) => output >= 0,
  },
})

/** The same laws over a planted bug, `>` for `>=`: the law that says so is broken, at 50. */
export const shippedLate = contract((total: number): number => (total > 50 ? 0 : 5), {
  requires: ({ input: [total] }) => total >= 0,
  ensures: {
    freeFrom50: { description: "An order of 50 or more ships free", condition: ({ input: [total], output }) => (total >= 50 ? output === 0 : true) },
  },
})

export interface Names {
  readonly set: (id: string, name: string) => Rejects<void, Error>
}
export const renamed = computation<{ names: Names }, Error>()(
  async (names: Names, id: string, name: string): Promise<void> => {
    if (name !== "") await names.set(id, name)
  },
  {
    ensures: {
      emptyNameTouchesNothing: {
        description: "An empty name never reaches the store",
        condition: ({ input: [, , name], calls }) => (name === "" ? calls.length === 0 : true),
      },
    },
  },
)

export interface StoreShape {
  readonly get: (key: string) => Effect.Effect<string | undefined>
}
export class Store extends Context.Service<Store, StoreShape>()("fixtures/described/Store") {}
export const readIf = Effect.fn("readIf")(function* (asked: boolean, key: string) {
  const store = yield* Store
  return asked && (yield* store.get(key)) !== undefined
})
export const readsWhenAsked = effectComputation<{ store: StoreShape }>()(readIf, {
  ensures: {
    readsOnlyWhenAsked: { description: "It reads the store only when asked to", condition: ({ input: [asked], calls }) => asked || calls.length === 0 },
  },
})

const what = "free"
/** A sentence that is not written in place: refused, saying how to write it. */
export const describedComputed = contract(shipping, {
  ensures: { freeFrom50: { description: `An order of 50 or more ships ${what}`, condition: ({ input: [total], output }) => (total >= 50 ? output === 0 : true) } },
})

/** The names before 0.3, `says` and `holds`: refused, saying what each is now. */
export const describedTheOldWay = contract(shipping, {
  // @ts-expect-error -- `says` and `holds` are `description` and `condition` since 0.3
  ensures: { freeFrom50: { says: "An order of 50 or more ships free", holds: ({ input: [total], output }) => (total >= 50 ? output === 0 : true) } },
})

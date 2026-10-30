// Default values and rests: a parameter's default, a default inside an object
// pattern (in a parameter, a `const` and a computation's parameter), and an
// object rest that leaves keys out. A default is taken where the value is
// `undefined`, never where it is `null`. `test/destructuring.test.ts` asks each.
import { Context, Effect } from "effect"
import { computation as effectComputation } from "../src/adapters/effect/contract.ts"
import { contract } from "../src/contract.ts"

/** One more than `n`, which is 1 when not given. */
export function next(n: bigint = 1n): bigint {
  return n + 1n
}

export const nextOfOne = contract(next, {
  ensures: { fromOneWhenNotGiven: (n, out) => out === (n === undefined ? 2n : n + 1n) },
})

/** A page's size: 20 unless the options say. */
export function pageSize({ size = 20n }: { size?: bigint } = {}): bigint {
  return size
}

export const pageOfTwenty = contract(pageSize, {
  ensures: { twentyUnlessSaid: (options, out) => out === (options === undefined || options.size === undefined ? 20n : options.size) },
})

/** A label, `"none"` when it is `undefined`; a `null` one is kept, as JavaScript keeps it. */
export function labelled(item: { label?: string | null }): string | null {
  const { label = "none" } = item
  return label
}

export const labelOrNone = contract(labelled, {
  ensures: {
    noneWhenUndefined: (item, out) => item.label !== undefined || out === "none",
    nullKept: (item, out) => item.label !== null || out === null,
    theLabelOtherwise: (item, out) => item.label === undefined || item.label === null || out === item.label,
  },
})

export interface User {
  readonly id: string
  readonly name: string
  readonly secret: string
}

/** A user as shown: every field but the secret. */
export function shown(user: User) {
  const { secret: _secret, ...rest } = user
  return rest
}

export const shownWithoutTheSecret = contract(shown, {
  ensures: { theRestKept: (user, out) => out.id === user.id && out.name === user.name },
})

/** A record of the code's own, its rest taken: what it holds but the key left out. */
export function renamed(user: User, name: string) {
  const { id, ...rest } = { ...user, name }
  return { ...rest, id: id + "-renamed" }
}

export const renamedKeepsTheSecret = contract(renamed, {
  ensures: {
    theNewName: (_user, name, out) => out.name === name,
    theSecretKept: (user, _name, out) => out.secret === user.secret,
    theIdMarked: (user, _name, out) => out.id === user.id + "-renamed",
  },
})

export interface StoreShape {
  readonly list: (prefix: string, limit: bigint) => Effect.Effect<ReadonlyArray<string>>
}
export class Store extends Context.Service<Store, StoreShape>()("fixtures/destructuring/Store") {}

/** The keys under `prefix`, at most `limit` of them, 10 unless the options say: the shape of a verb with options. */
export const listed = Effect.fn("listed")(function* (prefix: string, { limit = 10n }: { limit?: bigint } = {}) {
  const store = yield* Store
  return yield* store.list(prefix, limit)
})

export const listedTen = effectComputation<{ store: StoreShape }>()(listed, {
  ensures: {
    asksForTheLimit: (_prefix, options, _out, calls) => {
      const call = calls.at(0)
      return call !== undefined && call.args[1] === (options === undefined || options.limit === undefined ? 10n : options.limit)
    },
  },
})

// A field read once its object's tag is checked, where the value differs by
// path: a law that reads `c.args[1]` once `c.op === "set"`, where `c` may be a
// call with one argument; `last.args[0]` once `last.op === "bump"`, where the
// other operation's first argument is a string; `ev.n` once `ev.type === "add"`,
// where the other member's `n` is a string. Each read takes the paths the type
// checker leaves it. `test/narrow.test.ts` asks each, and plants a bug in each.
import { computation, contract, type Rejects } from "../src/contract.ts"

export interface Names {
  readonly get: (id: string) => Rejects<string | undefined, Error>
  readonly set: (id: string, name: string) => Rejects<void, Error>
}

export const renamed = computation<{ names: Names }, Error>()(
  async (names: Names, id: string, name: string): Promise<boolean> => {
    if (name === "") return false
    const current = await names.get(id)
    if (current === undefined) return false
    await names.set(id, name)
    return true
  },
  {
    ensures: {
      // `c.args[1]` exists only on a `set`: at the place of the `get`, no run reads it.
      writesWhatWasAsked: (_names, id, name, _out, calls) =>
        calls.every((c) => c.op !== "set" || (c.args[0] === id && c.args[1] === name)),
      // Read further: at the `get`'s place, what stands for `c.args[1]` is a string too.
      writesNoEmptyName: (_names, _id, _name, _out, calls) => calls.every((c) => c.op !== "set" || c.args[1].length > 0),
      lastIsTheWrite: (_names, id, name, out, calls) => {
        if (out._tag !== "Success" || !out.value) return true
        const last = calls.at(-1)
        return last !== undefined && last.op === "set" && last.args[0] === id && last.args[1] === name
      },
    },
  },
)

export interface User {
  readonly id: string
  readonly name: string
}
export interface Users {
  readonly get: (id: string) => Rejects<User | undefined, Error>
  readonly put: (user: User) => Rejects<void, Error>
}

export const renamedUser = computation<{ users: Users }, Error>()(
  async (users: Users, id: string, name: string): Promise<boolean> => {
    const user = await users.get(id)
    if (user === undefined) return false
    await users.put({ ...user, name })
    return true
  },
  {
    ensures: {
      // A `get`'s `args[0]` is a string, a `put`'s a user: once `op === "put"`, the user.
      lastWritesTheName: (_users, _id, name, out, calls) => {
        const last = calls.at(-1)
        return out._tag !== "Success" || !out.value || (last !== undefined && last.op === "put" && last.args[0].name === name)
      },
      everyPutTheName: (_users, _id, name, _out, calls) => calls.every((c) => c.op !== "put" || c.args[0].name === name),
    },
  },
)

/** A branded string: a string to the verifier, though the brand alone admits none. */
export type Id = string & { readonly __brand: "Id" }

export interface Store {
  readonly label: (id: Id) => Rejects<string | undefined, Error>
  readonly bump: (by: bigint) => Rejects<bigint, Error>
}

export const touched = computation<{ store: Store }, Error>()(
  async (store: Store, id: Id, by: bigint): Promise<bigint> => {
    const label = await store.label(id)
    if (label === undefined) return 0n
    return await store.bump(by)
  },
  {
    requires: (_store, _id, by) => by > 0n,
    ensures: {
      // A `label`'s first argument is a string, a `bump`'s a bigint: each read takes the operation its check left.
      bumpsUp: (_store, _id, _by, _out, calls) => calls.every((c) => c.op !== "bump" || c.args[0] > 0n),
      labelsTheId: (_store, id, _by, _out, calls) => calls.every((c) => c.op !== "label" || c.args[0] === id),
      lastBumpIsBy: (_store, _id, by, _out, calls) => {
        const last = calls.at(-1)
        return last === undefined || last.op !== "bump" || last.args[0] === by
      },
      returnsTheBump: (_store, _id, _by, out, calls) => {
        const last = calls.at(-1)
        if (last === undefined || last.op !== "bump" || last.outcome._tag !== "Success") return true
        return out._tag !== "Success" || out.value === last.outcome.value
      },
    },
  },
)

/** A union whose members give `n` different kinds: one record per member, and a read takes the member checked. */
export type Event =
  | { readonly type: "add"; readonly n: bigint }
  | { readonly type: "sub"; readonly n: bigint }
  | { readonly type: "name"; readonly n: string }

export const apply = (total: bigint, ev: Event): bigint => (ev.type === "add" ? total + ev.n : ev.type === "sub" ? total - ev.n : total)
export const applied = contract(apply, {
  ensures: {
    namesKeep: (total, ev, out) => ev.type !== "name" || out === total,
    addsAdd: (total, ev, out) => ev.type !== "add" || out === total + ev.n,
    subsSub: (total, ev, out) => ev.type !== "sub" || out === total - ev.n,
  },
})

export function sum(events: ReadonlyArray<Event>): bigint {
  let total = 0n
  for (const e of events)
    if (e.type === "add") {
      const { n } = e
      total += n
    }
  return total
}
export const summed = contract(sum, {
  requires: (events) => events.every((e) => e.type !== "add" || e.n >= 0n),
  ensures: { notNegative: (_events, out) => out >= 0n },
})

/** Read where the checker has not narrowed it, `n` is a bigint or a string: a value of either kind, which `===` tells apart. */
export const either = contract((ev: Event): boolean => ev.n === 0n, {
  ensures: { onlyACount: (ev, out) => !out || ev.type !== "name" },
})
export const eitherZero = contract((ev: Event): boolean => ev.n === 0n, { ensures: { never: (_ev, out) => !out } })

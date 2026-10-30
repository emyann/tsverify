// A ternary that picks one of two computations as a value, run after: the call
// taken where the condition holds, the other where it does not, and nothing of
// the one not taken. Async code, no library. `test/chosen.test.ts` asks each.
import { type Implementation, type Rejects, spec } from "../src/contract.ts"

export class Missing extends Error {
  readonly _tag = "Missing" as const
}
export interface Store {
  readonly get: (key: string) => Rejects<string, Missing>
}

const readsTheChosenKey = (primary: boolean, key: string, calls: ReadonlyArray<{ readonly args: ReadonlyArray<unknown> }>) =>
  calls.length === 1 && calls.at(0)?.args[0] === (primary ? key : "backup/" + key)

export const pickSpec = spec<(store: Store, primary: boolean, key: string) => Rejects<string, Missing>>({
  ensures: {
    readsTheChosenKey: (_store, primary, key, _out, calls) => readsTheChosenKey(primary, key, calls),
    givesWhatItRead: (_store, _primary, _key, out, calls) => {
      const c = calls.at(0)
      return c === undefined || c.outcome._tag !== "Success" || (out._tag === "Success" && out.value === c.outcome.value)
    },
  },
})
export type PickSpec = typeof pickSpec

/** The value at `key`, or at its backup: the read chosen first, awaited after. */
export const pick: Implementation<PickSpec> = async (store, primary, key) => {
  const read = primary ? store.get(key) : store.get("backup/" + key)
  return await read
}

export const fromSpec = spec<(store: Store, primary: boolean, backup: boolean, key: string) => Rejects<string, Missing>>({
  ensures: {
    readsOnce: (_store, _primary, _backup, _key, _out, calls) => calls.length === 1,
    readsWhereTold: (_store, primary, backup, key, _out, calls) =>
      calls.at(0)?.args[0] === (primary ? key : backup ? "backup/" + key : "last/" + key),
    failsAsTheRead: (_store, _primary, _backup, _key, out, calls) => (out._tag === "Failure") === (calls.at(0)?.outcome._tag === "Failure"),
  },
})
export type FromSpec = typeof fromSpec

/** The value at `key`, its backup or its last copy: a choice nested in a choice. */
export const from: Implementation<FromSpec> = async (store, primary, backup, key) =>
  primary ? store.get(key) : backup ? store.get("backup/" + key) : store.get("last/" + key)

// A `Map` or a `Set` read through `has` and `get`: the array of its entries, a key's entry the first that holds it (the
// last, for a `Map` the code builds from pairs, as its constructor keeps the last). A key is compared as the collection
// compares it (SameValueZero: `NaN` is found, `-0` is `0`). Iterating one, its `size`, and every change to one are
// refused: a `Map` the code is given is read, never written.
//
// Of one the code is given (`symbolicOf`), the entries are leaves: a length (`#entries`, `#members`) and each entry's
// key and value at `[]`, which a counterexample reads back as a `Map` or a `Set` (`concrete.ts`).
import type ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import { firstIndex, type Lowering } from "./lower.ts"
import { strictEq } from "./ops.ts"
import { NUM, Unsupported, type Val, jsString, lazyRecord } from "./value.ts"

export interface Entries {
  readonly length: Arith
  readonly maxSize?: number
  readonly key: (i: Arith) => Val
  /** A map's value at entry `i`; a set has none. */
  readonly value?: (i: Arith) => Val
  /** Whether a key's entry is the last that holds it (a map built from pairs), not the first. */
  readonly lastWins?: boolean
}

/** Whether two keys are the same key, as a `Map` or a `Set` compares them: `===`, but for `NaN`, which finds `NaN`. */
const sameKey = (L: Lowering, a: Val, b: Val, at: ts.Node): Bool => {
  const z3 = L.u.z3
  const eq = strictEq(L.u, a, b, at)
  return a.kind === "num" && b.kind === "num" ? z3.Or(eq, z3.And(a.cls.eq(NUM.nan), b.cls.eq(NUM.nan))) : eq
}

/**
 * A dictionary the code is given, `Record<string, T>`: the array of its own entries, a key's the first that holds it.
 * Its reads go through `entries` (`dictionaryRead` in `lower.ts`), and a counterexample reads it back as a plain object.
 * Where the code lists its keys (`Object.keys`), they are distinct and in the order JavaScript lists an object's: the
 * names of array positions first, by number, then the rest as they were written.
 */
export const dictionaryOf = (
  L: Lowering,
  entries: Entries & { readonly value: (i: Arith) => Val },
  indices: ReadonlyArray<Arith>,
  id?: string,
): Val => {
  const { u } = L
  const z3 = u.z3
  const searched = { kind: "array" as const, length: entries.length, elem: entries.key }
  const entryOf = (key: Val, call: unknown): { readonly found: Bool; readonly value: Val } => {
    const node = call as ts.Node
    const { found, k } = firstIndex(L, searched, (i) => sameKey(L, entries.key(i), key, node))
    return { found, value: entries.value(k) }
  }
  let listed = false
  const own = () => {
    if (!listed) {
      listed = true
      const i = z3.Int.const(u.fresh("own.i"))
      const j = z3.Int.const(u.fresh("own.j"))
      const ki = entries.key(i)
      const kj = entries.key(j)
      if (ki.kind !== "str" || kj.kind !== "str") throw new Unsupported("the keys of a record keyed by other than strings", undefined)
      const digit = z3.Range(jsString(z3, "0"), jsString(z3, "9"))
      const position = z3.Union(z3.Re.toRe(jsString(z3, "0")), z3.ReConcat(z3.Range(jsString(z3, "1"), jsString(z3, "9")), z3.Star(digit)))
      // Its number at least 0 as well, which the digits already say, said outright for the solver.
      const isPosition = (s: typeof ki.term) => z3.And(z3.InRe(s, position), s.toInt().ge(0), s.toInt().lt(4294967295))
      u.assume(
        z3.ForAll(
          [i, j],
          z3.Implies(
            z3.And(i.ge(0), i.lt(j), j.lt(entries.length)),
            z3.And(
              z3.Not(ki.term.eq(kj.term)),
              z3.Implies(isPosition(kj.term), z3.And(isPosition(ki.term), ki.term.toInt().lt(kj.term.toInt()))),
            ),
          ),
        ),
        indices,
      )
    }
    return {
      keys: { kind: "array" as const, length: entries.length, elem: entries.key },
      values: { kind: "array" as const, length: entries.length, elem: entries.value },
    }
  }
  return { ...lazyRecord(() => undefined, id, undefined, undefined, undefined, entryOf), own } as Val
}

export const collectionOf = (L: Lowering, kind: "Map" | "Set", entries: Entries, at: ts.Node, id?: string): Val => {
  const z3 = L.u.z3
  const { length } = entries
  // The entry of position `i` of the search: `i` itself, or counted from the end where the last entry wins.
  const entryAt = (i: Arith): Arith => (entries.lastWins === true ? length.sub(1).sub(i) : i)
  const searched = {
    kind: "array" as const,
    length,
    ...(entries.maxSize === undefined ? {} : { maxSize: entries.maxSize }),
    elem: (i: Arith) => entries.key(entryAt(i)),
  }
  const lookup = (name: string, args: ReadonlyArray<Val>, call: ts.Node): { readonly found: Bool; readonly k: Arith } => {
    const key = args[0]
    if (args.length !== 1 || key === undefined) throw new Unsupported(`\`.${name}\` of a \`${kind}\` takes one key`, call)
    const { found, k } = firstIndex(L, searched, (i) => sameKey(L, entries.key(entryAt(i)), key, call))
    return { found, k: entryAt(k) }
  }
  const reads = kind === "Map" ? "`has` and `get`" : "`has`"
  return lazyRecord((name) => {
    if (name === "has")
      return { kind: "builtin", name: `${kind}.has`, call: (args, call) => ({ kind: "bool", term: lookup(name, args, call).found }) }
    if (name === "get" && entries.value !== undefined) {
      const valueOf = entries.value
      return {
        kind: "builtin",
        name: `${kind}.get`,
        call: (args, call) => {
          const { found, k } = lookup(name, args, call)
          const v = valueOf(k)
          // `undefined` where the key has no entry, and where its entry holds `undefined`.
          if (v.kind === "maybe")
            return { kind: "maybe", isNull: z3.And(found, v.isNull), isUndefined: z3.Or(z3.Not(found), v.isUndefined), value: v.value }
          if (v.kind === "nullish")
            return {
              kind: "maybe",
              isNull: z3.And(found, z3.Bool.val(v.which === "null")),
              isUndefined: z3.Or(z3.Not(found), z3.Bool.val(v.which === "undefined")),
              value: undefined,
            }
          return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(found), value: v }
        },
      }
    }
    const refused = `a \`${kind}\` is read through ${reads}: \`.${name}\` is not modeled`
    // A property is refused where it is read (`size` would read as `undefined`), a method where it is called.
    if (name === "size") throw new Unsupported(refused, at)
    return {
      kind: "builtin",
      name: `${kind}.${name}`,
      call: (_args, call) => {
        throw new Unsupported(refused, call)
      },
    }
  }, id)
}

// A `Map` or a `Set` read through `has` and `get`: the array of its entries, a key's entry the first that holds it (the
// last, for a `Map` the code builds from pairs, as its constructor keeps the last). A key is compared as the collection
// compares it (SameValueZero: `NaN` is found, `-0` is `0`). One the code is given is read, never written nor listed; one
// it allocates is a table it may change, and is listed (`maps.ts`, `tableMethods`, `elementsOf`).
//
// Of one the code is given (`symbolicOf`), the entries are leaves: a length (`#entries`, `#members`) and each entry's
// key and value at `[]`, which a counterexample reads back as a `Map` or a `Set` (`concrete.ts`).
import type ts from "typescript"
import type { Arith, Bool, FuncDecl } from "z3-solver"
import { firstIndex } from "./lower/arrays.ts"
import { type Lowering } from "./lower.ts"
import { strictEq } from "./ops.ts"
import { holds, listing, lookup, sizeOf, type Table } from "./maps.ts"
import { tupleOf } from "./lower/records.ts"
import { NUM, UNDEFINED, Unsupported, type Val, jsString, lazyRecord, memoElems } from "./value.ts"

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
export const sameKey = (L: Lowering, a: Val, b: Val, at: ts.Node): Bool => {
  const z3 = L.u.z3
  const eq = strictEq(L.u, a, b, at)
  return a.kind === "num" && b.kind === "num" ? z3.Or(eq, z3.And(a.cls.eq(NUM.nan), b.cls.eq(NUM.nan))) : eq
}

/**
 * A dictionary the code is given, `Record<string, T>`: the array of its own entries, a key's the first that holds it.
 * Its reads go through `entries` (`dictionaryRead` in `lower/records.ts`), and a counterexample reads it back as a plain
 * object.
 * Where the code lists its keys (`Object.keys`), they are distinct and in the order JavaScript lists an object's: the
 * names of array positions first, by number, then the rest as they were written.
 */
export const dictionaryOf = (
  L: Lowering,
  entries: Entries & { readonly value: (i: Arith) => Val },
  indices: ReadonlyArray<Arith>,
  id?: string,
  family?: Family,
): Val => {
  const { u } = L
  const z3 = u.z3
  const searched = { kind: "array" as const, length: entries.length, elem: entries.key }
  // On the proof side, one in an array (`parents[].labels`) is a table: whether it holds a key, and the place of its
  // entry, functions of the dictionary's place (its path's indices) and the key, so one key read twice, by the code and
  // by a law, is one term. What every dictionary of the path keeps is said once, of all of them (`family`): never inside
  // a quantifier that reads one. One the code is given outright is read as an array of entries, a key at the first.
  const fns = u.bound === undefined && family !== undefined && indices.length > 0 ? familyOf(L, family, indices.length) : undefined
  const entryOf = (key: Val, call: unknown): { readonly found: Bool; readonly value: Val } => {
    const node = call as ts.Node
    if (fns !== undefined && key.kind === "str")
      return { found: fns.has.call(...indices, key.term) as Bool, value: entries.value(fns.at.call(...indices, key.term) as Arith) }
    const { found, k } = firstIndex(L, searched, (i) => sameKey(L, entries.key(i), key, node))
    return { found, value: entries.value(k) }
  }
  let listed = false
  const own = () => {
    if (fns !== undefined) fns.listed()
    else if (!listed) {
      listed = true
      const i = z3.Int.const(u.fresh("own.i"))
      const j = z3.Int.const(u.fresh("own.j"))
      const ki = entries.key(i)
      const kj = entries.key(j)
      if (ki.kind !== "str" || kj.kind !== "str") throw new Unsupported("the keys of a record keyed by other than strings", undefined)
      u.assume(z3.ForAll([i, j], z3.Implies(z3.And(i.ge(0), i.lt(j), j.lt(entries.length)), listedInOrder(z3, ki.term, kj.term))), indices)
    }
    return {
      keys: { kind: "array" as const, length: entries.length, elem: entries.key },
      values: { kind: "array" as const, length: entries.length, elem: entries.value },
    }
  }
  return { ...lazyRecord(() => undefined, id, undefined, undefined, undefined, entryOf), own } as Val
}

/** Of two keys an object lists, the first before the second: two keys, and an array position only after another. */
const listedInOrder = (z3: Lowering["u"]["z3"], a: Extract<Val, { kind: "str" }>["term"], b: Extract<Val, { kind: "str" }>["term"]): Bool =>
  z3.And(z3.Not(a.eq(b)), z3.Implies(isArrayIndex(z3, b), z3.And(isArrayIndex(z3, a), positionBefore(z3, a, b))))

/**
 * The dictionaries of one path (`input.parents[].labels`), one at each index of the arrays above it: its name, and its
 * count of entries and its key at an entry, at any indices (`symbolicOf`).
 */
export interface Family {
  readonly path: string
  readonly length: (indices: ReadonlyArray<Arith>) => Arith
  readonly key: (indices: ReadonlyArray<Arith>, i: Arith) => Val
}

/**
 * The functions the dictionaries of one path are read through on the proof side, and what each of them keeps, said once
 * of every index: each entry is held, at its place, so its keys are distinct, as an object's are; and once one is listed
 * (`listed`), an array position comes before any other key, and in number order.
 */
interface Functions {
  readonly has: FuncDecl
  readonly at: FuncDecl
  readonly listed: () => void
}
const families = new WeakMap<object, Map<string, Functions>>()
const familyOf = (L: Lowering, family: Family, arity: number): Functions => {
  const { u } = L
  const z3 = u.z3
  let byPath = families.get(u)
  if (byPath === undefined) {
    byPath = new Map()
    families.set(u, byPath)
  }
  const known = byPath.get(family.path)
  if (known !== undefined) return known
  const ints = Array.from({ length: arity }, () => z3.Int.sort())
  const has = z3.Function.declare(`${family.path}~holds`, ...ints, z3.String.sort(), z3.Bool.sort())
  const at = z3.Function.declare(`${family.path}~at`, ...ints, z3.String.sort(), z3.Int.sort())
  const where = Array.from({ length: arity }, () => z3.Int.const(u.fresh("dict.at")))
  const n = family.length(where)
  const q = z3.Int.const(u.fresh("dict.q"))
  const r = z3.Int.const(u.fresh("dict.r"))
  const kq = family.key(where, q)
  const kr = family.key(where, r)
  if (kq.kind !== "str" || kr.kind !== "str") throw new Unsupported("the keys of a record keyed by other than strings", undefined)
  const held = z3.And(has.call(...where, kq.term), at.call(...where, kq.term).eq(q))
  u.assume(z3.ForAll([q, ...where], z3.Implies(z3.And(q.ge(0), q.lt(n)), held)))
  // And a key it holds is an entry's, at its place: said once of every key, not at each read, where a key read inside a
  // quantifier (`output[i]`, the `i − n`th entry) would have the solver read entry after entry.
  const k = z3.String.const(u.fresh("dict.k"))
  const place = at.call(...where, k)
  const entry = family.key(where, place)
  if (entry.kind !== "str") throw new Unsupported("the keys of a record keyed by other than strings", undefined)
  u.assume(z3.ForAll([k, ...where], z3.Implies(has.call(...where, k), z3.And(place.ge(0), place.lt(n), entry.term.eq(k)))))
  let ordered = false
  const listed = () => {
    if (ordered) return
    ordered = true
    u.assume(z3.ForAll([q, r, ...where], z3.Implies(z3.And(q.ge(0), q.lt(r), r.lt(n)), listedInOrder(z3, kq.term, kr.term))))
  }
  const fns = { has, at, listed }
  byPath.set(family.path, fns)
  return fns
}

/** Whether a key names an array position (`"0"`, `"12"`, below 2³² − 1), which a plain object lists first, by number. */
export const isArrayIndex = (z3: Lowering["u"]["z3"], s: Extract<Val, { kind: "str" }>["term"]): Bool => {
  const digit = z3.Range(jsString(z3, "0"), jsString(z3, "9"))
  const position = z3.Union(z3.Re.toRe(jsString(z3, "0")), z3.ReConcat(z3.Range(jsString(z3, "1"), jsString(z3, "9")), z3.Star(digit)))
  return z3.And(z3.InRe(s, position), s.toInt().ge(0), s.toInt().lt(4294967295))
}

/** Of two array positions, whether the first is the smaller number. */
export const positionBefore = (
  z3: Lowering["u"]["z3"],
  a: Extract<Val, { kind: "str" }>["term"],
  b: Extract<Val, { kind: "str" }>["term"],
): Bool => a.toInt().lt(b.toInt())

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

/**
 * The methods of a `Map` or a `Set` the code allocated (`maps.ts`): `has`, a `Map`'s `get`, and `size`, read from its
 * table. A change (`set`, `add`, `delete`, `clear`) is a statement's (`exec.ts`); as a value it is refused.
 */
export const tableMethods = (t: Table, name: string): Val | undefined => {
  const z3 = t.L.u.z3
  const one = (args: ReadonlyArray<Val>, call: ts.Node): Val => {
    const key = args[0]
    if (args.length !== 1 || key === undefined) throw new Unsupported(`\`.${name}\` of a \`${t.kind}\` takes one key`, call)
    return key
  }
  if (name === "has") return { kind: "builtin", name: `${t.kind}.has`, call: (args, call) => holds(t, one(args, call), call) }
  if (name === "get" && t.kind === "Map")
    return {
      kind: "builtin",
      name: "Map.get",
      call: (args, call) => {
        const { found, value } = lookup(t, one(args, call), call)
        if (value.kind === "maybe")
          return {
            kind: "maybe",
            isNull: z3.And(found, value.isNull),
            isUndefined: z3.Or(z3.Not(found), value.isUndefined),
            value: value.value,
          }
        if (value.kind === "nullish")
          return {
            kind: "maybe",
            isNull: z3.And(found, z3.Bool.val(value.which === "null")),
            isUndefined: z3.Or(z3.Not(found), z3.Bool.val(value.which === "undefined")),
            value: undefined,
          }
        return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(found), value }
      },
    }
  if (name === "size") return sizeOf(t)
  const changes = ["set", "add", "delete", "clear"].includes(name)
  return {
    kind: "builtin",
    name: `${t.kind}.${name}`,
    call: (_args, call) => {
      throw new Unsupported(
        changes
          ? `\`.${name}\` of a \`${t.kind}\` is read as a statement, for the change it makes: its result is not`
          : `a \`${t.kind}\` the code builds is read through \`has\`${t.kind === "Map" ? ", `get`" : ""}, \`size\`, a spread and a \`for…of\`: \`.${name}\` is not modeled`,
        call,
      )
    },
  }
}

/** A `Map`'s or a `Set`'s elements as a spread or a `for…of` gives them: a `Set`'s keys, a `Map`'s `[key, value]` pairs. */
export const elementsOf = (L: Lowering, t: Table, at: ts.Node): Val => {
  const { keys, values } = listing(t)
  if (t.kind === "Set") return keys
  if (t.kind === "object") throw new Unsupported("a plain object is not iterable: list its keys with `Object.keys` or `Object.entries`", at)
  return {
    kind: "array",
    length: keys.length,
    ...(keys.maxSize === undefined ? {} : { maxSize: keys.maxSize }),
    elem: memoElems((i) => tupleOf(L, [() => keys.elem(i), () => values.elem(i)], () => UNDEFINED, at)),
  }
}

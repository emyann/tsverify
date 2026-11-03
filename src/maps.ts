// Maps the code builds: a plain object it uses as a dictionary (`const out: Record<string, string> = {}`), and a `Map` or
// a `Set` it allocates. Each is a table from a key to whether the map holds it and its value, written at keys the code
// computes, and the keys it holds, listed.
//
// A table is a chain of values, none of which changes: what the map held when it was made (nothing, a dictionary it
// copied, an array's elements), each write on top (`out[k] = v`, `delete out[k]`, `m.set(k, v)`, `s.add(k)`), two
// paths' tables merged under the branch each holds, and a loop's writes read whole (`loopWrites`, made in `exec.ts`). A
// key's value is the last write's that names it, else what the table below holds.
//
// Its keys, listed (`Object.keys`, a spread, a `for…of`, `size`):
// - on the search side exactly, in JavaScript's order: a plain object lists the keys that are array positions first,
//   by number, then the rest in the order they were first written; a `Map` and a `Set` list every key in that order. A
//   key deleted and written again is written last.
// - on the proof side as a list of the keys it holds, each once, in an order the solver does not know.
//
// A write at `__proto__` on a plain object sets its prototype, not a key: of a primitive value it does nothing, as
// JavaScript does; of an object, that the key is another is an obligation.
import type ts from "typescript"
import type { Arith, Bool, Expr, FuncDecl, Sort } from "z3-solver"
import { isArrayIndex, positionBefore, sameKey } from "./collections.ts"
import { firstIndex } from "./lower/arrays.ts"
import { type Lowering, bool, oblige } from "./lower.ts"
import { ite } from "./ops.ts"
import type { Universe } from "./universe.ts"
import { type Keyed, UNDEFINED, Unsupported, type Val, identity, jsString, locate, memoElems } from "./value.ts"

export type MapKind = "object" | "Map" | "Set"

type ArrayVal = Extract<Val, { kind: "array" }>
type RecordVal = Extract<Val, { kind: "record" }>

/** A key's entry: whether the map holds the key, and its value there (for a `Set`, `undefined`). */
export interface Found {
  readonly found: Bool
  readonly value: Val
}

/** One change: `set` writes `value` at `key` (`out[k] = v`, `m.set(k, v)`, `s.add(k)`); otherwise it deletes the key. */
export interface Write {
  readonly cond: Bool
  readonly key: Val
  readonly set: boolean
  readonly value: Val
}

/**
 * One write of every pass of a loop, by the pass's index `t`: whether the pass makes it (`cond`, its index inside the
 * loop said beside), at which key and with which value (`exec.ts`); and, for a key, whether some pass makes it there
 * (`has`) and the last that does (`last`), functions of the key and of the quantifier indices open where the loop runs.
 * That every pass that makes it at a key is at most `last` is said by whoever makes the loop's writes; that `last`'s
 * pass makes it, by each read (`loopEntry`).
 */
export interface LoopEffect {
  /** Whether the key is held after it: a set, a delete, or one of the two by branch. */
  readonly held: (t: Arith) => Bool
  readonly cond: (t: Arith) => Bool
  readonly key: (t: Arith) => Val
  readonly value: (t: Arith) => Val
  readonly has: FuncDecl
  readonly last: FuncDecl
}

/** A loop's writes: how many passes, the quantifier indices open where it runs, and each write of a pass, in order. */
export interface LoopWrites {
  readonly n: Arith
  readonly bounds: ReadonlyArray<Arith>
  readonly effects: ReadonlyArray<LoopEffect>
}

type Node =
  | { readonly node: "empty" }
  /** A dictionary the code was given, or a loop's state read through its invariants: its own entries. */
  | { readonly node: "given"; readonly dict: RecordVal }
  /** `new Set(xs)` and `new Map(pairs)`: an array's keys, a key's position its first, a map's value its last pair's. */
  | { readonly node: "from"; readonly arr: ArrayVal; readonly key: (i: Arith) => Val; readonly value?: (i: Arith) => Val }
  | { readonly node: "write"; readonly prev: Table; readonly write: Write }
  | { readonly node: "ite"; readonly cond: Bool; readonly a: Table; readonly b: Table }
  | { readonly node: "loop"; readonly prev: Table; readonly loop: LoopWrites }
  /**
   * A loop over a list of keys, each once, whose pass writes the map at its element alone (`exec.ts`): a key's entry is
   * the pass's at that key, where the list holds it, else what the table held before.
   */
  | {
      readonly node: "keyed"
      readonly prev: Table
      readonly list: ArrayVal & { readonly keyed: Keyed }
      readonly writesAt: (k: Val) => ReadonlyArray<Write>
    }
  /** What a loop builds, as one of its iterations sees it: never read, only written (`exec.ts`). */
  | { readonly node: "marker"; readonly name: string }

export type Table = Node & {
  readonly kind: MapKind
  readonly L: Lowering
  /** Where it was made: what a message about it points to. */
  readonly at: ts.Node
  readonly lookups: Map<string, Found>
  listed?: Listing
}

/** A map's keys and values, in its order: two arrays of one length. */
export interface Listing {
  readonly keys: ArrayVal
  readonly values: ArrayVal
}

const table = (L: Lowering, kind: MapKind, at: ts.Node, node: Node): Table => ({ ...node, kind, L, at, lookups: new Map() })

export const emptyTable = (L: Lowering, kind: MapKind, at: ts.Node): Table => table(L, kind, at, { node: "empty" })
export const givenTable = (L: Lowering, dict: RecordVal, at: ts.Node): Table => table(L, "object", at, { node: "given", dict })
export const fromTable = (
  L: Lowering,
  kind: "Map" | "Set",
  arr: ArrayVal,
  key: (i: Arith) => Val,
  value: ((i: Arith) => Val) | undefined,
  at: ts.Node,
): Table => {
  if (L.u.bound !== undefined) return table(L, kind, at, { node: "from", arr, key, ...(value === undefined ? {} : { value }) })
  // On the proof side, the array's elements written in turn, a pass each: a key's value is its last pair's, as the
  // constructor keeps it, and whether it holds a key a function of the key, not a search.
  const u = L.u
  const z3 = u.z3
  const bounds = u.openBounds()
  const i = z3.Int.const(u.fresh("from.i"))
  const each = u.within(i, () => key(i))
  const k = keyTerm(each.result)
  if (k === undefined) return table(L, kind, at, { node: "from", arr, key, ...(value === undefined ? {} : { value }) })
  const name = u.fresh(`${kind}.from`)
  const ints = bounds.map(() => z3.Int.sort())
  const has = z3.Function.declare(name, ...ints, k.sort, z3.Bool.sort())
  const last = z3.Function.declare(`${name}.last`, ...ints, k.sort, z3.Int.sort())
  // What is known of each element is said beside, as `elementwise` says it: under the claim alone, a model could break it.
  if (each.facts.length > 0) u.assume(z3.ForAll([i], z3.Implies(z3.And(i.ge(0), i.lt(arr.length)), z3.And(...each.facts))), bounds)
  u.assume(
    z3.ForAll(
      [i],
      z3.Implies(z3.And(i.ge(0), i.lt(arr.length), ...each.facts), z3.And(has.call(...bounds, k), i.le(last.call(...bounds, k)))),
    ),
    bounds,
  )
  const effect: LoopEffect = {
    held: () => z3.Bool.val(true),
    cond: () => z3.Bool.val(true),
    key,
    value: value ?? (() => UNDEFINED),
    has,
    last,
  }
  return loopTable(emptyTable(L, kind, at), { n: arr.length, bounds, effects: [effect] }, at)
}
export const markerTable = (L: Lowering, kind: MapKind, name: string, at: ts.Node): Table => table(L, kind, at, { node: "marker", name })
export const loopTable = (prev: Table, loop: LoopWrites, at: ts.Node): Table => table(prev.L, prev.kind, at, { node: "loop", prev, loop })
export const keyedTable = (
  prev: Table,
  list: ArrayVal & { readonly keyed: Keyed },
  writesAt: (k: Val) => ReadonlyArray<Write>,
  at: ts.Node,
): Table => table(prev.L, prev.kind, at, { node: "keyed", prev, list, writesAt })

/** The table a value holds, where it is a map the code built (or may be missing, `T | undefined`). */
export const tableOf = (v: Val | undefined): Table | undefined =>
  v?.kind === "record" ? v.table : v?.kind === "maybe" && v.value?.kind === "record" ? v.value.table : undefined

/**
 * A map as a value: a plain object reads as a dictionary does (`out[k]`, `k in out`, `Object.hasOwn`, `Object.keys`); a
 * `Map` and a `Set` through their methods (`methods`, in `collections.ts`).
 */
export const mapValue = (t: Table, methods?: (t: Table, name: string) => Val | undefined): Val => {
  if (t.kind === "object")
    return { kind: "record", field: () => undefined, table: t, entries: (key, at) => lookup(t, key, at as ts.Node), own: () => listing(t) }
  const memo = new Map<string, Val | undefined>()
  return {
    kind: "record",
    field: (name) => {
      if (!memo.has(name)) memo.set(name, methods?.(t, name))
      return memo.get(name)
    },
    table: t,
  }
}

// ——— A key's entry ———

/** The term a key is compared by, for a function of keys: a string's, a bigint's, a boolean's. */
const keyTerm = (v: Val): Expr | undefined => (v.kind === "str" || v.kind === "int" || v.kind === "bool" ? v.term : undefined)
const keySort = (L: Lowering, v: Val): Sort | undefined => {
  const z3 = L.u.z3
  return v.kind === "str" ? z3.String.sort() : v.kind === "int" ? z3.Int.sort() : v.kind === "bool" ? z3.Bool.sort() : undefined
}

/** Whether two keys are one: a plain object's keys are strings; a `Map`'s and a `Set`'s compare as they compare them. */
const same = (L: Lowering, a: Val, b: Val, at: ts.Node): Bool => sameKey(L, a, b, at)

/** The entry of `key` in `t`. */
export const lookup = (t: Table, key: Val, at: ts.Node): Found => {
  const id = identity(key)
  const memo = id === undefined ? undefined : t.lookups.get(id)
  if (memo !== undefined) return memo
  const found = entryOf(t, key, at)
  if (id !== undefined) t.lookups.set(id, found)
  return found
}

const entryOf = (t: Table, key: Val, at: ts.Node): Found => {
  const { L } = t
  const u = L.u
  const z3 = u.z3
  switch (t.node) {
    case "empty":
      return { found: z3.Bool.val(false), value: UNDEFINED }
    case "marker":
      throw new Unsupported(`reads \`${t.name}\` in the loop that builds it, which is read only where each pass writes it`, at)
    case "given":
      return t.dict.entries!(key, at)
    case "from": {
      const n = t.arr.length
      // A `Map` built from pairs keeps a key's last pair's value: its entry is found searching from the end.
      const fromEnd = t.value !== undefined
      const entry = (i: Arith): Arith => (fromEnd ? n.sub(1).sub(i) : i)
      const searched: ArrayVal = {
        kind: "array",
        length: n,
        ...(t.arr.maxSize === undefined ? {} : { maxSize: t.arr.maxSize }),
        elem: (i) => t.key(entry(i)),
      }
      const { found, k } = firstIndex(L, searched, (i) => same(L, t.key(entry(i)), key, at))
      return { found, value: t.value === undefined ? UNDEFINED : t.value(entry(k)) }
    }
    case "write": {
      const below = lookup(t.prev, key, at)
      const w = t.write
      const hit = z3.And(w.cond, same(L, w.key, key, at))
      if (z3.isFalse(hit)) return below
      return { found: z3.If(hit, z3.Bool.val(w.set), below.found), value: w.set ? ite(u, hit, w.value, below.value, at) : below.value }
    }
    case "ite": {
      const a = lookup(t.a, key, at)
      const b = lookup(t.b, key, at)
      return { found: z3.If(t.cond, a.found, b.found), value: ite(u, t.cond, a.value, b.value, at) }
    }
    case "loop":
      return loopEntry(t, t.loop, key, at)
    case "keyed": {
      // Only the pass at this key writes it: the list holds each key once.
      const below = lookup(t.prev, key, at)
      if (key.kind !== t.list.keyed.kind) return below
      let found = below.found
      let value = below.value
      for (const w of t.writesAt(key)) {
        found = z3.If(w.cond, z3.Bool.val(w.set), found)
        if (w.set) value = ite(u, w.cond, w.value, value, at)
      }
      return { found, value }
    }
  }
}

/**
 * A key's entry after a loop: the last write of the last iteration that wrote it, else what the table held before. For
 * each of an iteration's writes, `has` says whether some iteration made it at the key, and `last` which did last: that
 * every iteration that made it is at most `last` is said of every iteration (`exec.ts`), and that `last`'s iteration
 * made it, here, of this key.
 */
const loopEntry = (t: Table & { node: "loop" }, loop: LoopWrites, key: Val, at: ts.Node): Found => {
  const { L } = t
  const u = L.u
  const z3 = u.z3
  const k = keyTerm(key)
  const below = lookup(t.prev, key, at)
  if (k === undefined) {
    if (key.kind === "maybe" || key.kind === "nullish" || key.kind === "num")
      throw new Unsupported(`a key that is a ${key.kind}, read from a map a loop wrote: of a string, a bigint or a boolean it is read`, at)
    return below
  }
  const made = loop.effects.map((w, e) => {
    // A write of keys of another kind never finds this key.
    if (w.has.domain(w.has.arity() - 1).name() !== k.sort.name()) return undefined
    const has = w.has.call(...loop.bounds, k) as Bool
    const last = w.last.call(...loop.bounds, k) as Arith
    u.assume(z3.Implies(has, z3.And(last.ge(0), last.lt(loop.n), w.cond(last), same(L, w.key(last), key, at))), u.openBounds())
    return { e, has, last, held: w.held(last), value: w.value(last) }
  })
  let out = below
  for (const m of made) {
    if (m === undefined) continue
    // It wins over a later write of the same pass only where its pass is later.
    const beats = made.map((o) =>
      o === undefined || o === m ? z3.Bool.val(true) : z3.Or(z3.Not(o.has), o.e > m.e ? o.last.lt(m.last) : o.last.le(m.last)),
    )
    const wins = z3.And(m.has, ...beats)
    out = {
      found: z3.If(wins, m.held, out.found),
      value: z3.isFalse(m.held) ? out.value : ite(u, z3.And(wins, m.held), m.value, out.value, at),
    }
  }
  return out
}

// ——— Writing ———

/**
 * `t` with one write on top: under the branch `cond`, `key` set to `value`, or deleted. `named` is the key where the code
 * writes it as a name (`out.team`, `out["team"]`, `{ team: v }`).
 */
export const written = (t: Table, cond: Bool, key: Val, set: boolean, value: Val, at: ts.Node, named?: string): Table => {
  const { L } = t
  const z3 = L.u.z3
  if (t.kind === "object" && key.kind !== "str")
    throw new Unsupported(`a key of a record that is a ${key.kind}: the code writes it at a string`, at)
  if (t.kind === "object" && set && named === "__proto__")
    throw new Unsupported("sets the object's prototype (`__proto__`), which is not modeled", at)
  let c = cond
  if (t.kind === "object" && set && named === undefined) {
    // `__proto__` names the object's prototype: a primitive written there changes nothing, an object is its prototype.
    const proto = key.kind === "str" ? key.term.eq(jsString(z3, "__proto__")) : z3.Bool.val(false)
    const object = value.kind === "record" || value.kind === "array" || (value.kind === "maybe" && value.value?.kind === "record")
    if (object) {
      const where = locate(at)
      oblige(L, {
        key: `key@${where}#here`,
        kind: "key",
        text: at.getText(),
        at: where,
        phase: "here",
        cond,
        goal: z3.Not(proto),
        hints: L.hints.length,
      })
    } else c = z3.And(cond, z3.Not(proto))
  }
  return table(L, t.kind, at, { node: "write", prev: t, write: { cond: c, key, set, value } })
}

/** Whether `t` is what a pass of a loop builds: writes on a marker. */
export const building = (t: Table): boolean => {
  let x: Table = t
  while (x.node === "write") x = x.prev
  return x.node === "marker"
}

/** The writes on `t` since `base`, oldest first, where `t` is `base` with writes on top; `undefined` where it is not. */
export const writesSince = (t: Table, base: Table): ReadonlyArray<Write> | undefined => {
  const out: Array<Write> = []
  let at: Table = t
  while (at !== base) {
    if (at.node !== "write") return undefined
    out.push(at.write)
    at = at.prev
  }
  return out.reverse()
}

/**
 * Two paths' tables, `cond ? a : b`: where both are one table with writes on top, that table with each path's writes
 * under its branch; otherwise a choice between the two.
 */
export const mergeTables = (cond: Bool, a: Table, b: Table, at: ts.Node): Table => {
  if (a === b) return a
  const z3 = a.L.u.z3
  if (a.kind !== b.kind) throw new Unsupported(`a ${a.kind} on one path and a ${b.kind} on another is not modeled`, at)
  const below = new Set<Table>()
  for (let x: Table = a; ; x = x.prev) {
    below.add(x)
    if (x.node !== "write") break
  }
  let common: Table | undefined
  for (let x: Table = b; ; x = x.prev) {
    if (below.has(x)) {
      common = x
      break
    }
    if (x.node !== "write") break
  }
  if (common === undefined) return table(a.L, a.kind, at, { node: "ite", cond, a, b })
  let out = common
  for (const w of writesSince(a, common)!)
    out = table(a.L, a.kind, at, { node: "write", prev: out, write: { ...w, cond: z3.And(cond, w.cond) } })
  for (const w of writesSince(b, common)!)
    out = table(a.L, a.kind, at, { node: "write", prev: out, write: { ...w, cond: z3.And(z3.Not(cond), w.cond) } })
  return out
}

// ——— Its keys, listed ———

/** The keys `t` holds and their values, in its order: written out on the search side, a list of them on the proof side. */
export const listing = (t: Table): Listing => {
  if (t.listed !== undefined) return t.listed
  const l = t.L.u.bound === undefined ? (unwritten(t) ?? proofListing(t)) : searchListing(t)
  t.listed = l
  return l
}

/**
 * A table no write changed, listed exactly on either side: a dictionary the code was given, its own entries; nothing;
 * or one of two such, by the branch (`input.card ?? {}`). Undefined for any other.
 */
const unwritten = (t: Table): Listing | undefined => {
  const z3 = t.L.u.z3
  switch (t.node) {
    case "empty": {
      const none: ArrayVal = { kind: "array", length: z3.Int.val(0), size: 0, maxSize: 0, elem: () => UNDEFINED }
      return { keys: { ...none, keyed: heldBy(t, "str") }, values: none }
    }
    case "given": {
      const { keys, values } = t.dict.own!()
      return keys.kind === "array" && values.kind === "array" ? { keys: { ...keys, keyed: heldBy(t, "str") }, values } : undefined
    }
    case "ite": {
      const a = unwritten(t.a)
      const b = a === undefined ? undefined : unwritten(t.b)
      if (a === undefined || b === undefined) return undefined
      const keys = ite(t.L.u, t.cond, a.keys, b.keys, t.at)
      const values = ite(t.L.u, t.cond, a.values, b.values, t.at)
      return keys.kind === "array" && values.kind === "array" ? { keys: { ...keys, keyed: heldBy(t, "str") }, values } : undefined
    }
    default:
      return undefined
  }
}

/** A list of keys bounded by `maxSize`: its length, and its key at each place below the bound. */
interface Slots {
  readonly length: Arith
  readonly maxSize: number
  readonly key: (q: number) => Val
}

const searchListing = (t: Table): Listing => {
  const { L } = t
  const z3 = L.u.z3
  const s = slotsOf(t)
  const values = Array.from({ length: s.maxSize }, (_, q) => lookup(t, s.key(q), t.at).value)
  const pick = (each: (q: number) => Val) =>
    memoElems((j) => {
      if (s.maxSize === 0) return UNDEFINED
      if (z3.isIntVal(j)) {
        const q = Number(j.value())
        return q >= 0 && q < s.maxSize ? each(q) : each(s.maxSize - 1)
      }
      let v = each(s.maxSize - 1)
      for (let q = s.maxSize - 2; q >= 0; q--) v = ite(L.u, j.eq(q), each(q), v, t.at)
      return v
    })
  return {
    keys: { kind: "array", length: s.length, maxSize: s.maxSize, elem: pick(s.key) },
    values: { kind: "array", length: s.length, maxSize: s.maxSize, elem: pick((q) => values[q]!) },
  }
}

/** The keys `t` holds on the search side, in JavaScript's order. */
const slotsOf = (t: Table): Slots => {
  const { L } = t
  const u = L.u
  const z3 = u.z3
  const at = t.at
  switch (t.node) {
    case "empty":
      return { length: z3.Int.val(0), maxSize: 0, key: () => UNDEFINED }
    case "marker":
      throw new Unsupported(`lists \`${t.name}\` in the loop that builds it`, t.at)
    case "loop":
    case "keyed":
      throw new Error("a loop's writes are read whole on the proof side only")
    case "given": {
      const { keys } = t.dict.own!()
      if (keys.kind !== "array") throw new Unsupported("a dictionary whose keys are not a list", at)
      const maxSize = keys.maxSize ?? u.bound ?? 0
      return { length: keys.length, maxSize, key: (q) => keys.elem(z3.Int.val(q)) }
    }
    case "ite": {
      const a = slotsOf(t.a)
      const b = slotsOf(t.b)
      return {
        length: z3.If(t.cond, a.length, b.length),
        maxSize: Math.max(a.maxSize, b.maxSize),
        key: (q) => (q >= a.maxSize ? b.key(q) : q >= b.maxSize ? a.key(q) : ite(u, t.cond, a.key(q), b.key(q), at)),
      }
    }
    case "from": {
      // Each key at its first place: an element is listed where no earlier one is the same key.
      const maxSize = t.arr.maxSize ?? u.bound ?? 0
      const listed = Array.from({ length: maxSize }, (_, q) =>
        z3.And(
          z3.Int.val(q).lt(t.arr.length),
          ...Array.from({ length: q }, (_, p) => z3.Not(same(L, t.key(z3.Int.val(p)), t.key(z3.Int.val(q)), at))),
        ),
      )
      return ordered(
        t,
        Array.from({ length: maxSize }, (_, q) => ({ listed: listed[q]!, key: t.key(z3.Int.val(q)) })),
      )
    }
    case "write": {
      // The table below the writes, then each write that adds a key: one the table did not hold just before, and that no
      // later write deletes. A key of the table below is listed where no write deletes it.
      const chain: Array<Table & { node: "write" }> = []
      let base: Table = t
      while (base.node === "write") {
        chain.unshift(base)
        base = base.prev
      }
      const below = slotsOf(base)
      const deletes = (key: Val, from: number): Bool =>
        z3.Or(
          z3.Bool.val(false),
          ...chain.slice(from).flatMap((x) => (x.write.set ? [] : [z3.And(x.write.cond, same(L, x.write.key, key, at))])),
        )
      const slots: Array<{ listed: Bool; key: Val }> = []
      for (let q = 0; q < below.maxSize; q++) {
        const key = below.key(q)
        slots.push({ listed: z3.And(z3.Int.val(q).lt(below.length), z3.Not(deletes(key, 0))), key })
      }
      chain.forEach((x, m) => {
        const w = x.write
        if (!w.set) return
        slots.push({ listed: z3.And(w.cond, z3.Not(lookup(x.prev, w.key, at).found), z3.Not(deletes(w.key, m + 1))), key: w.key })
      })
      return ordered(t, slots)
    }
  }
}

/**
 * Listed slots in JavaScript's order: a `Map`'s and a `Set`'s as they come; a plain object's array positions first, by
 * number, then the rest as they come.
 */
const ordered = (t: Table, slots: ReadonlyArray<{ readonly listed: Bool; readonly key: Val }>): Slots => {
  const z3 = t.L.u.z3
  const one = (c: Bool): Arith => z3.If(c, z3.Int.val(1), z3.Int.val(0))
  const count = (cs: ReadonlyArray<Bool>): Arith => cs.reduce<Arith>((n, c) => n.add(one(c)), z3.Int.val(0))
  const length = count(slots.map((s) => s.listed))
  let place: Array<Arith>
  if (t.kind !== "object") place = slots.map((_, q) => count(slots.slice(0, q).map((s) => s.listed)))
  else {
    const terms = slots.map((s) => (s.key.kind === "str" ? s.key.term : undefined))
    const index = terms.map((k) => (k === undefined ? z3.Bool.val(false) : isArrayIndex(z3, k)))
    const before = (p: number, q: number): Bool =>
      terms[p] === undefined || terms[q] === undefined ? z3.Bool.val(false) : positionBefore(z3, terms[p], terms[q])
    const positions = count(slots.map((s, q) => z3.And(s.listed, index[q]!)))
    place = slots.map((_, q) =>
      z3.If(
        index[q]!,
        count(slots.map((s, p) => z3.And(s.listed, index[p]!, before(p, q)))),
        positions.add(count(slots.slice(0, q).map((s, p) => z3.And(s.listed, z3.Not(index[p]!))))),
      ),
    )
  }
  return {
    length,
    maxSize: slots.length,
    key: (j) => {
      if (slots.length === 0) return UNDEFINED
      let v = slots[slots.length - 1]!.key
      for (let q = slots.length - 2; q >= 0; q--) v = ite(t.L.u, z3.And(slots[q]!.listed, place[q]!.eq(j)), slots[q]!.key, v, t.at)
      return v
    },
  }
}

/**
 * Where a table's keys come from: each a key that may be held, or every key of a family indexed by `i` where `range`
 * holds, each read in the scope that binds `i`.
 */
type Source = { readonly key: Val } | { readonly i: Arith; readonly range: () => Bool; readonly key: () => Val }

const sourcesOf = (t: Table): Array<Source> => {
  const z3 = t.L.u.z3
  switch (t.node) {
    case "empty":
      return []
    case "marker":
      throw new Unsupported(`lists \`${t.name}\` in the loop that builds it`, t.at)
    case "given": {
      const { keys } = t.dict.own!()
      if (keys.kind !== "array") return []
      const i = z3.Int.const(t.L.u.fresh("own.i"))
      return [{ i, range: () => z3.And(i.ge(0), i.lt(keys.length)), key: () => keys.elem(i) }]
    }
    case "from": {
      const i = z3.Int.const(t.L.u.fresh("from.i"))
      return [{ i, range: () => z3.And(i.ge(0), i.lt(t.arr.length)), key: () => t.key(i) }]
    }
    case "write":
      return [...sourcesOf(t.prev), { key: t.write.key }]
    case "ite":
      return [...sourcesOf(t.a), ...sourcesOf(t.b)]
    case "loop":
      return [
        ...sourcesOf(t.prev),
        ...t.loop.effects.map((w) => {
          const i = z3.Int.const(t.L.u.fresh("pass.i"))
          return { i, range: () => z3.And(i.ge(0), i.lt(t.loop.n), w.cond(i)), key: () => w.key(i) }
        }),
      ]
    case "keyed": {
      const i = z3.Int.const(t.L.u.fresh("pass.i"))
      const { list } = t
      return [...sourcesOf(t.prev), { i, range: () => z3.And(i.ge(0), i.lt(list.length)), key: () => list.elem(i) }]
    }
  }
}

/**
 * The proof side's list of the keys `t` holds: a fresh list, each element a key it holds, and each once (an index of
 * every key, the place it is listed at); and every key it may hold (its sources), where it holds it, listed. Its order
 * is not known.
 */
const proofListing = (t: Table): Listing => {
  const { L } = t
  const u = L.u
  const z3 = u.z3
  const at = t.at
  const sources = sourcesOf(t)
  const keyOf = (s: Source): Val => ("i" in s ? u.within(s.i, s.key).result : s.key)
  const sample = sources.map(keyOf).find((k) => keySort(L, k) !== undefined)
  // A map no write or source fills holds nothing.
  if (sample === undefined) {
    if (sources.length > 0) throw new Unsupported("the keys of a map whose keys are no strings, bigints or booleans", at)
    const none: ArrayVal = { kind: "array", length: z3.Int.val(0), size: 0, maxSize: 0, elem: () => UNDEFINED }
    return { keys: none, values: none }
  }
  const bounds = u.openBounds()
  const name = u.fresh("listed")
  const length = u.leaf([name, "#len"], "int", bounds, "count") as never as Arith
  const sortName = sample.kind === "str" ? "str" : sample.kind === "int" ? "int" : "bool"
  const keyAt = memoElems((j): Val => {
    const term = u.leaf([name, "[]", "$"], sortName, [...bounds, j], sample.kind === "int" ? "bigint" : undefined)
    return sample.kind === "int" ? { kind: "int", origin: "bigint", term: term as Arith } : ({ kind: sample.kind, term } as Val)
  })
  const index = z3.Function.declare(u.fresh("listedAt"), ...bounds.map(() => z3.Int.sort()), keySort(L, sample)!, z3.Int.sort())
  const placeOf = (k: Val): Arith => index.call(...bounds, keyTerm(k)!)
  u.assume(length.ge(0), bounds)
  const j = z3.Int.const(u.fresh("listed.j"))
  const each = u.within(j, () => {
    const k = keyAt(j)
    return z3.And(lookup(t, k, at).found, placeOf(k).eq(j))
  })
  // What is known of each key read (a lookup's facts) holds of every place listed, said beside, as \`elementwise\` says it.
  if (each.facts.length > 0) u.assume(z3.ForAll([j], z3.Implies(z3.And(j.ge(0), j.lt(length)), z3.And(...each.facts))), bounds)
  u.assume(z3.ForAll([j], z3.Implies(z3.And(j.ge(0), j.lt(length), ...each.facts), each.result)), bounds)
  const listedThere = (k: Val): Bool => {
    const p = placeOf(k)
    return z3.And(p.ge(0), p.lt(length), sameKey(L, keyAt(p), k, at))
  }
  for (const s of sources) {
    if (!("i" in s)) {
      if (s.key.kind === sample.kind) u.assume(z3.Implies(lookup(t, s.key, at).found, listedThere(s.key)), u.openBounds())
      continue
    }
    const one = u.within(s.i, () => {
      const k = s.key()
      return { range: s.range(), held: k.kind === sample.kind ? z3.Implies(lookup(t, k, at).found, listedThere(k)) : undefined }
    })
    if (one.result.held === undefined) continue
    if (one.facts.length > 0) u.assume(z3.ForAll([s.i], z3.Implies(one.result.range, z3.And(...one.facts))), bounds)
    u.assume(z3.ForAll([s.i], z3.Implies(z3.And(one.result.range, ...one.facts), one.result.held)), bounds)
  }
  u.abstracted = true
  u.approximations.add(
    "the keys of a map the code builds are known on the proof side as a list of the keys it holds, each once, in an order not known",
  )
  return {
    keys: { kind: "array", length, elem: keyAt, keyed: heldBy(t, sortName) },
    values: { kind: "array", length, elem: memoElems((jj) => lookup(t, keyAt(jj), at).value) },
  }
}

/** A table's keys as a list holds them, each once: those it holds. */
const heldBy = (t: Table, kind: Keyed["kind"]): Keyed => ({ kind, member: (k) => lookup(t, k, t.at).found })

/** How many keys `t` holds. */
export const sizeOf = (t: Table): Val => ({ kind: "int", origin: "count", term: listing(t).keys.length })

/** Whether `t` holds `key`, as a value. */
export const holds = (t: Table, key: Val, at: ts.Node): Val => bool(lookup(t, key, at).found)

// ——— A list a loop builds ———

/**
 * `base` with `items` pushed onto it, each where its branch holds: an array a loop builds, as one of its passes sees it
 * (`exec.ts`). Its pushes are kept apart, so the loop can be read as the pushes of all its passes.
 */
export const pushedArray = (
  u: Universe,
  base: ArrayVal,
  items: ReadonlyArray<{ readonly cond: Bool; readonly value: Val }>,
  at: ts.Node,
): ArrayVal => {
  const z3 = u.z3
  const one = (c: Bool): Arith => z3.If(c, z3.Int.val(1), z3.Int.val(0))
  const places: Array<Arith> = []
  let length = base.length
  for (const item of items) {
    places.push(length)
    length = length.add(one(item.cond))
  }
  return {
    kind: "array",
    length,
    elem: memoElems((j) => {
      let v = base.elem(j)
      for (let q = items.length - 1; q >= 0; q--) v = ite(u, z3.And(items[q]!.cond, j.eq(places[q]!)), items[q]!.value, v, at)
      return v
    }),
    pushes: { base, items },
  }
}

/** The items a pass pushed, as a list of their own: those whose branch holds, in order. */
export const pushedItems = (L: Lowering, items: ReadonlyArray<{ readonly cond: Bool; readonly value: Val }>, at: ts.Node): ArrayVal => {
  const z3 = L.u.z3
  const one = (c: Bool): Arith => z3.If(c, z3.Int.val(1), z3.Int.val(0))
  const places: Array<Arith> = []
  let length: Arith = z3.Int.val(0)
  for (const item of items) {
    places.push(length)
    length = length.add(one(item.cond))
  }
  return {
    kind: "array",
    length,
    maxSize: items.length,
    elem: memoElems((j) => {
      if (items.length === 0) return UNDEFINED
      let v = items[items.length - 1]!.value
      for (let q = items.length - 2; q >= 0; q--) v = ite(L.u, z3.And(items[q]!.cond, j.eq(places[q]!)), items[q]!.value, v, at)
      return v
    }),
  }
}

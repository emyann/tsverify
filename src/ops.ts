// JavaScript's meaning of truthiness, `===`, `<` and friends, `??` and a value
// chosen by a condition, over symbolic values. Every rule here is the language's,
// not TypeScript's: a `number` compares as IEEE-754 does (NaN equals nothing and
// orders with nothing, -0 equals 0, the infinities bound everything else), and a
// string's truthiness is its being non-empty.
import type { Arith, Bool } from "z3-solver"
import type { Universe } from "./universe.ts"
import { KIND, NUM, Unsupported, type Val, jsString, lazyRecord, memoElems, termId } from "./value.ts"
import type ts from "typescript"

/** A read of a value of type `unknown`, refused: it may be anything. */
const refuseOpaque = (what: string, at?: ts.Node): never => {
  throw new Unsupported(
    `${what} of a value of type \`unknown\` is not modeled: such a value is carried and never read; give it a type where it is made (for an error, a \`catch\` that builds a typed one)`,
    at,
  )
}

const T = (u: Universe) => u.z3.Bool.val(true)
const F = (u: Universe) => u.z3.Bool.val(false)

/** The parts of a value that may be null or undefined: both flags, and the value present otherwise. */
const parts = (u: Universe, v: Val): { isNull: Bool; isUndefined: Bool; value: Val | undefined } =>
  v.kind === "opaque"
    ? refuseOpaque("whether it is null or undefined")
    : v.kind === "maybe"
      ? v
      : v.kind === "nullish"
        ? { isNull: v.which === "null" ? T(u) : F(u), isUndefined: v.which === "undefined" ? T(u) : F(u), value: undefined }
        : { isNull: F(u), isUndefined: F(u), value: v }

/** `v == null`: v is null or undefined. */
export const isNullish = (u: Universe, v: Val): Bool => {
  const p = parts(u, v)
  return u.z3.Or(p.isNull, p.isUndefined)
}

/** JavaScript's ToBoolean. */
export const truthy = (u: Universe, v: Val): Bool => {
  const z3 = u.z3
  switch (v.kind) {
    case "bool":
      return v.term
    case "str":
      return z3.Not(v.term.eq(jsString(z3, "")))
    case "num":
      return z3.Or(z3.And(v.cls.eq(NUM.finite), z3.Not(v.real.eq(0))), v.cls.eq(NUM.posInf), v.cls.eq(NUM.negInf))
    case "int":
      return z3.Not(v.term.eq(0))
    case "nullish":
      return F(u)
    case "maybe":
      return z3.And(z3.Not(v.isNull), z3.Not(v.isUndefined), v.value === undefined ? F(u) : truthy(u, v.value))
    case "record":
    case "array":
    case "fn":
    case "builtin":
    case "comp":
      return T(u)
    case "mixed":
      return z3.Or(...v.parts.map((p) => z3.And(v.tag.eq(p.tag), truthy(u, p.value))))
    case "opaque":
      return refuseOpaque("the truth")
  }
}

/** The kind a primitive value is, by `KIND`; `undefined` for any other. */
export const kindOf = (v: Val): number | undefined =>
  v.kind === "bool"
    ? KIND.bool
    : v.kind === "str"
      ? KIND.str
      : v.kind === "num" || (v.kind === "int" && v.origin === "count")
        ? KIND.num
        : v.kind === "int"
          ? KIND.bigint
          : undefined

/** A primitive or a value of more than one kind, as the parts of one: each kind it may be, by its tag. */
const kindParts = (
  u: Universe,
  v: Val,
): { readonly tag: Arith; readonly parts: ReadonlyArray<{ readonly tag: number; readonly value: Val }> } | undefined => {
  if (v.kind === "mixed") return v
  const k = kindOf(v)
  return k === undefined ? undefined : { tag: u.z3.Int.val(k), parts: [{ tag: k, value: v }] }
}

type Num = Extract<Val, { kind: "num" }>

/** A count as a number: finite, and exactly representable (at most 2^32 - 1). */
export const countAsNum = (u: Universe, n: Arith): Num => ({
  kind: "num",
  cls: u.z3.Int.val(NUM.finite),
  real: u.z3.ToReal(n),
  whole: u.z3.Bool.val(true),
  int: n,
})

/** The integer `v` is wherever it is whole: its `int` where it has one, else the real rounded down. */
export const intOf = (u: Universe, v: Num): Arith => v.int ?? u.z3.ToInt(v.real)

/** Whether `v`'s value is a whole number (its class aside): its `whole` where it has one, else `IsInt` of its value. */
export const isWhole = (u: Universe, v: Num): Bool => v.whole ?? u.z3.IsInt(v.real)

/** Whether `v` is `-0`: its `negZero` where it has one; a number made without one never is. */
export const isNegZero = (u: Universe, v: Num): Bool => v.negZero ?? u.z3.Bool.val(false)

/**
 * `Object.is(a, b)` on numbers, SameValue: `===` but that `NaN` is itself, and `-0` is not `0`. Its finite case says,
 * as `numEq` does, that the two are both whole or both not: a law comparing the two would otherwise ask the solver to
 * show it, an integer between two reals less than 1 apart, which it searches for without end.
 */
export const sameValue = (u: Universe, a: Num, b: Num): Bool => {
  const z3 = u.z3
  return z3.Or(
    z3.And(
      a.cls.eq(NUM.finite),
      b.cls.eq(NUM.finite),
      a.real.eq(b.real),
      isWhole(u, a).eq(isWhole(u, b)),
      isNegZero(u, a).eq(isNegZero(u, b)),
    ),
    z3.And(a.cls.eq(NUM.nan), b.cls.eq(NUM.nan)),
    z3.And(a.cls.eq(NUM.posInf), b.cls.eq(NUM.posInf)),
    z3.And(a.cls.eq(NUM.negInf), b.cls.eq(NUM.negInf)),
  )
}

/**
 * `a === b` on numbers: false on NaN, true for -0 and 0, true for one infinity and itself. `hinted`, the `===` the code
 * writes says beside that two equal values are both whole or both not; `<=` and `>=`, which compare values, do not.
 */
const numEq = (u: Universe, a: Num, b: Num, hinted = true): Bool => {
  const z3 = u.z3
  return z3.Or(
    // Two equal values are both whole or both not, said beside: it is so of every two equal reals, and lets the solver
    // carry wholeness across an equality (`y === x + 2`) without searching for it. Said of `a >= b` too, it would ask the
    // solver to show it wherever `>=` holds by equality (`Math.max`), an integer between two reals less than 1 apart,
    // which it searches for without end.
    z3.And(a.cls.eq(NUM.finite), b.cls.eq(NUM.finite), a.real.eq(b.real), hinted ? isWhole(u, a).eq(isWhole(u, b)) : z3.Bool.val(true)),
    z3.And(a.cls.eq(NUM.posInf), b.cls.eq(NUM.posInf)),
    z3.And(a.cls.eq(NUM.negInf), b.cls.eq(NUM.negInf)),
  )
}

/** `a < b` on numbers: false with NaN on either side; -Infinity below every finite value, Infinity above. */
const numLt = (u: Universe, a: Num, b: Num): Bool => {
  const z3 = u.z3
  const fin = (x: Num) => x.cls.eq(NUM.finite)
  return z3.Or(
    z3.And(fin(a), fin(b), a.real.lt(b.real)),
    z3.And(a.cls.eq(NUM.negInf), z3.Or(fin(b), b.cls.eq(NUM.posInf))),
    z3.And(fin(a), b.cls.eq(NUM.posInf)),
  )
}

export type Order = "<" | "<=" | ">" | ">="

const arithCmp = (a: Arith, b: Arith, op: Order): Bool => (op === "<" ? a.lt(b) : op === "<=" ? a.le(b) : op === ">" ? a.gt(b) : a.ge(b))

const numCmp = (u: Universe, a: Num, b: Num, op: Order): Bool =>
  op === "<"
    ? numLt(u, a, b)
    : op === ">"
      ? numLt(u, b, a)
      : op === "<="
        ? u.z3.Or(numLt(u, a, b), numEq(u, a, b, false))
        : u.z3.Or(numLt(u, b, a), numEq(u, a, b, false))

/** `a === b`. Objects compare by identity, which the verifier does not model. */
export const strictEq = (u: Universe, a: Val, b: Val, at: ts.Node): Bool => {
  const z3 = u.z3
  if (a.kind === "opaque" || b.kind === "opaque") return refuseOpaque("`===`", at)
  if (a.kind === "maybe" || b.kind === "maybe" || a.kind === "nullish" || b.kind === "nullish") {
    const pa = parts(u, a)
    const pb = parts(u, b)
    const bothPresent = z3.And(z3.Not(pa.isNull), z3.Not(pa.isUndefined), z3.Not(pb.isNull), z3.Not(pb.isUndefined))
    const valuesEqual = pa.value !== undefined && pb.value !== undefined ? strictEq(u, pa.value, pb.value, at) : F(u)
    return z3.Or(z3.And(pa.isNull, pb.isNull), z3.And(pa.isUndefined, pb.isUndefined), z3.And(bothPresent, valuesEqual))
  }
  // A value of more than one kind equals another where it is of that one's kind and its part there equals it.
  if (a.kind === "mixed") return z3.Or(...a.parts.map((p) => z3.And(a.tag.eq(p.tag), strictEq(u, p.value, b, at))))
  if (b.kind === "mixed") return strictEq(u, b, a, at)
  if (a.kind === "str" && b.kind === "str") return a.term.eq(b.term)
  if (a.kind === "bool" && b.kind === "bool") return a.term.eq(b.term)
  if (a.kind === "num" && b.kind === "num") return numEq(u, a, b)
  if (a.kind === "int" && b.kind === "int" && a.origin === b.origin) return a.term.eq(b.term)
  if (a.kind === "num" && b.kind === "int" && b.origin === "count") return numEq(u, a, countAsNum(u, b.term))
  if (a.kind === "int" && a.origin === "count" && b.kind === "num") return numEq(u, countAsNum(u, a.term), b)
  if (a.kind === "int" && b.kind === "num")
    throw new Unsupported("=== between a bigint and a number is always false; write what you mean", at)
  if (a.kind === "num" && b.kind === "int")
    throw new Unsupported("=== between a number and a bigint is always false; write what you mean", at)
  if (a.kind !== b.kind && isPrimitive(a) && isPrimitive(b)) return F(u)
  throw new Unsupported(`=== between a ${a.kind} and a ${b.kind} compares identity, which is not modeled`, at)
}

const isPrimitive = (v: Val): boolean => v.kind === "str" || v.kind === "bool" || v.kind === "num" || v.kind === "int"

/** `a op b` for `<`, `<=`, `>`, `>=` on numbers and bigints. */
export const compare = (u: Universe, a: Val, b: Val, op: Order, at: ts.Node): Bool => {
  if (a.kind === "int" && b.kind === "int" && a.origin === b.origin) return arithCmp(a.term, b.term, op)
  if (a.kind === "num" && b.kind === "num") return numCmp(u, a, b, op)
  if (a.kind === "num" && b.kind === "int" && b.origin === "count") return numCmp(u, a, countAsNum(u, b.term), op)
  if (a.kind === "int" && a.origin === "count" && b.kind === "num") return numCmp(u, countAsNum(u, a.term), b, op)
  throw new Unsupported(`${op} between a ${describe(a)} and a ${describe(b)} is not modeled`, at)
}

const describe = (v: Val): string => (v.kind === "int" ? v.origin : v.kind)

/** `a ?? b`. */
export const nullishOr = (u: Universe, a: Val, b: () => Val, at: ts.Node): Val => {
  if (a.kind === "opaque") return refuseOpaque("`??`", at)
  if (a.kind === "nullish") return b()
  if (a.kind !== "maybe") return a
  const rest = b()
  return a.value === undefined ? rest : ite(u, isNullish(u, a), rest, a.value, at)
}

/** `a`, or `b()` where `a` is `undefined`: a default value, which `null` does not take, as JavaScript reads one. */
export const undefinedOr = (u: Universe, a: Val, b: () => Val, at: ts.Node): Val => {
  if (a.kind === "opaque") return refuseOpaque("a default value", at)
  if (a.kind === "nullish") return a.which === "undefined" ? b() : a
  if (a.kind !== "maybe" || u.z3.isFalse(a.isUndefined)) return a
  const kept: Val =
    u.z3.isFalse(a.isNull) && a.value !== undefined
      ? a.value
      : { kind: "maybe", isNull: a.isNull, isUndefined: u.z3.Bool.val(false), value: a.value }
  return ite(u, a.isUndefined, b(), kept, at)
}

/** The value `c ? a : b`. */
export const ite = (u: Universe, c: Bool, a: Val, b: Val, at: ts.Node): Val => {
  const z3 = u.z3
  if (a === b || z3.isTrue(c)) return a
  if (z3.isFalse(c)) return b
  // What is known of one side is lost in the merge: nothing reads the merged value but to pass it along.
  if (a.kind === "opaque" || b.kind === "opaque") return { kind: "opaque" }
  if (a.kind === "maybe" || b.kind === "maybe" || a.kind === "nullish" || b.kind === "nullish") {
    if (a.kind === "nullish" && b.kind === "nullish" && a.which === b.which) return a
    const pa = parts(u, a)
    const pb = parts(u, b)
    const value = pa.value !== undefined && pb.value !== undefined ? ite(u, c, pa.value, pb.value, at) : (pa.value ?? pb.value)
    return {
      kind: "maybe",
      isNull: z3.If(c, pa.isNull, pb.isNull),
      isUndefined: z3.If(c, pa.isUndefined, pb.isUndefined),
      value,
    }
  }
  if (a.kind === "str" && b.kind === "str") return { kind: "str", term: z3.If(c, a.term, b.term) }
  if (a.kind === "bool" && b.kind === "bool") return { kind: "bool", term: z3.If(c, a.term, b.term) }
  if (a.kind === "num" && b.kind === "num")
    return {
      kind: "num",
      cls: z3.If(c, a.cls, b.cls),
      real: z3.If(c, a.real, b.real),
      ...(a.whole === undefined && b.whole === undefined ? {} : { whole: z3.If(c, isWhole(u, a), isWhole(u, b)) }),
      ...(a.int === undefined && b.int === undefined ? {} : { int: z3.If(c, intOf(u, a), intOf(u, b)) }),
      ...(a.negZero === undefined && b.negZero === undefined ? {} : { negZero: z3.If(c, isNegZero(u, a), isNegZero(u, b)) }),
    }
  if (a.kind === "int" && b.kind === "int" && a.origin === b.origin)
    return { kind: "int", origin: a.origin, term: z3.If(c, a.term, b.term) }
  // A count where the other path has a number (`let high = xs.length`, later `high = mid`): a number, which holds it.
  if (a.kind === "int" && a.origin === "count" && b.kind === "num") return ite(u, c, countAsNum(u, a.term), b, at)
  if (a.kind === "num" && b.kind === "int" && b.origin === "count") return ite(u, c, a, countAsNum(u, b.term), at)
  if (a.kind === "record" && b.kind === "record" && a.entries !== undefined && b.entries !== undefined) {
    // Two dictionaries, one on each path: a key read in the one its path holds.
    const ea = a.entries
    const eb = b.entries
    return lazyRecord(
      () => undefined,
      undefined,
      undefined,
      { cond: c, a, b },
      undefined,
      (key, call) => {
        const x = ea(key, call)
        const y = eb(key, call)
        return { found: z3.If(c, x.found, y.found), value: ite(u, c, x.value, y.value, at) }
      },
    )
  }
  if (a.kind === "record" && b.kind === "record") {
    // A field one side lacks belongs to a variant the other is not: the type checker lets it be read only where it
    // exists. A read it has narrowed further takes each side apart (`narrowedField`).
    return lazyRecord(
      (name) => {
        const fa = a.field(name)
        const fb = b.field(name)
        // A key both hold only on some paths: absent reads as undefined there.
        if (a.has !== undefined && b.has !== undefined && fa !== undefined && fb === undefined)
          return ite(u, c, fa, { kind: "nullish", which: "undefined" }, at)
        if (a.has !== undefined && b.has !== undefined && fb !== undefined && fa === undefined)
          return ite(u, c, { kind: "nullish", which: "undefined" }, fb, at)
        return fa === undefined ? fb : fb === undefined ? fa : ite(u, c, fa, fb, at)
      },
      a.id !== undefined && b.id !== undefined ? `ite(${termId(c)},${a.id},${b.id})` : undefined,
      a.has !== undefined && b.has !== undefined
        ? (name) => {
            const ha = a.has!(name)
            const hb = b.has!(name)
            return ha === undefined || hb === undefined ? undefined : ha === hb ? ha : z3.If(c, ha, hb)
          }
        : undefined,
      { cond: c, a, b },
    )
  }
  // One function on one path and another on the other: a call is the call of the one its path holds.
  if (a.kind === "builtin" && b.kind === "builtin")
    return {
      kind: "builtin",
      name: `${a.name} or ${b.name}`,
      call: (args, call) => ite(u, c, a.call(args, call), b.call(args, call), call),
    }
  if (a.kind === "array" && b.kind === "array") {
    const maxSize = a.maxSize !== undefined && b.maxSize !== undefined ? Math.max(a.maxSize, b.maxSize) : undefined
    return {
      kind: "array",
      length: z3.If(c, a.length, b.length),
      elem: memoElems((i) => ite(u, c, a.elem(i), b.elem(i), at)),
      ...(a.size !== undefined && a.size === b.size ? { size: a.size } : {}),
      ...(maxSize === undefined ? {} : { maxSize }),
      ...(a.id !== undefined && b.id !== undefined ? { id: `ite(${termId(c)},${a.id},${b.id})` } : {}),
    }
  }
  // Primitives of two kinds, one on each path: a value of more than one kind, its tag the one its path holds.
  const pa = kindParts(u, a)
  const pb = kindParts(u, b)
  if (pa !== undefined && pb !== undefined) {
    const tags = [...new Set([...pa.parts, ...pb.parts].map((p) => p.tag))].sort((x, y) => x - y)
    const parts = tags.map((tag) => {
      const x = pa.parts.find((p) => p.tag === tag)?.value
      const y = pb.parts.find((p) => p.tag === tag)?.value
      return { tag, value: x !== undefined && y !== undefined ? ite(u, c, x, y, at) : (x ?? y)! }
    })
    return { kind: "mixed", tag: z3.If(c, pa.tag, pb.tag), parts }
  }
  throw new Unsupported(`a value that is a ${describe(a)} on one path and a ${describe(b)} on another is not modeled`, at)
}

// JavaScript's meaning of truthiness, `===`, `<` and friends, `??` and a value
// chosen by a condition, over symbolic values. Every rule here is the language's,
// not TypeScript's: a `number` compares as IEEE-754 does (NaN equals nothing and
// orders with nothing, -0 equals 0, the infinities bound everything else), and a
// string's truthiness is its being non-empty.
import type { Arith, Bool } from "z3-solver"
import type { Universe } from "./universe.ts"
import { NUM, Unsupported, type Val, lazyRecord } from "./value.ts"
import type ts from "typescript"

const T = (u: Universe) => u.z3.Bool.val(true)
const F = (u: Universe) => u.z3.Bool.val(false)

/** The parts of a value that may be null or undefined: both flags, and the value present otherwise. */
const parts = (u: Universe, v: Val): { isNull: Bool<"main">; isUndefined: Bool<"main">; value: Val | undefined } =>
  v.kind === "maybe"
    ? v
    : v.kind === "nullish"
      ? { isNull: v.which === "null" ? T(u) : F(u), isUndefined: v.which === "undefined" ? T(u) : F(u), value: undefined }
      : { isNull: F(u), isUndefined: F(u), value: v }

/** `v == null`: v is null or undefined. */
export const isNullish = (u: Universe, v: Val): Bool<"main"> => {
  const p = parts(u, v)
  return u.z3.Or(p.isNull, p.isUndefined)
}

/** JavaScript's ToBoolean. */
export const truthy = (u: Universe, v: Val): Bool<"main"> => {
  const z3 = u.z3
  switch (v.kind) {
    case "bool":
      return v.term
    case "str":
      return z3.Not(v.term.eq(z3.String.val("")))
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
      return T(u)
  }
}

type Num = Extract<Val, { kind: "num" }>

/** A count as a number: finite, and exactly representable (at most 2^32 - 1). */
const countAsNum = (u: Universe, n: Arith<"main">): Num => ({ kind: "num", cls: u.z3.Int.val(NUM.finite), real: u.z3.ToReal(n) })

/** `a === b` on numbers: false on NaN, true for -0 and 0, true for one infinity and itself. */
const numEq = (u: Universe, a: Num, b: Num): Bool<"main"> => {
  const z3 = u.z3
  return z3.Or(
    z3.And(a.cls.eq(NUM.finite), b.cls.eq(NUM.finite), a.real.eq(b.real)),
    z3.And(a.cls.eq(NUM.posInf), b.cls.eq(NUM.posInf)),
    z3.And(a.cls.eq(NUM.negInf), b.cls.eq(NUM.negInf)),
  )
}

/** `a < b` on numbers: false with NaN on either side; -Infinity below every finite value, Infinity above. */
const numLt = (u: Universe, a: Num, b: Num): Bool<"main"> => {
  const z3 = u.z3
  const fin = (x: Num) => x.cls.eq(NUM.finite)
  return z3.Or(
    z3.And(fin(a), fin(b), a.real.lt(b.real)),
    z3.And(a.cls.eq(NUM.negInf), z3.Or(fin(b), b.cls.eq(NUM.posInf))),
    z3.And(fin(a), b.cls.eq(NUM.posInf)),
  )
}

export type Order = "<" | "<=" | ">" | ">="

const arithCmp = (a: Arith<"main">, b: Arith<"main">, op: Order): Bool<"main"> =>
  op === "<" ? a.lt(b) : op === "<=" ? a.le(b) : op === ">" ? a.gt(b) : a.ge(b)

const numCmp = (u: Universe, a: Num, b: Num, op: Order): Bool<"main"> =>
  op === "<"
    ? numLt(u, a, b)
    : op === ">"
      ? numLt(u, b, a)
      : op === "<="
        ? u.z3.Or(numLt(u, a, b), numEq(u, a, b))
        : u.z3.Or(numLt(u, b, a), numEq(u, a, b))

/** `a === b`. Objects compare by identity, which the verifier does not model. */
export const strictEq = (u: Universe, a: Val, b: Val, at: ts.Node): Bool<"main"> => {
  const z3 = u.z3
  if (a.kind === "maybe" || b.kind === "maybe" || a.kind === "nullish" || b.kind === "nullish") {
    const pa = parts(u, a)
    const pb = parts(u, b)
    const bothPresent = z3.And(z3.Not(pa.isNull), z3.Not(pa.isUndefined), z3.Not(pb.isNull), z3.Not(pb.isUndefined))
    const valuesEqual = pa.value !== undefined && pb.value !== undefined ? strictEq(u, pa.value, pb.value, at) : F(u)
    return z3.Or(z3.And(pa.isNull, pb.isNull), z3.And(pa.isUndefined, pb.isUndefined), z3.And(bothPresent, valuesEqual))
  }
  if (a.kind === "str" && b.kind === "str") return a.term.eq(b.term)
  if (a.kind === "bool" && b.kind === "bool") return a.term.eq(b.term)
  if (a.kind === "num" && b.kind === "num") return numEq(u, a, b)
  if (a.kind === "int" && b.kind === "int" && a.origin === b.origin) return a.term.eq(b.term)
  if (a.kind === "num" && b.kind === "int" && b.origin === "count") return numEq(u, a, countAsNum(u, b.term))
  if (a.kind === "int" && a.origin === "count" && b.kind === "num") return numEq(u, countAsNum(u, a.term), b)
  if (a.kind === "int" && b.kind === "num") throw new Unsupported("=== between a bigint and a number is always false; write what you mean", at)
  if (a.kind === "num" && b.kind === "int") throw new Unsupported("=== between a number and a bigint is always false; write what you mean", at)
  if (a.kind !== b.kind && isPrimitive(a) && isPrimitive(b)) return F(u)
  throw new Unsupported(`=== between a ${a.kind} and a ${b.kind} compares identity, which is not modeled`, at)
}

const isPrimitive = (v: Val): boolean => v.kind === "str" || v.kind === "bool" || v.kind === "num" || v.kind === "int"

/** `a op b` for `<`, `<=`, `>`, `>=` on numbers and bigints. */
export const compare = (u: Universe, a: Val, b: Val, op: Order, at: ts.Node): Bool<"main"> => {
  if (a.kind === "int" && b.kind === "int" && a.origin === b.origin) return arithCmp(a.term, b.term, op)
  if (a.kind === "num" && b.kind === "num") return numCmp(u, a, b, op)
  if (a.kind === "num" && b.kind === "int" && b.origin === "count") return numCmp(u, a, countAsNum(u, b.term), op)
  if (a.kind === "int" && a.origin === "count" && b.kind === "num") return numCmp(u, countAsNum(u, a.term), b, op)
  throw new Unsupported(`${op} between a ${describe(a)} and a ${describe(b)} is not modeled`, at)
}

const describe = (v: Val): string => (v.kind === "int" ? v.origin : v.kind)

/** `a ?? b`. */
export const nullishOr = (u: Universe, a: Val, b: () => Val, at: ts.Node): Val => {
  if (a.kind === "nullish") return b()
  if (a.kind !== "maybe") return a
  const rest = b()
  return a.value === undefined ? rest : ite(u, isNullish(u, a), rest, a.value, at)
}

/** The value `c ? a : b`. */
export const ite = (u: Universe, c: Bool<"main">, a: Val, b: Val, at: ts.Node): Val => {
  const z3 = u.z3
  if (a.kind === "maybe" || b.kind === "maybe" || a.kind === "nullish" || b.kind === "nullish") {
    if (a.kind === "nullish" && b.kind === "nullish" && a.which === b.which) return a
    const pa = parts(u, a)
    const pb = parts(u, b)
    const value =
      pa.value !== undefined && pb.value !== undefined ? ite(u, c, pa.value, pb.value, at) : (pa.value ?? pb.value)
    return {
      kind: "maybe",
      isNull: z3.If(c, pa.isNull, pb.isNull),
      isUndefined: z3.If(c, pa.isUndefined, pb.isUndefined),
      value,
    }
  }
  if (a.kind === "str" && b.kind === "str") return { kind: "str", term: z3.If(c, a.term, b.term) }
  if (a.kind === "bool" && b.kind === "bool") return { kind: "bool", term: z3.If(c, a.term, b.term) }
  if (a.kind === "num" && b.kind === "num") return { kind: "num", cls: z3.If(c, a.cls, b.cls), real: z3.If(c, a.real, b.real) }
  if (a.kind === "int" && b.kind === "int" && a.origin === b.origin)
    return { kind: "int", origin: a.origin, term: z3.If(c, a.term, b.term) }
  if (a.kind === "record" && b.kind === "record")
    return lazyRecord((name) => {
      const fa = a.field(name)
      const fb = b.field(name)
      return fa === undefined || fb === undefined ? undefined : ite(u, c, fa, fb, at)
    })
  if (a.kind === "array" && b.kind === "array")
    return { kind: "array", length: z3.If(c, a.length, b.length), elem: (i) => ite(u, c, a.elem(i), b.elem(i), at) }
  throw new Unsupported(`a value that is a ${describe(a)} on one path and a ${describe(b)} on another is not modeled`, at)
}

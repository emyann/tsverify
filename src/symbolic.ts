// A symbolic value for "any value of this TypeScript type", built lazily: a
// field, an element, a length becomes an unknown (a leaf of the universe) only
// when the code reads it. What the type says becomes an assumption beside it: a
// string-literal union's members, `true` for a `true`-typed field, an array's
// length range, null and undefined never both.
//
// The type is trusted as the domain. That is sound only for values that really
// have it: `any`, casts and non-null assertions in the code under verification
// are refused where the lowering meets them, and the report names the reliance.
import ts from "typescript"
import type { Arith } from "z3-solver"
import { operation } from "./computation.ts"
import type { Lowering } from "./lower.ts"
import { MAX_LENGTH, type Universe } from "./universe.ts"
import { NUM, Unsupported, type Val, exactRational, lazyRecord } from "./value.ts"

export interface Typing {
  readonly u: Universe
  readonly checker: ts.TypeChecker
}

const F = ts.TypeFlags

/** The members of a type or of several: unions flattened, each member once. */
const membersOf = (type: ts.Type | ReadonlyArray<ts.Type>): Array<ts.Type> => [
  ...new Set((Array.isArray(type) ? (type as ReadonlyArray<ts.Type>) : [type as ts.Type]).flatMap((m) => (m.isUnion() ? m.types : [m]))),
]

export const symbolicOf = (
  t: Lowering,
  type: ts.Type | ReadonlyArray<ts.Type>,
  segments: ReadonlyArray<string>,
  indices: ReadonlyArray<Arith<"main">>,
  at: ts.Node,
  optional = false,
): Val => {
  const { u } = t
  const z3 = u.z3
  const members = membersOf(type)
  const canNull = members.some((m) => m.flags & F.Null)
  const canUndefined = optional || members.some((m) => m.flags & (F.Undefined | F.Void))
  const rest = members.filter((m) => !(m.flags & (F.Null | F.Undefined | F.Void)))
  const path = segments.join("")

  if (rest.length === 0) {
    if (canNull && canUndefined) return maybeOf(t, segments, indices, true, true, undefined)
    return { kind: "nullish", which: canNull ? "null" : "undefined" }
  }
  if (!canNull && !canUndefined) return present(t, rest, segments, indices, at, path)
  return maybeOf(t, segments, indices, canNull, canUndefined, () => present(t, rest, [...segments, "!"], indices, at, path))

  function maybeOf(
    t: Lowering,
    segments: ReadonlyArray<string>,
    indices: ReadonlyArray<Arith<"main">>,
    canNull: boolean,
    canUndefined: boolean,
    value: (() => Val) | undefined,
  ): Val {
    const isNull = canNull ? (u.leaf([...segments, "?null"], "bool", indices) as never) : z3.Bool.val(false)
    const isUndefined = canUndefined ? (u.leaf([...segments, "?undef"], "bool", indices) as never) : z3.Bool.val(false)
    if (canNull && canUndefined) t.u.assume(z3.Not(z3.And(isNull, isUndefined)), indices)
    return { kind: "maybe", isNull, isUndefined, value: value?.() }
  }
}

/** A value of a union with no null or undefined left in it. */
const present = (
  t: Lowering,
  members: ReadonlyArray<ts.Type>,
  segments: ReadonlyArray<string>,
  indices: ReadonlyArray<Arith<"main">>,
  at: ts.Node,
  path: string,
): Val => {
  const { u, checker } = t
  const z3 = u.z3
  const all = (flags: ts.TypeFlags) => members.every((m) => m.flags & flags)
  const leaf = [...segments, "$"]

  if (all(F.BooleanLike)) {
    const term = u.leaf(leaf, "bool", indices) as never
    const values = new Set(members.map((m) => checker.typeToString(m)))
    if (values.size === 1 && (values.has("true") || values.has("false"))) u.assume(z3.Bool.val(values.has("true")).eq(term), indices)
    return { kind: "bool", term }
  }
  if (all(F.StringLike)) {
    const term = u.leaf(leaf, "str", indices) as never as ReturnType<typeof z3.String.val>
    if (members.every((m) => m.isStringLiteral()))
      u.assume(z3.Or(...members.map((m) => term.eq(z3.String.val((m as ts.StringLiteralType).value)))), indices)
    return { kind: "str", term }
  }
  if (all(F.NumberLike)) {
    const real = u.leaf(leaf, "num", indices) as never as ReturnType<typeof z3.Real.val>
    const cls = u.leaf([...segments, "~cls"], "int", indices) as never as ReturnType<typeof z3.Int.val>
    u.assume(z3.And(cls.ge(NUM.finite), cls.le(NUM.negInf)), indices)
    // The search side keeps to values a double holds exactly (multiples of 2^-10 below 2^40), so every
    // model it finds is a real input; the proof side keeps every real, a superset of the doubles.
    if (u.bound !== undefined)
      u.assume(z3.And(z3.IsInt(real.mul(1024)), real.ge(-(2 ** 40)), real.le(2 ** 40)), indices)
    if (members.every((m) => m.isNumberLiteral()))
      u.assume(
        z3.And(cls.eq(NUM.finite), z3.Or(...members.map((m) => real.eq(z3.Real.val(exactRational((m as ts.NumberLiteralType).value)))))),
        indices,
      )
    return { kind: "num", cls, real }
  }
  if (all(F.BigIntLike)) {
    const term = u.leaf(leaf, "int", indices, "bigint") as never as ReturnType<typeof z3.Int.val>
    if (members.every((m) => m.flags & F.BigIntLiteral))
      u.assume(
        z3.Or(...members.map((m) => term.eq(literalBigint(m as ts.BigIntLiteralType)))),
        indices,
      )
    return { kind: "int", origin: "bigint", term }
  }
  const id = `${path}@${indices.map((i) => i.sexpr()).join(",")}`
  if (members.length > 1) {
    // A union of object types: one record, each field the union of the types the members holding it give it. The
    // type checker lets a field be read only where the value is narrowed to members that have it.
    if (!members.every((m) => m.flags & F.Object && !checker.isArrayType(m) && m.getCallSignatures().length === 0))
      throw new Unsupported(`${path}: a union of ${members.map((m) => checker.typeToString(m)).join(" | ")} is not modeled`, at)
    return lazyRecord((name) => {
      const props = members.flatMap((m) => {
        const p = checker.getPropertyOfType(m, name)
        return p === undefined ? [] : [p]
      })
      if (props.length === 0) return undefined
      const optional = props.some((p) => (p.flags & ts.SymbolFlags.Optional) !== 0)
      return symbolicOf(t, props.map((p) => checker.getTypeOfSymbol(p)), [...segments, `.${name}`], indices, at, optional)
    }, id)
  }
  const type = members[0]!

  // A branded primitive, `bigint & Brand<"X">`: the brand is a name the checker sees and the value does not carry.
  if (type.isIntersection()) {
    const primitive = type.types.find((m) => m.flags & (F.BigIntLike | F.NumberLike | F.StringLike | F.BooleanLike))
    if (primitive !== undefined) {
      u.notes.add("A brand on a primitive is ignored: it names the value's validation, not a property the verifier can use.")
      return present(t, [primitive], segments, indices, at, path)
    }
  }
  if (type.flags & (F.Any | F.Unknown | F.Never)) throw new Unsupported(`${path}: type ${checker.typeToString(type)} is not modeled`, at)
  if (checker.isTupleType(type)) throw new Unsupported(`${path}: tuples are not modeled`, at)
  if (checker.isArrayType(type)) {
    const element = checker.getTypeArguments(type as ts.TypeReference)[0]
    if (element === undefined) throw new Unsupported(`${path}: an array with no element type`, at)
    const length = u.leaf([...segments, "#len"], "int", indices, "count") as never as ReturnType<typeof z3.Int.val>
    u.assume(z3.And(length.ge(0), length.le(u.bound ?? MAX_LENGTH)), indices)
    const elems = new Map<string, Val>()
    return {
      kind: "array",
      length,
      id,
      elem: (i) => {
        const key = i.sexpr()
        let v = elems.get(key)
        if (v === undefined) {
          v = symbolicOf(t, element, [...segments, "[]"], [...indices, i], at)
          elems.set(key, v)
        }
        return v
      },
    }
  }
  const signatures = type.getCallSignatures()
  if (signatures.length > 0) {
    // A method of something the code is given: an operation, when an adapter says its result is a computation.
    if (signatures.length > 1) throw new Unsupported(`${path}: an overloaded function is not modeled`, at)
    const returns = signatures[0]!.getReturnType()
    for (const a of t.adapters) {
      const op = a.operation?.(t, returns)
      if (op === undefined) continue
      const last = segments.at(-1) ?? ""
      if (indices.length > 0 || !last.startsWith(".")) throw new Unsupported(`${path}: an operation is a method of a value given to the code`, at)
      const target = segments.slice(0, -1).join("").replace(/[!$]/g, "")
      return operation(t, target, last.slice(1), op, at)
    }
    throw new Unsupported(`${path}: a function as data is not modeled (no adapter reads its result as a computation)`, at)
  }
  if (type.flags & F.Object || type.isIntersection())
    return lazyRecord((name) => {
      const prop = checker.getPropertyOfType(type, name)
      if (prop === undefined) return undefined
      const propType = checker.getTypeOfSymbol(prop)
      return symbolicOf(t, propType, [...segments, `.${name}`], indices, at, (prop.flags & ts.SymbolFlags.Optional) !== 0)
    }, id)
  throw new Unsupported(`${path}: type ${checker.typeToString(type)} is not modeled`, at)
}

const literalBigint = (m: ts.BigIntLiteralType): bigint =>
  (m.value.negative ? -1n : 1n) * BigInt(m.value.base10Value)

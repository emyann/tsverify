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
import type { Arith, Bool } from "z3-solver"
import { collectionOf, dictionaryOf } from "./collections.ts"
import { operation } from "./computation.ts"
import { ite } from "./ops.ts"
import type { Lowering } from "./lower.ts"
import { MAX_LENGTH, type Universe } from "./universe.ts"
import { KIND, NUM, UNDEFINED, Unsupported, type Val, exactRational, jsString, lazy, lazyRecord, memoElems, termId } from "./value.ts"

export interface Typing {
  readonly u: Universe
  readonly checker: ts.TypeChecker
  /**
   * Whether the program is compiled with `noUncheckedIndexedAccess`: an element read's type then says where it may be
   * missing, and a type that does not was narrowed by a check the code made.
   */
  readonly unchecked?: boolean
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
  indices: ReadonlyArray<Arith>,
  at: ts.Node,
  optional = false,
): Val => {
  const { u } = t
  const z3 = u.z3
  const members = membersOf(type)
  // `unknown` (or a union it absorbed, or a field marked optional on it): a value passed along, never read.
  if (members.some((m) => m.flags & F.Unknown)) return { kind: "opaque" }
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
    indices: ReadonlyArray<Arith>,
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

/** The types the members of a union give field `name`, each member that has it. */
const fieldTypes = (t: Lowering, members: ReadonlyArray<ts.Type>, name: string): Array<ts.Type> =>
  members.flatMap((m) => {
    const p = t.checker.getPropertyOfType(m, name)
    return p === undefined ? [] : membersOf(t.checker.getTypeOfSymbol(p))
  })

/** Whether one value holds every type of `types`, as `present` reads a union: one primitive kind, or records. */
const oneKind = (t: Lowering, types: ReadonlyArray<ts.Type>): boolean => {
  const rest = [...new Set(types)].filter((m) => !(m.flags & (F.Null | F.Undefined | F.Void)))
  if (rest.length <= 1 || types.some((m) => m.flags & F.Unknown)) return true
  const all = (flags: ts.TypeFlags) => rest.every((m) => m.flags & flags)
  if (all(F.BooleanLike) || all(F.StringLike) || all(F.NumberLike) || all(F.BigIntLike)) return true
  return rest.every(
    (m) =>
      ((m.flags & F.Object) !== 0 || (m.isIntersection() && m.types.every((x) => (x.flags & F.Object) !== 0))) &&
      !t.checker.isArrayType(m) &&
      m.getCallSignatures().length === 0,
  )
}

/** A value of a union with no null or undefined left in it. */
const present = (
  t: Lowering,
  members: ReadonlyArray<ts.Type>,
  segments: ReadonlyArray<string>,
  indices: ReadonlyArray<Arith>,
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
    if (members.every((m) => m.isStringLiteral())) u.assume(z3.Or(...members.map((m) => term.eq(jsString(z3, m.value)))), indices)
    return { kind: "str", term }
  }
  if (all(F.NumberLike)) {
    const real = u.leaf(leaf, "num", indices) as never as ReturnType<typeof z3.Real.val>
    const cls = u.leaf([...segments, "~cls"], "int", indices) as never as ReturnType<typeof z3.Int.val>
    u.assume(z3.And(cls.ge(NUM.finite), cls.le(NUM.negInf)), indices)
    // Its value is written in whole parts, and the value the code reads is that expression, not the leaf: the solver
    // reasons with a sum of whole numbers, never with `IsInt` of a real, from which it cannot even show the sum of two
    // whole inputs whole. Whether it is whole is a flag of its own. The leaf equals it, for a counterexample to read.
    let value: Arith
    let whole: Bool
    let int: Arith
    if (u.bound !== undefined) {
      // The search side keeps to values a double holds exactly (multiples of 2^-10 below 2^40), so every model it finds
      // is a real input.
      const m = u.leaf([...segments, "~m"], "int", indices) as never as Arith
      u.assume(z3.And(m.ge(-(2 ** 50)), m.le(2 ** 50)), indices)
      value = z3.ToReal(m).div(1024)
      whole = m.mod(1024).eq(0)
      int = m.div(1024)
    } else {
      // The proof side keeps every real, a superset of the doubles: a whole one, or one between two whole ones.
      const w = u.leaf([...segments, "~whole"], "bool", indices) as never as Bool
      const k = u.leaf([...segments, "~k"], "int", indices) as never as Arith
      const j = u.leaf([...segments, "~j"], "int", indices) as never as Arith
      const d = u.leaf([...segments, "~d"], "num", indices) as never as Arith
      u.assume(z3.And(d.gt(0), d.lt(1)), indices)
      value = z3.If(w, z3.ToReal(k), z3.ToReal(j).add(d))
      whole = w
      int = k
      // A real no double holds is no input: a model there is not a counterexample, and the search side is asked instead.
      if (!members.every((m) => m.isNumberLiteral())) {
        u.abstracted = true
        u.approximations.add("a `number` is any real on the proof side, a double or not")
      }
    }
    u.assume(real.eq(value), indices)
    // Whether it is `-0`, a flag of its own: a zero, which only `Object.is` tells apart.
    const negZero = u.leaf([...segments, "~neg0"], "bool", indices) as never as Bool
    u.assume(z3.Implies(negZero, z3.And(cls.eq(NUM.finite), value.eq(0))), indices)
    if (members.every((m) => m.isNumberLiteral()))
      u.assume(z3.And(cls.eq(NUM.finite), z3.Or(...members.map((m) => value.eq(z3.Real.val(exactRational(m.value)))))), indices)
    return { kind: "num", cls, real: value, whole, int, negZero }
  }
  if (all(F.BigIntLike)) {
    const term = u.leaf(leaf, "int", indices, "bigint") as never as ReturnType<typeof z3.Int.val>
    if (members.every((m) => m.flags & F.BigIntLiteral))
      u.assume(z3.Or(...members.map((m) => term.eq(literalBigint(m as ts.BigIntLiteralType)))), indices)
    return { kind: "int", origin: "bigint", term }
  }
  // Primitives of more than one kind (`boolean | "unsigned"`): which kind it is, and its value in each.
  const kindOfType = (m: ts.Type): number | undefined =>
    m.flags & F.BooleanLike
      ? KIND.bool
      : m.flags & F.StringLike
        ? KIND.str
        : m.flags & F.NumberLike
          ? KIND.num
          : m.flags & F.BigIntLike
            ? KIND.bigint
            : undefined
  if (members.length > 1 && members.every((m) => kindOfType(m) !== undefined)) {
    const tags = [...new Set(members.map((m) => kindOfType(m)!))].sort((x, y) => x - y)
    const tag = u.leaf([...segments, "~kind"], "int", indices) as never as Arith
    u.assume(z3.Or(...tags.map((k) => tag.eq(k))), indices)
    const names = ["bool", "str", "num", "bigint"]
    const parts = tags.map((k) => ({
      tag: k,
      value: present(
        t,
        members.filter((m) => kindOfType(m) === k),
        [...segments, `^${names[k]}`],
        indices,
        at,
        `${path}^${names[k]}`,
      ),
    }))
    return { kind: "mixed", tag, parts }
  }
  const id = `${path}@${indices.map(termId).join(",")}`
  if (members.length > 1) {
    // A union of object types: one record, each field the union of the types the members holding it give it. The
    // type checker lets a field be read only where the value is narrowed to members that have it.
    const objectLike = (m: ts.Type): boolean =>
      ((m.flags & F.Object) !== 0 || (m.isIntersection() && m.types.every((x) => (x.flags & F.Object) !== 0))) &&
      !checker.isArrayType(m) &&
      m.getCallSignatures().length === 0
    if (!members.every(objectLike))
      throw new Unsupported(`${path}: a union of ${members.map((m) => checker.typeToString(m)).join(" | ")} is not modeled`, at)
    // A field of one name whose kind differs by member (`{ type: "add"; n: bigint } | { type: "name"; n: string }`) is
    // no one value: the union is then one record per member, and a selector says which it is. A read the checker has
    // narrowed to some members takes theirs (`narrowedField`), and a member's tag is tied to its own fields.
    // So is a union whose members differ in the keys they require (`{ to; action } | { refused }`), which `in` tells apart.
    const required = (m: ts.Type, name: string): boolean => {
      const p = checker.getPropertyOfType(m, name)
      return p !== undefined && (p.flags & ts.SymbolFlags.Optional) === 0
    }
    const keyed = members.some((m) =>
      checker
        .getPropertiesOfType(m)
        .some((p) => required(m, p.name) && members.some((o) => checker.getPropertyOfType(o, p.name) === undefined)),
    )
    if (keyed || members.some((m) => checker.getPropertiesOfType(m).some((p) => !oneKind(t, fieldTypes(t, members, p.name))))) {
      const selector = u.leaf([...segments, "~variant"], "int", indices) as never as ReturnType<typeof z3.Int.val>
      u.assume(z3.And(selector.ge(0), selector.lt(members.length)), indices)
      const variants = members.map((m, k) => present(t, [m], [...segments, `|${k}`], indices, at, `${path}|${k}`))
      return variants.reduceRight((rest, v, k) => ite(u, selector.eq(k), v, rest, at))
    }
    return lazyRecord((name) => {
      const props = members.flatMap((m) => {
        const p = checker.getPropertyOfType(m, name)
        return p === undefined ? [] : [p]
      })
      if (props.length === 0) return undefined
      const optional = props.some((p) => (p.flags & ts.SymbolFlags.Optional) !== 0)
      return symbolicOf(
        t,
        props.map((p) => checker.getTypeOfSymbol(p)),
        [...segments, `.${name}`],
        indices,
        at,
        optional,
      )
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
  if (type.flags & (F.Any | F.Never)) throw new Unsupported(`${path}: type ${checker.typeToString(type)} is not modeled`, at)
  if (checker.isTupleType(type)) {
    // A tuple: an array of its fixed length, each position of its own type, read back as an array (`[k]`, `concrete.ts`).
    const flags = ((type as ts.TypeReference).target as ts.TupleType).elementFlags
    if (flags.some((f) => f & (ts.ElementFlags.Optional | ts.ElementFlags.Rest | ts.ElementFlags.Variadic)))
      throw new Unsupported(`${path}: a tuple with an optional or a rest element is not modeled`, at)
    const parts = checker.getTypeArguments(type as ts.TypeReference)
    const n = parts.length
    const length = u.leaf([...segments, "#len"], "int", indices, "count") as never as ReturnType<typeof z3.Int.val>
    u.assume(length.eq(n), indices)
    const at_ = parts.map((p, k) => lazy(() => symbolicOf(t, p, [...segments, `[${k}]`], indices, at)))
    return {
      kind: "array",
      length,
      size: n,
      maxSize: n,
      elem: memoElems((i) => {
        if (n === 0) return UNDEFINED
        if (z3.isIntVal(i)) {
          const k = Number(i.value())
          return k >= 0 && k < n ? at_[k]!() : UNDEFINED
        }
        let v = at_[n - 1]!()
        for (let k = n - 2; k >= 0; k--) v = ite(u, i.eq(k), at_[k]!(), v, at)
        return v
      }),
    }
  }
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
        const key = termId(i)
        let v = elems.get(key)
        if (v === undefined) {
          v = symbolicOf(t, element, [...segments, "[]"], [...indices, i], at)
          elems.set(key, v)
        }
        return v
      },
    }
  }
  if (isLibDate(type)) return dateOf(t, segments, indices, at, id)
  const keyedBy = checker.getIndexInfosOfType(type).find((info) => info.keyType.flags & F.String)
  if (keyedBy !== undefined && checker.getPropertiesOfType(type).length === 0 && type.getCallSignatures().length === 0) {
    // A dictionary, `Record<string, T>`: the array of its own entries (`dictionaryOf`), read back as a plain object.
    const length = u.leaf([...segments, "#own"], "int", indices, "count") as never as Arith
    u.assume(z3.And(length.ge(0), length.le(u.bound ?? MAX_LENGTH)), indices)
    const keys = memoElems((i) => symbolicOf(t, checker.getStringType(), [...segments, "[]", "{key}"], [...indices, i], at))
    const values = memoElems((i) => symbolicOf(t, keyedBy.type, [...segments, "[]", "{value}"], [...indices, i], at))
    return dictionaryOf(t, { length, key: keys, value: values }, at, id)
  }
  const collection = libCollection(type)
  if (collection !== undefined) return givenCollection(t, collection, type, segments, indices, at, id)
  const signatures = type.getCallSignatures()
  if (signatures.length > 0) {
    // A method of something the code is given: an operation, when an adapter says its result is a computation.
    if (signatures.length > 1) throw new Unsupported(`${path}: an overloaded function is not modeled`, at)
    const returns = signatures[0]!.getReturnType()
    for (const a of t.adapters) {
      const op = a.operation?.(t, returns)
      if (op === undefined) continue
      const last = segments.at(-1) ?? ""
      if (indices.length > 0 || !last.startsWith("."))
        throw new Unsupported(`${path}: an operation is a method of a value given to the code`, at)
      const target = segments.slice(0, -1).join("").replace(/[!$]/g, "")
      return operation(t, target, last.slice(1), op, at)
    }
    // A function the code is given: some function, each call some value of its return type, as many as the calls, and
    // a counterexample leans on what it gave (`opaqueCalls`).
    const name = path.replace(/^\./, "").replace(/[!$]/g, "") || "a function"
    return {
      kind: "builtin",
      name,
      id: `fn:${id}`,
      call: (_args, call) => {
        u.opaqueCalls.add(name)
        u.notes.add(
          "A function the code is given is read as some function that changes nothing: each call gives some value of its return type.",
        )
        return symbolicOf(t, returns, [u.given(`${name}()`, t.guard)], u.openBounds(), call)
      },
    }
  }
  if (type.flags & F.Object || type.isIntersection())
    return lazyRecord(
      (name) => {
        const prop = checker.getPropertyOfType(type, name)
        if (prop === undefined) return undefined
        const propType = checker.getTypeOfSymbol(prop)
        return symbolicOf(t, propType, [...segments, `.${name}`], indices, at, (prop.flags & ts.SymbolFlags.Optional) !== 0)
      },
      id,
      undefined,
      undefined,
      (name) => {
        const prop = checker.getPropertyOfType(type, name)
        return prop === undefined ? false : (prop.flags & ts.SymbolFlags.Optional) === 0 ? true : undefined
      },
    )
  throw new Unsupported(`${path}: type ${checker.typeToString(type)} is not modeled`, at)
}

/** Whether `type` is a `Map` or a `Set` of TypeScript's own library, read-only or not. */
const libCollection = (type: ts.Type): "Map" | "Set" | undefined => {
  const sym = type.getSymbol()
  const name = sym?.getName()
  if (!(sym !== undefined && fromLib(sym))) return undefined
  return name === "Map" || name === "ReadonlyMap" ? "Map" : name === "Set" || name === "ReadonlySet" ? "Set" : undefined
}

/**
 * A `Map` or a `Set` the code is given: the array of its entries (`collectionOf`), each key one the code can compare
 * as the collection does, a string, a boolean or a bigint. A `number` key (where `-0` is `0`) and an object key (by
 * identity) are refused.
 */
const givenCollection = (
  t: Lowering,
  kind: "Map" | "Set",
  type: ts.Type,
  segments: ReadonlyArray<string>,
  indices: ReadonlyArray<Arith>,
  at: ts.Node,
  id: string,
): Val => {
  const { u, checker } = t
  const z3 = u.z3
  const [keyType, valueType] = checker.getTypeArguments(type as ts.TypeReference)
  if (keyType === undefined || (kind === "Map" && valueType === undefined))
    throw new Unsupported(`${segments.join("")}: a \`${kind}\` whose types are not known`, at)
  if (!membersOf(keyType).every((m) => m.flags & (F.StringLike | F.BooleanLike | F.BigIntLike)))
    throw new Unsupported(
      `${segments.join("")}: a \`${kind}\` is read with keys that are strings, booleans or bigints; of \`${checker.typeToString(keyType)}\` it is not modeled`,
      at,
    )
  const length = u.leaf([...segments, kind === "Map" ? "#entries" : "#members"], "int", indices, "count") as never as Arith
  u.assume(z3.And(length.ge(0), length.le(u.bound ?? MAX_LENGTH)), indices)
  const keys = memoElems((i) => symbolicOf(t, keyType, [...segments, "[]", "{key}"], [...indices, i], at))
  const values =
    valueType === undefined || kind === "Set"
      ? undefined
      : memoElems((i) => symbolicOf(t, valueType, [...segments, "[]", "{value}"], [...indices, i], at))
  return collectionOf(t, kind, { length, key: keys, ...(values === undefined ? {} : { value: values }) }, at, id)
}

/** Whether every declaration of `sym` is TypeScript's own library's. */
const fromLib = (sym: ts.Symbol): boolean => {
  const decls = sym.declarations ?? []
  return decls.length > 0 && decls.every((d) => /\/node_modules\/typescript\/lib\//.test(d.getSourceFile().fileName.replaceAll("\\", "/")))
}

/** The largest time a `Date` holds, in milliseconds either side of 1970 (ECMAScript's time values). */
export const MAX_TIME = 8.64e15

/** Whether `type` is the `Date` of TypeScript's own library. */
const isLibDate = (type: ts.Type): boolean => {
  const sym = type.getSymbol()
  return sym?.getName() === "Date" && fromLib(sym)
}

/**
 * A `Date` the code is given: its time value, read through `getTime()` and `valueOf()`, which is `NaN` (an invalid date)
 * or a whole number of milliseconds within `MAX_TIME` of 1970, and never `-0`. Read back as `new Date(time)`
 * (`concrete.ts`, the `@time` segment).
 */
const dateOf = (t: Lowering, segments: ReadonlyArray<string>, indices: ReadonlyArray<Arith>, at: ts.Node, id: string): Val => {
  const { u, checker } = t
  const z3 = u.z3
  const time = present(t, [checker.getNumberType()], [...segments, "@time"], indices, at, `${segments.join("")}@time`)
  if (time.kind !== "num") throw new Error("a time that is no number")
  u.assume(
    z3.Or(
      time.cls.eq(NUM.nan),
      z3.And(time.cls.eq(NUM.finite), time.whole ?? z3.IsInt(time.real), time.real.le(MAX_TIME), time.real.ge(-MAX_TIME)),
    ),
    indices,
  )
  const signed = time.negZero === undefined ? time : { ...time, negZero: z3.Bool.val(false) }
  if (time.negZero !== undefined) u.assume(z3.Not(time.negZero), indices)
  return lazyRecord((name) => {
    if (name === "getTime" || name === "valueOf")
      return {
        kind: "builtin",
        name: `Date.${name}`,
        call: (args, call) => {
          if (args.length > 0) throw new Unsupported(`\`${name}\` takes no argument`, call)
          return signed
        },
      }
    return {
      kind: "builtin",
      name: `Date.${name}`,
      call: (_args, call) => {
        throw new Unsupported(
          `a \`Date\` the code is given is read through \`getTime()\` and \`valueOf()\`; \`${name}\` is not modeled`,
          call,
        )
      },
    }
  }, id)
}

const literalBigint = (m: ts.BigIntLiteralType): bigint => (m.value.negative ? -1n : 1n) * BigInt(m.value.base10Value)

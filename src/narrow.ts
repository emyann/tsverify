// A field read where the type checker has narrowed its object: `c.args[1]` once `c.op === "set"`, `ev.n` once
// `ev.type === "add"`. A value merged from several paths, calls of different operations or the variants of a union,
// holds on some of them no such field, or one of another kind. The checker lets the code read the field only where
// it exists with the type it gives the read, so those paths do not reach the read: it takes the others. When none is
// left, no run reaches the read, and a value of its type stands for it, read by nothing that matters.
import ts from "typescript"
import type { Lowering } from "./lower.ts"
import { ite } from "./ops.ts"
import { symbolicOf } from "./symbolic.ts"
import { UNDEFINED, Unsupported, type Val, lazyRecord } from "./value.ts"

const F = ts.TypeFlags

/** A kind of JavaScript value, as far as a read's type can tell a value apart from another. */
type Family = "bool" | "str" | "num" | "bigint" | "nullish" | "object"

/**
 * The kinds of value a type admits, or more, never fewer; `undefined` when it may be any. An object type admits a
 * primitive the checker finds assignable to it: a string is a `{ length: number }`, and not a `User`.
 */
export const familiesOf = (checker: ts.TypeChecker, type: ts.Type): ReadonlySet<Family> | undefined => {
  const out = new Set<Family>()
  for (const m of type.isUnion() ? type.types : [type]) {
    const f = m.flags
    if (f & F.BooleanLike) out.add("bool")
    else if (f & F.StringLike) out.add("str")
    else if (f & F.NumberLike) out.add("num")
    else if (f & F.BigIntLike) out.add("bigint")
    else if (f & (F.Null | F.Undefined | F.Void)) out.add("nullish")
    else if (f & F.Never) continue
    else if (m.isIntersection()) {
      // A value of `A & B` is a value of each, so of the kinds of any part: `string & { __brand: "Id" }` is a string,
      // which the brand alone does not admit.
      for (const part of m.types) {
        const p = familiesOf(checker, part)
        if (p === undefined) return undefined
        for (const x of p) out.add(x)
      }
    } else if (f & F.NonPrimitive) out.add("object")
    else if (f & F.Object) {
      out.add("object")
      const primitives = [
        ["bool", checker.getBooleanType()],
        ["str", checker.getStringType()],
        ["num", checker.getNumberType()],
        ["bigint", checker.getBigIntType()],
      ] as const
      for (const [family, primitive] of primitives) if (checker.isTypeAssignableTo(primitive, m)) out.add(family)
    } else return undefined
  }
  return out
}

/** The kinds a value may be; `undefined` when it may be any. */
const familiesOfVal = (v: Val): ReadonlySet<Family> | undefined => {
  switch (v.kind) {
    case "bool":
      return new Set(["bool"])
    case "str":
      return new Set(["str"])
    case "num":
      return new Set(["num"])
    case "int":
      return new Set([v.origin === "bigint" ? "bigint" : "num"])
    case "nullish":
      return new Set(["nullish"])
    case "maybe": {
      if (v.value === undefined) return new Set(["nullish"])
      const inner = familiesOfVal(v.value)
      return inner === undefined ? undefined : new Set<Family>(["nullish", ...inner])
    }
    case "mixed": {
      const out = new Set<Family>()
      for (const p of v.parts) for (const f of familiesOfVal(p.value) ?? []) out.add(f)
      return out
    }
    case "opaque":
      return undefined
    default:
      return new Set(["object"])
  }
}

const fits = (v: Val, families: ReadonlySet<Family> | undefined): boolean => {
  const own = familiesOfVal(v)
  return own === undefined || families === undefined || [...own].some((f) => families.has(f))
}

/**
 * A value of `type` on no path: fresh, so nothing is assumed of it. An object, a tuple among them, is a record
 * whose fields are built the same way as they are read.
 */
const unreached = (L: Lowering, type: ts.Type, at: ts.Node): Val => {
  const checker = L.checker
  if ((type.flags & F.Object) !== 0 && !checker.isArrayType(type) && type.getCallSignatures().length === 0)
    return lazyRecord((name) => {
      const p = checker.getPropertyOfType(type, name)
      return p === undefined ? undefined : unreached(L, checker.getTypeOfSymbol(p), at)
    })
  try {
    return symbolicOf(L, type, [L.u.fresh("unreached")], L.u.openBounds(), at)
  } catch (err) {
    if (!(err instanceof Unsupported)) throw err
    throw new Unsupported(
      `\`${at.getText()}\` is read on no path, and a value of its type, ${checker.typeToString(type)}, is not modeled`,
      at,
    )
  }
}

/** What a read found of each merged record already read: records share their paths' records, so each is read once. */
const reads = new WeakMap<Val, Map<string, Val | "none" | undefined>>()

/**
 * Field `name` of a record, read where the checker types its object `objType` and the read itself `type`: the
 * paths of a merged record whose field can be of that type. A field a path lacks is `undefined` there, as in
 * JavaScript, unless the object's narrowed type requires it, which leaves that path out. `undefined` when the
 * read is none the checker's types decide: a field nothing declares, of an object whose keys are not known.
 */
export const narrowedField = (L: Lowering, rec: Val, name: string, objType: ts.Type, type: ts.Type, at: ts.Node): Val | undefined => {
  const checker = L.checker
  const prop = checker.getPropertyOfType(checker.getNonNullableType(objType), name)
  const required = prop !== undefined && (prop.flags & ts.SymbolFlags.Optional) === 0
  const families = familiesOf(checker, type)
  const key = `${name}\0${required}\0${prop !== undefined}\0${families === undefined ? "*" : [...families].sort().join(",")}`
  // What the paths that reach the read hold: their merge, or "none" when the checker narrowed every one away.
  const read = (r: Val): Val | "none" | undefined => {
    if (r.kind !== "record") return fits(r, families) ? r : "none"
    let known = reads.get(r)
    if (known === undefined) reads.set(r, (known = new Map()))
    if (known.has(key)) return known.get(key)
    const found = readOnce(r)
    known.set(key, found)
    return found
  }
  const readOnce = (r: Val & { kind: "record" }): Val | "none" | undefined => {
    if (r.split !== undefined) {
      const a = read(r.split.a)
      const b = read(r.split.b)
      if (a === undefined || b === undefined) return undefined
      if (a === "none") return b
      if (b === "none") return a
      try {
        return ite(L.u, r.split.cond, a, b, at)
      } catch (err) {
        if (!(err instanceof Unsupported) || a.kind === b.kind) throw err
        const kind = (v: Val) => (v.kind === "int" ? v.origin : v.kind)
        throw new Unsupported(
          `\`${at.getText()}\` is a ${kind(a)} on some paths and a ${kind(b)} on others: read it once a check of its object's tag (\`=== "…"\`) has narrowed it to one`,
          at,
        )
      }
    }
    const v = r.field(name)
    if (v !== undefined) return fits(v, families) ? v : "none"
    if (required) return "none"
    return prop !== undefined || r.has?.(name) !== undefined ? UNDEFINED : undefined
  }
  const r = read(rec)
  return r === "none" ? unreached(L, type, at) : r
}

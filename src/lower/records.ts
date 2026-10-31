// Records: an object literal and its own keys, a dictionary read at a key, and `in`.
import ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import { isNullish, ite, strictEq } from "../ops.ts"
import { type Env, type Thunk, UNDEFINED, Unsupported, type Val, jsString, lazyRecord, locate, memoElems } from "../value.ts"
import { type Lowering, bool, later, lowerExpr } from "../lower.ts"
import { unwrapParens } from "./numbers.ts"
import { shown } from "./strings.ts"
import { propertyKey } from "./patterns.ts"

/** What `Object.prototype` holds, which a plain object finds under any key it does not hold itself. */
export const PROTO = [
  "constructor",
  "hasOwnProperty",
  "isPrototypeOf",
  "propertyIsEnumerable",
  "toLocaleString",
  "toString",
  "valueOf",
  "__proto__",
  "__defineGetter__",
  "__defineSetter__",
  "__lookupGetter__",
  "__lookupSetter__",
]

/** Whether `key` names a member of `Object.prototype`. */
const protoKey = (L: Lowering, key: Val, at: ts.Node): Bool =>
  L.u.z3.Or(...PROTO.map((n) => strictEq(L.u, key, { kind: "str", term: jsString(L.u.z3, n) }, at)))

/**
 * `obj[key]` of a dictionary (`Record<string, T>`), read where its type says it may be missing
 * (`noUncheckedIndexedAccess`): the value of the key's entry, `undefined` where it has none. Where it has none and the key
 * is a name `Object.prototype` holds (`"constructor"`, `"toString"`), JavaScript finds that member, a function, which is
 * not modeled: that the key is the dictionary's own or none of those is an obligation, listed under `keys read:`.
 */
export const dictionaryRead = (L: Lowering, d: Extract<Val, { kind: "record" }>, key: Val, at: ts.Node): Val => {
  const z3 = L.u.z3
  // Its type says what the entry is, read so (`noUncheckedIndexedAccess`) or narrowed by a check the code made; with
  // neither, it says the key is there, which may be false.
  const t = L.checker.getTypeAtLocation(at)
  if (L.unchecked !== true && !(t.isUnion() ? t.types : [t]).some((m) => m.flags & ts.TypeFlags.Undefined))
    throw new Unsupported(
      `\`${at.getText()}\` on a record keyed by any string is read where its type says the key is there, which may be false: turn on \`noUncheckedIndexedAccess\``,
      at,
    )
  if (key.kind !== "str" && !(key.kind === "maybe" && key.value?.kind === "str"))
    throw new Unsupported(`a key of a record that is a ${key.kind}: of a string it is read`, at)
  const { found, value } = d.entries!(key, at)
  const literal = ts.isPropertyAccessExpression(at) || (ts.isElementAccessExpression(at) && ts.isStringLiteralLike(at.argumentExpression))
  const named = ts.isPropertyAccessExpression(at)
    ? at.name.text
    : ts.isElementAccessExpression(at) && ts.isStringLiteralLike(at.argumentExpression)
      ? at.argumentExpression.text
      : undefined
  if (!(literal && named !== undefined && !PROTO.includes(named))) {
    const goal = z3.Or(found, z3.Not(protoKey(L, key, at)))
    if (L.mode === "spec" && L.defined !== undefined) L.defined.push(z3.Implies(L.guard, goal))
    else {
      const where = locate(at)
      L.obligations.push({
        key: `key@${where}#here`,
        kind: "key",
        text: at.getText(),
        at: where,
        phase: "here",
        cond: L.guard,
        goal,
        hints: L.hints.length,
      })
    }
  }
  if (value.kind === "maybe")
    return { kind: "maybe", isNull: z3.And(found, value.isNull), isUndefined: z3.Or(z3.Not(found), value.isUndefined), value: value.value }
  return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(found), value }
}

/**
 * `"key" in obj`, of a key written as a string: of an object the code built, whether it holds the key (`has`); of one it
 * is given, whether its type requires the key, every value taken to hold the keys its type declares and no other, as
 * TypeScript's narrowing by `in` takes it; of a union, which member it is (`split`). A key the type makes optional is
 * refused: an absent key and one holding `undefined` read alike.
 */
export const keyIn = (L: Lowering, e: ts.BinaryExpression, env: Env): Val => {
  const z3 = L.u.z3
  const key = unwrapParens(e.left)
  if (!ts.isStringLiteral(key) && !ts.isNoSubstitutionTemplateLiteral(key)) {
    // A key the code computes, of a dictionary: an entry it has, or a name `Object.prototype` holds.
    const target = lowerExpr(L, e.right, env)
    const d = target.kind === "maybe" ? target.value : target
    if (d?.kind === "record" && d.entries !== undefined) {
      const k = shown(L, lowerExpr(L, e.left, env), e.left)
      if (k.kind !== "str") throw new Unsupported(`a key of a record that is a ${k.kind}: of a string it is read`, e.left)
      return bool(z3.Or(d.entries(k, e).found, protoKey(L, k, e)))
    }
    throw new Unsupported('`in` is read with a key written as a string (`"refused" in moved`), or of a dictionary', e.left)
  }
  const name = key.text
  const holds = (v: Val): Bool => {
    if (v.kind === "maybe" && v.value !== undefined) return holds(v.value)
    if (v.kind === "array") {
      if (name === "length") return z3.Bool.val(true)
      throw new Unsupported(`\`${JSON.stringify(name)} in\` an array is not modeled`, e)
    }
    if (v.kind !== "record") throw new Unsupported(`\`in\` of a ${v.kind} is not modeled`, e)
    // A dictionary holds a key it has an entry for, and every name `Object.prototype` holds.
    if (v.entries !== undefined) {
      const key: Val = { kind: "str", term: jsString(z3, name) }
      return z3.Or(v.entries(key, e).found, protoKey(L, key, e))
    }
    const built = v.has?.(name)
    if (built !== undefined) return built
    if (v.split !== undefined) return z3.If(v.split.cond, holds(v.split.a), holds(v.split.b))
    const declared = v.declares?.(name)
    if (declared === undefined)
      throw new Unsupported(
        v.declares === undefined
          ? `\`in\` of a value whose keys the verifier does not know`
          : `\`${JSON.stringify(name)} in\` a value whose type makes \`${name}\` optional is not modeled: an absent key and one holding \`undefined\` read alike; compare the field with \`undefined\``,
        e,
      )
    L.u.notes.add(
      "`in` reads a value the code is given by its type: it holds the keys its type requires, and no key its type does not declare.",
    )
    return z3.Bool.val(declared)
  }
  return bool(holds(lowerExpr(L, e.right, env)))
}

/** Whether every member of `type` declares `name` as a property it requires (not optional, not a method). */
const requiredKey = (checker: ts.TypeChecker, type: ts.Type, name: string): boolean =>
  (type.isUnion() ? type.types : [type]).every((t) => {
    const p = checker.getPropertyOfType(t, name)
    return p !== undefined && !(p.flags & (ts.SymbolFlags.Optional | ts.SymbolFlags.Method))
  })

/**
 * An object literal. A field's value is the last property's that may hold it: a property written in place holds its
 * key; a spread holds the keys of what it spreads, which the verifier knows of an object the code built (`has`) and of
 * nothing else. A spread is read only when a field it may hold is.
 */
export const objectLiteral = (L: Lowering, e: ts.ObjectLiteralExpression, env: Env): Val => {
  const { u } = L
  const z3 = u.z3
  type Part = { readonly key: string; readonly value: Thunk } | { readonly spread: Thunk; readonly node: ts.Node }
  const parts: Array<Part> = e.properties.map((p): Part => {
    if (ts.isPropertyAssignment(p)) return { key: propertyKey(p.name), value: later(L, () => lowerExpr(L, p.initializer, env)) }
    if (ts.isShorthandPropertyAssignment(p)) return { key: p.name.text, value: later(L, () => lowerExpr(L, p.name, env)) }
    if (ts.isSpreadAssignment(p)) return { spread: later(L, () => lowerExpr(L, p.expression, env)), node: p }
    throw new Unsupported("methods and accessors in an object literal are not modeled", p)
  })
  const spreadOf = (v: Val, name: string, at: ts.Node): { has: Bool; value: Val | undefined } => {
    if (v.kind === "nullish") return { has: z3.Bool.val(false), value: undefined }
    if (v.kind === "maybe") {
      if (v.value === undefined) return { has: z3.Bool.val(false), value: undefined }
      const inner = spreadOf(v.value, name, at)
      return { has: z3.And(z3.Not(isNullish(u, v)), inner.has), value: inner.value }
    }
    if (v.kind === "record" && v.has !== undefined) {
      const has = v.has(name)
      if (has !== undefined) return { has, value: v.field(name) }
    }
    // A key its type requires: the value holds it, its own, as a value of its type is taken to be plain data.
    if (
      v.kind === "record" &&
      ts.isSpreadAssignment(at) &&
      requiredKey(L.checker, L.checker.getNonNullableType(L.checker.getTypeAtLocation(at.expression)), name)
    ) {
      u.notes.add(
        "A spread copies each property its value's type requires: the value is taken to be plain data, its properties its own, none a getter.",
      )
      return { has: z3.Bool.val(true), value: v.field(name) }
    }
    throw new Unsupported(
      `\`${name}\` is read from an object built with a spread of a value whose keys the verifier does not know (at run time it may hold more than its type says)`,
      at,
    )
  }
  const resolved = new Map<string, { has: Bool; value: Val | undefined }>()
  const resolve = (name: string) => {
    let r = resolved.get(name)
    if (r !== undefined) return r
    let has: Bool = z3.Bool.val(false)
    let value: Val | undefined
    for (const p of parts) {
      if ("key" in p) {
        if (p.key === name) {
          has = z3.Bool.val(true)
          value = p.value()
        }
        continue
      }
      const sp = spreadOf(p.spread(), name, p.node)
      if (z3.isFalse(sp.has)) continue
      const v = sp.value ?? UNDEFINED
      value = z3.isTrue(sp.has) ? v : ite(u, sp.has, v, value ?? UNDEFINED, p.node)
      has = z3.isTrue(sp.has) ? sp.has : z3.Or(has, sp.has)
    }
    r = { has, value }
    resolved.set(name, r)
    return r
  }
  const record = lazyRecord(
    (name) => {
      const r = resolve(name)
      return z3.isFalse(r.has) ? undefined : (r.value ?? UNDEFINED)
    },
    undefined,
    (name) => resolve(name).has,
  )
  if (parts.some((p) => "spread" in p)) return record
  // Its own keys are the ones written, in the order JavaScript lists them: array positions first, by number.
  const written = [...new Set(parts.map((p) => ("key" in p ? p.key : "")))]
  const position = (k: string) => /^(0|[1-9]\d*)$/.test(k) && Number(k) < 4294967295
  const names = [...written.filter(position).sort((a, b) => Number(a) - Number(b)), ...written.filter((k) => !position(k))]
  const own = () => ({
    keys: tupleOf(
      L,
      names.map((n) => (): Val => ({ kind: "str", term: jsString(z3, n) })),
      () => ({ kind: "str", term: u.leaf([u.fresh("beyond"), "$"], "str", u.openBounds()) as never }),
      e,
    ),
    values: tupleOf(
      L,
      names.map((n) => () => resolve(n).value ?? UNDEFINED),
      () => (names.length === 0 ? UNDEFINED : (resolve(names.at(-1)!).value ?? UNDEFINED)),
      e,
    ),
  })
  return { ...record, own } as Val
}

/** A list of values the code wrote, as an array literal holds them; past its end, `past` (read on no run that happens). */
export const tupleOf = (L: Lowering, items: ReadonlyArray<() => Val>, past: (i: Arith) => Val, at: ts.Node): Val => {
  const z3 = L.u.z3
  return {
    kind: "array",
    length: z3.Int.val(items.length),
    size: items.length,
    maxSize: items.length,
    elem: memoElems((i) => {
      if (z3.isIntVal(i)) {
        const k = Number(i.value())
        return k >= 0 && k < items.length ? items[k]!() : past(i)
      }
      let v = past(i)
      for (let k = items.length - 1; k >= 0; k--) v = ite(L.u, i.eq(k), items[k]!(), v, at)
      return v
    }),
  }
}

/**
 * What `Object.keys`, `Object.values` and `Object.entries` read: the value's own keys and their values, in
 * JavaScript's order. Known of an object the code built with no spread, of a dictionary it is given, and of either of
 * two such on two paths; of anything else refused, since a value may hold more keys than its type says, in any order.
 */
export const ownOf = (L: Lowering, v: Val, name: string, at: ts.Node): { readonly keys: Val; readonly values: Val } => {
  if (v.kind !== "record") throw new Unsupported(`\`${name}\` of a ${v.kind}`, at)
  if (v.own !== undefined) return v.own()
  if (v.split !== undefined) {
    const a = ownOf(L, v.split.a, name, at)
    const b = ownOf(L, v.split.b, name, at)
    return { keys: ite(L.u, v.split.cond, a.keys, b.keys, at), values: ite(L.u, v.split.cond, a.values, b.values, at) }
  }
  throw new Unsupported(
    `\`${name}\` of a value whose keys the verifier does not know: one the code is given may hold more than its type says, in any order; of a dictionary (\`Record<string, T>\`) or an object the code built they are read`,
    at,
  )
}

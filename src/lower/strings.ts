// Strings: template strings, positions as JavaScript counts them, and a string's own methods.
import ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import { countAsNum, intOf, isWhole } from "../ops.ts"
import { type Env, NUM, Unsupported, type Val, identity, jsString, listed, termId } from "../value.ts"
import { type Lowering, bool, lowerExpr } from "../lower.ts"

/**
 * A template string: an unknown string, the same for the same parts (its literal
 * text and its substitutions' identities), and non-empty when its literal text is.
 */
export const template = (L: Lowering, e: ts.TemplateExpression, env: Env): Val => {
  const z3 = L.u.z3
  const text = e.head.text + e.templateSpans.map((s) => s.literal.text).join("")
  const ids = e.templateSpans.map((s) => {
    try {
      return identity(lowerExpr(L, s.expression, env))
    } catch (err) {
      if (err instanceof Unsupported) return undefined
      throw err
    }
  })
  const indices = L.u.openBounds()
  const key = ids.every((i) => i !== undefined)
    ? `template:${e.getSourceFile().fileName}:${e.pos}(${ids.join(",")})[${indices.map(termId).join(",")}]`
    : undefined
  const known = key === undefined ? undefined : L.opaque.get(key)
  if (known !== undefined) return known
  const term = L.u.leaf([L.u.fresh("template"), "$"], "str", indices) as never as ReturnType<typeof z3.String.val>
  if (text.length > 0) L.u.assume(z3.Not(term.eq(jsString(z3, ""))), indices)
  const v: Val = { kind: "str", term }
  if (key !== undefined) L.opaque.set(key, v)
  L.u.notes.add("A template string is an unknown string of its parts: equal parts, equal strings; non-empty when its literal text is.")
  return v
}

/**
 * The index `v` names, as an integer, and where it names one: a count always does, a `number` where it is a finite
 * whole number (`-0` is 0). Elsewhere `term` is some integer, and `whole` false.
 */
export const indexOf = (L: Lowering, v: Val, at: ts.Node): { readonly term: Arith; readonly whole: Bool } => {
  const z3 = L.u.z3
  if (v.kind === "int" && v.origin === "count") return { term: v.term, whole: z3.Bool.val(true) }
  if (v.kind === "num") return { term: intOf(L.u, v), whole: z3.And(v.cls.eq(NUM.finite), isWhole(L.u, v)) }
  throw new Unsupported(`an index that is a ${v.kind}`, at)
}

/**
 * `v`, an argument, where the type checker has shown it neither `null` nor `undefined` (`out === undefined ||
 * s.endsWith(out)`): what it holds, since no run reaches here with it missing.
 */
export const shown = (L: Lowering, v: Val, e: ts.Expression): Val => {
  if (v.kind !== "maybe" || v.value === undefined) return v
  const t = L.checker.getTypeAtLocation(e)
  const parts = t.isUnion() ? t.types : [t]
  return parts.some((m) => m.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined | ts.TypeFlags.Void)) ? v : v.value
}

/**
 * The integer JavaScript makes of a position (`ToIntegerOrInfinity`): a count as it is, a `number` truncated toward 0,
 * NaN as 0, and either infinity said apart, where `t` is 0.
 */
export const positionOf = (
  L: Lowering,
  v: Val,
  what: string,
  at: ts.Node,
): { readonly t: Arith; readonly posInf: Bool; readonly negInf: Bool } => {
  const z3 = L.u.z3
  if (v.kind === "int" && v.origin === "count") return { t: v.term, posInf: z3.Bool.val(false), negInf: z3.Bool.val(false) }
  if (v.kind !== "num") throw new Unsupported(`${what} of a ${v.kind}`, at)
  const truncated = z3.If(isWhole(L.u, v), intOf(L.u, v), z3.If(v.real.ge(0), z3.ToInt(v.real), z3.ToInt(v.real.neg()).neg()))
  return { t: z3.If(v.cls.eq(NUM.finite), truncated, z3.Int.val(0)), posInf: v.cls.eq(NUM.posInf), negInf: v.cls.eq(NUM.negInf) }
}

/**
 * A position `.slice` takes in something `length` long (`v`, or `given` where it is missing or `undefined`): made an
 * integer, counted from the end where negative, then kept between 0 and the length.
 */
export const relativePosition = (L: Lowering, length: Arith, v: Val | undefined, given: Arith, at: ts.Node): Arith => {
  const z3 = L.u.z3
  if (v === undefined || (v.kind === "nullish" && v.which === "undefined")) return given
  const p = positionOf(L, v, "`.slice`", at)
  const counted = z3.If(p.t.lt(0), length.add(p.t), p.t)
  const kept = z3.If(counted.lt(0), z3.Int.val(0), z3.If(counted.gt(length), length, counted))
  return z3.If(p.negInf, z3.Int.val(0), z3.If(p.posInf, length, kept))
}

/**
 * The element `.at(v)` names of something `length` long, as JavaScript finds it: `v` made an integer (NaN is 0, a
 * fraction truncated toward 0), a negative one counted from the end; missing outside, at either infinity among them.
 */
const atPosition = (L: Lowering, length: Arith, v: Val, at: ts.Node): { readonly index: Arith; readonly isUndefined: Bool } => {
  const z3 = L.u.z3
  const p = positionOf(L, v, "`.at`", at)
  const index = z3.If(p.t.lt(0), length.add(p.t), p.t)
  return { index, isUndefined: z3.Or(p.posInf, p.negInf, index.lt(0), index.ge(length)) }
}

/** The element `.at(v)` names in `arr` (`atPosition`). */
export const atIndex = (
  L: Lowering,
  arr: Extract<Val, { kind: "array" }>,
  v: Val,
  at: ts.Node,
): { readonly index: Arith; readonly isUndefined: Bool } => atPosition(L, arr.length, v, at)

/** The methods of a string the verifier reads; any other is refused, naming these. */
export const STRING_METHODS = [
  "startsWith",
  "endsWith",
  "includes",
  "indexOf",
  "charAt",
  "at",
  "slice",
  "trim",
  "trimStart",
  "trimEnd",
] as const
const readStringMethod = (name: string): name is (typeof STRING_METHODS)[number] => (STRING_METHODS as ReadonlyArray<string>).includes(name)

/**
 * A string's method, on its UTF-16 code units, as Z3 holds them (`jsString`): `startsWith`, `endsWith` and `includes`
 * of one string; `indexOf` of one, -1 where it is not there and 0 for `""`; `charAt` and `at` at a position, `""` and
 * `undefined` outside it; and `slice`, its positions counted from the end where negative, and kept inside.
 */
export const stringMethod = (L: Lowering, s: Extract<Val, { kind: "str" }>, name: string, e: ts.CallExpression, env: Env): Val => {
  const z3 = L.u.z3
  const args = e.arguments.map((a) => shown(L, lowerExpr(L, a, env), a))
  const taking = (n: number, said: string): void => {
    if (e.arguments.length !== n) throw new Unsupported(`\`.${name}\` is modeled with ${said}`, e)
  }
  const text = (k: number): Extract<Val, { kind: "str" }>["term"] => {
    const v = args[k]!
    if (v.kind !== "str") throw new Unsupported(`\`.${name}\` of a ${v.kind}`, e.arguments[k])
    return v.term
  }
  const length = s.term.length()
  const str = (term: unknown): Val => ({ kind: "str", term: term as Extract<Val, { kind: "str" }>["term"] })
  if (!readStringMethod(name)) throw new Unsupported(`method \`${name}\` of a string is not modeled: ${listed(STRING_METHODS)} are`, e)
  switch (name) {
    case "startsWith":
      taking(1, "one argument, the prefix")
      return bool(text(0).prefixOf(s.term))
    case "endsWith":
      taking(1, "one argument, the suffix")
      return bool(text(0).suffixOf(s.term))
    case "includes":
      taking(1, "one argument, what to find")
      return bool(s.term.contains(text(0)))
    case "indexOf":
      taking(1, "one argument, what to find")
      return countAsNum(L.u, s.term.indexOf(text(0), 0))
    case "charAt": {
      taking(1, "one argument, the position")
      const p = positionOf(L, args[0]!, "`.charAt`", e.arguments[0]!)
      return str(z3.If(z3.Or(p.posInf, p.negInf), jsString(z3, ""), s.term.at(p.t)))
    }
    case "at": {
      taking(1, "one argument, the position")
      const { index, isUndefined } = atPosition(L, length, args[0]!, e.arguments[0]!)
      return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined, value: str(s.term.at(index)) }
    }
    case "slice": {
      if (args.length > 2) throw new Unsupported("`.slice` takes a start and an end", e)
      const from = relativePosition(L, length, args[0], z3.Int.val(0), e.arguments[0] ?? e)
      const to = relativePosition(L, length, args[1], length, e.arguments[1] ?? e)
      return str(s.term.extract(from, z3.If(to.gt(from), to.sub(from), z3.Int.val(0))))
    }
    case "trim":
    case "trimStart":
    case "trimEnd":
      taking(0, "no argument")
      return str(trimmed(L, s.term, name === "trim" || name === "trimStart", name === "trim" || name === "trimEnd"))
  }
}

/** The code units JavaScript's `trim` takes off: its white space and its line terminators. */
const WHITE = ["\t", "\n", "\v", "\f", "\r", " ", "\u00a0", "\u1680", "\u2028", "\u2029", "\u202f", "\u205f", "\u3000", "\ufeff"]

/**
 * `s` with its white space taken off its start (`start`) and its end (`end`), as `trim`, `trimStart` and `trimEnd` take it:
 * the part `t` of `s = p + t + q` where `p` and `q` are white space alone and `t` starts and ends with a code unit that
 * is not, or is empty. That part is one, whatever `s` is.
 */
const trimmed = (
  L: Lowering,
  s: Extract<Val, { kind: "str" }>["term"],
  start: boolean,
  end: boolean,
): Extract<Val, { kind: "str" }>["term"] => {
  const { u } = L
  const z3 = u.z3
  const white = z3.Union(z3.Range(jsString(z3, "\u2000"), jsString(z3, "\u200a")), ...WHITE.map((c) => z3.Re.toRe(jsString(z3, c))))
  const any = z3.AllChar(z3.Re.sort(z3.String.sort()))
  const other = z3.Diff(any, white)
  const indices = u.openBounds()
  const part = (what: string) => u.leaf([u.fresh(what), "$"], "str", indices) as never as Extract<Val, { kind: "str" }>["term"]
  const t = part("trimmed")
  const p = start ? part("trim.start") : jsString(z3, "")
  const q = end ? part("trim.end") : jsString(z3, "")
  const body =
    start && end
      ? z3.Option(z3.ReConcat(other, z3.Option(z3.ReConcat(z3.Star(any), other))))
      : start
        ? z3.Option(z3.ReConcat(other, z3.Star(any)))
        : z3.Option(z3.ReConcat(z3.Star(any), other))
  u.assume(z3.And(s.eq(p.concat(t).concat(q)), z3.InRe(p, z3.Star(white)), z3.InRe(q, z3.Star(white)), z3.InRe(t, body)), indices)
  return t
}

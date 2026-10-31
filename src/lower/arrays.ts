// Arrays: an element at an index, an array literal, and an array's methods, each said of every element.
import ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import { isNullish, ite, strictEq, truthy } from "../ops.ts"
import { narrowedField } from "../narrow.ts"
import { symbolicOf } from "../symbolic.ts"
import { type Env, UNDEFINED, Unsupported, type Val, jsString, listed, memoElems, termId } from "../value.ts"
import { type Lowering, bool, later, lowerCall, lowerExpr, member, optionally } from "../lower.ts"
import { atIndex, indexOf, relativePosition, shown } from "./strings.ts"
import { PROTO, dictionaryRead } from "./records.ts"
import { fresh } from "./numbers.ts"

const K = ts.SyntaxKind

/** `xs[i]` on an array or a string at any index, missing outside it; `t[k]` for a whole-number literal k on a tuple (or any record), its field `k`. */
export const elementAccess = (L: Lowering, e: ts.ElementAccessExpression, env: Env): Val => {
  const k = literalIndex(e.argumentExpression)
  const obj = lowerExpr(L, e.expression, env)
  return optionally(L, obj, e, e.expression, (v) => {
    // A tuple's position, or a literal array's, at a literal index it has: there, as its type says.
    if (v.kind === "array" && v.size !== undefined && k !== undefined && k >= 0n && k < BigInt(v.size))
      return v.elem(L.u.z3.Int.val(Number(k)))
    if (v.kind === "array") {
      // Its type says what the element is; without `noUncheckedIndexedAccess` it says the element is there, which may be
      // false: the read is refused there.
      const t = L.checker.getTypeAtLocation(e)
      if (!(t.isUnion() ? t.types : [t]).some((m) => m.flags & ts.TypeFlags.Undefined))
        throw new Unsupported(
          `\`${e.getText()}\` on an array is read where its type says it may be missing: turn on \`noUncheckedIndexedAccess\`, or write \`${e.expression.getText()}.at(${e.argumentExpression.getText()})\``,
          e,
        )
      const z3 = L.u.z3
      // A literal index stays a literal, which reads that one element exactly.
      const { term, whole } =
        k !== undefined && k >= 0n
          ? { term: z3.Int.val(Number(k)), whole: z3.Bool.val(true) }
          : indexOf(L, lowerExpr(L, e.argumentExpression, env), e.argumentExpression)
      return {
        kind: "maybe",
        isNull: z3.Bool.val(false),
        isUndefined: z3.Not(z3.And(whole, term.ge(0), term.lt(v.length))),
        value: v.elem(term),
      }
    }
    if (v.kind === "str") {
      // A code unit, as an array's element is read: missing wherever the index is no whole number inside the string.
      const t = L.checker.getTypeAtLocation(e)
      if (!(t.isUnion() ? t.types : [t]).some((m) => m.flags & ts.TypeFlags.Undefined))
        throw new Unsupported(
          `\`${e.getText()}\` on a string is read where its type says it may be missing: turn on \`noUncheckedIndexedAccess\`, or write \`${e.expression.getText()}.charAt(${e.argumentExpression.getText()})\``,
          e,
        )
      const z3 = L.u.z3
      const { term, whole } =
        k !== undefined && k >= 0n
          ? { term: z3.Int.val(Number(k)), whole: z3.Bool.val(true) }
          : indexOf(L, lowerExpr(L, e.argumentExpression, env), e.argumentExpression)
      return {
        kind: "maybe",
        isNull: z3.Bool.val(false),
        isUndefined: z3.Not(z3.And(whole, term.ge(0), term.lt(v.term.length()))),
        value: { kind: "str", term: v.term.at(term) },
      }
    }
    if (v.kind === "record" && v.entries !== undefined) {
      const key = ts.isStringLiteralLike(e.argumentExpression)
        ? ({ kind: "str", term: jsString(L.u.z3, e.argumentExpression.text) } as const)
        : shown(L, lowerExpr(L, e.argumentExpression, env), e.argumentExpression)
      return dictionaryRead(L, v, key, e)
    }
    if (v.kind === "record" && k === undefined) {
      // A key the type checker holds to a few names (`why[status]`, `status: "running" | "failed"`): the field of the
      // name it is, read as each one is.
      const kt = L.checker.getTypeAtLocation(e.argumentExpression)
      const names = (kt.isUnion() ? kt.types : [kt]).map((m) => (m.isStringLiteral() ? m.value : undefined))
      if (names.length > 0 && names.every((n) => n !== undefined)) {
        const proto = names.find((n) => PROTO.includes(n) && v.field(n) === undefined)
        if (proto !== undefined)
          throw new Unsupported(`\`${e.getText()}\` may be \`${proto}\`, a name \`Object.prototype\` holds, which is not modeled`, e)
        const key = lowerExpr(L, e.argumentExpression, env)
        const objType = L.checker.getTypeAtLocation(e.expression)
        const last = names.at(-1)!
        return names
          .slice(0, -1)
          .reduceRight<Val>(
            (rest, n) => ite(L.u, strictEq(L.u, key, { kind: "str", term: jsString(L.u.z3, n) }, e), member(L, v, n, e, objType), rest, e),
            member(L, v, last, e, objType),
          )
      }
    }
    if (k === undefined || k < 0n) throw new Unsupported(`an element at a computed index of a ${v.kind} is not read`, e)
    if (v.kind === "record") {
      const narrowed = narrowedField(L, v, String(k), L.checker.getTypeAtLocation(e.expression), L.checker.getTypeAtLocation(e), e)
      if (narrowed !== undefined) return narrowed
      const f = v.field(String(k))
      if (f === undefined) throw new Unsupported(`no element ${k}`, e)
      return f
    }
    throw new Unsupported(`an element of a ${v.kind} is not read`, e)
  })
}

/** A whole-number literal argument, such as the -1 of `.at(-1)`. */
const literalIndex = (e: ts.Expression): bigint | undefined => {
  if (ts.isNumericLiteral(e) && /^\d+$/.test(e.text)) return BigInt(e.text)
  if (ts.isPrefixUnaryExpression(e) && e.operator === K.MinusToken && ts.isNumericLiteral(e.operand) && /^\d+$/.test(e.operand.text))
    return -BigInt(e.operand.text)
  return undefined
}

/**
 * `f` read at the index `i` a quantifier binds (`quantified`), or at one element written out, where `inRange` holds:
 * with what its `number` operations need said of every element, for they name `i` and must not reach past the
 * quantifier. In a law or a `requires`, where they are exact (`exactSpec`); in the program, their obligations, each
 * goal then held of every element.
 */
export const elementwise = (
  L: Lowering,
  i: Arith,
  inRange: Bool,
  f: () => Bool,
  quantified: boolean,
): { readonly result: Bool; readonly facts: ReadonlyArray<Bool> } => {
  const z3 = L.u.z3
  const outer = L.exact
  const inner: Array<Bool> = []
  if (outer !== undefined) L.exact = inner
  const before = L.obligations.length
  try {
    const out = quantified ? L.u.within(i, f) : { result: f(), facts: [] }
    // What is known of each element (its type's facts, a declared function's laws) holds of every element in range, read
    // or not: said of each beside the quantifier, so that a statement of every element is not made empty, at one the
    // code never reads, by facts left free there.
    if (quantified && out.facts.length > 0) L.u.assume(z3.ForAll([i], z3.Implies(inRange, z3.And(...out.facts))), L.u.openBounds())
    const hyp = z3.And(inRange, ...out.facts)
    const each = (goal: Bool) => (quantified ? z3.ForAll([i], z3.Implies(hyp, goal)) : z3.Implies(hyp, goal))
    if (outer !== undefined && inner.length > 0) outer.push(each(z3.And(...inner)))
    for (let k = before; k < L.obligations.length; k++) {
      const o = L.obligations[k]!
      L.obligations[k] = { ...o, cond: L.guard, goal: each(z3.Implies(o.cond, o.goal)) }
    }
    return out
  } finally {
    L.exact = outer
  }
}

/** The methods of an array the verifier reads (`push` is a statement's: `exec.ts`); any other is refused, naming these. */
export const ARRAY_METHODS = [
  "at",
  "find",
  "toReversed",
  "reverse",
  "slice",
  "some",
  "every",
  "includes",
  "map",
  "join",
  "flatMap",
  "filter",
] as const
const readArrayMethod = (name: string): name is (typeof ARRAY_METHODS)[number] => (ARRAY_METHODS as ReadonlyArray<string>).includes(name)

export const arrayMethod = (L: Lowering, arr: Extract<Val, { kind: "array" }>, name: string, e: ts.CallExpression, env: Env): Val => {
  const { u } = L
  const z3 = u.z3
  const arg = (k: number): ts.Expression => {
    const a = e.arguments[k]
    if (a === undefined) throw new Unsupported(`\`.${name}\` with no argument ${k + 1}`, e)
    return a
  }
  /** The function the method is given, written in the code, called at an index with the element and the index. */
  const given = (): ((i: Arith) => Val) => {
    if (e.arguments.length !== 1) throw new Unsupported(`\`.${name}\` with a \`this\` argument is not modeled`, e)
    const f = lowerExpr(L, arg(0), env)
    if (f.kind !== "fn") throw new Unsupported(`\`.${name}\` of a ${f.kind}: a function the code writes is read`, e)
    if (f.node.parameters.length > 2) throw new Unsupported(`\`.${name}\` with a callback reading the array is not modeled`, f.node)
    return (i) => lowerCall(L, f.node, f.env, [arr.elem(i), { kind: "int", origin: "count", term: i }], e)
  }
  /** Its truth at an index (`.find`, `.some`), read again where it is asked, under the branch that asks. */
  const predicate = (): ((i: Arith) => Bool) => {
    const call = given()
    return (i) => truthy(u, call(i))
  }
  /** Its value at each index (`.map`, `.flatMap`), each read once. */
  const callback = (): ((i: Arith) => Val) => memoElems(given())
  /** `exists` (or `forall`) an index of the array where `p` holds, with the facts about element i inside. */
  /** How many elements to write a quantifier out over: the array's own bound (exact on both sides), else the search side's. */
  const writtenOut = arr.maxSize ?? u.bound
  /**
   * The callback run on every element, read or not, as JavaScript runs it: what each call obliges (an exact operation),
   * it obliges of each element there is, written out over the bound or said of every index.
   */
  const eachCall = (apply: (i: Arith) => Val): void => {
    const run = (i: Arith, inRange: Bool, quantified: boolean) =>
      elementwise(
        L,
        i,
        inRange,
        () => {
          apply(i)
          return z3.Bool.val(true)
        },
        quantified,
      )
    if (writtenOut !== undefined)
      for (let k = 0; k < writtenOut; k++) {
        const i = z3.Int.val(k)
        run(i, i.lt(arr.length), false)
      }
    else {
      const i = z3.Int.const(u.fresh("i"))
      run(i, z3.And(i.ge(0), i.lt(arr.length)), true)
    }
  }
  /** What the proof side knows of a fold over an array of unknown length (`.join`, `.flatMap`): what is said beside, no more. */
  const folded = (what: string): void => {
    u.abstracted = true
    u.approximations.add(`\`${e.getText()}\` is known on the proof side only ${what}`)
  }
  const quantify = (q: "exists" | "forall", p: (i: Arith) => Bool): Bool => {
    if (writtenOut !== undefined) {
      // Written out: element k for each k below the bound, counted only where k < length.
      const each = Array.from({ length: writtenOut }, (_, k) => {
        const i = z3.Int.val(k)
        const { result } = elementwise(L, i, i.lt(arr.length), () => p(i), false)
        return q === "exists" ? z3.And(i.lt(arr.length), result) : z3.Implies(i.lt(arr.length), result)
      })
      return q === "exists" ? z3.Or(z3.Bool.val(false), ...each) : z3.And(z3.Bool.val(true), ...each)
    }
    const i = z3.Int.const(u.fresh("i"))
    const inRange = z3.And(i.ge(0), i.lt(arr.length))
    const { result, facts } = elementwise(L, i, inRange, () => p(i), true)
    return q === "exists"
      ? z3.Exists([i], z3.And(inRange, ...facts, result))
      : z3.ForAll([i], z3.Implies(z3.And(inRange, ...facts), result))
  }
  if (!readArrayMethod(name)) throw new Unsupported(`array method \`.${name}\` is not modeled: ${listed(ARRAY_METHODS)} are`, e)
  switch (name) {
    case "at": {
      if (e.arguments.length !== 1) throw new Unsupported("`.at` with other than one argument", e)
      const k = literalIndex(arg(0))
      if (k === undefined) {
        const { index, isUndefined } = atIndex(L, arr, lowerExpr(L, arg(0), env), arg(0))
        return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined, value: arr.elem(index) }
      }
      if (arr.size !== undefined) {
        const index = k < 0n ? arr.size + Number(k) : Number(k)
        return index < 0 || index >= arr.size ? { kind: "nullish", which: "undefined" } : arr.elem(z3.Int.val(index))
      }
      const index = k < 0n ? arr.length.add(z3.Int.val(k)) : z3.Int.val(k)
      return {
        kind: "maybe",
        isNull: z3.Bool.val(false),
        isUndefined: z3.Or(index.lt(0), index.ge(arr.length)),
        value: arr.elem(index),
      }
    }
    case "find": {
      const { found, k } = firstIndex(L, arr, predicate())
      return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(found), value: arr.elem(k) }
    }
    case "toReversed":
    case "reverse": {
      // `reverse` turns the array it is called on around and returns it: read where nothing else holds that array, a
      // copy made where it is called (`[...xs].reverse()`), so that no other name sees the change.
      if (e.arguments.length > 0) throw new Unsupported(`\`.${name}\` takes no argument`, e)
      if (name === "reverse" && !fresh(e))
        throw new Unsupported(
          "`.reverse()` changes the array it is called on, which is read only of a copy made there: write `[...xs].reverse()` or `xs.toReversed()`",
          e,
        )
      const last = arr.length.sub(1)
      return {
        kind: "array",
        length: arr.length,
        elem: memoElems((i) => arr.elem(last.sub(i))),
        ...(arr.size === undefined ? {} : { size: arr.size }),
        ...(arr.maxSize === undefined ? {} : { maxSize: arr.maxSize }),
      }
    }
    case "slice":
      return slice(
        L,
        arr,
        e.arguments.map((a) => shown(L, lowerExpr(L, a, env), a)),
        e,
      )
    case "some":
      return bool(quantify("exists", predicate()))
    case "every":
      return bool(quantify("forall", predicate()))
    case "includes": {
      if (e.arguments.length !== 1) throw new Unsupported("`.includes(x, from)` is not modeled", e)
      const x = lowerExpr(L, arg(0), env)
      // `includes` compares as `===` does but for NaN, which only a `number` can be: bigints and counts are whole.
      // A value that may be missing is compared as `===` compares it: `undefined` is no string.
      const present = x.kind === "maybe" ? x.value : x
      if (present?.kind === "num")
        throw new Unsupported(
          "`.includes` of a `number` finds NaN, which `===` does not, and is not modeled: write `.some((y) => y === x)`",
          e,
        )
      if (present !== undefined && present.kind !== "str" && present.kind !== "bool" && present.kind !== "int")
        throw new Unsupported(`\`.includes\` of a ${x.kind} is not modeled: of a string, a boolean or a bigint it is`, e)
      return bool(quantify("exists", (i) => strictEq(u, arr.elem(i), x, e)))
    }
    case "map": {
      const apply = callback()
      eachCall(apply)
      return {
        kind: "array",
        length: arr.length,
        elem: apply,
        ...(arr.size === undefined ? {} : { size: arr.size }),
        ...(arr.maxSize === undefined ? {} : { maxSize: arr.maxSize }),
      }
    }
    case "join": {
      if (e.arguments.length > 1) throw new Unsupported("`.join` takes one separator", e)
      const sepVal = e.arguments.length === 0 ? undefined : lowerExpr(L, arg(0), env)
      if (sepVal !== undefined && sepVal.kind !== "str") throw new Unsupported(`\`.join\` with a separator that is a ${sepVal.kind}`, e)
      const sep = sepVal?.term ?? jsString(z3, ",")
      // An element as `join` writes it: a string as it is, `null` and `undefined` as nothing.
      const piece = (i: Arith): Extract<Val, { kind: "str" }>["term"] => {
        const v = arr.elem(i)
        if (v.kind === "str") return v.term
        if (v.kind === "nullish") return jsString(z3, "")
        if (v.kind === "maybe" && v.value?.kind === "str") return z3.If(isNullish(u, v), jsString(z3, ""), v.value.term)
        throw new Unsupported(
          `\`.join\` of an array of ${v.kind === "maybe" ? (v.value?.kind ?? "nothing") : v.kind}: of strings it is read`,
          e,
        )
      }
      const empty = jsString(z3, "")
      if (writtenOut !== undefined) {
        // Written out: what it is of each length up to the bound.
        let joined = empty
        let prefix = empty
        for (let k = 0; k < writtenOut; k++) {
          prefix = k === 0 ? piece(z3.Int.val(0)) : prefix.concat(sep).concat(piece(z3.Int.val(k)))
          joined = z3.If(arr.length.eq(k + 1), prefix, joined)
        }
        return { kind: "str", term: joined }
      }
      const out = symbolicOf(L, L.checker.getTypeAtLocation(e), [u.fresh("joined")], u.openBounds(), e)
      if (out.kind !== "str") throw new Unsupported("`.join` whose result is no string", e)
      u.assume(
        z3.And(z3.Implies(arr.length.eq(0), out.term.eq(empty)), z3.Implies(arr.length.eq(1), out.term.eq(piece(z3.Int.val(0))))),
        u.openBounds(),
      )
      folded("for none or one element")
      return out
    }
    case "flatMap": {
      const apply = callback()
      eachCall(apply)
      const segment = (i: Arith): Extract<Val, { kind: "array" }> => {
        const v = apply(i)
        if (v.kind !== "array") throw new Unsupported(`\`.flatMap\` whose callback gives a ${v.kind}: an array is read`, e)
        return v
      }
      if (writtenOut !== undefined) {
        // Written out: each element's array in turn, as a spread of each joins them (`arrayLiteral`).
        if (writtenOut === 0) return { kind: "array", length: z3.Int.val(0), size: 0, maxSize: 0, elem: arr.elem }
        const segments = Array.from({ length: writtenOut }, (_, k) => segment(z3.Int.val(k)))
        const offsets: Array<Arith> = []
        let length: Arith = z3.Int.val(0)
        let maxSize: number | undefined = 0
        segments.forEach((seg, k) => {
          offsets.push(length)
          length = length.add(z3.If(z3.Int.val(k).lt(arr.length), seg.length, z3.Int.val(0)))
          const m = seg.maxSize ?? u.bound
          maxSize = maxSize === undefined || m === undefined ? undefined : maxSize + m
        })
        return {
          kind: "array",
          length,
          ...(maxSize === undefined ? {} : { maxSize }),
          elem: memoElems((j) => {
            let v = segments[segments.length - 1]!.elem(j.sub(offsets[segments.length - 1]!))
            for (let k = segments.length - 2; k >= 0; k--) v = ite(u, j.lt(offsets[k + 1]!), segments[k]!.elem(j.sub(offsets[k]!)), v, e)
            return v
          }),
        }
      }
      const out = symbolicOf(L, L.checker.getTypeAtLocation(e), [u.fresh("flatMapped")], u.openBounds(), e)
      if (out.kind !== "array") throw new Unsupported("`.flatMap` whose result is no array", e)
      u.assume(z3.Implies(arr.length.eq(0), out.length.eq(0)), u.openBounds())
      folded("as empty when the array is")
      return out
    }
    case "filter": {
      // The kept elements, in order. Written out (the search side, and an array of known bound), exactly: element k is
      // kept where it is in range and the predicate holds there, and the j-th kept is the k with j kept before it. On
      // the proof side, a count that is only "none or some", and the j-th kept element an element at an index where
      // the predicate holds, the indices rising with j: every real filter is one of these, so a proof stands, and a
      // model there proves nothing.
      if (u.depth > 0) throw new Unsupported("`.filter` inside a quantifier (`.some`, `.every`, another `.filter`) is not modeled", e)
      const p = predicate()
      const bounds = arr.maxSize === undefined ? {} : { maxSize: arr.maxSize }
      if (writtenOut !== undefined) {
        const kept: Array<Bool> = []
        const before: Array<Arith> = []
        let count: Arith = z3.Int.val(0)
        for (let k = 0; k < writtenOut; k++) {
          const i = z3.Int.val(k)
          const { result } = elementwise(L, i, i.lt(arr.length), () => p(i), false)
          kept.push(z3.And(i.lt(arr.length), result))
          before.push(count)
          count = count.add(z3.If(kept[k]!, z3.Int.val(1), z3.Int.val(0)))
        }
        return {
          kind: "array",
          length: count,
          ...bounds,
          elem: memoElems((j) => {
            if (writtenOut === 0) return arr.elem(j)
            let v = arr.elem(z3.Int.val(writtenOut - 1))
            for (let k = writtenOut - 2; k >= 0; k--) v = ite(u, z3.And(kept[k]!, before[k]!.eq(j)), arr.elem(z3.Int.val(k)), v, e)
            return v
          }),
        }
      }
      const count = z3.Int.const(u.fresh("filtered"))
      u.assume(z3.And(count.ge(0), count.le(arr.length), count.ge(1).eq(quantify("exists", p))))
      const position = z3.Function.declare(u.fresh("kept"), z3.Int.sort(), z3.Int.sort())
      const positionOf = (j: Arith): Arith => position.call(j)
      const j = z3.Int.const(u.fresh("j"))
      const inRange = z3.And(j.ge(0), j.lt(count))
      // Where the kept indices lie holds of every j in range, whatever is said of the element there; that the predicate
      // holds there leans on what its elements are (their facts), as any statement of every element does.
      u.assume(
        z3.ForAll(
          [j],
          z3.Implies(
            inRange,
            z3.And(positionOf(j).ge(0), positionOf(j).lt(arr.length), z3.Implies(j.gt(0), positionOf(j.sub(1)).lt(positionOf(j)))),
          ),
        ),
      )
      const { result, facts } = elementwise(L, j, inRange, () => p(positionOf(j)), true)
      u.assume(z3.ForAll([j], z3.Implies(z3.And(inRange, ...facts), result)))
      u.abstracted = true
      u.approximations.add(`\`${e.getText()}\` is known on the proof side as some of the elements its predicate keeps, in order`)
      return { kind: "array", length: count, ...bounds, elem: memoElems((k) => arr.elem(positionOf(k))) }
    }
  }
}

/**
 * The first index below the array's length where `p` holds, and whether there is one: written out where the array's
 * bound is known, else a fresh index defined by quantifiers (it holds there, and nowhere before it).
 */
export const firstIndex = (
  L: Lowering,
  arr: Extract<Val, { kind: "array" }>,
  p: (i: Arith) => Bool,
): { readonly found: Bool; readonly k: Arith } => {
  const { u } = L
  const z3 = u.z3
  const bound = arr.maxSize ?? u.bound
  if (bound !== undefined) {
    let k: Arith = z3.Int.val(bound)
    let found: Bool = z3.Bool.val(false)
    for (let j = bound - 1; j >= 0; j--) {
      const hit = z3.And(z3.Int.val(j).lt(arr.length), p(z3.Int.val(j)))
      k = z3.If(hit, z3.Int.val(j), k)
      found = z3.Or(hit, found)
    }
    return { found, k }
  }
  // Inside a quantifier the index is one per element the quantifier binds, and so are the facts that define it.
  const indices = u.openBounds()
  const some = z3.Int.const(u.fresh("i"))
  const hasOne = elementwise(L, some, z3.And(some.ge(0), some.lt(arr.length)), () => p(some), true)
  // The same array searched by the same predicate twice (the code's `.find` and a law's) is one search: the predicate
  // is compared at one index of no search's.
  const SEARCHED = z3.Int.const("searched~i")
  const key =
    arr.id === undefined
      ? undefined
      : `${arr.id}[${indices.map(termId).join(",")}]:${termId(z3.substitute(z3.And(hasOne.result, ...hasOne.facts), [some, SEARCHED]))}`
  const known = key === undefined ? undefined : L.searches.get(key)
  if (known !== undefined) return known
  const k = u.leaf([u.fresh("first"), "$"], "int", indices, "count") as never as Arith
  const found = z3.Exists([some], z3.And(some.ge(0), some.lt(arr.length), ...hasOne.facts, hasOne.result))
  const before = z3.Int.const(u.fresh("j"))
  const none = elementwise(L, before, z3.And(before.ge(0), before.lt(k)), () => p(before), true)
  u.assume(
    z3.Implies(
      found,
      z3.And(
        k.ge(0),
        k.lt(arr.length),
        p(k),
        z3.ForAll([before], z3.Implies(z3.And(before.ge(0), before.lt(k), ...none.facts), z3.Not(none.result))),
      ),
    ),
    indices,
  )
  if (key !== undefined) L.searches.set(key, { found, k })
  return { found, k }
}

/**
 * `arr.slice(start?, end?)`: a view of the same elements, from `start`, below `end`, each a position as JavaScript
 * reads one (`relativePosition`): counted from the end where negative, and kept inside the array.
 */
export const slice = (L: Lowering, arr: Extract<Val, { kind: "array" }>, args: ReadonlyArray<Val>, at: ts.Node): Val => {
  const z3 = L.u.z3
  if (args.length > 2) throw new Unsupported("`.slice` takes a start and an end", at)
  const lo = relativePosition(L, arr.length, args[0], z3.Int.val(0), at)
  const hi = relativePosition(L, arr.length, args[1], arr.length, at)
  return {
    kind: "array",
    length: z3.If(hi.ge(lo), hi.sub(lo), z3.Int.val(0)),
    elem: memoElems((i) => arr.elem(i.add(lo))),
    ...(arr.maxSize === undefined ? {} : { maxSize: arr.maxSize }),
    ...(arr.id === undefined ? {} : { id: `slice(${arr.id},${termId(lo)},${termId(hi)})` }),
  }
}

/** An array literal: its items and the elements of what it spreads, in order. */
export const arrayLiteral = (L: Lowering, e: ts.ArrayLiteralExpression, env: Env): Val => {
  const { u } = L
  const z3 = u.z3
  if (e.elements.some(ts.isOmittedExpression)) throw new Unsupported("holes in an array literal are not modeled", e)
  if (!e.elements.some(ts.isSpreadElement)) {
    const items = e.elements.map((x) => later(L, () => lowerExpr(L, x, env)))
    // Past its end the array holds nothing; it is read there only on a path that does not happen (`.find` found
    // nothing in it, a loop's iteration beyond it), where any value of its element type stands in.
    const t = L.checker.getContextualType(e) ?? L.checker.getTypeAtLocation(e)
    const elementType = L.checker.isArrayType(L.checker.getNonNullableType(t))
      ? L.checker.getTypeArguments(L.checker.getNonNullableType(t) as ts.TypeReference)[0]
      : undefined
    const beyond = new Map<string, Val>()
    const past = (i: Arith): Val => {
      if (elementType === undefined || elementType.flags & ts.TypeFlags.Never) return UNDEFINED
      let v = beyond.get(termId(i))
      if (v === undefined) {
        v = symbolicOf(L, elementType, [u.fresh("beyond")], u.openBounds(), e)
        beyond.set(termId(i), v)
      }
      return v
    }
    return {
      kind: "array",
      length: z3.Int.val(items.length),
      size: items.length,
      maxSize: items.length,
      elem: memoElems((i) => {
        if (items.length === 0) return past(i)
        if (z3.isIntVal(i)) {
          const k = Number(i.value())
          if (k >= 0 && k < items.length) return items[k]!()
          return past(i)
        }
        let v = past(i)
        for (let k = items.length - 1; k >= 0; k--) v = ite(u, i.eq(k), items[k]!(), v, e)
        return v
      }),
    }
  }
  type Part = { readonly item: Val } | { readonly spread: Extract<Val, { kind: "array" }> }
  const parts = e.elements.map((x): Part => {
    if (!ts.isSpreadElement(x)) return { item: lowerExpr(L, x, env) }
    const v = lowerExpr(L, x.expression, env)
    if (v.kind !== "array") throw new Unsupported(`a spread of a ${v.kind} into an array is not modeled`, x)
    return { spread: v }
  })
  let length: Arith = z3.Int.val(0)
  let maxSize: number | undefined = 0
  const offsets: Array<Arith> = []
  for (const p of parts) {
    offsets.push(length)
    if ("item" in p) {
      length = length.add(1)
      if (maxSize !== undefined) maxSize += 1
    } else {
      length = length.add(p.spread.length)
      const m = p.spread.maxSize ?? u.bound
      maxSize = maxSize === undefined || m === undefined ? undefined : maxSize + m
    }
  }
  return {
    kind: "array",
    length,
    ...(maxSize === undefined ? {} : { maxSize }),
    elem: memoElems((i) => {
      // Element i is the part's whose range holds it: below the next part's offset, and not in an earlier part.
      const here = (k: number): Val => {
        const p = parts[k]!
        return "item" in p ? p.item : p.spread.elem(i.sub(offsets[k]!))
      }
      let v = here(parts.length - 1)
      for (let k = parts.length - 2; k >= 0; k--) v = ite(u, i.lt(offsets[k + 1]!), here(k), v, e)
      return v
    }),
  }
}

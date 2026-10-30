// Between Z3's world and JavaScript's: a model's leaves read back as JavaScript
// values (a counterexample one can run the real code on), and JavaScript values
// written as constraints on the leaves (to check the lowering against the code).
//
// Only leaves the lowering created exist. A record keeps the fields that were
// read; an unread present value is `{}`; an array keeps its length and its
// elements, `{}` where none of an element was read.
import type { Arith, Bool, Expr, Model } from "z3-solver"
import type { Leaf, Universe } from "./universe.ts"
import { NUM, exactRational, fromZ3String, jsString } from "./value.ts"

interface Node {
  readonly children: Map<string, Node>
  leaf: Leaf | undefined
}

const trie = (u: Universe): Node => {
  const root: Node = { children: new Map(), leaf: undefined }
  for (const leaf of u.leaves.values()) {
    let n = root
    for (const seg of leaf.segments) {
      let next = n.children.get(seg)
      if (next === undefined) {
        next = { children: new Map(), leaf: undefined }
        n.children.set(seg, next)
      }
      n = next
    }
    n.leaf = leaf
  }
  return root
}

const term = (u: Universe, leaf: Leaf, indices: ReadonlyArray<number>): Expr =>
  leaf.constant ?? leaf.decl!.call(...indices.map((i) => u.z3.Int.val(i)))

/** Arrays longer than this make a counterexample too big to replay. */
export const REPLAY_LENGTH = 64

export class TooLong extends Error {}

/** The JavaScript value of root `name` (a parameter's name) in a model. */
export const fromModel = (u: Universe, model: Model, name: string): unknown => {
  const root = trie(u).children.get(name)
  return root === undefined ? {} : read(u, model, root, [])
}

const read = (u: Universe, model: Model, n: Node, indices: ReadonlyArray<number>): unknown => {
  const z3 = u.z3
  const leafAt = (seg: string): unknown => {
    const leaf = n.children.get(seg)?.leaf
    if (leaf === undefined) return undefined
    const v = model.eval(term(u, leaf, indices), true)
    switch (leaf.sort) {
      case "bool":
        return z3.isTrue(v)
      case "str":
        return fromZ3String((v as unknown as { asString(): string }).asString())
      case "num": {
        const cls = Number(model.eval(term(u, n.children.get("~cls")!.leaf!, indices), true).sexpr())
        if (cls === NUM.nan) return Number.NaN
        if (cls === NUM.posInf) return Number.POSITIVE_INFINITY
        if (cls === NUM.negInf) return Number.NEGATIVE_INFINITY
        // The value the code read: its whole parts (`symbolicOf`), which the leaf equals only where its facts are
        // asserted, and inside a quantifier's scope they are not always.
        const rational = (e: unknown) => (e as { value(): { numerator: bigint; denominator: bigint } }).value()
        const intOf = (seg: string) => {
          const x = model.eval(term(u, n.children.get(seg)!.leaf!, indices), true)
          return z3.isIntVal(x) ? x.value() : BigInt(x.sexpr())
        }
        // `-0` where its flag says so and its value is 0: the value is read through its parts, as the code reads it.
        const signed = (x: number): number =>
          x === 0 && n.children.has("~neg0") && z3.isTrue(model.eval(term(u, n.children.get("~neg0")!.leaf!, indices), true)) ? -0 : x
        if (n.children.has("~m")) return signed(Number(intOf("~m")) / 1024)
        if (n.children.has("~whole")) {
          if (z3.isTrue(model.eval(term(u, n.children.get("~whole")!.leaf!, indices), true))) return signed(Number(intOf("~k")))
          const d = rational(model.eval(term(u, n.children.get("~d")!.leaf!, indices), true))
          return Number(intOf("~j")) + Number(d.numerator) / Number(d.denominator)
        }
        const { numerator, denominator } = rational(v)
        return Number(numerator) / Number(denominator)
      }
      case "int":
        return leaf.origin === "bigint"
          ? u.z3.isIntVal(v)
            ? v.value()
            : BigInt(v.sexpr())
          : Number(u.z3.isIntVal(v) ? v.value() : v.sexpr())
    }
  }
  if (n.children.has("$")) return leafAt("$")
  // A union held one record per member: the one its selector names.
  if (n.children.has("~variant")) {
    const chosen = n.children.get(`|${String(leafAt("~variant"))}`)
    return chosen === undefined ? {} : read(u, model, chosen, indices)
  }
  if (n.children.has("?null") || n.children.has("?undef")) {
    if (leafAt("?null") === true) return null
    if (leafAt("?undef") === true) return undefined
    const inner = n.children.get("!")
    return inner === undefined ? {} : read(u, model, inner, indices)
  }
  if (n.children.has("#len")) {
    const length = leafAt("#len") as number
    if (length > REPLAY_LENGTH) throw new TooLong(`an array of ${length} elements`)
    const elem = n.children.get("[]")
    return Array.from({ length }, (_, k) => (elem === undefined ? {} : read(u, model, elem, [...indices, k])))
  }
  const out: Record<string, unknown> = {}
  for (const [seg, child] of n.children) if (seg.startsWith(".")) out[seg.slice(1)] = read(u, model, child, indices)
  return out
}

/** Constraints saying root `name`'s leaves hold the JavaScript value `value`. */
export const pin = (u: Universe, name: string, value: unknown): Array<Bool> => {
  const root = trie(u).children.get(name)
  const out: Array<Bool> = []
  if (root !== undefined) write(u, root, [], value, out)
  return out
}

const write = (u: Universe, n: Node, indices: ReadonlyArray<number>, value: unknown, out: Array<Bool>): void => {
  const z3 = u.z3
  const leafAt = (seg: string) => n.children.get(seg)?.leaf
  const prim = leafAt("$")
  if (prim !== undefined) {
    const t = term(u, prim, indices)
    if (prim.sort === "num") {
      const x = value as number
      const cls = Number.isNaN(x) ? NUM.nan : x === Infinity ? NUM.posInf : x === -Infinity ? NUM.negInf : NUM.finite
      out.push((term(u, n.children.get("~cls")!.leaf!, indices) as Arith).eq(cls))
      const neg0 = n.children.get("~neg0")?.leaf
      if (neg0 !== undefined) out.push((term(u, neg0, indices) as Bool).eq(z3.Bool.val(Object.is(x, -0))))
      if (cls === NUM.finite) {
        out.push((t as Arith).eq(z3.Real.val(exactRational(x))))
        // And its whole parts, which are what the code reads (`symbolicOf`).
        const part = (seg: string) => term(u, n.children.get(seg)!.leaf!, indices) as Arith
        if (n.children.has("~m")) {
          const scaled = x * 1024
          out.push(Number.isInteger(scaled) ? part("~m").eq(z3.Int.val(BigInt(scaled))) : z3.Bool.val(false))
        } else if (n.children.has("~whole")) {
          const w = term(u, n.children.get("~whole")!.leaf!, indices) as Bool
          // Every part is fixed, the ones the value does not use too: a fact about a part left free could be broken by
          // the solver inside a quantifier's scope, and the element it is read in dropped.
          if (Number.isInteger(x))
            out.push(w, part("~k").eq(z3.Int.val(BigInt(x))), part("~j").eq(z3.Int.val(0)), part("~d").eq(z3.Real.val("1/2")))
          else {
            const j = Math.floor(x)
            out.push(
              z3.Not(w),
              part("~k").eq(z3.Int.val(0)),
              part("~j").eq(z3.Int.val(BigInt(j))),
              z3
                .ToReal(part("~j"))
                .add(part("~d"))
                .eq(z3.Real.val(exactRational(x))),
            )
          }
        }
      }
    } else out.push(t.eq(literal(u, value)))
    return
  }
  const selector = leafAt("~variant")
  if (selector !== undefined) {
    // Whichever member holds the value: a member whose fields cannot hold it gives no constraint.
    const options: Array<Bool> = []
    for (const [seg, child] of n.children) {
      if (!seg.startsWith("|")) continue
      const parts: Array<Bool> = []
      try {
        write(u, child, indices, value, parts)
      } catch {
        continue
      }
      options.push(z3.And((term(u, selector, indices) as Arith).eq(Number(seg.slice(1))), ...parts))
    }
    out.push(options.length === 0 ? z3.Bool.val(false) : z3.Or(...options))
    return
  }
  const isNull = leafAt("?null")
  const isUndef = leafAt("?undef")
  if (isNull !== undefined || isUndef !== undefined) {
    if (isNull !== undefined) out.push(term(u, isNull, indices).eq(z3.Bool.val(value === null)))
    if (isUndef !== undefined) out.push(term(u, isUndef, indices).eq(z3.Bool.val(value === undefined)))
    const inner = n.children.get("!")
    if (inner !== undefined && value !== null && value !== undefined) write(u, inner, indices, value, out)
    return
  }
  const len = leafAt("#len")
  if (len !== undefined) {
    const arr = value as ReadonlyArray<unknown>
    out.push((term(u, len, indices) as Arith).eq(arr.length))
    const elem = n.children.get("[]")
    if (elem !== undefined) arr.forEach((x, k) => write(u, elem, [...indices, k], x, out))
    return
  }
  for (const [seg, child] of n.children)
    if (seg.startsWith(".")) write(u, child, indices, (value as Record<string, unknown>)[seg.slice(1)], out)
}

/** A JavaScript string, boolean or bigint as a Z3 literal. */
export const literal = (u: Universe, value: unknown): Expr => {
  const z3 = u.z3
  if (typeof value === "string") return jsString(z3, value)
  if (typeof value === "boolean") return z3.Bool.val(value)
  if (typeof value === "bigint") return z3.Int.val(value)
  throw new Error(`no literal for ${typeof value}`)
}

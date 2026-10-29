// The symbolic values the verifier reasons about, and the one error it raises
// when a construct is outside the supported subset.
//
// A value mirrors JavaScript's, not TypeScript's: a `number` is NaN, an
// infinity or a finite value, a `bigint` an unbounded integer, `null` and
// `undefined` are values of their own, and a record or an array is built
// lazily, so a field the code never reads is never modeled (and never refused).
import ts from "typescript"
import type { Arith, Bool, Context, Seq } from "z3-solver"

export type Ctx = Context
export type FunctionNode = ts.ArrowFunction | ts.FunctionExpression | ts.FunctionDeclaration

/** A binding: evaluated the first time it is read, then kept. */
export type Thunk = () => Val
export type Env = ReadonlyMap<string, Thunk>

export type Val =
  /** An exact integer: a `bigint`, or a `number` known to be a whole count (an array's length). The two never mix. */
  | { readonly kind: "int"; readonly origin: "bigint" | "count"; readonly term: Arith }
  /**
   * A `number`, for comparison: its class (`NUM.finite`, `NUM.nan`, `NUM.posInf`,
   * `NUM.negInf`) and, when finite, its value as a real. Every double is such a
   * value, so a law proved over them holds of every double; arithmetic, whose
   * rounding this does not see, is refused.
   */
  | { readonly kind: "num"; readonly cls: Arith; readonly real: Arith }
  | { readonly kind: "bool"; readonly term: Bool }
  | { readonly kind: "str"; readonly term: Seq }
  | { readonly kind: "nullish"; readonly which: "null" | "undefined" }
  /** `null`, `undefined` or `value`; `value` means something only where neither flag holds. Never nested. */
  | {
      readonly kind: "maybe"
      readonly isNull: Bool
      readonly isUndefined: Bool
      readonly value: Val | undefined
    }
  /**
   * An object: a field is built on first read; `undefined` for a field its type does not have. `id`, when set,
   * names the value for an opaque call: two records with one id are the same value. `has`, when set, says whether
   * the object holds a key (an object the code built, whose keys are known); a spread of it is read through it.
   */
  | {
      readonly kind: "record"
      readonly field: (name: string) => Val | undefined
      readonly id?: string
      readonly has?: (name: string) => Bool | undefined
    }
  /**
   * An array: its length, and its element at an index (built on demand; may refuse). `size` is its length when
   * known exactly; `maxSize` bounds it, so a quantifier over it can be written out element by element.
   */
  | {
      readonly kind: "array"
      readonly length: Arith
      readonly elem: (i: Arith) => Val
      readonly id?: string
      readonly size?: number
      readonly maxSize?: number
    }
  /** A function value: its node and the bindings it closes over. */
  | { readonly kind: "fn"; readonly node: FunctionNode; readonly env: Env }
  /** A function the verifier models itself: a library's, or an operation's. */
  | { readonly kind: "builtin"; readonly name: string; readonly call: (args: ReadonlyArray<Val>, at: ts.Node) => Val }
  /**
   * A computation not yet run: an Effect, a pending call of an async function or an operation. Running it from a
   * trace gives its outcome and the trace with its calls added; each run is a run of its own.
   */
  | { readonly kind: "comp"; readonly run: (trace: Val) => Ran }
  /**
   * A value of type `unknown`: passed along, stored, returned, never read. What would read it (a field, a comparison,
   * its truth, `??`) is refused, since it may be anything, `undefined` included.
   */
  | { readonly kind: "opaque" }

/** A computation's end: its outcome (`{ _tag: "Success", value } | { _tag: "Failure", error }`) and the trace after it. */
export interface Ran {
  readonly outcome: Val
  readonly trace: Val
}

/** The classes of a `number`. */
export const NUM = { finite: 0, nan: 1, posInf: 2, negInf: 3 } as const

/** A finite double's exact value as a fraction: every double is m * 2^k. */
export const exactRational = (x: number): { numerator: bigint; denominator: bigint } => {
  if (Number.isInteger(x)) return { numerator: BigInt(x), denominator: 1n }
  let v = x
  let d = 1n
  while (!Number.isInteger(v)) {
    v *= 2
    d *= 2n
  }
  return { numerator: BigInt(v), denominator: d }
}

/** A construct the verifier will not model. Never read as "true": the obligation is not discharged. */
export class Unsupported extends Error {
  readonly where: string | undefined
  constructor(reason: string, node?: ts.Node) {
    const where = node === undefined ? undefined : locate(node)
    super(where === undefined ? reason : `${where}: ${reason}`)
    this.name = "Unsupported"
    this.where = where
  }
}

export const locate = (node: ts.Node): string => {
  const sf = node.getSourceFile()
  const { line, character } = sf.getLineAndCharacterOfPosition(node.getStart(sf))
  return `${sf.fileName}:${line + 1}:${character + 1}`
}

/** A thunk that runs once. */
export const lazy = (f: () => Val): Thunk => {
  let done: { v: Val } | undefined
  return () => (done ??= { v: f() }).v
}

/** A record whose fields are built on first read and kept. */
export const lazyRecord = (build: (name: string) => Val | undefined, id?: string, has?: (name: string) => Bool | undefined): Val => {
  const memo = new Map<string, Val | undefined>()
  return {
    kind: "record",
    field: (name) => {
      if (!memo.has(name)) memo.set(name, build(name))
      return memo.get(name)
    },
    ...(id === undefined ? {} : { id }),
    ...(has === undefined ? {} : { has }),
  }
}

export const UNDEFINED: Val = { kind: "nullish", which: "undefined" }

/**
 * A term's identity, as text: Z3 gives structurally equal terms of one context one id, but reuses the id of a term it
 * has freed, so the term is kept alive for as long as the process may compare its key.
 */
const kept: Array<{ id(): number }> = []
export const termId = (t: { id(): number }): string => {
  kept.push(t)
  return `t${t.id()}`
}

/**
 * An array's elements, each built once per index: an array made from another (a write, a merge of two paths, a push)
 * reads the other's elements, and without the memo each read would rebuild every array below it.
 */
export const memoElems = (elem: (i: Arith) => Val): ((i: Arith) => Val) => {
  const built = new Map<string, Val>()
  return (i) => {
    const key = termId(i)
    let v = built.get(key)
    if (v === undefined) {
      v = elem(i)
      built.set(key, v)
    }
    return v
  }
}

/** A value's identity for an opaque call: equal identities are equal values; `undefined` when it has none. */
export const identity = (v: Val): string | undefined => {
  switch (v.kind) {
    case "int":
    case "bool":
    case "str":
      return `${v.kind}#${termId(v.term)}`
    case "num":
      return `num(${termId(v.cls)},${termId(v.real)})`
    case "nullish":
      return v.which
    case "maybe": {
      const inner = v.value === undefined ? "none" : identity(v.value)
      return inner === undefined ? undefined : `maybe(${termId(v.isNull)},${termId(v.isUndefined)},${inner})`
    }
    case "record":
    case "array":
      return v.id
    case "fn":
    case "builtin":
    case "comp":
    case "opaque":
      return undefined
  }
}

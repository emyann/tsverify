// The symbolic values the verifier reasons about, and the one error it raises
// when a construct is outside the supported subset.
//
// A value mirrors JavaScript's, not TypeScript's: a `number` is NaN, an
// infinity or a finite value, a `bigint` an unbounded integer, `null` and
// `undefined` are values of their own, and a record or an array is built
// lazily, so a field the code never reads is never modeled (and never refused).
import ts from "typescript"
import type { Arith, Bool, Context, Seq } from "z3-solver"

export type Ctx = Context<"main">
export type FunctionNode = ts.ArrowFunction | ts.FunctionExpression | ts.FunctionDeclaration

/** A binding: evaluated the first time it is read, then kept. */
export type Thunk = () => Val
export type Env = ReadonlyMap<string, Thunk>

export type Val =
  /** An exact integer: a `bigint`, or a `number` known to be a whole count (an array's length). The two never mix. */
  | { readonly kind: "int"; readonly origin: "bigint" | "count"; readonly term: Arith<"main"> }
  /**
   * A `number`, for comparison: its class (`NUM.finite`, `NUM.nan`, `NUM.posInf`,
   * `NUM.negInf`) and, when finite, its value as a real. Every double is such a
   * value, so a law proved over them holds of every double; arithmetic, whose
   * rounding this does not see, is refused.
   */
  | { readonly kind: "num"; readonly cls: Arith<"main">; readonly real: Arith<"main"> }
  | { readonly kind: "bool"; readonly term: Bool<"main"> }
  | { readonly kind: "str"; readonly term: Seq<"main"> }
  | { readonly kind: "nullish"; readonly which: "null" | "undefined" }
  /** `null`, `undefined` or `value`; `value` means something only where neither flag holds. Never nested. */
  | {
      readonly kind: "maybe"
      readonly isNull: Bool<"main">
      readonly isUndefined: Bool<"main">
      readonly value: Val | undefined
    }
  /** An object: a field is built on first read; `undefined` for a field its type does not have. */
  | { readonly kind: "record"; readonly field: (name: string) => Val | undefined }
  /** An array: its length, and its element at an index (built on demand; may refuse). */
  | { readonly kind: "array"; readonly length: Arith<"main">; readonly elem: (i: Arith<"main">) => Val }
  /** A function value: its node and the bindings it closes over. */
  | { readonly kind: "fn"; readonly node: FunctionNode; readonly env: Env }

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
export const lazyRecord = (build: (name: string) => Val | undefined): Val => {
  const memo = new Map<string, Val | undefined>()
  return {
    kind: "record",
    field: (name) => {
      if (!memo.has(name)) memo.set(name, build(name))
      return memo.get(name)
    },
  }
}

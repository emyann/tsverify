// The boundary between the core and a library: what an adapter tells the core.
//
// The core reads TypeScript and knows computations in general — a body that
// runs steps, ends in an outcome and calls operations on the way. An adapter
// says which of a library's forms are those: which function is a computation,
// what a step's operand runs, which method type is an operation, and what its
// library's functions and constructors mean. The core never names a library.
import ts from "typescript"
import type { Lowering } from "./lower.ts"
import type { Env, FunctionNode, Val } from "./value.ts"

/**
 * How a computation's body marks its steps: `yield*` in a generator, `await` in an async function. `returns`: a plain
 * function that returns a computation (`(id) => Effect.gen(...)`), which has no steps of its own; running it runs the
 * computation it returns.
 */
export type Style = "gen" | "async" | "returns"

export interface ComputationFn {
  readonly node: FunctionNode
  readonly style: Style
}

/** An operation's result types: what it succeeds with, and what it fails with (`undefined`: not declared). */
export interface OperationType {
  readonly success: ts.Type
  readonly failure: ts.Type | undefined
}

export interface Adapter {
  readonly name: string
  /** The computation an expression defines, when it is this adapter's form: `Effect.fn(...)(function* ...)`, an async function. */
  readonly computation?: (L: Lowering, e: ts.Node) => ComputationFn | undefined
  /** What a step's operand runs, when this adapter has a meaning for it the core does not (a service key yielded). */
  readonly operand?: (L: Lowering, operand: ts.Expression, env: Env) => Val | undefined
  /** An expression this adapter models: one of its library's functions or constructors. */
  readonly expr?: (L: Lowering, e: ts.Expression, env: Env) => Val | undefined
  /** When a function's return type is this adapter's computation type, the types it succeeds and fails with. */
  readonly operation?: (L: Lowering, returns: ts.Type) => OperationType | undefined
}

/** The module and name a node's symbol resolves to in a package's declarations: `{ pkg: "effect", module: "Effect", name: "fail" }`. */
export const packageExport = (
  checker: ts.TypeChecker,
  node: ts.Node,
): { readonly pkg: string; readonly module: string; readonly name: string } | undefined => {
  const at = ts.isPropertyAccessExpression(node) ? node.name : node
  let sym = checker.getSymbolAtLocation(at)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
  const file = sym?.declarations?.[0]?.getSourceFile().fileName.replaceAll("\\", "/")
  const m = file === undefined ? null : /\/node_modules\/((?:@[^/]+\/)?[^/]+)\/(?:.*\/)?([^/]+)\.d\.ts$/.exec(file)
  return sym === undefined || m === null ? undefined : { pkg: m[1]!, module: m[2]!, name: sym.name }
}

/** Whether a type is the global `Promise` (from the TypeScript lib), and its value type. */
export const promiseOf = (checker: ts.TypeChecker, t: ts.Type): ts.Type | undefined => {
  const parts = t.isIntersection() ? t.types : [t]
  for (const p of parts) {
    const decl = p.getSymbol()?.declarations?.[0]
    if (
      p.getSymbol()?.name === "Promise" &&
      decl?.getSourceFile().isDeclarationFile &&
      /\/typescript\/lib\//.test(decl.getSourceFile().fileName)
    )
      return checker.getTypeArguments(p as ts.TypeReference)[0]
  }
  return undefined
}

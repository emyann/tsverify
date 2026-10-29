// The core's adapter for async/await: an async function is a computation whose
// steps are its `await`s, whose failure is what it throws or what an awaited
// promise rejects with; a method that returns a promise, on a value the code is
// given, is an operation. A promise's rejection type is declared with
// `Rejects<A, E>` from the contract package; otherwise it is not known.
import ts from "typescript"
import { type Adapter, promiseOf } from "../adapter.ts"

const isAsync = (n: ts.Node): n is ts.ArrowFunction | ts.FunctionExpression | ts.FunctionDeclaration =>
  (ts.isArrowFunction(n) || ts.isFunctionExpression(n) || ts.isFunctionDeclaration(n)) &&
  n.asteriskToken === undefined &&
  (n.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword) ?? false)

export const asyncAdapter: Adapter = {
  name: "async",
  computation: (_, e) => (isAsync(e) ? { node: e, style: "async" } : undefined),
  operation: (L, returns) => {
    const success = promiseOf(L.checker, returns)
    if (success === undefined) return undefined
    // A promise may reject with anything: `unknown`, carried and never read, unless `Rejects<A, E>` says what.
    const rejects = L.checker.getPropertyOfType(returns, "~rejects")
    return {
      success,
      failure: rejects === undefined ? L.checker.getUnknownType() : L.checker.getNonNullableType(L.checker.getTypeOfSymbol(rejects)),
    }
  },
}

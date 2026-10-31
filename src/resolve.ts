// What a name in the program refers to, answered once for every part of the verifier that asks: the contracts read
// from source, the purity check, the trust in what a spec declares, the lowering, and the closure check.
import ts from "typescript"
import type { FunctionNode } from "./value.ts"

/** An expression as written, through parentheses and `satisfies`, neither of which changes its value. */
export const unwrap = (e: ts.Expression): ts.Expression =>
  ts.isParenthesizedExpression(e) || ts.isSatisfiesExpression(e) ? unwrap(e.expression) : e

/**
 * The symbol a name refers to, through an import to what it imports, and, for the name of a shorthand property
 * (`{ requires }`), to the binding it reads.
 */
export const symbolOf = (checker: ts.TypeChecker, e: ts.Node): ts.Symbol | undefined => {
  const p = e.parent as ts.Node | undefined
  const sym =
    p !== undefined && ts.isShorthandPropertyAssignment(p) && p.name === e
      ? checker.getShorthandAssignmentValueSymbol(p)
      : checker.getSymbolAtLocation(e)
  return sym !== undefined && sym.flags & ts.SymbolFlags.Alias ? checker.getAliasedSymbol(sym) : sym
}

/** Whether a declaration has a source the verifier can read: not a declaration file (`.d.ts`). */
export const hasSource = (d: ts.Node): boolean => !d.getSourceFile().isDeclarationFile

/** Whether a declaration is the program's own: a source, and none of a package's (`node_modules`). */
export const inProgram = (d: ts.Node): boolean => hasSource(d) && !d.getSourceFile().fileName.includes("/node_modules/")

/**
 * The function a declaration holds: a function declaration with a body, or the arrow or function expression a `const`
 * holds. A `let` may be given another function before a call, so it holds none.
 */
export const functionIn = (d: ts.Declaration | undefined): FunctionNode | undefined => {
  if (d === undefined) return undefined
  if (ts.isFunctionDeclaration(d)) return d.body === undefined ? undefined : d
  const value = constValue(d)
  return value !== undefined && (ts.isArrowFunction(value) || ts.isFunctionExpression(value)) ? value : undefined
}

/** What a `const` holds, as written; undefined for any other declaration. */
export const constValue = (d: ts.Declaration | undefined): ts.Expression | undefined =>
  d !== undefined && ts.isVariableDeclaration(d) && d.initializer !== undefined && (d.parent.flags & ts.NodeFlags.Const) !== 0
    ? unwrap(d.initializer)
    : undefined

/** The function of the program's own source a name refers to, if it refers to one. */
export const functionNamed = (checker: ts.TypeChecker, e: ts.Node): FunctionNode | undefined => {
  const d = symbolOf(checker, e)?.valueDeclaration
  return d !== undefined && hasSource(d) ? functionIn(d) : undefined
}

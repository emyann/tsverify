// Functions as values: what a closure reads of its scope, the key a call of one is remembered by, and whether a closure
// kept for later still reads what it captured.
import ts from "typescript"
import { undefinedOr } from "../ops.ts"
import { type Purity, purityOf } from "../purity.ts"
import { functionNamed } from "../resolve.ts"
import type { AssumedFn } from "../trust.ts"
import { UNDEFINED, Unsupported, type Val } from "../value.ts"
import { EMPTY, type Lowering } from "../lower.ts"
import { applyValue, nameOf } from "./calls.ts"

const K = ts.SyntaxKind

/**
 * A function the code writes, as a value that may stand where a function it is given does (a default for a parameter
 * of a function's type): called, it is called as the code wrote it.
 */
export const callable = (L: Lowering, v: Val): Val => {
  if (v.kind !== "fn") return v
  const id = closedId(L.checker, v.node)
  return {
    kind: "builtin",
    name: nameOf(v.node),
    call: (args, at) => applyValue(L, v, args, at),
    effects: () => effectsOf(L, v),
    ...(id === undefined ? {} : { id }),
  }
}

/** Why a call of a function the code wrote may change something, or `undefined`: the purity check's answer. */
const effectsOf = (L: Lowering, v: Extract<Val, { kind: "fn" }>): string | undefined => {
  const p = purityOf(L.checker, v.node, L.trust.assumptions.of)
  return !p.pure ? p.why : p.calls.length > 0 ? `\`${nameOf(v.node)}\` calls a function it is given` : undefined
}

/**
 * A function written with nothing of its scope in it — every name it reads its own, a module's constant or import, or
 * a global — is one function wherever it is evaluated: its place in the source names it.
 */
const closedId = (checker: ts.TypeChecker, node: ts.Node): string | undefined => {
  const within = (d: ts.Node): boolean => d.pos >= node.pos && d.end <= node.end && d.getSourceFile() === node.getSourceFile()
  const fixed = (d: ts.Declaration): boolean => {
    if (d.getSourceFile().isDeclarationFile || within(d)) return true
    if (ts.isImportSpecifier(d) || ts.isImportClause(d) || ts.isNamespaceImport(d)) return true
    if (ts.isFunctionDeclaration(d) || ts.isClassDeclaration(d)) return ts.isSourceFile(d.parent)
    return (
      ts.isVariableDeclaration(d) &&
      ts.isVariableDeclarationList(d.parent) &&
      (d.parent.flags & ts.NodeFlags.Const) !== 0 &&
      ts.isSourceFile(d.parent.parent.parent)
    )
  }
  let closed = true
  let local = false
  const visit = (n: ts.Node): void => {
    if (!closed) return
    if (ts.isIdentifier(n)) {
      const sym = ts.isShorthandPropertyAssignment(n.parent)
        ? checker.getShorthandAssignmentValueSymbol(n.parent)
        : checker.getSymbolAtLocation(n)
      const binding = ts.SymbolFlags.Variable | ts.SymbolFlags.Function | ts.SymbolFlags.Alias | ts.SymbolFlags.Class
      if (sym !== undefined && sym.flags & binding) {
        const decls = sym.declarations ?? []
        if (!decls.every(fixed)) closed = false
        else if (!decls.every((d) => d.getSourceFile().isDeclarationFile || within(d))) local = true
      }
    }
    ts.forEachChild(n, visit)
  }
  visit(node)
  if (!closed) return undefined
  // Reading only its own names and the globals, it is its text; reading a module's, its place in that module.
  return local ? `fn:${node.getSourceFile().fileName}:${node.pos}` : `fn:${node.getText().replace(/\s+/g, " ")}`
}

/**
 * The arguments a declared function binds, for telling two calls apart: a function written in place as the function it
 * is, and where one is `undefined` or left out and its parameter's default is a function written with nothing of its
 * scope in it, that default where it is `undefined`. Two calls that bind the same values are the same call, whichever
 * of them wrote the default out.
 */
export const boundArgs = (L: Lowering, a: AssumedFn, args: ReadonlyArray<Val>, at: ts.Node): ReadonlyArray<Val> => {
  const params = a.body?.parameters
  // A rest parameter binds every argument past it: they are told apart as they are passed.
  if (params === undefined || params.some((p) => p.dotDotDotToken !== undefined)) return args
  return params.map((p, k) => {
    // A function written here is the function its text is, where it reads nothing of its scope (`closedId`).
    const given = args[k]?.kind === "fn" ? callable(L, args[k]) : (args[k] ?? UNDEFINED)
    const init = p.initializer
    if (init === undefined || !(ts.isArrowFunction(init) || ts.isFunctionExpression(init))) return given
    if (closedId(L.checker, init) === undefined) return given
    if (given.kind !== "nullish" && !(given.kind === "maybe" && given.value?.kind === "builtin")) return given
    return undefinedOr(L.u, given, () => callable(L, { kind: "fn", node: init, env: EMPTY }), at)
  })
}

/** Why a function passed where a pure function calls one may change something, or `undefined` where it changes nothing. */
export const effectsOfValue = (L: Lowering, v: Val | undefined): string | undefined => {
  if (v === undefined || v.kind === "nullish") return undefined
  if (v.kind === "maybe") return effectsOfValue(L, v.value)
  if (v.kind === "builtin") return v.effects?.()
  if (v.kind === "fn") return effectsOf(L, v)
  return `it is a ${v.kind}, not a function the verifier reads`
}

/** The names each function body assigns or changes (cached), for the closure check. */
const changedIn = new WeakMap<ts.Node, Set<string>>()
/** What the purity check, reading its source, finds of each function of the program a closure's host calls. */
const purityRead = new WeakMap<ts.Node, Purity>()
const programPurity = (checker: ts.TypeChecker, callee: ts.Expression): Purity | undefined => {
  const fn = ts.isIdentifier(callee) ? functionNamed(checker, callee) : undefined
  if (fn === undefined) return undefined
  let p = purityRead.get(fn)
  if (p === undefined) {
    p = purityOf(checker, fn, () => undefined)
    purityRead.set(fn, p)
  }
  return p
}
/**
 * Whether a call changes nothing it is passed: a function of the program found pure, each function it calls of those it is
 * passed being a parameter of `host`, the function the call is written in (a function it is given, which its own purity
 * is relative to), or one found pure outright.
 */
const changesNothing = (checker: ts.TypeChecker, call: ts.CallExpression, host: ts.Node): boolean => {
  const p = programPurity(checker, call.expression)
  if (p === undefined || !p.pure) return false
  return p.calls.every((k) => {
    const a = call.arguments[k]
    if (a === undefined) return true
    if (!ts.isIdentifier(a)) return false
    const d = checker.getSymbolAtLocation(a)?.valueDeclaration
    if (d !== undefined && ts.isParameter(d) && d.parent === host) return true
    const q = programPurity(checker, a)
    return q !== undefined && q.pure && q.calls.length === 0
  })
}

const changedNames = (body: ts.Node, checker: ts.TypeChecker): Set<string> => {
  let out = changedIn.get(body)
  if (out !== undefined) return out
  out = new Set()
  const rootName = (x: ts.Expression): string | undefined => {
    while (ts.isPropertyAccessExpression(x) || ts.isElementAccessExpression(x) || ts.isParenthesizedExpression(x)) x = x.expression
    return ts.isIdentifier(x) ? x.text : undefined
  }
  // A value no callee can change: a primitive (`BigInt(text)`, `text.trim()` change nothing).
  const PRIMITIVE =
    ts.TypeFlags.StringLike |
    ts.TypeFlags.NumberLike |
    ts.TypeFlags.BigIntLike |
    ts.TypeFlags.BooleanLike |
    ts.TypeFlags.EnumLike |
    ts.TypeFlags.Null |
    ts.TypeFlags.Undefined |
    ts.TypeFlags.Void
  const primitive = (x: ts.Expression): boolean => {
    const t = checker.getTypeAtLocation(x)
    return (t.isUnion() ? t.types : [t]).every((m) => (m.flags & PRIMITIVE) !== 0)
  }
  const passedName = (x: ts.Expression): string | undefined => (primitive(x) ? undefined : rootName(x))
  const found = out
  const visit = (n: ts.Node): void => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= K.FirstAssignment && n.operatorToken.kind <= K.LastAssignment) {
      const r = rootName(n.left)
      if (r !== undefined) found.add(r)
    } else if (
      (ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
      (n.operator === K.PlusPlusToken || n.operator === K.MinusMinusToken)
    ) {
      const r = rootName(n.operand)
      if (r !== undefined) found.add(r)
    } else if (ts.isDeleteExpression(n)) {
      const r = rootName(n.expression)
      if (r !== undefined) found.add(r)
    } else if (ts.isCallExpression(n)) {
      if (ts.isPropertyAccessExpression(n.expression)) {
        const r = passedName(n.expression.expression)
        if (r !== undefined) found.add(r)
      }
      // A function of the program the purity check reads as pure changes nothing it is passed.
      if (!changesNothing(checker, n, body.parent))
        for (const a of n.arguments) {
          const r = passedName(a)
          if (r !== undefined) found.add(r)
        }
    }
    ts.forEachChild(n, visit)
  }
  visit(body)
  changedIn.set(body, out)
  return out
}

/**
 * A closure is read with the variables it captures as they are where it is written. That is JavaScript's meaning when
 * it is called there (a callback); one kept for later, over a variable its function changes, is refused.
 */
export const closureCheck = (L: Lowering, e: ts.ArrowFunction | ts.FunctionExpression): void => {
  if (ts.isCallExpression(e.parent) && e.parent.arguments.includes(e)) return
  let host: ts.Node | undefined = e.parent
  while (host !== undefined && !ts.isFunctionLike(host)) host = host.parent
  if (host === undefined || !("body" in host) || host.body === undefined) return
  const changed = changedNames(host.body, L.checker)
  const captured: Array<string> = []
  const visit = (n: ts.Node): void => {
    if (ts.isIdentifier(n) && changed.has(n.text)) {
      // `{ x }` names the variable `x` as well as the field.
      const shorthand = ts.isShorthandPropertyAssignment(n.parent) && n.parent.name === n
      const d = (shorthand ? L.checker.getShorthandAssignmentValueSymbol(n.parent) : L.checker.getSymbolAtLocation(n))?.valueDeclaration
      if (d !== undefined && d.pos >= host.pos && d.end <= host.end && !(d.pos >= e.pos && d.end <= e.end)) captured.push(n.text)
    }
    ts.forEachChild(n, visit)
  }
  visit(e.body)
  if (captured.length > 0)
    throw new Unsupported(
      `a closure kept for later over \`${captured[0]}\`, which its function changes: call it where it is written, or pass it the value`,
      e,
    )
}

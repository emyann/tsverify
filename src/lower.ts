// Lowers pure TypeScript to symbolic values, keeping JavaScript's meaning.
//
// Supported: literals of every primitive, null and undefined; `const` bindings
// (evaluated when first read); `if` with early returns; `?:`, `&&`, `||`, `!`,
// `??`, `===`, `!==`, `<` and friends; `+ - *` on bigints, `+` on strings;
// unary `-`; property access and optional chaining; `t[k]` for a literal k on a
// tuple; object and array literals; template strings (as unknown strings of
// their parts); calls to functions of the program (inlined, or opaque when they
// cannot be read), to closures, to an adapter's functions and to computations;
// on arrays `.length`, `.at(k)` for a literal k, `.filter(p).length`, `.some(p)`,
// `.every(p)`, `.includes(x)` for strings and booleans.
//
// A function it does not read — a package's, or one of the program's whose body
// it cannot lower — is refused unless an `assume(...)` is in force for it; one
// that is in force replaces the function, read or not (`trust.ts`).
//
// Code runs in one of two modes, as in Verus: `exec`, the program, and `spec`,
// the laws and `requires` and whatever they call. Spec code runs no
// computation, calls no operation and calls nothing declared `pure: false`. A
// binding keeps the mode of the code that wrote it, however late it is read.
//
// Refused with a source span: arithmetic on `number` (its rounding is not
// modeled) and bigint `/` `%` (they truncate; Z3's do not), `==`, assignments
// and loops, casts and non-null assertions (each is a claim the verifier would
// have to trust), `any`, recursion, a binding it cannot see (a `let`, a global,
// an import from a package no adapter models), string length (code units).
//
// Reading a binding only when it is used means a binding the result does not
// need is never checked. The code under verification is taken to throw nothing:
// a `const` whose evaluation would throw, but whose value is never read, is not
// seen. The report says so.
import ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import type { Adapter } from "./adapter.ts"
import { computationCall } from "./computation.ts"
import { type Order, compare, isNullish, ite, nullishOr, strictEq, truthy } from "./ops.ts"
import { type Purity, purityOf } from "./purity.ts"
import { type Typing, symbolicOf } from "./symbolic.ts"
import { type AssumedFn, type Assumptions, coveringViews } from "./trust.ts"
import { type Env, type FunctionNode, NUM, type Thunk, Unsupported, type Val, exactRational, identity, lazy, lazyRecord } from "./value.ts"

/** What a verification trusts, shared by its two sides: the declarations in force, and what came of using them. */
export interface Trust {
  readonly assumptions: Assumptions
  /** Each declared-pure function's purity, checked once. */
  readonly purity: Map<AssumedFn, Purity>
  /** The declarations a lowering leaned on. */
  readonly used: Set<AssumedFn>
}

export const trustOf = (assumptions: Assumptions): Trust => ({ assumptions, purity: new Map(), used: new Set() })

const NO_TRUST: Assumptions = { all: [], of: () => undefined }

/** `exec`: the program. `spec`: a law, a `requires`, and what they call. */
export type Mode = "exec" | "spec"

/** A function the verifier would have to read and cannot: what to declare instead is in the message. */
export class Unread extends Unsupported {}

export interface Lowering extends Typing {
  /** The functions being inlined, innermost last: a guard against recursion. */
  readonly stack: Array<FunctionNode>
  /** Module-level constants, lowered once each. */
  readonly constants: Map<ts.Declaration, Val>
  /** The libraries' adapters, asked in order. */
  readonly adapters: ReadonlyArray<Adapter>
  /** Results of declared pure functions and template strings, by callee and arguments' identities: the same call, the same value. */
  readonly opaque: Map<string, Val>
  readonly trust: Trust
  /** The mode of the code being lowered now. */
  mode: Mode
  /** The declarations whose laws are being assumed now: a law that calls its own function is refused. */
  readonly assuming: Array<AssumedFn>
}

/** A fresh lowering over a universe. */
export const lowering = (typing: Typing, adapters: ReadonlyArray<Adapter>, trust: Trust = trustOf(NO_TRUST)): Lowering => ({
  ...typing,
  adapters,
  stack: [],
  constants: new Map(),
  opaque: new Map(),
  trust,
  mode: "exec",
  assuming: [],
})

/** Runs `f` as spec code. */
export const inSpec = <A>(L: Lowering, f: () => A): A => {
  const prev = L.mode
  L.mode = "spec"
  try {
    return f()
  } finally {
    L.mode = prev
  }
}

/** A binding evaluated when first read, in the mode of the code that wrote it. */
export const later = (L: Lowering, f: () => Val): Thunk => {
  const mode = L.mode
  return lazy(() => {
    const prev = L.mode
    L.mode = mode
    try {
      return f()
    } finally {
      L.mode = prev
    }
  })
}

const K = ts.SyntaxKind
const EMPTY: Env = new Map()

const bool = (term: Bool<"main">): Val => ({ kind: "bool", term })

/** The value of calling `fn` (closing over `env`) with `args`. */
export const lowerCall = (L: Lowering, fn: FunctionNode, env: Env, args: ReadonlyArray<Val>, at: ts.Node): Val => {
  if (L.stack.includes(fn)) throw new Unsupported("recursion is not modeled", at)
  if (fn.asteriskToken !== undefined) throw new Unsupported("a generator called as a plain function is not modeled", fn)
  if (fn.modifiers?.some((m) => m.kind === K.AsyncKeyword)) throw new Unsupported("an async function read as a plain one", fn)
  L.stack.push(fn)
  try {
    const scope = bindParameters(L, fn, env, args)
    const body = fn.body
    if (body === undefined) throw new Unsupported("a function with no body", fn)
    if (!ts.isBlock(body)) return lowerExpr(L, body, scope)
    return lowerStatements(L, body.statements, 0, scope, () => {
      throw new Unsupported("the function can end without a `return`, which is not modeled", body)
    })
  } finally {
    L.stack.pop()
  }
}

/** A function's parameters bound to `args` over `env`: a missing argument is its default, or undefined. */
export const bindParameters = (L: Lowering, fn: FunctionNode, env: Env, args: ReadonlyArray<Val>): Map<string, Thunk> => {
  const scope = new Map(env)
  fn.parameters.forEach((p, i) => {
    const given = args[i]
    if (p.dotDotDotToken !== undefined) throw new Unsupported("rest parameters are not modeled", p)
    const value: Thunk =
      given !== undefined
        ? () => given
        : p.initializer !== undefined
          ? later(L, () => lowerExpr(L, p.initializer!, scope))
          : () => ({ kind: "nullish", which: "undefined" })
    bind(L, p.name, value, scope)
  })
  return scope
}

/** Binds a name or an object pattern to a value, each name read on first use. */
export const bind = (L: Lowering, name: ts.BindingName, value: Thunk, scope: Map<string, Thunk>): void => {
  if (ts.isIdentifier(name)) {
    scope.set(name.text, value)
    return
  }
  if (!ts.isObjectBindingPattern(name)) throw new Unsupported("array destructuring is not modeled", name)
  for (const el of name.elements) {
    if (el.dotDotDotToken !== undefined || el.initializer !== undefined)
      throw new Unsupported("rest and default values in destructuring are not modeled", el)
    const key = el.propertyName === undefined ? (el.name as ts.Identifier).text : propertyKey(el.propertyName)
    bind(L, el.name, later(L, () => member(L, value(), key, el)), scope)
  }
}

const propertyKey = (name: ts.PropertyName): string => {
  if (ts.isIdentifier(name) || ts.isStringLiteral(name) || ts.isNoSubstitutionTemplateLiteral(name)) return name.text
  throw new Unsupported("a computed property name is not modeled", name)
}

/** A sequence of statements, then `rest` if it falls off the end. */
const lowerStatements = (
  L: Lowering,
  stmts: ReadonlyArray<ts.Statement>,
  i: number,
  env: Env,
  rest: () => Val,
): Val => {
  if (i === stmts.length) return rest()
  const s = stmts[i]!
  const next = (): Val => lowerStatements(L, stmts, i + 1, env, rest)
  if (ts.isVariableStatement(s)) {
    if ((s.declarationList.flags & ts.NodeFlags.Const) === 0) throw new Unsupported("only `const` bindings are modeled", s)
    const scope = new Map(env)
    for (const d of s.declarationList.declarations) {
      if (d.initializer === undefined) throw new Unsupported("a `const` with no value", d)
      const init = d.initializer
      bind(L, d.name, later(L, () => lowerExpr(L, init, scope)), scope)
    }
    return lowerStatements(L, stmts, i + 1, scope, rest)
  }
  if (ts.isReturnStatement(s))
    return s.expression === undefined ? { kind: "nullish", which: "undefined" } : lowerExpr(L, s.expression, env)
  if (ts.isIfStatement(s)) {
    const c = cond(L, s.expression, env)
    const thenV = lowerBranch(L, s.thenStatement, env, next)
    const elseV = s.elseStatement === undefined ? next() : lowerBranch(L, s.elseStatement, env, next)
    return ite(L.u, c, thenV, elseV, s)
  }
  if (ts.isBlock(s)) return lowerStatements(L, s.statements, 0, env, next)
  if (ts.isEmptyStatement(s)) return next()
  throw new Unsupported(`a ${K[s.kind]} is not modeled`, s)
}

const lowerBranch = (L: Lowering, s: ts.Statement, env: Env, next: () => Val): Val =>
  lowerStatements(L, ts.isBlock(s) ? s.statements : [s], 0, env, next)

/** A condition's truth, read as JavaScript reads it: `a && b` is truthy when both are. */
export const cond = (L: Lowering, e: ts.Expression, env: Env): Bool<"main"> => {
  const z3 = L.u.z3
  if (ts.isParenthesizedExpression(e)) return cond(L, e.expression, env)
  if (ts.isPrefixUnaryExpression(e) && e.operator === K.ExclamationToken) return z3.Not(cond(L, e.operand, env))
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === K.AmpersandAmpersandToken)
    return z3.And(cond(L, e.left, env), cond(L, e.right, env))
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === K.BarBarToken)
    return z3.Or(cond(L, e.left, env), cond(L, e.right, env))
  return truthy(L.u, lowerExpr(L, e, env))
}

export const lowerExpr = (L: Lowering, e: ts.Expression, env: Env): Val => {
  const { u } = L
  const z3 = u.z3
  if (ts.isParenthesizedExpression(e)) return lowerExpr(L, e.expression, env)
  if (ts.isAsExpression(e) && ts.isConstTypeReference(e.type)) return lowerExpr(L, e.expression, env)
  if (ts.isSatisfiesExpression(e)) return lowerExpr(L, e.expression, env)
  if (ts.isAsExpression(e) || ts.isTypeAssertionExpression(e))
    throw new Unsupported("a cast is a claim the verifier would have to trust", e)
  if (ts.isNonNullExpression(e)) throw new Unsupported("`!` is a claim the verifier would have to trust", e)

  // Literals.
  if (ts.isBigIntLiteral(e)) return { kind: "int", origin: "bigint", term: z3.Int.val(BigInt(e.text.slice(0, -1).replaceAll("_", ""))) }
  if (ts.isNumericLiteral(e)) return num(z3, Number(e.text.replaceAll("_", "")))
  if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return { kind: "str", term: z3.String.val(e.text) }
  if (e.kind === K.TrueKeyword) return bool(z3.Bool.val(true))
  if (e.kind === K.FalseKeyword) return bool(z3.Bool.val(false))
  if (e.kind === K.NullKeyword) return { kind: "nullish", which: "null" }
  if (ts.isTemplateExpression(e)) return template(L, e, env)
  if (ts.isYieldExpression(e) || ts.isAwaitExpression(e))
    throw new Unsupported("a step (`yield*`, `await`) is modeled as a statement: `const x = yield* e`, `yield* e`, `return yield* e`", e)

  if (ts.isIdentifier(e) && env.has(e.text)) return env.get(e.text)!()
  if (ts.isIdentifier(e) || ts.isPropertyAccessExpression(e) || ts.isCallExpression(e) || ts.isNewExpression(e))
    for (const a of L.adapters) {
      const v = a.expr?.(L, e, env)
      if (v !== undefined) return v
    }
  if (ts.isIdentifier(e)) return identifier(L, e, env)
  if (ts.isPropertyAccessExpression(e)) return propertyAccess(L, e, env)
  if (ts.isElementAccessExpression(e)) return elementAccess(L, e, env)
  if (ts.isNewExpression(e)) throw new Unsupported(`\`new\` of a class no adapter models`, e)
  if (ts.isCallExpression(e)) return call(L, e, env)
  if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) return { kind: "fn", node: e, env }

  if (ts.isObjectLiteralExpression(e)) {
    const fields = new Map<string, Thunk>()
    for (const p of e.properties) {
      if (ts.isPropertyAssignment(p)) fields.set(propertyKey(p.name), later(L, () => lowerExpr(L, p.initializer, env)))
      else if (ts.isShorthandPropertyAssignment(p)) fields.set(p.name.text, later(L, () => identifier(L, p.name, env)))
      else throw new Unsupported("spreads, methods and accessors in an object literal are not modeled", p)
    }
    return lazyRecord((name) => fields.get(name)?.())
  }
  if (ts.isArrayLiteralExpression(e)) {
    if (e.elements.some((x) => ts.isSpreadElement(x) || ts.isOmittedExpression(x)))
      throw new Unsupported("spreads and holes in an array literal are not modeled", e)
    const items = e.elements.map((x) => later(L, () => lowerExpr(L, x, env)))
    return {
      kind: "array",
      length: z3.Int.val(items.length),
      elem: (i) => {
        if (items.length === 0) throw new Unsupported("an element of an empty array", e)
        let v = items[items.length - 1]!()
        for (let k = items.length - 2; k >= 0; k--) v = ite(u, i.eq(k), items[k]!(), v, e)
        return v
      },
    }
  }

  if (ts.isConditionalExpression(e))
    return ite(u, cond(L, e.condition, env), lowerExpr(L, e.whenTrue, env), lowerExpr(L, e.whenFalse, env), e)

  if (ts.isPrefixUnaryExpression(e)) {
    if (e.operator === K.ExclamationToken) return bool(z3.Not(cond(L, e.operand, env)))
    if (e.operator === K.MinusToken) {
      const v = lowerExpr(L, e.operand, env)
      if (v.kind === "int" && v.origin === "bigint") return { ...v, term: v.term.neg() }
      if (v.kind === "num")
        return {
          kind: "num",
          cls: z3.If(v.cls.eq(NUM.posInf), z3.Int.val(NUM.negInf), z3.If(v.cls.eq(NUM.negInf), z3.Int.val(NUM.posInf), v.cls)),
          real: v.real.neg(),
        }
      throw new Unsupported(`unary - on a ${v.kind}`, e)
    }
    throw new Unsupported(`prefix ${ts.tokenToString(e.operator)} is not modeled`, e)
  }
  if (ts.isBinaryExpression(e)) return binary(L, e, env)
  throw new Unsupported(`a ${K[e.kind]} is not modeled`, e)
}

/**
 * A template string: an unknown string, the same for the same parts (its literal
 * text and its substitutions' identities), and non-empty when its literal text is.
 */
const template = (L: Lowering, e: ts.TemplateExpression, env: Env): Val => {
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
  const key = ids.every((i) => i !== undefined) ? `template:${e.getSourceFile().fileName}:${e.pos}(${ids.join(",")})[${indices.map((i) => i.sexpr()).join(",")}]` : undefined
  const known = key === undefined ? undefined : L.opaque.get(key)
  if (known !== undefined) return known
  const term = L.u.leaf([L.u.fresh("template"), "$"], "str", indices) as never as ReturnType<typeof z3.String.val>
  if (text.length > 0) L.u.assume(z3.Not(term.eq(z3.String.val(""))), indices)
  const v: Val = { kind: "str", term }
  if (key !== undefined) L.opaque.set(key, v)
  L.u.notes.add("A template string is an unknown string of its parts: equal parts, equal strings; non-empty when its literal text is.")
  return v
}

/** `t[k]` for a whole-number literal k on a tuple (or any record): its field `k`. */
const elementAccess = (L: Lowering, e: ts.ElementAccessExpression, env: Env): Val => {
  const k = literalIndex(e.argumentExpression)
  if (k === undefined || k < 0n) throw new Unsupported("element access `a[i]` is modeled for a literal index on a tuple; `.at(i)` on an array", e)
  const obj = lowerExpr(L, e.expression, env)
  return optionally(L, obj, e, e.expression, (v) => {
    if (v.kind === "record") {
      const f = v.field(String(k))
      if (f === undefined) throw new Unsupported(`no element ${k}`, e)
      return f
    }
    throw new Unsupported(`element access on a ${v.kind}: \`.at(${k})\` reads an array`, e)
  })
}

export const num = (z3: Lowering["u"]["z3"], n: number): Val => ({
  kind: "num",
  cls: z3.Int.val(Number.isNaN(n) ? NUM.nan : n === Infinity ? NUM.posInf : n === -Infinity ? NUM.negInf : NUM.finite),
  real: z3.Real.val(Number.isFinite(n) ? exactRational(n) : 0),
})

const identifier = (L: Lowering, e: ts.Identifier, env: Env): Val => {
  const bound = env.get(e.text)
  if (bound !== undefined) return bound()
  let sym = L.checker.getSymbolAtLocation(e)
  const imported = sym !== undefined && (sym.flags & ts.SymbolFlags.Alias) !== 0
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = L.checker.getAliasedSymbol(sym)
  if (sym?.name === "undefined" && sym.declarations === undefined) return { kind: "nullish", which: "undefined" }
  if (sym?.name === "undefined" && sym.declarations?.every((d) => d.getSourceFile().isDeclarationFile))
    return { kind: "nullish", which: "undefined" }
  const declared = L.trust.assumptions.of(e)
  if (declared !== undefined) return assumedFn(L, declared)
  const decl = sym?.valueDeclaration
  if (decl !== undefined && !decl.getSourceFile().isDeclarationFile && !decl.getSourceFile().fileName.includes("/node_modules/")) {
    if (ts.isFunctionDeclaration(decl)) return { kind: "fn", node: decl, env: EMPTY }
    if (ts.isVariableDeclaration(decl) && isModuleConst(decl) && decl.initializer !== undefined) {
      let v = L.constants.get(decl)
      if (v === undefined) {
        v = lowerExpr(L, decl.initializer, EMPTY)
        L.constants.set(decl, v)
      }
      return v
    }
  }
  if (imported && decl !== undefined && (decl.getSourceFile().isDeclarationFile || decl.getSourceFile().fileName.includes("/node_modules/")))
    throw new Unread(`\`${e.text}\` is a package's, which the verifier does not read: declare what it may assume of it, \`assume(${e.text}, { pure: true, ensures: { ... } })\`, in the spec or a pack the spec imports`, e)
  throw new Unsupported(`\`${e.text}\` is a binding the verifier cannot see (a \`let\` or a global)`, e)
}

const isModuleConst = (d: ts.VariableDeclaration): boolean =>
  ts.isVariableDeclarationList(d.parent) &&
  (d.parent.flags & ts.NodeFlags.Const) !== 0 &&
  ts.isVariableStatement(d.parent.parent) &&
  ts.isSourceFile(d.parent.parent.parent) &&
  ts.isIdentifier(d.name)

/** Whether `e` sits in an optional chain (`a?.b.c`): its object may be undefined only because the chain stopped. */
const inChain = (e: ts.Node): boolean => (e.flags & ts.NodeFlags.OptionalChain) !== 0

const propertyAccess = (L: Lowering, e: ts.PropertyAccessExpression, env: Env): Val => {
  const t = L.checker.getTypeAtLocation(e.expression)
  if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) throw new Unsupported("a property of an `any` or `unknown`", e)
  const obj = lowerExpr(L, e.expression, env)
  return optionally(L, obj, e, e.expression, (v) => member(L, v, e.name.text, e))
}

/**
 * Applies `f` to a value that may be null or undefined: in an optional chain the
 * result is undefined when it is; outside one, `f` reads the value present, which
 * is sound only where the type checker has narrowed `objExpr` to neither, so its
 * narrowed type there is asked and anything else refused.
 */
const optionally = (L: Lowering, obj: Val, e: ts.Node, objExpr: ts.Expression, f: (v: Val) => Val): Val => {
  if (obj.kind === "nullish") {
    if (inChain(e)) return { kind: "nullish", which: "undefined" }
    throw new Unsupported(`reading a member of ${obj.which}`, e)
  }
  if (obj.kind !== "maybe") return f(obj)
  if (!inChain(e)) {
    const t = L.checker.getTypeAtLocation(objExpr)
    const parts = t.isUnion() ? t.types : [t]
    if (parts.some((m) => m.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined | ts.TypeFlags.Void)))
      throw new Unsupported("a member of a value the type checker has not shown to be neither null nor undefined here", e)
  }
  if (obj.value === undefined) return { kind: "nullish", which: "undefined" }
  const inner = f(obj.value)
  if (!inChain(e)) return inner
  return ite(L.u, isNullish(L.u, obj), { kind: "nullish", which: "undefined" }, inner, e)
}

const member = (L: Lowering, obj: Val, name: string, at: ts.Node): Val => {
  if (obj.kind === "record") {
    const v = obj.field(name)
    if (v === undefined) throw new Unsupported(`no field \`${name}\` the verifier can read`, at)
    return v
  }
  if (obj.kind === "array" && name === "length") return { kind: "int", origin: "count", term: obj.length }
  if (obj.kind === "str" && name === "length")
    throw new Unsupported("a string's length counts UTF-16 code units, which is not modeled", at)
  throw new Unsupported(`member \`${name}\` of a ${obj.kind} is not modeled`, at)
}

const call = (L: Lowering, e: ts.CallExpression, env: Env): Val => {
  if (e.questionDotToken !== undefined) throw new Unsupported("an optional call is not modeled", e)
  const callee = e.expression
  if (ts.isPropertyAccessExpression(callee)) {
    // A library function named through its namespace (`Effect.fail`): the adapter's, before any receiver is read.
    for (const a of L.adapters) {
      const f = a.expr?.(L, callee, env)
      if (f !== undefined) return callValue(L, f, e, env)
    }
    const declared = L.trust.assumptions.of(callee)
    if (declared !== undefined) return callValue(L, assumedFn(L, declared), e, env)
    const receiver = lowerExpr(L, callee.expression, env)
    return optionally(L, receiver, callee, callee.expression, (r) => {
      if (r.kind === "array") return arrayMethod(L, r, callee.name.text, e, env)
      if (r.kind === "record") return callValue(L, member(L, r, callee.name.text, callee), e, env)
      throw new Unsupported(`method \`${callee.name.text}\` of a ${r.kind} is not modeled`, e)
    })
  }
  return callValue(L, lowerExpr(L, callee, env), e, env)
}

const callValue = (L: Lowering, f: Val, e: ts.CallExpression, env: Env): Val => {
  if (e.arguments.some(ts.isSpreadElement)) throw new Unsupported("spread arguments are not modeled", e)
  if (f.kind === "builtin") {
    const v = f.call(e.arguments.map((a) => lowerExpr(L, a, env)), e)
    if (L.mode === "spec" && v.kind === "comp")
      throw new Unsupported(`spec code calls no operation: \`${f.name}\` is one. A law reads the calls a computation made from the trace it is given`, e)
    return v
  }
  if (f.kind !== "fn") throw new Unsupported(`calling a ${f.kind}`, e)
  const args = e.arguments.map((a) => lowerExpr(L, a, env))
  for (const a of L.adapters) {
    const c = a.computation?.(L, f.node)
    if (c === undefined) continue
    if (L.mode === "spec")
      throw new Unsupported(`spec code runs no computation: \`${nameOf(c.node)}\` is one. A law reads a computation's outcome and calls from the arguments it is given`, e)
    return computationCall(L, c.node, c.style, f.env, args, e)
  }
  if (f.env !== EMPTY) return lowerCall(L, f.node, f.env, args, e)
  // A function of the program: inlined; when its body cannot be read, refused with what to declare instead.
  try {
    return lowerCall(L, f.node, f.env, args, e)
  } catch (err) {
    if (!(err instanceof Unsupported) || err instanceof Unread) throw err
    const name = nameOf(f.node)
    throw new Unread(
      `\`${name}\` is not read (${err.message.replace(/^\S+:\d+:\d+: /, "")}): declare what the verifier may assume of it, \`assume(${name}, { pure: true, ensures: { ... } })\` in the spec, or write its body in the subset the verifier reads`,
      e,
    )
  }
}

const nameOf = (fn: FunctionNode): string =>
  fn.name?.getText() ?? (ts.isVariableDeclaration(fn.parent) ? fn.parent.name.getText() : "a function")

/** A declared function as a value: calling it is `assumedCall`. */
const assumedFn = (L: Lowering, a: AssumedFn): Val => ({ kind: "builtin", name: a.name, call: (args, at) => assumedCall(L, a, args, at) })

/**
 * A call to a declared function: an unknown result of the call's type, the same for the same arguments when the
 * function is pure, of which every law of every view covering the call is assumed.
 */
const assumedCall = (L: Lowering, a: AssumedFn, args: ReadonlyArray<Val>, at: ts.Node): Val => {
  const { u, checker } = L
  if (L.mode === "spec" && !a.pure)
    throw new Unsupported(`spec code is deterministic, and \`${a.name}\` is declared \`pure: false\`: call it from the program and pass its result to the law`, at)
  if (L.assuming.includes(a)) throw new Unsupported(`a law of \`${a.name}\`'s assumption calls \`${a.name}\` itself`, at)
  if (!ts.isCallExpression(at)) throw new Unsupported(`\`${a.name}\` is used as a value; a declared function is modeled where it is called`, at)
  if (a.pure && a.body !== undefined) {
    let p = L.trust.purity.get(a)
    if (p === undefined) {
      p = purityOf(checker, a.body, L.trust.assumptions.of)
      L.trust.purity.set(a, p)
    }
    if (!p.pure)
      throw new Unsupported(`\`${a.name}\` is declared pure and is not: ${p.why}. Declare it \`pure: false\`, or change it so it changes only what it allocates`, at)
  }
  const views = coveringViews(checker, a, at.arguments)
  if (views.length === 0) {
    const given = at.arguments.map((x) => checker.typeToString(checker.getTypeAtLocation(x))).join(", ")
    const declared = a.views.map((v) => `(${v.params.map((t) => checker.typeToString(t)).join(", ")}) at ${v.where}`).join("; ")
    throw new Unsupported(`\`${a.name}\` is called with (${given}), which no declaration covers: ${declared}. Add an \`assume\` whose view takes these types`, at)
  }
  // Inside a quantifier the result depends on the bound index, as the arguments may: one constant for every element
  // would claim the function constant over them.
  const indices = u.openBounds()
  const ids = args.map(identity)
  const key =
    a.pure && ids.every((i) => i !== undefined)
      ? `assumed:${a.views[0]!.where}(${ids.join(",")})[${indices.map((i) => i.sexpr()).join(",")}]`
      : undefined
  const known = key === undefined ? undefined : L.opaque.get(key)
  if (known !== undefined) return known
  const result = symbolicOf(L, checker.getTypeAtLocation(at), [u.fresh(a.name.replace(/\s.*/, ""))], indices, at)
  if (key !== undefined) L.opaque.set(key, result)
  L.trust.used.add(a)
  u.opaqueCalls.add(a.name)
  L.assuming.push(a)
  try {
    inSpec(L, () => {
      for (const v of views)
        for (const law of v.ensures) {
          try {
            u.assume(truthy(u, lowerCall(L, law.law, EMPTY, [...args, result], law.law)), indices)
          } catch (err) {
            if (!(err instanceof Unsupported)) throw err
            throw new Unsupported(`the law \`${law.name}\` of \`${a.name}\` (${v.where}) cannot be read: ${err.message}`, at)
          }
        }
    })
  } finally {
    L.assuming.pop()
  }
  return result
}

/** A whole-number literal argument, such as the -1 of `.at(-1)`. */
const literalIndex = (e: ts.Expression): bigint | undefined => {
  if (ts.isNumericLiteral(e) && /^\d+$/.test(e.text)) return BigInt(e.text)
  if (ts.isPrefixUnaryExpression(e) && e.operator === K.MinusToken && ts.isNumericLiteral(e.operand) && /^\d+$/.test(e.operand.text))
    return -BigInt(e.operand.text)
  return undefined
}

const arrayMethod = (L: Lowering, arr: Extract<Val, { kind: "array" }>, name: string, e: ts.CallExpression, env: Env): Val => {
  const { u } = L
  const z3 = u.z3
  const arg = (k: number): ts.Expression => {
    const a = e.arguments[k]
    if (a === undefined) throw new Unsupported(`\`.${name}\` with no argument ${k + 1}`, e)
    return a
  }
  const predicate = (): ((i: Arith<"main">) => Bool<"main">) => {
    if (e.arguments.length !== 1) throw new Unsupported(`\`.${name}\` with a \`this\` argument is not modeled`, e)
    const f = lowerExpr(L, arg(0), env)
    if (f.kind !== "fn") throw new Unsupported(`\`.${name}\` of a ${f.kind}`, e)
    if (f.node.parameters.length > 1) throw new Unsupported(`\`.${name}\` with a callback reading the index or the array is not modeled`, f.node)
    return (i) => truthy(u, lowerCall(L, f.node, f.env, [arr.elem(i)], e))
  }
  /** `exists` (or `forall`) an index of the array where `p` holds, with the facts about element i inside. */
  /** How many elements to write a quantifier out over: the array's own bound (exact on both sides), else the search side's. */
  const writtenOut = arr.maxSize ?? u.bound
  const quantify = (q: "exists" | "forall", p: (i: Arith<"main">) => Bool<"main">): Bool<"main"> => {
    if (writtenOut !== undefined) {
      // Written out: element k for each k below the bound, counted only where k < length.
      const each = Array.from({ length: writtenOut }, (_, k) => {
        const i = z3.Int.val(k)
        return q === "exists" ? z3.And(i.lt(arr.length), p(i)) : z3.Implies(i.lt(arr.length), p(i))
      })
      return q === "exists" ? z3.Or(z3.Bool.val(false), ...each) : z3.And(z3.Bool.val(true), ...each)
    }
    const i = z3.Int.const(u.fresh("i"))
    const inRange = z3.And(i.ge(0), i.lt(arr.length))
    const { result, facts } = u.within(i, () => p(i))
    return q === "exists"
      ? z3.Exists([i], z3.And(inRange, ...facts, result))
      : z3.ForAll([i], z3.Implies(z3.And(inRange, ...facts), result))
  }
  switch (name) {
    case "at": {
      const k = literalIndex(arg(0))
      if (k === undefined || e.arguments.length !== 1) throw new Unsupported("`.at(k)` is modeled for a whole-number literal k", e)
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
    case "some":
      return bool(quantify("exists", predicate()))
    case "every":
      return bool(quantify("forall", predicate()))
    case "includes": {
      if (e.arguments.length !== 1) throw new Unsupported("`.includes(x, from)` is not modeled", e)
      const x = lowerExpr(L, arg(0), env)
      if (x.kind !== "str" && x.kind !== "bool")
        throw new Unsupported("`.includes` is modeled on strings and booleans (it finds NaN, which `===` does not)", e)
      return bool(quantify("exists", (i) => strictEq(u, arr.elem(i), x, e)))
    }
    case "filter": {
      // The kept elements' count; their identities are not modeled. On the search side the count is
      // exact (a sum over the bounded elements); on the proof side it is only "none or some", which
      // admits every real count, so a proof stands and a model there proves nothing.
      if (u.depth > 0) throw new Unsupported("`.filter` inside a quantifier (`.some`, `.every`, another `.filter`) is not modeled", e)
      const p = predicate()
      let count: Arith<"main">
      if (writtenOut !== undefined) {
        count = z3.Sum(
          z3.Int.val(0),
          ...Array.from({ length: writtenOut }, (_, k) => z3.If(z3.And(z3.Int.val(k).lt(arr.length), p(z3.Int.val(k))), z3.Int.val(1), z3.Int.val(0))),
        )
      } else {
        count = z3.Int.const(u.fresh("filtered"))
        u.assume(z3.And(count.ge(0), count.le(arr.length), count.ge(1).eq(quantify("exists", p))))
        u.abstracted = true
      }
      u.notes.add("A filtered array is modeled by its length alone; its elements are refused where read.")
      return {
        kind: "array",
        length: count,
        ...(arr.maxSize === undefined ? {} : { maxSize: arr.maxSize }),
        elem: () => {
          throw new Unsupported("an element of a filtered array is not modeled (its length is)", e)
        },
      }
    }
    default:
      throw new Unsupported(`array method \`.${name}\` is not modeled`, e)
  }
}

const binary = (L: Lowering, e: ts.BinaryExpression, env: Env): Val => {
  const { u } = L
  const z3 = u.z3
  const op = e.operatorToken.kind
  if (op === K.AmpersandAmpersandToken || op === K.BarBarToken) {
    const l = lowerExpr(L, e.left, env)
    const r = lowerExpr(L, e.right, env)
    if (l.kind === "bool" && r.kind === "bool") return bool(op === K.AmpersandAmpersandToken ? z3.And(l.term, r.term) : z3.Or(l.term, r.term))
    return op === K.AmpersandAmpersandToken ? ite(u, truthy(u, l), r, l, e) : ite(u, truthy(u, l), l, r, e)
  }
  if (op === K.QuestionQuestionToken) return nullishOr(u, lowerExpr(L, e.left, env), () => lowerExpr(L, e.right, env), e)
  const l = lowerExpr(L, e.left, env)
  const r = lowerExpr(L, e.right, env)
  switch (op) {
    case K.EqualsEqualsEqualsToken:
      return bool(strictEq(u, l, r, e))
    case K.ExclamationEqualsEqualsToken:
      return bool(z3.Not(strictEq(u, l, r, e)))
    case K.LessThanToken:
    case K.LessThanEqualsToken:
    case K.GreaterThanToken:
    case K.GreaterThanEqualsToken:
      return bool(compare(u, l, r, ts.tokenToString(op) as Order, e))
    case K.PlusToken:
    case K.MinusToken:
    case K.AsteriskToken:
    case K.SlashToken:
      return arithmetic(L, op, l, r, e)
    default:
      throw new Unsupported(`operator ${ts.tokenToString(op)} is not modeled`, e.operatorToken)
  }
}

const arithmetic = (L: Lowering, op: ts.SyntaxKind, l: Val, r: Val, e: ts.BinaryExpression): Val => {
  const { u } = L
  if (l.kind === "int" && r.kind === "int" && l.origin === "bigint" && r.origin === "bigint") {
    if (op === K.PlusToken) return { ...l, term: l.term.add(r.term) }
    if (op === K.MinusToken) return { ...l, term: l.term.sub(r.term) }
    if (op === K.AsteriskToken) return { ...l, term: l.term.mul(r.term) }
    throw new Unsupported("bigint `/` truncates toward zero, which Z3's division does not", e.operatorToken)
  }
  if (l.kind === "num" && r.kind === "num")
    throw new Unsupported("arithmetic on `number` rounds, which the model of numbers does not see", e.operatorToken)
  if (op === K.PlusToken && l.kind === "str" && r.kind === "str") return { kind: "str", term: l.term.concat(r.term) }
  throw new Unsupported(`${ts.tokenToString(op)} between a ${l.kind} and a ${r.kind} is not modeled`, e)
}

export const emptyEnv = EMPTY

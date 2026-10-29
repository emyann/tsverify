// Lowers pure TypeScript to symbolic values, keeping JavaScript's meaning.
//
// Statements are run by `exec.ts`: `const` and `let`, assignment, changes to
// what the function allocated, `if`, `switch` and loops. This module reads
// expressions. Supported: literals of every primitive, null and undefined; `?:`, `&&`, `||`, `!`,
// `??`, `===`, `!==`, `<` and friends; `+ - *` on bigints, `+` on strings;
// unary `-`; property access and optional chaining; `t[k]` for a literal k on a
// tuple; object and array literals, spreads in them read when a field or an element is; template strings (as unknown strings of
// their parts); calls to functions of the program (inlined, or opaque when they
// cannot be read), to closures, to an adapter's functions and to computations;
// on arrays `.length`, `.at(k)` for a literal k, `.filter(p).length`, `.some(p)`,
// `.every(p)`, `.find(p)`, `.slice(a, b)` for counts, `.includes(x)` for strings and booleans; a callback may read the
// element's index.
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
// inside an expression, casts and non-null assertions (each is a claim the verifier would
// have to trust), `any`, recursion, a binding it cannot see (a global,
// an import from a package no adapter models), string length (code units), a
// closure kept for later over a variable that changes.
//
// Reading a binding only when it is used means a binding the result does not
// need is never checked. The code under verification is taken to throw nothing:
// a `const` whose evaluation would throw, but whose value is never read, is not
// seen. The report says so.
import ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import type { Adapter } from "./adapter.ts"
import { computationCall } from "./computation.ts"
import { type LemmaUse, type Obligation, runFunction } from "./exec.ts"
import { type Order, compare, isNullish, ite, nullishOr, strictEq, truthy } from "./ops.ts"
import { type Purity, purityOf } from "./purity.ts"
import { type Typing, symbolicOf } from "./symbolic.ts"
import { type AssumedFn, type Assumptions, coveringViews } from "./trust.ts"
import {
  type Env,
  type FunctionNode,
  NUM,
  type Thunk,
  UNDEFINED,
  Unsupported,
  type Val,
  exactRational,
  identity,
  lazy,
  lazyRecord,
  memoElems,
  termId,
} from "./value.ts"

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
  /** What the proof code asks proved: invariants, asserts, lemmas' preconditions. */
  readonly obligations: Array<Obligation>
  /**
   * What the proof code lets the proof side know once it is proved: an assert, a lemma's statement, a loop's invariant
   * after it. Never an assumption of the universe: each obligation is checked with the hints made before it only, so
   * no hint proves itself, and a law with all of them.
   */
  readonly hints: Array<Bool>
  /** The lemmas the proof code called, by `file#name`: each is proved too. */
  readonly lemmas: Map<string, LemmaUse>
  /**
   * Invariants the verifier guesses for a `for…of` loop with none written, each read in the loop's scope at `i`
   * elements gone through: candidates, proved or dropped like any other (`verify`).
   */
  guess?: (loop: ts.ForOfStatement) => ReadonlyArray<GuessedInvariant>
  /** Whether a loop with invariants written gets the guesses too, beside them (`verify`'s second round). */
  guessBeside?: boolean
  /** Set when a loop of this side has invariants written. */
  wrote?: boolean
}

/** An invariant the verifier guessed: its obligation's key, place and words, and its claim in a scope at `i`. */
export interface GuessedInvariant {
  /** The law it restates. */
  readonly law: string
  readonly key: string
  readonly at: string
  readonly text: string
  readonly claim: (env: Env, i: Arith) => Bool
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
  obligations: [],
  hints: [],
  lemmas: new Map(),
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

const bool = (term: Bool): Val => ({ kind: "bool", term })

/** The value of calling `fn` (closing over `env`) with `args`. */
export const lowerCall = (L: Lowering, fn: FunctionNode, env: Env, args: ReadonlyArray<Val>, at: ts.Node): Val => {
  if (L.stack.includes(fn)) throw new Unsupported("recursion is not modeled", at)
  if (fn.asteriskToken !== undefined) throw new Unsupported("a generator called as a plain function is not modeled", fn)
  if (fn.modifiers?.some((m) => m.kind === K.AsyncKeyword)) throw new Unsupported("an async function read as a plain one", fn)
  if (fn.body === undefined) throw new Unsupported("a function with no body", fn)
  L.stack.push(fn)
  try {
    return runFunction(
      L,
      fn,
      env,
      args.map((v) => ({ kind: "value", thunk: () => v, owned: false })),
      undefined,
      at,
    ).value()
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
    bind(
      L,
      el.name,
      later(L, () => member(L, value(), key, el)),
      scope,
    )
  }
}

export const propertyKey = (name: ts.PropertyName): string => {
  if (ts.isIdentifier(name) || ts.isStringLiteral(name) || ts.isNoSubstitutionTemplateLiteral(name)) return name.text
  throw new Unsupported("a computed property name is not modeled", name)
}

/** A condition's truth, read as JavaScript reads it: `a && b` is truthy when both are. */
export const cond = (L: Lowering, e: ts.Expression, env: Env): Bool => {
  const z3 = L.u.z3
  const stepped = ranStep(e, env)
  if (stepped !== undefined) return truthy(L.u, stepped())
  if (ts.isParenthesizedExpression(e)) return cond(L, e.expression, env)
  if (ts.isPrefixUnaryExpression(e) && e.operator === K.ExclamationToken) return z3.Not(cond(L, e.operand, env))
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === K.AmpersandAmpersandToken)
    return z3.And(cond(L, e.left, env), cond(L, e.right, env))
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === K.BarBarToken) return z3.Or(cond(L, e.left, env), cond(L, e.right, env))
  return truthy(L.u, lowerExpr(L, e, env))
}

/**
 * The name a step's value is bound under once its computation ran it, and that of an expression whose steps run on some
 * of its paths only (`a && (yield* b)`): one per node, a name no identifier has.
 */
const stepKeys = new WeakMap<ts.Node, string>()
export const stepKey = (n: ts.Node): string => {
  let k = stepKeys.get(n)
  if (k === undefined) {
    k = `\0step${++stepCount}`
    stepKeys.set(n, k)
  }
  return k
}
let stepCount = 0
const LOGICAL = new Set([K.AmpersandAmpersandToken, K.BarBarToken, K.QuestionQuestionToken])
export const isLogical = (e: ts.Node): e is ts.BinaryExpression => ts.isBinaryExpression(e) && LOGICAL.has(e.operatorToken.kind)
/** The value a computation bound for `e` when it ran the steps in it. */
const ranStep = (e: ts.Expression, env: Env): Thunk | undefined => {
  if (!(ts.isYieldExpression(e) || ts.isAwaitExpression(e) || ts.isConditionalExpression(e) || isLogical(e))) return undefined
  const k = stepKeys.get(e)
  return k === undefined ? undefined : env.get(k)
}

export const lowerExpr = (L: Lowering, e: ts.Expression, env: Env): Val => {
  const { u } = L
  const z3 = u.z3
  const stepped = ranStep(e, env)
  if (stepped !== undefined) return stepped()
  if (ts.isParenthesizedExpression(e)) return lowerExpr(L, e.expression, env)
  if (ts.isAsExpression(e) && ts.isConstTypeReference(e.type)) return lowerExpr(L, e.expression, env)
  if (ts.isSatisfiesExpression(e)) return lowerExpr(L, e.expression, env)
  if (ts.isAsExpression(e) || ts.isTypeAssertionExpression(e))
    throw new Unsupported(
      "a cast is a claim the verifier would have to trust: check the value instead (`===`, its `_tag`, `x !== undefined`), so its type follows from the check",
      e,
    )
  if (ts.isNonNullExpression(e))
    throw new Unsupported(
      "`!` is a claim the verifier would have to trust: check the value (`x !== undefined`) and say what happens when it is missing",
      e,
    )

  // Literals.
  if (ts.isBigIntLiteral(e)) return { kind: "int", origin: "bigint", term: z3.Int.val(BigInt(e.text.slice(0, -1).replaceAll("_", ""))) }
  if (ts.isNumericLiteral(e)) return num(z3, Number(e.text.replaceAll("_", "")))
  if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return { kind: "str", term: z3.String.val(e.text) }
  if (e.kind === K.TrueKeyword) return bool(z3.Bool.val(true))
  if (e.kind === K.FalseKeyword) return bool(z3.Bool.val(false))
  if (e.kind === K.NullKeyword) return { kind: "nullish", which: "null" }
  if (ts.isTemplateExpression(e)) return template(L, e, env)
  if (ts.isYieldExpression(e) || ts.isAwaitExpression(e))
    throw new Unsupported("a step (`yield*`, `await`) is modeled in a computation's body, outside any function it defines", e)

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
  if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) {
    closureCheck(L, e)
    return { kind: "fn", node: e, env }
  }

  if (ts.isObjectLiteralExpression(e)) return objectLiteral(L, e, env)
  if (ts.isArrayLiteralExpression(e)) return arrayLiteral(L, e, env)

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
  const key = ids.every((i) => i !== undefined)
    ? `template:${e.getSourceFile().fileName}:${e.pos}(${ids.join(",")})[${indices.map(termId).join(",")}]`
    : undefined
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
  if (k === undefined || k < 0n)
    throw new Unsupported(
      "an element at a computed index is not read: `.at(k)` with a whole-number literal `k`, or `.find`, `.some`, `.every` or a `for…of` loop over the elements",
      e,
    )
  const obj = lowerExpr(L, e.expression, env)
  return optionally(L, obj, e, e.expression, (v) => {
    if (v.kind === "record") {
      const f = v.field(String(k))
      if (f === undefined) throw new Unsupported(`no element ${k}`, e)
      return f
    }
    throw new Unsupported(
      `\`${e.expression.getText()}[${k}]\` on an array is not read: write \`${e.expression.getText()}.at(${k})\`, whose type says it may be missing`,
      e,
    )
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
  return named(L, e)
}

/**
 * `ns.f` where `ns` is a namespace import of one of the program's modules (`import * as laws from "./laws.ts"`): the
 * member `f`, read as its name would be. `undefined` for anything else, a package's namespace among them.
 */
const namespaceMember = (L: Lowering, e: ts.PropertyAccessExpression, env: Env): Val | undefined => {
  const ns = e.expression
  if (!ts.isIdentifier(ns) || env.has(ns.text)) return undefined
  const sym = L.checker.getSymbolAtLocation(ns)
  if (sym === undefined || (sym.flags & ts.SymbolFlags.Alias) === 0) return undefined
  const target = L.checker.getAliasedSymbol(sym)
  const module = target.valueDeclaration ?? target.declarations?.[0]
  if ((target.flags & ts.SymbolFlags.ValueModule) === 0 || module === undefined || !ts.isSourceFile(module) || module.isDeclarationFile)
    return undefined
  if (module.fileName.includes("/node_modules/")) return undefined
  return ts.isIdentifier(e.name) ? named(L, e.name) : undefined
}

/** What a name the code does not bind refers to, by its declaration: a module's function or constant, or a declaration's. */
const named = (L: Lowering, e: ts.Identifier): Val => {
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
  if (
    imported &&
    decl !== undefined &&
    (decl.getSourceFile().isDeclarationFile || decl.getSourceFile().fileName.includes("/node_modules/"))
  ) {
    // A namespace's member is named whole (`Effect.gen`): it is the member that is not read.
    const named = ts.isPropertyAccessExpression(e.parent) && e.parent.expression === e ? e.parent.getText() : e.text
    throw new Unread(
      `\`${named}\` is a package's, which the verifier does not read: declare what it may assume of it, \`assume(${named}, { pure: true, ensures: { ... } })\`, in the spec or a pack the spec imports`,
      e,
    )
  }
  throw new Unsupported(
    `\`${e.text}\` is a binding the verifier cannot see (a \`let\` or a global): read it from a \`const\` or an argument, or move it into a function the spec declares with \`assume\``,
    e,
  )
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
  const fromNamespace = namespaceMember(L, e, env)
  if (fromNamespace !== undefined) return fromNamespace
  const t = L.checker.getTypeAtLocation(e.expression)
  if (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) throw new Unsupported("a property of an `any` or `unknown`", e)
  const obj = lowerExpr(L, e.expression, env)
  return optionally(L, obj, e, e.expression, (v) => member(L, v, e.name.text, e, t))
}

/**
 * Applies `f` to a value that may be null or undefined: in an optional chain the
 * result is undefined when it is; outside one, `f` reads the value present, which
 * is sound only where the type checker has narrowed `objExpr` to neither, so its
 * narrowed type there is asked and anything else refused.
 */
const optionally = (L: Lowering, obj: Val, e: ts.Node, objExpr: ts.Expression, f: (v: Val) => Val): Val => {
  const shownPresent = (): boolean => {
    const t = L.checker.getTypeAtLocation(objExpr)
    const parts = t.isUnion() ? t.types : [t]
    return !parts.some((m) => m.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined | ts.TypeFlags.Void))
  }
  if (obj.kind === "nullish") {
    if (inChain(e)) return { kind: "nullish", which: "undefined" }
    // Shown neither here, and always one: no run reaches this read (`x !== undefined && x.f` where x is undefined).
    if (shownPresent()) return UNDEFINED
    throw new Unsupported(`reading a member of ${obj.which}`, e)
  }
  if (obj.kind !== "maybe") return f(obj)
  if (!inChain(e) && !shownPresent())
    throw new Unsupported("a member of a value the type checker has not shown to be neither null nor undefined here", e)
  if (obj.value === undefined) return { kind: "nullish", which: "undefined" }
  const inner = f(obj.value)
  if (!inChain(e)) return inner
  return ite(L.u, isNullish(L.u, obj), { kind: "nullish", which: "undefined" }, inner, e)
}

/** `obj.name`. A field the object lacks reads as undefined where its type declares it (an optional field left out). */
export const member = (L: Lowering, obj: Val, name: string, at: ts.Node, objType?: ts.Type): Val => {
  if (obj.kind === "record") {
    const v = obj.field(name)
    if (v !== undefined) return v
    const declared = objType === undefined ? undefined : L.checker.getPropertyOfType(L.checker.getNonNullableType(objType), name)
    if (declared !== undefined || obj.has?.(name) !== undefined) return UNDEFINED
    throw new Unsupported(`no field \`${name}\` the verifier can read`, at)
  }
  if (obj.kind === "array" && name === "length") return { kind: "int", origin: "count", term: obj.length }
  if (obj.kind === "str" && name === "length")
    throw new Unsupported(
      'a string\'s length counts UTF-16 code units, which is not modeled: compare with `""` to ask whether it is empty, or move it into a function the spec declares with `assume`',
      at,
    )
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
    const fromNamespace = namespaceMember(L, callee, env)
    if (fromNamespace !== undefined) return callValue(L, fromNamespace, e, env)
    const receiver = lowerExpr(L, callee.expression, env)
    return optionally(L, receiver, callee, callee.expression, (r) => {
      if (r.kind === "array") return arrayMethod(L, r, callee.name.text, e, env)
      if (r.kind === "record") return callValue(L, member(L, r, callee.name.text, callee), e, env)
      throw new Unsupported(`method \`${callee.name.text}\` of a ${r.kind} is not modeled`, e)
    })
  }
  return callValue(L, lowerExpr(L, callee, env), e, env)
}

/** `f` applied to values already lowered: a library's function, a closure, or a function that defines a computation. */
export const applyValue = (L: Lowering, f: Val, args: ReadonlyArray<Val>, at: ts.Node): Val => {
  if (f.kind === "builtin") return f.call(args, at)
  if (f.kind !== "fn") throw new Unsupported(`calling a ${f.kind}`, at)
  for (const a of L.adapters) {
    const c = a.computation?.(L, f.node)
    if (c !== undefined) return computationCall(L, c.node, c.style, f.env, args, at)
  }
  return lowerCall(L, f.node, f.env, args, at)
}

const callValue = (L: Lowering, f: Val, e: ts.CallExpression, env: Env): Val => {
  if (e.arguments.some(ts.isSpreadElement)) throw new Unsupported("spread arguments are not modeled", e)
  if (f.kind === "builtin") {
    const v = f.call(
      e.arguments.map((a) => lowerExpr(L, a, env)),
      e,
    )
    if (L.mode === "spec" && v.kind === "comp")
      throw new Unsupported(
        `spec code calls no operation: \`${f.name}\` is one. A law reads the calls a computation made from the trace it is given`,
        e,
      )
    return v
  }
  if (f.kind !== "fn") throw new Unsupported(`calling a ${f.kind}`, e)
  const args = e.arguments.map((a) => lowerExpr(L, a, env))
  for (const a of L.adapters) {
    const c = a.computation?.(L, f.node)
    if (c === undefined) continue
    if (L.mode === "spec")
      throw new Unsupported(
        `spec code runs no computation: \`${nameOf(c.node)}\` is one. A law reads a computation's outcome and calls from the arguments it is given`,
        e,
      )
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
    throw new Unsupported(
      `spec code is deterministic, and \`${a.name}\` is declared \`pure: false\`: call it from the program and pass its result to the law`,
      at,
    )
  if (L.assuming.includes(a)) throw new Unsupported(`a law of \`${a.name}\`'s assumption calls \`${a.name}\` itself`, at)
  if (!ts.isCallExpression(at))
    throw new Unsupported(`\`${a.name}\` is used as a value; a declared function is modeled where it is called`, at)
  if (a.pure && a.body !== undefined) {
    let p = L.trust.purity.get(a)
    if (p === undefined) {
      p = purityOf(checker, a.body, L.trust.assumptions.of)
      L.trust.purity.set(a, p)
    }
    if (!p.pure)
      throw new Unsupported(
        `\`${a.name}\` is declared pure and is not: ${p.why}. Declare it \`pure: false\`, or change it so it changes only what it allocates`,
        at,
      )
  }
  const views = coveringViews(checker, a, at.arguments)
  if (views.length === 0) {
    const given = at.arguments.map((x) => checker.typeToString(checker.getTypeAtLocation(x))).join(", ")
    const declared = a.views.map((v) => `(${v.params.map((t) => checker.typeToString(t)).join(", ")}) at ${v.where}`).join("; ")
    throw new Unsupported(
      `\`${a.name}\` is called with (${given}), which no declaration covers: ${declared}. Add an \`assume\` whose view takes these types`,
      at,
    )
  }
  // Inside a quantifier the result depends on the bound index, as the arguments may: one constant for every element
  // would claim the function constant over them.
  const indices = u.openBounds()
  const ids = args.map(identity)
  const key =
    a.pure && ids.every((i) => i !== undefined)
      ? `assumed:${a.views[0]!.where}(${ids.join(",")})[${indices.map(termId).join(",")}]`
      : undefined
  const known = key === undefined ? undefined : L.opaque.get(key)
  if (known !== undefined) return known
  const result = symbolicOf(L, checker.getTypeAtLocation(at), [u.given(a.name.replace(/\s.*/, ""))], indices, at)
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
  const predicate = (): ((i: Arith) => Bool) => {
    if (e.arguments.length !== 1) throw new Unsupported(`\`.${name}\` with a \`this\` argument is not modeled`, e)
    const f = lowerExpr(L, arg(0), env)
    if (f.kind !== "fn") throw new Unsupported(`\`.${name}\` of a ${f.kind}`, e)
    if (f.node.parameters.length > 2) throw new Unsupported(`\`.${name}\` with a callback reading the array is not modeled`, f.node)
    return (i) => truthy(u, lowerCall(L, f.node, f.env, [arr.elem(i), { kind: "int", origin: "count", term: i }], e))
  }
  /** `exists` (or `forall`) an index of the array where `p` holds, with the facts about element i inside. */
  /** How many elements to write a quantifier out over: the array's own bound (exact on both sides), else the search side's. */
  const writtenOut = arr.maxSize ?? u.bound
  const quantify = (q: "exists" | "forall", p: (i: Arith) => Bool): Bool => {
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
    case "find": {
      const { found, k } = firstIndex(L, arr, predicate(), e)
      return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(found), value: arr.elem(k) }
    }
    case "slice":
      return slice(
        L,
        arr,
        e.arguments.map((a) => lowerExpr(L, a, env)),
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
      if (x.kind !== "str" && x.kind !== "bool" && x.kind !== "int")
        throw new Unsupported(
          "`.includes` of a `number` finds NaN, which `===` does not, and is not modeled: write `.some((y) => y === x)`",
          e,
        )
      return bool(quantify("exists", (i) => strictEq(u, arr.elem(i), x, e)))
    }
    case "filter": {
      // The kept elements' count; their identities are not modeled. On the search side the count is
      // exact (a sum over the bounded elements); on the proof side it is only "none or some", which
      // admits every real count, so a proof stands and a model there proves nothing.
      if (u.depth > 0) throw new Unsupported("`.filter` inside a quantifier (`.some`, `.every`, another `.filter`) is not modeled", e)
      const p = predicate()
      let count: Arith
      if (writtenOut !== undefined) {
        count = z3.Sum(
          z3.Int.val(0),
          ...Array.from({ length: writtenOut }, (_, k) =>
            z3.If(z3.And(z3.Int.val(k).lt(arr.length), p(z3.Int.val(k))), z3.Int.val(1), z3.Int.val(0)),
          ),
        )
      } else {
        count = z3.Int.const(u.fresh("filtered"))
        u.assume(z3.And(count.ge(0), count.le(arr.length), count.ge(1).eq(quantify("exists", p))))
        u.abstracted = true
        u.approximations.add(`\`${e.getText()}\` is counted only as none or some on the proof side`)
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
    if (l.kind === "bool" && r.kind === "bool")
      return bool(op === K.AmpersandAmpersandToken ? z3.And(l.term, r.term) : z3.Or(l.term, r.term))
    return op === K.AmpersandAmpersandToken ? ite(u, truthy(u, l), r, l, e) : ite(u, truthy(u, l), l, r, e)
  }
  if (op === K.QuestionQuestionToken) return nullishOr(u, lowerExpr(L, e.left, env), () => lowerExpr(L, e.right, env), e)
  const l = narrowed(L, e.left, lowerExpr(L, e.left, env), op)
  const r = narrowed(L, e.right, lowerExpr(L, e.right, env), op)
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
    case K.PercentToken:
      return arithmetic(L, op, l, r, e)
    default:
      throw new Unsupported(
        `operator ${ts.tokenToString(op)} is not modeled${op === K.EqualsEqualsToken || op === K.ExclamationEqualsToken ? `: write \`${op === K.EqualsEqualsToken ? "===" : "!=="}\` (and \`x === null || x === undefined\` for a nullish check)` : ""}`,
        e.operatorToken,
      )
  }
}

/**
 * An operand of `<` or `+`, read as present where the type checker has narrowed it to neither null nor undefined
 * (`out === undefined || out < 0n`): the value then only matters on the paths where it is present.
 */
const narrowed = (L: Lowering, e: ts.Expression, v: Val, op: ts.SyntaxKind): Val => {
  if (v.kind !== "maybe" || op === K.EqualsEqualsEqualsToken || op === K.ExclamationEqualsEqualsToken) return v
  const t = L.checker.getTypeAtLocation(e)
  if ((t.isUnion() ? t.types : [t]).some((m) => m.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined | ts.TypeFlags.Void))) return v
  return v.value ?? v
}

export const arithmetic = (L: Lowering, op: ts.SyntaxKind, l: Val, r: Val, e: ts.BinaryExpression): Val => {
  if (l.kind === "int" && r.kind === "int" && l.origin === "bigint" && r.origin === "bigint") {
    if (op === K.PlusToken) return { ...l, term: l.term.add(r.term) }
    if (op === K.MinusToken) return { ...l, term: l.term.sub(r.term) }
    if (op === K.AsteriskToken) return { ...l, term: l.term.mul(r.term) }
    throw new Unsupported(
      `bigint \`${ts.tokenToString(op)}\` is not modeled (\`/\` and \`%\` truncate toward zero, which Z3's division does not): keep it out of the code a law reads, or move it into a function the spec declares with \`assume\``,
      e.operatorToken,
    )
  }
  if (l.kind === "num" && r.kind === "num")
    throw new Unsupported(
      "arithmetic on `number` rounds, which the model of numbers does not see: use `bigint` where the values are whole, or move it into a function the spec declares with `assume`",
      e.operatorToken,
    )
  if (op === K.PlusToken && l.kind === "str" && r.kind === "str") return { kind: "str", term: l.term.concat(r.term) }
  throw new Unsupported(`${ts.tokenToString(op)} between a ${l.kind} and a ${r.kind} is not modeled`, e)
}

export const emptyEnv = EMPTY

/**
 * The first index below the array's length where `p` holds, and whether there is one: written out where the array's
 * bound is known, else a fresh index defined by quantifiers (it holds there, and nowhere before it).
 */
export const firstIndex = (
  L: Lowering,
  arr: Extract<Val, { kind: "array" }>,
  p: (i: Arith) => Bool,
  at: ts.Node,
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
  if (u.depth > 0) throw new Unsupported("a search (`.find`) inside a quantifier is not modeled", at)
  const k = u.leaf([u.fresh("first"), "$"], "int", [], "count") as never as Arith
  const some = z3.Int.const(u.fresh("i"))
  const hasOne = u.within(some, () => p(some))
  const found = z3.Exists([some], z3.And(some.ge(0), some.lt(arr.length), ...hasOne.facts, hasOne.result))
  const before = z3.Int.const(u.fresh("j"))
  const none = u.within(before, () => p(before))
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
  )
  return { found, k }
}

/** A count from a value: a count itself, or a whole-number literal. */
const countOf = (L: Lowering, v: Val, at: ts.Node): Arith => {
  if (v.kind === "int" && v.origin === "count") return v.term
  if (v.kind === "num" && L.u.z3.isRealVal(v.real) && L.u.z3.isIntVal(v.cls) && Number(v.cls.value()) === NUM.finite) {
    const r = v.real.value()
    if (r.denominator === 1n && r.numerator >= 0n) return L.u.z3.Int.val(r.numerator)
  }
  throw new Unsupported("`.slice` is modeled with counts (an index, a length) and non-negative whole-number literals", at)
}

/** `arr.slice(start?, end?)`: a view of the same elements, from `start`, below `end`, both clamped to the length. */
export const slice = (L: Lowering, arr: Extract<Val, { kind: "array" }>, args: ReadonlyArray<Val>, at: ts.Node): Val => {
  const z3 = L.u.z3
  if (args.length > 2) throw new Unsupported("`.slice` takes a start and an end", at)
  const start = args[0] === undefined ? z3.Int.val(0) : countOf(L, args[0], at)
  const end = args[1] === undefined ? arr.length : countOf(L, args[1], at)
  const lo = z3.If(start.le(arr.length), start, arr.length)
  const hi = z3.If(end.le(arr.length), end, arr.length)
  return {
    kind: "array",
    length: z3.If(hi.ge(lo), hi.sub(lo), z3.Int.val(0)),
    elem: memoElems((i) => arr.elem(i.add(lo))),
    ...(arr.maxSize === undefined ? {} : { maxSize: arr.maxSize }),
    ...(arr.id === undefined ? {} : { id: `slice(${arr.id},${termId(lo)},${termId(hi)})` }),
  }
}

/** Whether every member of `type` declares `name` as a property it requires (not optional, not a method). */
const requiredKey = (checker: ts.TypeChecker, type: ts.Type, name: string): boolean =>
  (type.isUnion() ? type.types : [type]).every((t) => {
    const p = checker.getPropertyOfType(t, name)
    return p !== undefined && !(p.flags & (ts.SymbolFlags.Optional | ts.SymbolFlags.Method))
  })

/**
 * An object literal. A field's value is the last property's that may hold it: a property written in place holds its
 * key; a spread holds the keys of what it spreads, which the verifier knows of an object the code built (`has`) and of
 * nothing else. A spread is read only when a field it may hold is.
 */
const objectLiteral = (L: Lowering, e: ts.ObjectLiteralExpression, env: Env): Val => {
  const { u } = L
  const z3 = u.z3
  type Part = { readonly key: string; readonly value: Thunk } | { readonly spread: Thunk; readonly node: ts.Node }
  const parts: Array<Part> = e.properties.map((p): Part => {
    if (ts.isPropertyAssignment(p)) return { key: propertyKey(p.name), value: later(L, () => lowerExpr(L, p.initializer, env)) }
    if (ts.isShorthandPropertyAssignment(p)) return { key: p.name.text, value: later(L, () => lowerExpr(L, p.name, env)) }
    if (ts.isSpreadAssignment(p)) return { spread: later(L, () => lowerExpr(L, p.expression, env)), node: p }
    throw new Unsupported("methods and accessors in an object literal are not modeled", p)
  })
  const spreadOf = (v: Val, name: string, at: ts.Node): { has: Bool; value: Val | undefined } => {
    if (v.kind === "nullish") return { has: z3.Bool.val(false), value: undefined }
    if (v.kind === "maybe") {
      if (v.value === undefined) return { has: z3.Bool.val(false), value: undefined }
      const inner = spreadOf(v.value, name, at)
      return { has: z3.And(z3.Not(isNullish(u, v)), inner.has), value: inner.value }
    }
    if (v.kind === "record" && v.has !== undefined) {
      const has = v.has(name)
      if (has !== undefined) return { has, value: v.field(name) }
    }
    // A key its type requires: the value holds it, its own, as a value of its type is taken to be plain data.
    if (
      v.kind === "record" &&
      ts.isSpreadAssignment(at) &&
      requiredKey(L.checker, L.checker.getNonNullableType(L.checker.getTypeAtLocation(at.expression)), name)
    ) {
      u.notes.add(
        "A spread copies each property its value's type requires: the value is taken to be plain data, its properties its own, none a getter.",
      )
      return { has: z3.Bool.val(true), value: v.field(name) }
    }
    throw new Unsupported(
      `\`${name}\` is read from an object built with a spread of a value whose keys the verifier does not know (at run time it may hold more than its type says)`,
      at,
    )
  }
  const resolved = new Map<string, { has: Bool; value: Val | undefined }>()
  const resolve = (name: string) => {
    let r = resolved.get(name)
    if (r !== undefined) return r
    let has: Bool = z3.Bool.val(false)
    let value: Val | undefined
    for (const p of parts) {
      if ("key" in p) {
        if (p.key === name) {
          has = z3.Bool.val(true)
          value = p.value()
        }
        continue
      }
      const sp = spreadOf(p.spread(), name, p.node)
      if (z3.isFalse(sp.has)) continue
      const v = sp.value ?? UNDEFINED
      value = z3.isTrue(sp.has) ? v : ite(u, sp.has, v, value ?? UNDEFINED, p.node)
      has = z3.isTrue(sp.has) ? sp.has : z3.Or(has, sp.has)
    }
    r = { has, value }
    resolved.set(name, r)
    return r
  }
  return lazyRecord(
    (name) => {
      const r = resolve(name)
      return z3.isFalse(r.has) ? undefined : (r.value ?? UNDEFINED)
    },
    undefined,
    (name) => resolve(name).has,
  )
}

/** An array literal: its items and the elements of what it spreads, in order. */
const arrayLiteral = (L: Lowering, e: ts.ArrayLiteralExpression, env: Env): Val => {
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

/** The names each function body assigns or changes (cached), for the closure check. */
const changedIn = new WeakMap<ts.Node, Set<string>>()
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
  const passedName = (x: ts.Expression): string | undefined => (ts.isIdentifier(x) && primitive(x) ? undefined : rootName(x))
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
const closureCheck = (L: Lowering, e: ts.ArrowFunction | ts.FunctionExpression): void => {
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

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
// Arithmetic on `number` is read where it is exact, each operation an
// obligation that it is (`exactly`). Refused with a source span: `%` on
// `number`, `==`, assignments inside an expression, casts and non-null assertions (each is a claim the verifier would
// have to trust), `any`, recursion, a binding it cannot see (a global,
// an import from a package no adapter models), a closure kept for later over a
// variable that changes.
//
// Reading a binding only when it is used means a binding the result does not
// need is never checked. The code under verification is taken to throw nothing:
// a `const` whose evaluation would throw, but whose value is never read, is not
// seen. The report says so.
import ts from "typescript"
import type { Arith, Bool, FuncDecl } from "z3-solver"
import type { Adapter } from "./adapter.ts"
import { chosen, computationCall } from "./computation.ts"
import { type LemmaUse, type Obligation, runFunction } from "./exec.ts"
import {
  type Order,
  compare,
  countAsNum,
  intOf,
  isNegZero,
  isNullish,
  isWhole,
  ite,
  nullishOr,
  sameValue,
  strictEq,
  truthy,
  undefinedOr,
} from "./ops.ts"
import { narrowedField } from "./narrow.ts"
import { type Purity, isLib, purityOf } from "./purity.ts"
import { MAX_TIME, type Typing, symbolicOf } from "./symbolic.ts"
import type { Universe } from "./universe.ts"
import { type AssumedFn, type Assumptions, coveringViews } from "./trust.ts"
import {
  type Env,
  type FunctionNode,
  KIND,
  NUM,
  type Thunk,
  UNDEFINED,
  Unsupported,
  type Val,
  exactRational,
  identity,
  jsString,
  lazy,
  lazyRecord,
  locate,
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
  /** Searches of an array by a predicate, by the array's identity and the predicate's term: the same search, the same index. */
  readonly searches: Map<string, { readonly found: Bool; readonly k: Arith }>
  readonly trust: Trust
  /** The mode of the code being lowered now. */
  mode: Mode
  /**
   * The condition the code being lowered now runs under: the branches taken to reach it from the contract's entry. A
   * division holds its divisor non-zero there, and nowhere else (`under`, `onBranch`).
   */
  guard: Bool
  /**
   * While spec code is read (a law, a `requires`): what each division it runs needs, a divisor other than 0n where it
   * runs. Spec code that throws does not hold, so these are part of what it says (`definedSpec`).
   */
  defined: Array<Bool> | undefined
  /** While a law or a `requires` is read: where each of its `number` operations is exact (`definedSpec`). */
  exact: Array<Bool> | undefined
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
  searches: new Map(),
  trust,
  mode: "exec",
  exact: undefined,
  guard: typing.u.z3.Bool.val(true),
  defined: undefined,
  assuming: [],
  obligations: [],
  hints: [],
  lemmas: new Map(),
})

/** Runs `f` with `guard` as the condition the code it lowers runs under. */
export const under = <A>(L: Lowering, guard: Bool, f: () => A): A => {
  const prev = L.guard
  L.guard = guard
  try {
    return f()
  } finally {
    L.guard = prev
  }
}

/** Runs `f` on the branch where `c` holds, from the one being lowered now. */
export const onBranch = <A>(L: Lowering, c: Bool, f: () => A): A => (L.u.z3.isTrue(c) ? f() : under(L, L.u.z3.And(L.guard, c), f))

/**
 * Spec code's truth (a law, a `requires`): `f`'s, where every division it runs has a divisor other than 0n. Spec code
 * that divides by 0n throws, so it does not hold there.
 *
 * Its `number` operations are read exactly, which they are where the model says so (`exactly`); elsewhere JavaScript
 * may round, and what the spec says there is not known. So a law is proved only where they are exact, and broken only
 * where they are; a `requires` admits every input where they may not be on the proof side, so no proof leaves one out,
 * and none on the search side, so every counterexample is one JavaScript allows.
 */
export const definedSpec = (L: Lowering, f: () => Bool, role: "law" | "requires" = "law"): Bool => {
  const prev = L.defined
  const gathered: Array<Bool> = []
  L.defined = gathered
  try {
    const read = exactSpec(L, f, role === "law" ? "asserted" : "assumed")
    return gathered.length === 0 ? read : L.u.z3.And(...gathered, read)
  } finally {
    L.defined = prev
  }
}

/**
 * Spec code read by the way it is used, for its `number` operations, each read exactly where it is exact and unknown
 * elsewhere: what is `asserted`, a goal, holds only where they are exact on the proof side, and is broken only where
 * they are on the search side; what is `assumed` admits every run where they may not be on the proof side, and none on
 * the search side. So no proof leans on a value JavaScript may round, and no counterexample is a run it would not make.
 */
export const exactSpec = (L: Lowering, f: () => Bool, role: "asserted" | "assumed"): Bool => {
  const prev = L.exact
  const exact: Array<Bool> = []
  L.exact = exact
  try {
    const z3 = L.u.z3
    const holds = f()
    if (exact.length === 0) return holds
    return (role === "asserted") === (L.u.bound === undefined) ? z3.And(...exact, holds) : z3.Or(z3.Not(z3.And(...exact)), holds)
  } finally {
    L.exact = prev
  }
}

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
export const later = (L: Lowering, f: () => Val, guard: Bool = L.guard): Thunk => {
  const mode = L.mode
  const depth = L.u.depth
  return lazy(() => {
    const prev = L.mode
    L.mode = mode
    try {
      return L.u.outside(depth, () => under(L, guard, f))
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
    // A default is taken where the argument is `undefined`: left out, or given as one.
    const value: Thunk = defaulted(
      L,
      given !== undefined ? () => given : () => UNDEFINED,
      p.initializer === undefined ? undefined : later(L, () => lowerExpr(L, p.initializer!, scope)),
      p,
    )
    bind(L, p.name, value, scope)
  })
  return scope
}

/** `value`, or what `fallback` gives where it is `undefined`: a default, of a parameter or of a pattern's name. */
export const defaulted = (L: Lowering, value: Thunk, fallback: Thunk | undefined, at: ts.Node): Thunk =>
  fallback === undefined
    ? value
    : later(L, () => {
        const given = value()
        // A function the caller may give, or leave to the default the code writes: the default called as written.
        const merged = given.kind === "maybe" && given.value?.kind === "builtin"
        return undefinedOr(L.u, given, merged ? () => callable(L, fallback()) : fallback, at)
      })

/**
 * A function the code writes, as a value that may stand where a function it is given does (a default for a parameter
 * of a function's type): called, it is called as the code wrote it.
 */
const callable = (L: Lowering, v: Val): Val => {
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
const boundArgs = (L: Lowering, a: AssumedFn, args: ReadonlyArray<Val>, at: ts.Node): ReadonlyArray<Val> => {
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
const effectsOfValue = (L: Lowering, v: Val | undefined): string | undefined => {
  if (v === undefined || v.kind === "nullish") return undefined
  if (v.kind === "maybe") return effectsOfValue(L, v.value)
  if (v.kind === "builtin") return v.effects?.()
  if (v.kind === "fn") return effectsOf(L, v)
  return `it is a ${v.kind}, not a function the verifier reads`
}

/**
 * What an object pattern's rest holds: every property of `v` but the keys the pattern named before it. As a spread,
 * it copies what the value's type says it holds, the value taken to be plain data.
 */
export const restOf = (L: Lowering, v: Val, named: ReadonlyArray<string>, at: ts.Node): Val => {
  const obj = v.kind === "maybe" ? (v.value ?? v) : v
  if (obj.kind !== "record") throw new Unsupported(`the rest of a ${obj.kind} is not modeled`, at)
  L.u.notes.add(
    "An object rest copies each property but those named before it: the value is taken to be plain data, its properties its own, none a getter.",
  )
  const left = new Set(named)
  // The keys named are known absent, whatever the value held: a spread of the rest never brings them back.
  return lazyRecord(
    (n) => (left.has(n) ? undefined : obj.field(n)),
    undefined,
    (n) => (left.has(n) ? L.u.z3.Bool.val(false) : obj.has?.(n)),
  )
}

/**
 * Element `k` of what an array pattern takes apart: an array's, `undefined` past its end, as `xs[k]` reads it, and
 * refused where its type says it is there and nothing says so (no `noUncheckedIndexedAccess`, no default); a tuple's
 * field `k`.
 */
export const patternElement = (L: Lowering, v: Val, k: number, el: ts.BindingElement): Val => {
  const z3 = L.u.z3
  const p = v.kind === "maybe" && v.value !== undefined ? v.value : v
  if (p.kind === "array") {
    const known = p.size !== undefined && k < p.size
    if (!known && el.initializer === undefined) {
      const t = L.checker.getTypeAtLocation(el)
      if (!(t.isUnion() ? t.types : [t]).some((m) => m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Any | ts.TypeFlags.Unknown)))
        throw new Unsupported(
          `\`${el.getText()}\` takes an element of an array where its type says it is there, which may be false: turn on \`noUncheckedIndexedAccess\`, or give it a default`,
          el,
        )
    }
    const i = z3.Int.val(k)
    return known ? p.elem(i) : { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(i.lt(p.length)), value: p.elem(i) }
  }
  if (p.kind === "record") {
    const f = p.field(String(k))
    if (f === undefined) throw new Unsupported(`no element ${k} to take apart`, el)
    return f
  }
  throw new Unsupported(`an array pattern over a ${p.kind}`, el)
}

/** What `...rest` in an array pattern holds: the elements from `k` on, a copy, as `.slice(k)` gives them. */
export const patternRest = (L: Lowering, v: Val, k: number, el: ts.BindingElement): Val => {
  const p = v.kind === "maybe" && v.value !== undefined ? v.value : v
  if (p.kind !== "array") throw new Unsupported(`the rest of a ${p.kind} in an array pattern is not modeled`, el)
  return slice(L, p, [{ kind: "int", origin: "count", term: L.u.z3.Int.val(k) }], el)
}

/** The keys an object pattern names, each with its element, and its rest, if it has one. */
export const patternKeys = (
  pattern: ts.ObjectBindingPattern,
): { readonly keys: ReadonlyArray<{ readonly key: string; readonly el: ts.BindingElement }>; readonly rest?: ts.BindingElement } => {
  const keys: Array<{ key: string; el: ts.BindingElement }> = []
  let rest: ts.BindingElement | undefined
  for (const el of pattern.elements) {
    if (el.dotDotDotToken !== undefined) rest = el
    else keys.push({ key: el.propertyName === undefined ? (el.name as ts.Identifier).text : propertyKey(el.propertyName), el })
  }
  return rest === undefined ? { keys } : { keys, rest }
}

/** Binds a name or an object pattern to a value, each name read on first use; a default where its value is `undefined`. */
export const bind = (L: Lowering, name: ts.BindingName, value: Thunk, scope: Map<string, Thunk>): void => {
  if (ts.isIdentifier(name)) {
    scope.set(name.text, value)
    return
  }
  if (ts.isArrayBindingPattern(name)) {
    name.elements.forEach((el, k) => {
      if (ts.isOmittedExpression(el)) return
      if (el.dotDotDotToken !== undefined) {
        bind(
          L,
          el.name,
          later(L, () => patternRest(L, value(), k, el)),
          scope,
        )
        return
      }
      bind(
        L,
        el.name,
        defaulted(
          L,
          later(L, () => patternElement(L, value(), k, el)),
          el.initializer === undefined ? undefined : later(L, () => lowerExpr(L, el.initializer!, scope)),
          el,
        ),
        scope,
      )
    })
    return
  }
  const { keys, rest } = patternKeys(name)
  // Each name read at its type, as a property access is: a path where the object lacks the key reads `undefined` there.
  const objType = L.checker.getTypeAtLocation(name)
  const whole = (): Val => shownPresent(value(), objType)
  for (const { key, el } of keys)
    bind(
      L,
      el.name,
      defaulted(
        L,
        later(L, () => member(L, whole(), key, el, objType, L.checker.getTypeAtLocation(el))),
        el.initializer === undefined ? undefined : later(L, () => lowerExpr(L, el.initializer!, scope)),
        el,
      ),
      scope,
    )
  if (rest !== undefined)
    bind(
      L,
      rest.name,
      later(L, () =>
        restOf(
          L,
          whole(),
          keys.map((k) => k.key),
          rest,
        ),
      ),
      scope,
    )
}

export const propertyKey = (name: ts.PropertyName): string => {
  if (ts.isIdentifier(name) || ts.isStringLiteral(name) || ts.isNoSubstitutionTemplateLiteral(name)) return name.text
  // A number names the key JavaScript writes it as: `0x10` is "16", `1.50` is "1.5".
  if (ts.isNumericLiteral(name)) return String(Number(name.text.replaceAll("_", "")))
  throw new Unsupported("a computed property name is not modeled", name)
}

/** A condition's truth, read as JavaScript reads it: `a && b` is truthy when both are. */
export const cond = (L: Lowering, e: ts.Expression, env: Env): Bool => {
  const z3 = L.u.z3
  const stepped = ranStep(e, env)
  if (stepped !== undefined) return truthy(L.u, stepped())
  if (ts.isParenthesizedExpression(e)) return cond(L, e.expression, env)
  if (ts.isPrefixUnaryExpression(e) && e.operator === K.ExclamationToken) return z3.Not(cond(L, e.operand, env))
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === K.AmpersandAmpersandToken) {
    const l = cond(L, e.left, env)
    return z3.And(
      l,
      onBranch(L, l, () => cond(L, e.right, env)),
    )
  }
  if (ts.isBinaryExpression(e) && e.operatorToken.kind === K.BarBarToken) {
    const l = cond(L, e.left, env)
    return z3.Or(
      l,
      onBranch(L, z3.Not(l), () => cond(L, e.right, env)),
    )
  }
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
  if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) return { kind: "str", term: jsString(z3, e.text) }
  if (e.kind === K.TrueKeyword) return bool(z3.Bool.val(true))
  if (e.kind === K.FalseKeyword) return bool(z3.Bool.val(false))
  if (e.kind === K.NullKeyword) return { kind: "nullish", which: "null" }
  if (ts.isTemplateExpression(e)) return template(L, e, env)
  if (ts.isYieldExpression(e) || ts.isAwaitExpression(e))
    throw new Unsupported("a step (`yield*`, `await`) is modeled in a computation's body, outside any function it defines", e)

  if (ts.isIdentifier(e) && env.has(e.text)) return narrowedKind(L, e, env.get(e.text)!())
  if (ts.isIdentifier(e) || ts.isPropertyAccessExpression(e) || ts.isCallExpression(e) || ts.isNewExpression(e))
    for (const a of L.adapters) {
      const v = a.expr?.(L, e, env)
      if (v !== undefined) return v
    }
  if (ts.isIdentifier(e)) return narrowedKind(L, e, identifier(L, e, env))
  if (ts.isPropertyAccessExpression(e)) return narrowedKind(L, e, propertyAccess(L, e, env))
  if (ts.isElementAccessExpression(e)) return narrowedKind(L, e, elementAccess(L, e, env))
  if (ts.isNewExpression(e)) throw new Unsupported(`\`new\` of a class no adapter models`, e)
  if (ts.isCallExpression(e)) return narrowedKind(L, e, call(L, e, env))
  if (ts.isTypeOfExpression(e)) return typeOf(L, lowerExpr(L, e.expression, env), e)
  if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) {
    closureCheck(L, e)
    return { kind: "fn", node: e, env }
  }

  if (ts.isObjectLiteralExpression(e)) return objectLiteral(L, e, env)
  if (ts.isArrayLiteralExpression(e)) return arrayLiteral(L, e, env)

  if (ts.isConditionalExpression(e)) {
    const c = cond(L, e.condition, env)
    const yes = onBranch(L, c, () => lowerExpr(L, e.whenTrue, env))
    const no = onBranch(L, z3.Not(c), () => lowerExpr(L, e.whenFalse, env))
    if (yes.kind === "comp" && no.kind === "comp") return chosen(L, c, yes, no, e)
    return ite(u, c, yes, no, e)
  }

  if (ts.isPrefixUnaryExpression(e)) {
    if (e.operator === K.ExclamationToken) return bool(z3.Not(cond(L, e.operand, env)))
    if (e.operator === K.TildeToken) {
      const v = lowerExpr(L, e.operand, env)
      const n = asNumber(L, v)
      if (n === undefined) throw new Unsupported(`\`~\` of a ${v.kind} is not modeled: bitwise operators are read on \`number\``, e)
      return integral(L, int32(L, truncatedOf(L, n)).neg().sub(1))
    }
    if (e.operator === K.MinusToken) {
      const v = lowerExpr(L, e.operand, env)
      if (v.kind === "int" && v.origin === "bigint") return { ...v, term: v.term.neg() }
      const n = asNumber(L, v)
      if (n !== undefined)
        return {
          kind: "num",
          cls: z3.If(n.cls.eq(NUM.posInf), z3.Int.val(NUM.negInf), z3.If(n.cls.eq(NUM.negInf), z3.Int.val(NUM.posInf), n.cls)),
          real: n.real.neg(),
          ...(n.whole === undefined ? {} : { whole: n.whole }),
          ...(n.int === undefined ? {} : { int: n.int.neg() }),
          // `-0` of `0`, and `0` of `-0`.
          negZero: z3.And(n.cls.eq(NUM.finite), n.real.eq(0), z3.Not(isNegZero(L.u, n))),
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
  if (text.length > 0) L.u.assume(z3.Not(term.eq(jsString(z3, ""))), indices)
  const v: Val = { kind: "str", term }
  if (key !== undefined) L.opaque.set(key, v)
  L.u.notes.add("A template string is an unknown string of its parts: equal parts, equal strings; non-empty when its literal text is.")
  return v
}

/** A value the type checker has shown present (`if (!run.pruned) return`, then `const { at } = run.pruned`): what it holds. */
export const shownPresent = (v: Val, type: ts.Type): Val => {
  const parts = type.isUnion() ? type.types : [type]
  return v.kind === "maybe" && v.value !== undefined && !parts.some((m) => m.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined))
    ? v.value
    : v
}

/** `xs[i]` on an array or a string at any index, missing outside it; `t[k]` for a whole-number literal k on a tuple (or any record), its field `k`. */
const elementAccess = (L: Lowering, e: ts.ElementAccessExpression, env: Env): Val => {
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

/**
 * A value of more than one kind, read where the type checker has narrowed it (`typeof x === "string"`, `x === "unsigned"`):
 * its part of the kinds the narrowed type allows. No run reaches the read with the value of another kind.
 */
const narrowedKind = (L: Lowering, e: ts.Expression, v: Val): Val => {
  const inner = v.kind === "maybe" ? v.value : v
  if (inner?.kind !== "mixed") return v
  const t = L.checker.getTypeAtLocation(e)
  const allowed = new Set<number>(
    (t.isUnion() ? t.types : [t]).flatMap((m) =>
      m.flags & ts.TypeFlags.BooleanLike
        ? [KIND.bool]
        : m.flags & ts.TypeFlags.StringLike
          ? [KIND.str]
          : m.flags & ts.TypeFlags.NumberLike
            ? [KIND.num]
            : m.flags & ts.TypeFlags.BigIntLike
              ? [KIND.bigint]
              : [],
    ),
  )
  const kept = inner.parts.filter((p) => allowed.has(p.tag))
  if (kept.length === 0 || kept.length === inner.parts.length) return v
  const picked: Val = kept.length === 1 ? kept[0]!.value : { ...inner, parts: kept }
  return v.kind === "maybe" ? { ...v, value: picked } : picked
}

/** `typeof v`, as JavaScript names a value's kind: `"object"` of `null` among them. */
const typeOf = (L: Lowering, v: Val, at: ts.Node): Val => {
  const z3 = L.u.z3
  const word = (w: string) => jsString(z3, w)
  const of = (x: Val): ReturnType<typeof word> => {
    switch (x.kind) {
      case "bool":
        return word("boolean")
      case "str":
        return word("string")
      case "num":
        return word("number")
      case "int":
        return word(x.origin === "bigint" ? "bigint" : "number")
      case "nullish":
        return word(x.which === "null" ? "object" : "undefined")
      case "maybe":
        return z3.If(
          x.isNull,
          word("object"),
          z3.If(x.isUndefined, word("undefined"), x.value === undefined ? word("undefined") : of(x.value)),
        )
      case "mixed":
        return x.parts.reduceRight<ReturnType<typeof word>>((rest, p) => z3.If(x.tag.eq(p.tag), of(p.value), rest), word("undefined"))
      case "record":
      case "array":
      case "comp":
        return word("object")
      case "fn":
      case "builtin":
        return word("function")
      case "opaque":
        if (x.typeOf !== undefined) return x.typeOf()
        throw new Unsupported("`typeof` of a value of type `unknown` the code was not given is not modeled", at)
    }
  }
  return { kind: "str", term: of(v) }
}

export const num = (z3: Lowering["u"]["z3"], n: number): Val => ({
  kind: "num",
  cls: z3.Int.val(Number.isNaN(n) ? NUM.nan : n === Infinity ? NUM.posInf : n === -Infinity ? NUM.negInf : NUM.finite),
  real: z3.Real.val(Number.isFinite(n) ? exactRational(n) : 0),
  whole: z3.Bool.val(!Number.isFinite(n) || Number.isInteger(n)),
  ...(Number.isInteger(n) ? { int: z3.Int.val(n) } : {}),
  ...(Object.is(n, -0) ? { negZero: z3.Bool.val(true) } : {}),
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
  // `Boolean(x)`: whether `x` is truthy, as a condition reads it.
  if (e.text === "Boolean" && isLib(L.checker, e))
    return { kind: "builtin", name: "Boolean", call: ([v]) => ({ kind: "bool", term: truthy(L.u, v ?? UNDEFINED) }) }
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
  return optionally(L, obj, e, e.expression, (v) => member(L, v, e.name.text, e, t, L.checker.getTypeAtLocation(e)))
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
  const present = obj.value
  const inner = inChain(e) ? onBranch(L, L.u.z3.Not(isNullish(L.u, obj)), () => f(present)) : f(present)
  if (!inChain(e)) return inner
  return ite(L.u, isNullish(L.u, obj), { kind: "nullish", which: "undefined" }, inner, e)
}

/**
 * `obj.name`. Where the type checker has narrowed `obj` (`c.op === "set"`), the read takes the paths it leaves
 * (`narrowedField`). A field the object lacks reads as undefined where its type declares it (an optional field left out).
 */
export const member = (L: Lowering, obj: Val, name: string, at: ts.Node, objType?: ts.Type, type?: ts.Type): Val => {
  if (obj.kind === "record" && obj.entries !== undefined) return dictionaryRead(L, obj, { kind: "str", term: jsString(L.u.z3, name) }, at)
  if (obj.kind === "record") {
    const narrowed = objType === undefined || type === undefined ? undefined : narrowedField(L, obj, name, objType, type, at)
    if (narrowed !== undefined) return narrowed
    const v = obj.field(name)
    if (v !== undefined) return v
    const declared = objType === undefined ? undefined : L.checker.getPropertyOfType(L.checker.getNonNullableType(objType), name)
    if (declared !== undefined || obj.has?.(name) !== undefined) return UNDEFINED
    throw new Unsupported(`no field \`${name}\` the verifier can read`, at)
  }
  if (obj.kind === "array" && name === "length") return { kind: "int", origin: "count", term: obj.length }
  // UTF-16 code units, as JavaScript counts them: Z3's characters are code units (`jsString`).
  if (obj.kind === "str" && name === "length") return { kind: "int", origin: "count", term: obj.term.length() }
  throw new Unsupported(`member \`${name}\` of a ${obj.kind} is not modeled`, at)
}

const call = (L: Lowering, e: ts.CallExpression, env: Env): Val => {
  if (e.questionDotToken !== undefined) throw new Unsupported("an optional call is not modeled", e)
  const callee = e.expression
  if (ts.isPropertyAccessExpression(callee)) {
    const std = standard(L, callee)
    if (std !== undefined) return roundedQuotient(L, std, e, env) ?? callValue(L, std, e, env)
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
      if (r.kind === "str") return stringMethod(L, r, callee.name.text, e, env)
      if (r.kind === "record") return callValue(L, member(L, r, callee.name.text, callee), e, env)
      throw new Unsupported(`method \`${callee.name.text}\` of a ${r.kind} is not modeled`, e)
    })
  }
  return callValue(L, lowerExpr(L, callee, env), e, env)
}

/**
 * A function of JavaScript's own `Math`, `Number` or `Object` the model reads: what a double makes of it, exactly.
 * `floor`, `trunc` and `ceil` give an integral double, which the double holds, `-0` where JavaScript gives it; `max` and
 * `min` are `NaN` where an argument is, and tell `-0` from `0`; the `Number` checks read the class and the value; and
 * `Object.is` is SameValue.
 */
const standard = (L: Lowering, callee: ts.PropertyAccessExpression): Val | undefined => {
  const o = callee.expression
  if (!ts.isIdentifier(o) || !["Math", "Number", "Object", "Date"].includes(o.text) || !isLib(L.checker, o)) return undefined
  const z3 = L.u.z3
  const name = `${o.text}.${callee.name.text}`
  const one = (f: (v: Val, at: ts.Node) => Val): Val => ({
    kind: "builtin",
    name,
    call: ([v], at) => {
      if (v === undefined) throw new Unsupported(`\`${name}\` of no argument`, at)
      return f(v, at)
    },
  })
  type Num = Extract<Val, { kind: "num" }>
  const asNum = (v: Val, at: ts.Node): Num => {
    const n = asNumber(L, v)
    if (n === undefined) throw new Unsupported(`\`${name}\` of a ${v.kind}`, at)
    return n
  }
  /**
   * `f` of a fraction; and `toZero` where a fraction rounds to `-0`: between -1 and 0 for `ceil` and `trunc`, from -0.5
   * for `round`.
   */
  const rounded = (f: (r: Arith) => Arith, toZero?: (r: Arith) => Bool) =>
    one((v, at) => {
      if (v.kind === "int" && v.origin === "count") return v
      if (v.kind !== "num") throw new Unsupported(`\`${name}\` of a ${v.kind}`, at)
      const finite = v.cls.eq(NUM.finite)
      // A whole number rounds to itself; a fraction, by `f`.
      const r = z3.If(isWhole(L.u, v), intOf(L.u, v), f(v.real))
      return {
        kind: "num",
        cls: v.cls,
        real: z3.If(finite, z3.ToReal(r), v.real),
        whole: z3.If(finite, z3.Bool.val(true), isWhole(L.u, v)),
        int: z3.If(finite, r, intOf(L.u, v)),
        negZero:
          toZero === undefined
            ? isNegZero(L.u, v)
            : z3.Or(isNegZero(L.u, v), z3.And(finite, z3.Not(isWhole(L.u, v)), toZero(v.real), v.real.lt(0))),
      }
    })
  /** `Math.max` (`largest`) or `Math.min` of any number of numbers: `NaN` where one is; of two zeros, `0` and `-0`. */
  const extreme = (largest: boolean): Val => ({
    kind: "builtin",
    name,
    call: (args, at) => {
      const ns = args.map((v) => asNum(v, at))
      const nan = num(z3, Number.NaN) as Num
      const pair = (a: Num, b: Num): Num => {
        const picked = ite(L.u, compare(L.u, b, a, largest ? ">" : "<", at), b, a, at) as Num
        const zeros = z3.And(a.cls.eq(NUM.finite), b.cls.eq(NUM.finite), a.real.eq(0), b.real.eq(0))
        const sign = largest ? z3.And(isNegZero(L.u, a), isNegZero(L.u, b)) : z3.Or(isNegZero(L.u, a), isNegZero(L.u, b))
        const signed: Num = { ...picked, negZero: z3.If(zeros, sign, isNegZero(L.u, picked)) }
        return ite(L.u, z3.Or(a.cls.eq(NUM.nan), b.cls.eq(NUM.nan)), nan, signed, at) as Num
      }
      const [first, ...rest] = ns
      return first === undefined ? num(z3, largest ? -Infinity : Infinity) : rest.reduce(pair, first)
    },
  })
  // A `Number` check: of a number, what `f` says; of a value that may be missing, that it is there and a number `f`
  // holds of; of anything else (a string, a boolean), false, as JavaScript gives it.
  const check = (f: (v: Extract<Val, { kind: "num" }>) => Bool) => {
    const of = (v: Val, at: ts.Node): Bool => {
      if (v.kind === "num") return f(v)
      if (v.kind === "int" && v.origin === "count") return f(countAsNum(L.u, v.term))
      if (v.kind === "maybe") return v.value === undefined ? z3.Bool.val(false) : z3.And(z3.Not(isNullish(L.u, v)), of(v.value, at))
      if (v.kind === "opaque" || v.kind === "builtin" || v.kind === "fn" || v.kind === "comp")
        throw new Unsupported(`\`${name}\` of a ${v.kind} is not modeled`, at)
      return z3.Bool.val(false)
    }
    return one((v, at) => bool(of(v, at)))
  }
  const whole = (v: Extract<Val, { kind: "num" }>) => z3.And(v.cls.eq(NUM.finite), isWhole(L.u, v))
  switch (name) {
    case "Math.floor":
      return rounded((r) => z3.ToInt(r))
    case "Math.ceil":
      return rounded(
        (r) => z3.ToInt(r.neg()).neg(),
        (r) => r.gt(-1),
      )
    case "Math.trunc":
      return rounded(
        (r) => z3.If(r.ge(0), z3.ToInt(r), z3.ToInt(r.neg()).neg()),
        (r) => r.gt(-1),
      )
    case "Math.round":
      // Half way rounds up, toward +Infinity: 2.5 to 3, -2.5 to -2, and -0.5 to -0.
      return rounded(
        (r) => z3.ToInt(r.add(z3.Real.val("1/2"))),
        (r) => r.ge(z3.Real.val("-1/2")),
      )
    case "Math.max":
      return extreme(true)
    case "Math.min":
      return extreme(false)
    case "Math.abs":
      return one((v, at) => {
        if (v.kind === "int" && v.origin === "count") return v
        const n = asNum(v, at)
        const negative = n.real.lt(0)
        return {
          kind: "num",
          cls: z3.If(n.cls.eq(NUM.negInf), z3.Int.val(NUM.posInf), n.cls),
          real: z3.If(negative, n.real.neg(), n.real),
          ...(n.whole === undefined ? {} : { whole: n.whole }),
          ...(n.int === undefined ? {} : { int: z3.If(n.int.lt(0), n.int.neg(), n.int) }),
        }
      })
    case "Object.is":
      return {
        kind: "builtin",
        name,
        call: (args, at) => {
          const [a, b] = args
          if (args.length !== 2 || a === undefined || b === undefined) throw new Unsupported("`Object.is` of other than two values", at)
          const na = asNumber(L, a)
          const nb = asNumber(L, b)
          if (na !== undefined && nb !== undefined) return bool(sameValue(L.u, na, nb))
          // Of two values neither a number nor an object, SameValue is `===`.
          const plain = (v: Val) =>
            v.kind === "str" || v.kind === "bool" || v.kind === "nullish" || (v.kind === "int" && v.origin === "bigint")
          if (plain(a) && plain(b)) return bool(strictEq(L.u, a, b, at))
          throw new Unsupported(
            "`Object.is` is modeled of two numbers, or of two values neither of which is a number or an object: an object's identity is not",
            at,
          )
        },
      }
    case "Date.parse":
      // A function of its string the verifier does not compute: the same string, the same time, which is `NaN` or a
      // whole number of milliseconds within `MAX_TIME` of 1970. A counterexample leans on that and on nothing more.
      return one((given, at) => {
        const arg = ts.isCallExpression(at) ? at.arguments[0] : undefined
        const v = arg === undefined ? given : shown(L, given, arg)
        if (v.kind !== "str") throw new Unsupported(`\`Date.parse\` of a ${v.kind}: of a string it is read`, at)
        const f = parsing(L.u)
        const ms = f.ms.call(v.term) as Arith
        const cls = f.cls.call(v.term) as Arith
        // What every string's time is, said of this one: `NaN`, or a whole number of milliseconds within `MAX_TIME`.
        L.u.assume(z3.And(z3.Or(cls.eq(NUM.nan), cls.eq(NUM.finite)), ms.le(MAX_TIME), ms.ge(-MAX_TIME)), L.u.openBounds())
        L.u.opaqueCalls.add("Date.parse")
        L.u.notes.add(
          "`Date.parse` is read as some function of its string: the same string gives the same time, `NaN` or a whole number of milliseconds; which time, the verifier does not compute.",
        )
        return { kind: "num", cls, real: z3.ToReal(ms), whole: z3.Bool.val(true), int: ms }
      })
    case "Object.keys":
      return one((v, at) => ownOf(L, v, name, at).keys)
    case "Object.values":
      return one((v, at) => ownOf(L, v, name, at).values)
    case "Object.entries":
      return one((v, at) => {
        const { keys, values } = ownOf(L, v, name, at)
        if (keys.kind !== "array" || values.kind !== "array") throw new Unsupported(`\`${name}\` of a value whose keys are not a list`, at)
        return {
          kind: "array",
          length: keys.length,
          elem: memoElems((i) => tupleOf(L, [() => keys.elem(i), () => values.elem(i)], () => UNDEFINED, at)),
          ...(keys.maxSize === undefined ? {} : { maxSize: keys.maxSize }),
          ...(keys.size === undefined ? {} : { size: keys.size }),
        }
      })
    case "Object.hasOwn":
      return {
        kind: "builtin",
        name,
        call: (args, at) => {
          const [o, key] = args
          const d = o?.kind === "maybe" ? o.value : o
          if (args.length !== 2 || d?.kind !== "record" || d.entries === undefined || key === undefined)
            throw new Unsupported("`Object.hasOwn` is read of a record keyed by any string (`Record<string, T>`) and a key", at)
          return bool(d.entries(key, at).found)
        },
      }
    case "Number.isInteger":
      return check(whole)
    case "Number.isSafeInteger":
      return check((v) => z3.And(whole(v), v.real.le(TWO_53 - 1), v.real.ge(1 - TWO_53)))
    case "Number.isFinite":
      return check((v) => v.cls.eq(NUM.finite))
    case "Number.isNaN":
      return check((v) => v.cls.eq(NUM.nan))
    default:
      return undefined
  }
}

const ROUNDING = new Set(["Math.floor", "Math.ceil", "Math.trunc", "Math.round"])

/**
 * `Math.floor(a / b)`, and `ceil`, `trunc` and `round`, of two whole numbers: the quotient's real value rounded, which
 * is what JavaScript gives while `a` is within 2^52 of 0. A quotient that is not whole is no exact double, but it lies
 * at least `1 / |b|` from a whole number and half that from a half, more than the double it rounds to strays from it,
 * so rounding the double and rounding the real agree. What that needs of `a` and `b` is an obligation, as an exact
 * operation's is. Undefined where the argument is no quotient of two numbers, which reads as the call does.
 */
const roundedQuotient = (L: Lowering, f: Val, e: ts.CallExpression, env: Env): Val | undefined => {
  const quotient = e.arguments.length === 1 ? unwrapParens(e.arguments[0]!) : undefined
  if (f.kind !== "builtin" || !ROUNDING.has(f.name) || quotient === undefined || !ts.isBinaryExpression(quotient)) return undefined
  if (quotient.operatorToken.kind !== K.SlashToken) return undefined
  const numberTyped = (x: ts.Expression) => (L.checker.getTypeAtLocation(x).flags & ts.TypeFlags.NumberLike) !== 0
  if (!numberTyped(quotient.left) || !numberTyped(quotient.right)) return undefined
  const z3 = L.u.z3
  const a = asNumber(L, lowerExpr(L, quotient.left, env))
  const b = asNumber(L, lowerExpr(L, quotient.right, env))
  if (a === undefined || b === undefined) throw new Unsupported("a quotient of values that are no numbers", quotient)
  const wholeFinite = (v: Extract<Val, { kind: "num" }>) => z3.And(v.cls.eq(NUM.finite), isWhole(L.u, v))
  const goal = z3.And(wholeFinite(a), wholeFinite(b), z3.Not(b.real.eq(0)), a.real.le(TWO_52), a.real.ge(-TWO_52))
  if (L.mode === "spec") L.exact?.push(z3.Implies(L.guard, goal))
  else {
    const where = locate(quotient)
    L.obligations.push({
      key: `exact@${where}#here`,
      kind: "exact",
      text: e.getText(),
      at: where,
      phase: "here",
      cond: L.guard,
      goal,
      hints: L.hints.length,
    })
  }
  const r = a.real.div(b.real)
  const negative = (v: Extract<Val, { kind: "num" }>) => z3.Or(v.real.lt(0), isNegZero(L.u, v))
  const q: Val = {
    kind: "num",
    cls: z3.Int.val(NUM.finite),
    real: r,
    whole: z3.IsInt(r),
    negZero: z3.And(r.eq(0), z3.Not(negative(a).eq(negative(b)))),
  }
  return f.call([q], e)
}

/** `Date.parse` of a universe, one function of the string for its class and one for its milliseconds. */
const PARSING = new WeakMap<Universe, { readonly cls: FuncDecl; readonly ms: FuncDecl }>()
const parsing = (u: Universe): { readonly cls: FuncDecl; readonly ms: FuncDecl } => {
  let f = PARSING.get(u)
  if (f === undefined) {
    const z3 = u.z3
    f = {
      cls: z3.Function.declare("Date.parse~cls", z3.String.sort(), z3.Int.sort()),
      ms: z3.Function.declare("Date.parse~ms", z3.String.sort(), z3.Int.sort()),
    }
    PARSING.set(u, f)
  }
  return f
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
const assumedFn = (L: Lowering, a: AssumedFn): Val => ({
  kind: "builtin",
  name: a.name,
  call: (args, at) => assumedCall(L, a, args, at),
  ...(a.pure ? {} : { effects: () => `\`${a.name}\` is declared \`pure: false\`` }),
})

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
    // Pure where the functions it calls are: each passed here must change nothing.
    for (const k of p.calls) {
      const why = effectsOfValue(L, args[k])
      if (why !== undefined)
        throw new Unsupported(
          `\`${a.name}\` is pure where the functions it is given are, and \`${at.arguments[k]?.getText() ?? k}\` may change something: ${why}`,
          at,
        )
    }
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
  const ids = boundArgs(L, a, args, at).map(identity)
  const key =
    a.pure && ids.every((i) => i !== undefined)
      ? `assumed:${a.views[0]!.where}(${ids.join(",")})[${indices.map(termId).join(",")}]`
      : undefined
  const known = key === undefined ? undefined : L.opaque.get(key)
  if (known !== undefined) return known
  const result = symbolicOf(
    L,
    checker.getTypeAtLocation(at),
    [u.given(a.name.replace(/\s.*/, ""), u.openBounds().length === 0 ? L.guard : undefined)],
    indices,
    at,
  )
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

/**
 * The index `v` names, as an integer, and where it names one: a count always does, a `number` where it is a finite
 * whole number (`-0` is 0). Elsewhere `term` is some integer, and `whole` false.
 */
export const indexOf = (L: Lowering, v: Val, at: ts.Node): { readonly term: Arith; readonly whole: Bool } => {
  const z3 = L.u.z3
  if (v.kind === "int" && v.origin === "count") return { term: v.term, whole: z3.Bool.val(true) }
  if (v.kind === "num") return { term: intOf(L.u, v), whole: z3.And(v.cls.eq(NUM.finite), isWhole(L.u, v)) }
  throw new Unsupported(`an index that is a ${v.kind}`, at)
}

/**
 * `v`, an argument, where the type checker has shown it neither `null` nor `undefined` (`out === undefined ||
 * s.endsWith(out)`): what it holds, since no run reaches here with it missing.
 */
const shown = (L: Lowering, v: Val, e: ts.Expression): Val => {
  if (v.kind !== "maybe" || v.value === undefined) return v
  const t = L.checker.getTypeAtLocation(e)
  const parts = t.isUnion() ? t.types : [t]
  return parts.some((m) => m.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined | ts.TypeFlags.Void)) ? v : v.value
}

/**
 * The integer JavaScript makes of a position (`ToIntegerOrInfinity`): a count as it is, a `number` truncated toward 0,
 * NaN as 0, and either infinity said apart, where `t` is 0.
 */
const positionOf = (
  L: Lowering,
  v: Val,
  what: string,
  at: ts.Node,
): { readonly t: Arith; readonly posInf: Bool; readonly negInf: Bool } => {
  const z3 = L.u.z3
  if (v.kind === "int" && v.origin === "count") return { t: v.term, posInf: z3.Bool.val(false), negInf: z3.Bool.val(false) }
  if (v.kind !== "num") throw new Unsupported(`${what} of a ${v.kind}`, at)
  const truncated = z3.If(isWhole(L.u, v), intOf(L.u, v), z3.If(v.real.ge(0), z3.ToInt(v.real), z3.ToInt(v.real.neg()).neg()))
  return { t: z3.If(v.cls.eq(NUM.finite), truncated, z3.Int.val(0)), posInf: v.cls.eq(NUM.posInf), negInf: v.cls.eq(NUM.negInf) }
}

/**
 * A position `.slice` takes in something `length` long (`v`, or `given` where it is missing or `undefined`): made an
 * integer, counted from the end where negative, then kept between 0 and the length.
 */
const relativePosition = (L: Lowering, length: Arith, v: Val | undefined, given: Arith, at: ts.Node): Arith => {
  const z3 = L.u.z3
  if (v === undefined || (v.kind === "nullish" && v.which === "undefined")) return given
  const p = positionOf(L, v, "`.slice`", at)
  const counted = z3.If(p.t.lt(0), length.add(p.t), p.t)
  const kept = z3.If(counted.lt(0), z3.Int.val(0), z3.If(counted.gt(length), length, counted))
  return z3.If(p.negInf, z3.Int.val(0), z3.If(p.posInf, length, kept))
}

/**
 * The element `.at(v)` names of something `length` long, as JavaScript finds it: `v` made an integer (NaN is 0, a
 * fraction truncated toward 0), a negative one counted from the end; missing outside, at either infinity among them.
 */
const atPosition = (L: Lowering, length: Arith, v: Val, at: ts.Node): { readonly index: Arith; readonly isUndefined: Bool } => {
  const z3 = L.u.z3
  const p = positionOf(L, v, "`.at`", at)
  const index = z3.If(p.t.lt(0), length.add(p.t), p.t)
  return { index, isUndefined: z3.Or(p.posInf, p.negInf, index.lt(0), index.ge(length)) }
}

/** The element `.at(v)` names in `arr` (`atPosition`). */
export const atIndex = (
  L: Lowering,
  arr: Extract<Val, { kind: "array" }>,
  v: Val,
  at: ts.Node,
): { readonly index: Arith; readonly isUndefined: Bool } => atPosition(L, arr.length, v, at)

/**
 * A string's method, on its UTF-16 code units, as Z3 holds them (`jsString`): `startsWith`, `endsWith` and `includes`
 * of one string; `indexOf` of one, -1 where it is not there and 0 for `""`; `charAt` and `at` at a position, `""` and
 * `undefined` outside it; and `slice`, its positions counted from the end where negative, and kept inside.
 */
const stringMethod = (L: Lowering, s: Extract<Val, { kind: "str" }>, name: string, e: ts.CallExpression, env: Env): Val => {
  const z3 = L.u.z3
  const args = e.arguments.map((a) => shown(L, lowerExpr(L, a, env), a))
  const taking = (n: number, said: string): void => {
    if (e.arguments.length !== n) throw new Unsupported(`\`.${name}\` is modeled with ${said}`, e)
  }
  const text = (k: number): Extract<Val, { kind: "str" }>["term"] => {
    const v = args[k]!
    if (v.kind !== "str") throw new Unsupported(`\`.${name}\` of a ${v.kind}`, e.arguments[k])
    return v.term
  }
  const length = s.term.length()
  const str = (term: unknown): Val => ({ kind: "str", term: term as Extract<Val, { kind: "str" }>["term"] })
  switch (name) {
    case "startsWith":
      taking(1, "one argument, the prefix")
      return bool(text(0).prefixOf(s.term))
    case "endsWith":
      taking(1, "one argument, the suffix")
      return bool(text(0).suffixOf(s.term))
    case "includes":
      taking(1, "one argument, what to find")
      return bool(s.term.contains(text(0)))
    case "indexOf":
      taking(1, "one argument, what to find")
      return countAsNum(L.u, s.term.indexOf(text(0), 0))
    case "charAt": {
      taking(1, "one argument, the position")
      const p = positionOf(L, args[0]!, "`.charAt`", e.arguments[0]!)
      return str(z3.If(z3.Or(p.posInf, p.negInf), jsString(z3, ""), s.term.at(p.t)))
    }
    case "at": {
      taking(1, "one argument, the position")
      const { index, isUndefined } = atPosition(L, length, args[0]!, e.arguments[0]!)
      return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined, value: str(s.term.at(index)) }
    }
    case "slice": {
      if (args.length > 2) throw new Unsupported("`.slice` takes a start and an end", e)
      const from = relativePosition(L, length, args[0], z3.Int.val(0), e.arguments[0] ?? e)
      const to = relativePosition(L, length, args[1], length, e.arguments[1] ?? e)
      return str(s.term.extract(from, z3.If(to.gt(from), to.sub(from), z3.Int.val(0))))
    }
    case "trim":
    case "trimStart":
    case "trimEnd":
      taking(0, "no argument")
      return str(trimmed(L, s.term, name === "trim" || name === "trimStart", name === "trim" || name === "trimEnd"))
    default:
      throw new Unsupported(
        `method \`${name}\` of a string is not modeled: \`startsWith\`, \`endsWith\`, \`includes\`, \`indexOf\`, \`charAt\`, \`at\`, \`slice\` and \`trim\` are`,
        e,
      )
  }
}

/** The code units JavaScript's `trim` takes off: its white space and its line terminators. */
const WHITE = ["\t", "\n", "\v", "\f", "\r", " ", "\u00a0", "\u1680", "\u2028", "\u2029", "\u202f", "\u205f", "\u3000", "\ufeff"]

/**
 * `s` with its white space taken off its start (`start`) and its end (`end`), as `trim`, `trimStart` and `trimEnd` take it:
 * the part `t` of `s = p + t + q` where `p` and `q` are white space alone and `t` starts and ends with a code unit that
 * is not, or is empty. That part is one, whatever `s` is.
 */
const trimmed = (
  L: Lowering,
  s: Extract<Val, { kind: "str" }>["term"],
  start: boolean,
  end: boolean,
): Extract<Val, { kind: "str" }>["term"] => {
  const { u } = L
  const z3 = u.z3
  const white = z3.Union(z3.Range(jsString(z3, "\u2000"), jsString(z3, "\u200a")), ...WHITE.map((c) => z3.Re.toRe(jsString(z3, c))))
  const any = z3.AllChar(z3.Re.sort(z3.String.sort()))
  const other = z3.Diff(any, white)
  const indices = u.openBounds()
  const part = (what: string) => u.leaf([u.fresh(what), "$"], "str", indices) as never as Extract<Val, { kind: "str" }>["term"]
  const t = part("trimmed")
  const p = start ? part("trim.start") : jsString(z3, "")
  const q = end ? part("trim.end") : jsString(z3, "")
  const body =
    start && end
      ? z3.Option(z3.ReConcat(other, z3.Option(z3.ReConcat(z3.Star(any), other))))
      : start
        ? z3.Option(z3.ReConcat(other, z3.Star(any)))
        : z3.Option(z3.ReConcat(z3.Star(any), other))
  u.assume(z3.And(s.eq(p.concat(t).concat(q)), z3.InRe(p, z3.Star(white)), z3.InRe(q, z3.Star(white)), z3.InRe(t, body)), indices)
  return t
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
  /** A callback's value at each index (`.map`, `.flatMap`), each read once. */
  const callback = (): ((i: Arith) => Val) => {
    if (e.arguments.length !== 1) throw new Unsupported(`\`.${name}\` with a \`this\` argument is not modeled`, e)
    const f = lowerExpr(L, arg(0), env)
    if (f.kind !== "fn") throw new Unsupported(`\`.${name}\` of a ${f.kind}: a function the code writes is read`, e)
    if (f.node.parameters.length > 2) throw new Unsupported(`\`.${name}\` with a callback reading the array is not modeled`, f.node)
    return memoElems((i) => lowerCall(L, f.node, f.env, [arr.elem(i), { kind: "int", origin: "count", term: i }], e))
  }
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
    const r = onBranch(L, op === K.AmpersandAmpersandToken ? truthy(u, l) : z3.Not(truthy(u, l)), () => lowerExpr(L, e.right, env))
    if (l.kind === "bool" && r.kind === "bool")
      return bool(op === K.AmpersandAmpersandToken ? z3.And(l.term, r.term) : z3.Or(l.term, r.term))
    return op === K.AmpersandAmpersandToken ? ite(u, truthy(u, l), r, l, e) : ite(u, truthy(u, l), l, r, e)
  }
  if (op === K.QuestionQuestionToken) {
    const l = lowerExpr(L, e.left, env)
    // A function the code writes, standing where one it is given may be missing (`closeoutOf ?? (() => undefined)`).
    const fns = l.kind === "maybe" && l.value?.kind === "builtin"
    return nullishOr(
      u,
      l,
      () =>
        onBranch(L, l.kind === "maybe" ? isNullish(u, l) : z3.Bool.val(true), () => {
          const r = lowerExpr(L, e.right, env)
          return fns ? callable(L, r) : r
        }),
      e,
    )
  }
  if (op === K.InKeyword) return keyIn(L, e, env)
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
    case K.BarToken:
    case K.AmpersandToken:
    case K.CaretToken:
    case K.LessThanLessThanToken:
    case K.GreaterThanGreaterThanToken:
    case K.GreaterThanGreaterThanGreaterThanToken:
      return arithmetic(L, op, l, r, e)
    case K.AsteriskAsteriskToken: {
      // Of two literals, what JavaScript computes (`2 ** 32`); of anything else, a power the solver does not reason with.
      const c = constantOf(e)
      if (c === undefined)
        throw new Unsupported(
          "`**` is read of two literals (`2 ** 32`): a power of a value the code computes is not modeled",
          e.operatorToken,
        )
      return typeof c === "bigint" ? { kind: "int", origin: "bigint", term: z3.Int.val(c) } : num(z3, c)
    }
    default:
      throw new Unsupported(
        `operator ${ts.tokenToString(op)} is not modeled${op === K.EqualsEqualsToken || op === K.ExclamationEqualsToken ? `: write \`${op === K.EqualsEqualsToken ? "===" : "!=="}\` (and \`x === null || x === undefined\` for a nullish check)` : ""}`,
        e.operatorToken,
      )
  }
}

/** What `Object.prototype` holds, which a plain object finds under any key it does not hold itself. */
const PROTO = [
  "constructor",
  "hasOwnProperty",
  "isPrototypeOf",
  "propertyIsEnumerable",
  "toLocaleString",
  "toString",
  "valueOf",
  "__proto__",
  "__defineGetter__",
  "__defineSetter__",
  "__lookupGetter__",
  "__lookupSetter__",
]

/** Whether `key` names a member of `Object.prototype`. */
const protoKey = (L: Lowering, key: Val, at: ts.Node): Bool =>
  L.u.z3.Or(...PROTO.map((n) => strictEq(L.u, key, { kind: "str", term: jsString(L.u.z3, n) }, at)))

/**
 * `obj[key]` of a dictionary (`Record<string, T>`), read where its type says it may be missing
 * (`noUncheckedIndexedAccess`): the value of the key's entry, `undefined` where it has none. Where it has none and the key
 * is a name `Object.prototype` holds (`"constructor"`, `"toString"`), JavaScript finds that member, a function, which is
 * not modeled: that the key is the dictionary's own or none of those is an obligation, listed under `keys read:`.
 */
const dictionaryRead = (L: Lowering, d: Extract<Val, { kind: "record" }>, key: Val, at: ts.Node): Val => {
  const z3 = L.u.z3
  // Its type says what the entry is, read so (`noUncheckedIndexedAccess`) or narrowed by a check the code made; with
  // neither, it says the key is there, which may be false.
  const t = L.checker.getTypeAtLocation(at)
  if (L.unchecked !== true && !(t.isUnion() ? t.types : [t]).some((m) => m.flags & ts.TypeFlags.Undefined))
    throw new Unsupported(
      `\`${at.getText()}\` on a record keyed by any string is read where its type says the key is there, which may be false: turn on \`noUncheckedIndexedAccess\``,
      at,
    )
  if (key.kind !== "str" && !(key.kind === "maybe" && key.value?.kind === "str"))
    throw new Unsupported(`a key of a record that is a ${key.kind}: of a string it is read`, at)
  const { found, value } = d.entries!(key, at)
  const literal = ts.isPropertyAccessExpression(at) || (ts.isElementAccessExpression(at) && ts.isStringLiteralLike(at.argumentExpression))
  const named = ts.isPropertyAccessExpression(at)
    ? at.name.text
    : ts.isElementAccessExpression(at) && ts.isStringLiteralLike(at.argumentExpression)
      ? at.argumentExpression.text
      : undefined
  if (!(literal && named !== undefined && !PROTO.includes(named))) {
    const goal = z3.Or(found, z3.Not(protoKey(L, key, at)))
    if (L.mode === "spec" && L.defined !== undefined) L.defined.push(z3.Implies(L.guard, goal))
    else {
      const where = locate(at)
      L.obligations.push({
        key: `key@${where}#here`,
        kind: "key",
        text: at.getText(),
        at: where,
        phase: "here",
        cond: L.guard,
        goal,
        hints: L.hints.length,
      })
    }
  }
  if (value.kind === "maybe")
    return { kind: "maybe", isNull: z3.And(found, value.isNull), isUndefined: z3.Or(z3.Not(found), value.isUndefined), value: value.value }
  return { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(found), value }
}

/**
 * `"key" in obj`, of a key written as a string: of an object the code built, whether it holds the key (`has`); of one it
 * is given, whether its type requires the key, every value taken to hold the keys its type declares and no other, as
 * TypeScript's narrowing by `in` takes it; of a union, which member it is (`split`). A key the type makes optional is
 * refused: an absent key and one holding `undefined` read alike.
 */
const keyIn = (L: Lowering, e: ts.BinaryExpression, env: Env): Val => {
  const z3 = L.u.z3
  const key = unwrapParens(e.left)
  if (!ts.isStringLiteral(key) && !ts.isNoSubstitutionTemplateLiteral(key)) {
    // A key the code computes, of a dictionary: an entry it has, or a name `Object.prototype` holds.
    const target = lowerExpr(L, e.right, env)
    const d = target.kind === "maybe" ? target.value : target
    if (d?.kind === "record" && d.entries !== undefined) {
      const k = shown(L, lowerExpr(L, e.left, env), e.left)
      if (k.kind !== "str") throw new Unsupported(`a key of a record that is a ${k.kind}: of a string it is read`, e.left)
      return bool(z3.Or(d.entries(k, e).found, protoKey(L, k, e)))
    }
    throw new Unsupported('`in` is read with a key written as a string (`"refused" in moved`), or of a dictionary', e.left)
  }
  const name = key.text
  const holds = (v: Val): Bool => {
    if (v.kind === "maybe" && v.value !== undefined) return holds(v.value)
    if (v.kind === "array") {
      if (name === "length") return z3.Bool.val(true)
      throw new Unsupported(`\`${JSON.stringify(name)} in\` an array is not modeled`, e)
    }
    if (v.kind !== "record") throw new Unsupported(`\`in\` of a ${v.kind} is not modeled`, e)
    // A dictionary holds a key it has an entry for, and every name `Object.prototype` holds.
    if (v.entries !== undefined) {
      const key: Val = { kind: "str", term: jsString(z3, name) }
      return z3.Or(v.entries(key, e).found, protoKey(L, key, e))
    }
    const built = v.has?.(name)
    if (built !== undefined) return built
    if (v.split !== undefined) return z3.If(v.split.cond, holds(v.split.a), holds(v.split.b))
    const declared = v.declares?.(name)
    if (declared === undefined)
      throw new Unsupported(
        v.declares === undefined
          ? `\`in\` of a value whose keys the verifier does not know`
          : `\`${JSON.stringify(name)} in\` a value whose type makes \`${name}\` optional is not modeled: an absent key and one holding \`undefined\` read alike; compare the field with \`undefined\``,
        e,
      )
    L.u.notes.add(
      "`in` reads a value the code is given by its type: it holds the keys its type requires, and no key its type does not declare.",
    )
    return z3.Bool.val(declared)
  }
  return bool(holds(lowerExpr(L, e.right, env)))
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
  if (BITWISE.has(op)) return bitwise(L, op, l, r, e)
  if (l.kind === "int" && r.kind === "int" && l.origin === "bigint" && r.origin === "bigint") {
    if (op === K.PlusToken) return { ...l, term: l.term.add(r.term) }
    if (op === K.MinusToken) return { ...l, term: l.term.sub(r.term) }
    if (op === K.AsteriskToken) return { ...l, term: l.term.mul(r.term) }
    if (op === K.SlashToken || op === K.PercentToken) return divided(L, op, l, r, e)
    throw new Unsupported(`bigint \`${ts.tokenToString(op)}\` is not modeled`, e.operatorToken)
  }
  const a = asNumber(L, l)
  const b = asNumber(L, r)
  if (a !== undefined && b !== undefined) {
    if (op === K.PercentToken) throw new Unsupported("`%` on `number` is not modeled: `bigint` where the values are whole", e.operatorToken)
    // A count plus or minus a count or a small whole literal (`b.length + c.length`, `i - 1`) is exact whatever the
    // input, a whole number below 2^34: nothing to oblige.
    const small = (x: ts.Expression, v: Val) =>
      (v.kind === "int" && v.origin === "count") || (ts.isNumericLiteral(x) && /^\d{1,9}$/.test(x.text))
    const known = (op === K.PlusToken || op === K.MinusToken) && small(e.left, l) && small(e.right, r)
    if (L.mode === "spec") {
      // Spec code has no runs to hold an obligation: elsewhere than a law, a `requires` or proof code it reads only
      // what is exact whatever the input.
      if (known) return exactly(L, op, a, b, e, true)
      // A law, a `requires` and proof code say where it is exact as part of what they say (`exactSpec`).
      if (L.exact !== undefined) return exactly(L, op, a, b, e)
      throw new Unsupported(
        "here (a declaration's laws, a guessed invariant) arithmetic on `number` is read only on counts and small whole literals (`i - 1`): its rounding is not modeled. Compute the value in the program, or use `bigint`",
        e.operatorToken,
      )
    }
    return exactly(L, op, a, b, e, known)
  }
  if (op === K.PlusToken && l.kind === "str" && r.kind === "str") return { kind: "str", term: l.term.concat(r.term) }
  throw new Unsupported(`${ts.tokenToString(op)} between a ${l.kind} and a ${r.kind} is not modeled`, e)
}

/** `v` as a `number`: itself, or a count (a length, an index), which a double holds exactly. */
export const asNumber = (L: Lowering, v: Val): Extract<Val, { kind: "num" }> | undefined =>
  v.kind === "num" ? v : v.kind === "int" && v.origin === "count" ? countAsNum(L.u, v.term) : undefined

const TWO_53 = 9007199254740992
const TWO_52 = 4503599627370496
const TWO_32 = 4294967296
const TWO_31 = 2147483648

const BITWISE: ReadonlySet<ts.SyntaxKind> = new Set([
  K.BarToken,
  K.AmpersandToken,
  K.CaretToken,
  K.LessThanLessThanToken,
  K.GreaterThanGreaterThanToken,
  K.GreaterThanGreaterThanGreaterThanToken,
])

/** The number a literal, a negated one, or a `**` of two of them is, as JavaScript computes it; else `undefined`. */
const constantOf = (e: ts.Expression): number | bigint | undefined => {
  const x = unwrapParens(e)
  if (ts.isNumericLiteral(x)) return Number(x.text)
  if (ts.isBigIntLiteral(x)) return BigInt(x.text.slice(0, -1))
  if (ts.isPrefixUnaryExpression(x) && x.operator === K.MinusToken) {
    const c = constantOf(x.operand)
    return c === undefined ? undefined : -c
  }
  if (ts.isBinaryExpression(x) && x.operatorToken.kind === K.AsteriskAsteriskToken) {
    const a = constantOf(x.left)
    const b = constantOf(x.right)
    if (typeof a === "number" && typeof b === "number") return a ** b
    if (typeof a === "bigint" && typeof b === "bigint" && b >= 0n) return a ** b
  }
  return undefined
}

/** Methods that give a new array, which nothing else holds. */
const FRESH = new Set(["slice", "map", "filter", "flatMap", "concat", "toReversed", "toSorted"])

/** Whether the receiver of the method `e` calls is an array made right there: a literal, or one a method gave anew. */
const fresh = (e: ts.CallExpression): boolean => {
  if (!ts.isPropertyAccessExpression(e.expression)) return false
  const r = unwrapParens(e.expression.expression)
  return (
    ts.isArrayLiteralExpression(r) ||
    (ts.isCallExpression(r) && ts.isPropertyAccessExpression(r.expression) && FRESH.has(r.expression.name.text))
  )
}

const unwrapParens = (e: ts.Expression): ts.Expression => (ts.isParenthesizedExpression(e) ? unwrapParens(e.expression) : e)

/** The results of `x >> 31` (a count of 31 mod 32): a sign mask, 0 or -1 by construction. */
const MASKS = new WeakSet<Arith>()

/** Whether `v` is a sign mask, made by `>> 31`. */
const isMask = (v: Val): boolean => v.kind === "num" && v.int !== undefined && MASKS.has(v.int)

/** A whole number the code made as an integer (a bitwise result): finite, never `-0`. */
const integral = (L: Lowering, t: Arith): Val => ({
  kind: "num",
  cls: L.u.z3.Int.val(NUM.finite),
  real: L.u.z3.ToReal(t),
  whole: L.u.z3.Bool.val(true),
  int: t,
})

/** The first step of `ToInt32` and `ToUint32`: 0 of `NaN`, the infinities and the zeros; else truncated toward 0. */
const truncatedOf = (L: Lowering, v: Extract<Val, { kind: "num" }>): Arith => {
  const z3 = L.u.z3
  const t = z3.If(isWhole(L.u, v), intOf(L.u, v), z3.If(v.real.ge(0), z3.ToInt(v.real), z3.ToInt(v.real.neg()).neg()))
  return z3.If(v.cls.eq(NUM.finite), t, z3.Int.val(0))
}

/** `t` as a signed 32-bit integer (`ToInt32`): `t` mod 2^32, from -2^31. */
const int32 = (L: Lowering, t: Arith): Arith => {
  const z3 = L.u.z3
  const m = t.mod(TWO_32)
  return z3.If(m.ge(TWO_31), m.sub(TWO_32), m)
}

/**
 * A bitwise operator on two numbers, as JavaScript computes it: each operand made a 32-bit integer (`ToInt32`, and
 * `ToUint32` for `>>>`), the result one too, so exact and never `-0`. Shifts are arithmetic, by 2^(count mod 32); `|`,
 * `&` and `^` go through 32-bit vectors, but for `x | 0`, `x ^ 0` and `x & (2^k - 1)`, which are arithmetic too.
 */
const bitwise = (L: Lowering, op: ts.SyntaxKind, l: Val, r: Val, e: ts.BinaryExpression): Val => {
  const z3 = L.u.z3
  const a = asNumber(L, l)
  const b = asNumber(L, r)
  if (a === undefined || b === undefined)
    throw new Unsupported(
      `\`${ts.tokenToString(op)}\` between a ${l.kind} and a ${r.kind} is not modeled: bitwise operators are read on \`number\``,
      e.operatorToken,
    )
  const x = truncatedOf(L, a)
  const y = truncatedOf(L, b)
  const k = constantOf(e.right)
  const literal = typeof k === "number" && Number.isInteger(k) ? k : undefined
  const x32 = int32(L, x)
  const y32 = int32(L, y)
  const vector = (
    f: (p: ReturnType<typeof z3.Int2BV<32>>, q: ReturnType<typeof z3.Int2BV<32>>) => ReturnType<typeof z3.Int2BV<32>>,
  ): Arith => {
    L.u.vectors = true
    return z3.BV2Int(f(z3.Int2BV(x, 32), z3.Int2BV(y, 32)), true)
  }
  // Of 0 or -1, a sign mask (`x >> 31`), each of `|`, `&` and `^` is arithmetic: the vectors are left to other operands.
  const ones = z3.Int.val(-1)
  const zero = z3.Int.val(0)
  // An operand that is a sign mask by construction leaves no other case, and no vectors at all.
  const masked = isMask(r) ? { mask: y32, other: x32 } : isMask(l) ? { mask: x32, other: y32 } : undefined
  if (masked !== undefined && (op === K.BarToken || op === K.AmpersandToken || op === K.CaretToken)) {
    const { mask, other } = masked
    const isZero = mask.eq(zero)
    return integral(
      L,
      op === K.BarToken
        ? z3.If(isZero, other, ones)
        : op === K.AmpersandToken
          ? z3.If(isZero, zero, other)
          : z3.If(isZero, other, other.neg().sub(1)),
    )
  }
  // 2^(count mod 32): a constant of a literal count, else one of the 32.
  const power = (): Arith => {
    if (literal !== undefined) return z3.Int.val(2 ** (((literal % 32) + 32) % 32))
    const c = y.mod(32)
    let p: Arith = z3.Int.val(2 ** 31)
    for (let j = 30; j >= 0; j--) p = z3.If(c.eq(j), z3.Int.val(2 ** j), p)
    return p
  }
  switch (op) {
    case K.BarToken:
      return integral(
        L,
        literal === 0
          ? x32
          : z3.If(
              z3.Or(x32.eq(ones), y32.eq(ones)),
              ones,
              z3.If(
                x32.eq(zero),
                y32,
                z3.If(
                  y32.eq(zero),
                  x32,
                  vector((p, q) => p.or(q)),
                ),
              ),
            ),
      )
    case K.CaretToken:
      return integral(
        L,
        literal === 0
          ? x32
          : z3.If(
              x32.eq(zero),
              y32,
              z3.If(
                y32.eq(zero),
                x32,
                z3.If(
                  x32.eq(ones),
                  y32.neg().sub(1),
                  z3.If(
                    y32.eq(ones),
                    x32.neg().sub(1),
                    vector((p, q) => p.xor(q)),
                  ),
                ),
              ),
            ),
      )
    case K.AmpersandToken: {
      // A mask of the low bits keeps the 32-bit value's remainder: never negative, below the mask.
      const mask = literal !== undefined && literal >= 0 && literal < TWO_31 && Number.isInteger(Math.log2(literal + 1))
      return integral(
        L,
        mask
          ? x.mod(TWO_32).mod(literal + 1)
          : z3.If(
              z3.Or(x32.eq(zero), y32.eq(zero)),
              zero,
              z3.If(
                x32.eq(ones),
                y32,
                z3.If(
                  y32.eq(ones),
                  x32,
                  vector((p, q) => p.and(q)),
                ),
              ),
            ),
      )
    }
    case K.LessThanLessThanToken:
      return integral(L, int32(L, int32(L, x).mul(power())))
    case K.GreaterThanGreaterThanToken: {
      const shifted = int32(L, x).div(power())
      if (literal !== undefined && ((literal % 32) + 32) % 32 === 31) MASKS.add(shifted)
      return integral(L, shifted)
    }
    default:
      return integral(L, x.mod(TWO_32).div(power()))
  }
}

/**
 * `a op b` on doubles, read where it is exact: both finite (and the divisor not 0), the exact result a whole number or
 * a half within 2^53, which a double holds. A double operation rounds its exact result, so there it gives that result.
 * Elsewhere it may round, which the model does not see: each operation is an obligation that it is exact, proved, or
 * broken by an input where it may not be. A law is judged on the runs where every operation is exact, and is proved
 * only once each is (`MODELS`). Where it is `known` exact whatever the input (a count plus a count), it obliges nothing.
 */
export const exactly = (
  L: Lowering,
  op: ts.SyntaxKind,
  a: Extract<Val, { kind: "num" }>,
  b: Extract<Val, { kind: "num" }>,
  at: ts.Node,
  known = false,
): Val => {
  const z3 = L.u.z3
  const r =
    op === K.PlusToken
      ? a.real.add(b.real)
      : op === K.MinusToken
        ? a.real.sub(b.real)
        : op === K.AsteriskToken
          ? a.real.mul(b.real)
          : op === K.SlashToken
            ? a.real.div(b.real)
            : undefined
  if (r === undefined) throw new Unsupported(`\`${ts.tokenToString(op)}\` on \`number\` is not modeled`, at)
  // Whether the result is whole, in terms the solver reasons with: of two whole numbers, a sum, a difference and a
  // product are; `IsInt` beside, for the rest (0.5 + 0.5). Twice a half of a whole number is that number.
  const both = z3.And(isWhole(L.u, a), isWhole(L.u, b))
  const whole = op === K.SlashToken ? z3.IsInt(r) : z3.Or(both, z3.IsInt(r))
  const ia = intOf(L.u, a)
  const ib = intOf(L.u, b)
  const int = op === K.PlusToken ? ia.add(ib) : op === K.MinusToken ? ia.sub(ib) : op === K.AsteriskToken ? ia.mul(ib) : undefined
  const intOfResult = int === undefined ? z3.ToInt(r) : z3.If(both, int, z3.ToInt(r))
  const halfOfTwo = op === K.SlashToken && b.real.eqIdentity(z3.Real.val(2))
  const twiceWhole = halfOfTwo ? isWhole(L.u, a) : op === K.SlashToken ? z3.IsInt(r.mul(2)) : z3.Or(both, z3.IsInt(r.mul(2)))
  const bounded = (x: Arith) => z3.And(x.le(TWO_53), x.ge(-TWO_53))
  const finite = z3.And(a.cls.eq(NUM.finite), b.cls.eq(NUM.finite), op === K.SlashToken ? z3.Not(b.real.eq(0)) : z3.Bool.val(true))
  const goal = z3.And(finite, z3.Or(z3.And(whole, bounded(r)), z3.And(twiceWhole, bounded(r.mul(2)))))
  if (known) {
    // Exact by construction: no condition to say, nor to oblige.
  } else if (L.mode === "spec") L.exact?.push(z3.Implies(L.guard, goal))
  else {
    const where = locate(at)
    L.obligations.push({
      key: `exact@${where}#here`,
      kind: "exact",
      text: at.getText(),
      at: where,
      phase: "here",
      cond: L.guard,
      goal,
      hints: L.hints.length,
    })
  }
  // Its sign where it is 0, as IEEE 754 gives it: `-0 + -0` and `-0 - 0` are `-0`, any other sum or difference that is 0
  // is `0`; a product or quotient that is 0 is `-0` where exactly one operand is negative, `-0` among them.
  const negative = (v: Extract<Val, { kind: "num" }>) => z3.Or(v.real.lt(0), isNegZero(L.u, v))
  const negZero =
    op === K.PlusToken
      ? z3.And(isNegZero(L.u, a), isNegZero(L.u, b))
      : op === K.MinusToken
        ? z3.And(isNegZero(L.u, a), b.real.eq(0), z3.Not(isNegZero(L.u, b)))
        : z3.And(r.eq(0), z3.Not(negative(a).eq(negative(b))))
  return { kind: "num", cls: z3.Int.val(NUM.finite), real: r, whole, int: intOfResult, ...(known ? {} : { negZero }) }
}

/**
 * A bigint `/` or `%`, as JavaScript computes it: the quotient truncated toward zero, the remainder with the dividend's
 * sign. A divisor of 0n throws a RangeError, so wherever the division runs (`L.guard`) its divisor must be another: in
 * the program, an obligation, proved, or broken by the input that throws; in a law or a `requires`, part of what it says.
 */
const divided = (L: Lowering, op: ts.SyntaxKind, l: Val & { kind: "int" }, r: Val & { kind: "int" }, e: ts.BinaryExpression): Val => {
  const z3 = L.u.z3
  // A divisor that is a literal other than 0n never throws: nothing to oblige, and the quotient and remainder are Z3's
  // own, truncated toward 0 as JavaScript's are, which read inside a quantifier as well as out.
  if (z3.isIntVal(r.term) && r.term.value() !== 0n) {
    const d = r.term.value()
    const negative = l.term.lt(0)
    const size = z3.If(negative, l.term.neg(), l.term)
    if (op === K.SlashToken) {
      const q = z3.If(negative, size.div(d < 0n ? -d : d).neg(), size.div(d < 0n ? -d : d))
      return { ...l, term: d < 0n ? q.neg() : q }
    }
    const m = size.mod(d < 0n ? -d : d)
    return { ...l, term: z3.If(negative, m.neg(), m) }
  }
  // Inside a quantifier the element is any index's, read or not, so the obligation would ask more than the code needs.
  if (L.u.openBounds().length > 0)
    throw new Unsupported(
      `a bigint \`${ts.tokenToString(op)}\` by a value the code computes, inside \`.some\`, \`.every\`, \`.find\`, \`.filter\`, \`.map\` or \`.flatMap\`, is not modeled: divide in a \`for…of\` over the elements, or outside the callback`,
      e.operatorToken,
    )
  const nonZero = z3.Not(r.term.eq(0))
  if (L.mode === "spec" && L.defined !== undefined) L.defined.push(z3.Implies(L.guard, nonZero))
  else {
    const at = locate(e.right)
    L.obligations.push({
      key: `division@${at}#here`,
      kind: "division",
      text: e.right.getText(),
      at,
      phase: "here",
      cond: L.guard,
      goal: nonZero,
      hints: L.hints.length,
    })
  }
  // JavaScript truncates: the quotient rounds toward 0, and the remainder takes the dividend's sign. Each is a fresh
  // integer, defined where the divisor is not 0n by what the two are together: the dividend is the divisor times the
  // quotient plus the remainder, which is smaller than the divisor and has the dividend's sign, or is 0n. That is one
  // pair, so the two are exact; and a law as plain as `a === b * (a / b) + a % b` is a fact, not a search.
  const abs = (t: Arith): Arith => z3.If(t.ge(0), t, t.neg())
  const q = z3.Int.const(L.u.fresh("div.q"))
  const m = z3.Int.const(L.u.fresh("div.r"))
  L.u.assume(z3.Implies(nonZero, z3.And(l.term.eq(r.term.mul(q).add(m)), abs(m).lt(abs(r.term)), z3.Or(m.eq(0), m.lt(0).eq(l.term.lt(0))))))
  return { ...l, term: op === K.SlashToken ? q : m }
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
  const record = lazyRecord(
    (name) => {
      const r = resolve(name)
      return z3.isFalse(r.has) ? undefined : (r.value ?? UNDEFINED)
    },
    undefined,
    (name) => resolve(name).has,
  )
  if (parts.some((p) => "spread" in p)) return record
  // Its own keys are the ones written, in the order JavaScript lists them: array positions first, by number.
  const written = [...new Set(parts.map((p) => ("key" in p ? p.key : "")))]
  const position = (k: string) => /^(0|[1-9]\d*)$/.test(k) && Number(k) < 4294967295
  const names = [...written.filter(position).sort((a, b) => Number(a) - Number(b)), ...written.filter((k) => !position(k))]
  const own = () => ({
    keys: tupleOf(
      L,
      names.map((n) => (): Val => ({ kind: "str", term: jsString(z3, n) })),
      () => ({ kind: "str", term: u.leaf([u.fresh("beyond"), "$"], "str", u.openBounds()) as never }),
      e,
    ),
    values: tupleOf(
      L,
      names.map((n) => () => resolve(n).value ?? UNDEFINED),
      () => (names.length === 0 ? UNDEFINED : (resolve(names.at(-1)!).value ?? UNDEFINED)),
      e,
    ),
  })
  return { ...record, own } as Val
}

/** A list of values the code wrote, as an array literal holds them; past its end, `past` (read on no run that happens). */
const tupleOf = (L: Lowering, items: ReadonlyArray<() => Val>, past: (i: Arith) => Val, at: ts.Node): Val => {
  const z3 = L.u.z3
  return {
    kind: "array",
    length: z3.Int.val(items.length),
    size: items.length,
    maxSize: items.length,
    elem: memoElems((i) => {
      if (z3.isIntVal(i)) {
        const k = Number(i.value())
        return k >= 0 && k < items.length ? items[k]!() : past(i)
      }
      let v = past(i)
      for (let k = items.length - 1; k >= 0; k--) v = ite(L.u, i.eq(k), items[k]!(), v, at)
      return v
    }),
  }
}

/**
 * What `Object.keys`, `Object.values` and `Object.entries` read: the value's own keys and their values, in
 * JavaScript's order. Known of an object the code built with no spread, of a dictionary it is given, and of either of
 * two such on two paths; of anything else refused, since a value may hold more keys than its type says, in any order.
 */
const ownOf = (L: Lowering, v: Val, name: string, at: ts.Node): { readonly keys: Val; readonly values: Val } => {
  if (v.kind !== "record") throw new Unsupported(`\`${name}\` of a ${v.kind}`, at)
  if (v.own !== undefined) return v.own()
  if (v.split !== undefined) {
    const a = ownOf(L, v.split.a, name, at)
    const b = ownOf(L, v.split.b, name, at)
    return { keys: ite(L.u, v.split.cond, a.keys, b.keys, at), values: ite(L.u, v.split.cond, a.values, b.values, at) }
  }
  throw new Unsupported(
    `\`${name}\` of a value whose keys the verifier does not know: one the code is given may hold more than its type says, in any order; of a dictionary (\`Record<string, T>\`) or an object the code built they are read`,
    at,
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
/** What the purity check, reading its source, finds of each function of the program a closure's host calls. */
const purityRead = new WeakMap<ts.Node, Purity>()
const programPurity = (checker: ts.TypeChecker, callee: ts.Expression): Purity | undefined => {
  if (!ts.isIdentifier(callee)) return undefined
  let sym = checker.getSymbolAtLocation(callee)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
  const d = sym?.valueDeclaration
  if (d === undefined || d.getSourceFile().isDeclarationFile) return undefined
  const fn =
    ts.isFunctionDeclaration(d) && d.body !== undefined
      ? d
      : ts.isVariableDeclaration(d) &&
          d.initializer !== undefined &&
          (d.parent.flags & ts.NodeFlags.Const) !== 0 &&
          (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer))
        ? d.initializer
        : undefined
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

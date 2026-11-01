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
//
// This file holds the state of a lowering and what every expression goes through: names, members, conditions,
// operators and calls' dispatch. The rest is in `lower/`, one file to what it reads: `patterns`, `closures`, `calls`,
// `library` (`Math`, `Number`, `Object`, `Date`), `numbers`, `strings`, `arrays` and `records`.
import ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import type { Adapter } from "./adapter.ts"
import { chosen } from "./computation.ts"
import { type LemmaUse, type Obligation, runFunction } from "./exec.ts"
import { type Order, compare, isNegZero, isNullish, ite, nullishOr, strictEq, truthy } from "./ops.ts"
import { narrowedField } from "./narrow.ts"
import { isLib } from "./effects.ts"
import type { Purity } from "./purity.ts"
import { inProgram, symbolOf } from "./resolve.ts"
import type { Typing } from "./symbolic.ts"
import type { AssumedFn, Assumptions } from "./trust.ts"
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
  jsString,
  lazy,
} from "./value.ts"
import { bind, defaulted } from "./lower/patterns.ts"
import { template } from "./lower/strings.ts"
import { arrayLiteral, elementAccess } from "./lower/arrays.ts"
import { assumedFn, call } from "./lower/calls.ts"
import { callable, closureCheck } from "./lower/closures.ts"
import { dictionaryRead, keyIn, objectLiteral } from "./lower/records.ts"
import { arithmetic, asNumber, constantOf, int32, integral, truncatedOf } from "./lower/numbers.ts"

/** What a verification trusts, shared by its two sides: the declarations in force, and what came of using them. */
export interface Trust {
  readonly assumptions: Assumptions
  /** Each declared-pure function's purity, checked once. */
  readonly purity: Map<AssumedFn, Purity>
  /** The declarations a lowering leaned on. */
  readonly used: Set<AssumedFn>
}

export const trustOf = (assumptions: Assumptions): Trust => ({ assumptions, purity: new Map(), used: new Set() })

const NO_TRUST: Assumptions = { all: [], of: () => undefined, forTarget: () => NO_TRUST }

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
export const EMPTY: Env = new Map()

export const bool = (term: Bool): Val => ({ kind: "bool", term })

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

/** A value the type checker has shown present (`if (!run.pruned) return`, then `const { at } = run.pruned`): what it holds. */
export const shownPresent = (v: Val, type: ts.Type): Val => {
  const parts = type.isUnion() ? type.types : [type]
  return v.kind === "maybe" && v.value !== undefined && !parts.some((m) => m.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined))
    ? v.value
    : v
}

/**
 * A value of more than one kind, read where the type checker has narrowed it (`typeof x === "string"`, `x === "unsigned"`):
 * its part of the kinds the narrowed type allows. No run reaches the read with the value of another kind.
 */
const narrowedKind = (L: Lowering, e: ts.Expression, v: Val): Val => {
  // A value of type `unknown` read where the checker has narrowed it to a type it names: that type's value. Not `{}`,
  // which `x != null` narrows it to: a string is one too.
  if (v.kind === "opaque" && v.as !== undefined) {
    const t = L.checker.getTypeAtLocation(e)
    const open = (t.isUnion() ? t.types : [t]).some(
      (m) =>
        m.flags & (ts.TypeFlags.Unknown | ts.TypeFlags.Any | ts.TypeFlags.TypeParameter | ts.TypeFlags.NonPrimitive) ||
        (m.flags & ts.TypeFlags.Object &&
          L.checker.getPropertiesOfType(m).length === 0 &&
          L.checker.getIndexInfosOfType(m).length === 0 &&
          m.getCallSignatures().length === 0 &&
          !L.checker.isArrayType(m)),
    )
    return open ? v : (v.as(t, e) ?? v)
  }
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
export const namespaceMember = (L: Lowering, e: ts.PropertyAccessExpression, env: Env): Val | undefined => {
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
export const named = (L: Lowering, e: ts.Identifier): Val => {
  const imported = ((L.checker.getSymbolAtLocation(e)?.flags ?? 0) & ts.SymbolFlags.Alias) !== 0
  const sym = symbolOf(L.checker, e)
  if (sym?.name === "undefined" && sym.declarations === undefined) return { kind: "nullish", which: "undefined" }
  if (sym?.name === "undefined" && sym.declarations?.every((d) => d.getSourceFile().isDeclarationFile))
    return { kind: "nullish", which: "undefined" }
  const declared = L.trust.assumptions.of(e)
  if (declared !== undefined) return assumedFn(L, declared)
  const decl = sym?.valueDeclaration
  if (decl !== undefined && inProgram(decl)) {
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
export const optionally = (L: Lowering, obj: Val, e: ts.Node, objExpr: ts.Expression, f: (v: Val) => Val): Val => {
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

/**
 * `x instanceof C`, of a class the program declares: false of a primitive, and of a value of type `unknown` the code was
 * given, whether it is one of the class's instances (`instanceOf`). Of a class a package declares (`Error`), whose
 * ancestry its declarations need not show, and of a value the code built, it is refused.
 */
const instanceOf = (L: Lowering, e: ts.BinaryExpression, env: Env): Val => {
  const decl = symbolOf(L.checker, e.right)?.valueDeclaration
  if (decl === undefined || !ts.isClassLike(decl) || !inProgram(decl))
    throw new Unsupported(
      `\`instanceof ${e.right.getText()}\`, a class the program does not declare, is not modeled: test a field that tells the values apart (a \`_tag\`)`,
      e,
    )
  const v = lowerExpr(L, e.left, env)
  if (v.kind === "str" || v.kind === "num" || v.kind === "int" || v.kind === "bool" || v.kind === "nullish" || v.kind === "mixed")
    return bool(L.u.z3.Bool.val(false))
  if (v.kind === "opaque" && v.instanceOf !== undefined) return bool(v.instanceOf(decl, e))
  throw new Unsupported(
    `\`instanceof\` of a ${v.kind} the code ${v.kind === "opaque" ? "merged from two paths" : "built or was given"} is not modeled`,
    e,
  )
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
  if (op === K.InstanceOfKeyword) return instanceOf(L, e, env)
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

/**
 * An operand of `<` or `+`, read as present where the type checker has narrowed it to neither null nor undefined
 * (`out === undefined || out < 0n`): the value then only matters on the paths where it is present.
 */
export const narrowed = (L: Lowering, e: ts.Expression, v: Val, op: ts.SyntaxKind): Val => {
  if (v.kind !== "maybe" || op === K.EqualsEqualsEqualsToken || op === K.ExclamationEqualsEqualsToken) return v
  const t = L.checker.getTypeAtLocation(e)
  if ((t.isUnion() ? t.types : [t]).some((m) => m.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined | ts.TypeFlags.Void))) return v
  return v.value ?? v
}

export const emptyEnv = EMPTY

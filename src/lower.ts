// Lowers pure TypeScript to symbolic values, keeping JavaScript's meaning.
//
// Supported: literals of every primitive, null and undefined; `const` bindings
// (evaluated when first read); `if` with early returns; `?:`, `&&`, `||`, `!`,
// `??`, `===`, `!==`, `<` and friends; `+ - *` on bigints, `+` on strings;
// unary `-`; property access and optional chaining; object and
// array literals; calls to functions of the program (inlined) and to closures;
// on arrays `.length`, `.at(k)` for a literal k, `.filter(p).length`, `.some(p)`,
// `.every(p)`, `.includes(x)` for strings and booleans.
//
// Refused with a source span: arithmetic on `number` (its rounding is not
// modeled) and bigint `/` `%` (they truncate; Z3's do not), `==`, assignments and loops, casts and non-null assertions (each is
// a claim the verifier would have to trust), `any`, recursion, a binding it
// cannot see (a `let`, a global, an import from a package), string length and
// template strings (code units and number formatting).
//
// Reading a binding only when it is used means a binding the result does not
// need is never checked. The code under verification is taken to throw nothing:
// a `const` whose evaluation would throw, but whose value is never read, is not
// seen. The report says so.
import ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import { type Order, compare, isNullish, ite, nullishOr, strictEq, truthy } from "./ops.ts"
import type { Typing } from "./symbolic.ts"
import { type Env, type FunctionNode, NUM, type Thunk, Unsupported, type Val, exactRational, lazy, lazyRecord } from "./value.ts"

export interface Lowering extends Typing {
  /** The functions being inlined, innermost last: a guard against recursion. */
  readonly stack: Array<FunctionNode>
  /** Module-level constants, lowered once each. */
  readonly constants: Map<ts.Declaration, Val>
}

const K = ts.SyntaxKind
const EMPTY: Env = new Map()

const bool = (term: Bool<"main">): Val => ({ kind: "bool", term })

/** The value of calling `fn` (closing over `env`) with `args`. */
export const lowerCall = (L: Lowering, fn: FunctionNode, env: Env, args: ReadonlyArray<Val>, at: ts.Node): Val => {
  if (L.stack.includes(fn)) throw new Unsupported("recursion is not modeled", at)
  if (fn.asteriskToken !== undefined) throw new Unsupported("generators are not modeled", fn)
  if (fn.modifiers?.some((m) => m.kind === K.AsyncKeyword)) throw new Unsupported("async functions are not modeled", fn)
  L.stack.push(fn)
  try {
    const scope = new Map(env)
    fn.parameters.forEach((p, i) => {
      const given = args[i]
      if (p.dotDotDotToken !== undefined) throw new Unsupported("rest parameters are not modeled", p)
      const value: Thunk =
        given !== undefined
          ? () => given
          : p.initializer !== undefined
            ? lazy(() => lowerExpr(L, p.initializer!, scope))
            : () => ({ kind: "nullish", which: "undefined" })
      bind(L, p.name, value, scope)
    })
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

/** Binds a name or an object pattern to a value, each name read on first use. */
const bind = (L: Lowering, name: ts.BindingName, value: Thunk, scope: Map<string, Thunk>): void => {
  if (ts.isIdentifier(name)) {
    scope.set(name.text, value)
    return
  }
  if (!ts.isObjectBindingPattern(name)) throw new Unsupported("array destructuring is not modeled", name)
  for (const el of name.elements) {
    if (el.dotDotDotToken !== undefined || el.initializer !== undefined)
      throw new Unsupported("rest and default values in destructuring are not modeled", el)
    const key = el.propertyName === undefined ? (el.name as ts.Identifier).text : propertyKey(el.propertyName)
    bind(L, el.name, lazy(() => member(L, value(), key, el)), scope)
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
      bind(L, d.name, lazy(() => lowerExpr(L, init, scope)), scope)
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
  if (ts.isTemplateExpression(e)) throw new Unsupported("template strings format numbers, which is not modeled", e)

  if (ts.isIdentifier(e)) return identifier(L, e, env)
  if (ts.isPropertyAccessExpression(e)) return propertyAccess(L, e, env)
  if (ts.isElementAccessExpression(e)) throw new Unsupported("element access `a[i]` is not modeled; `.at(i)` is", e)
  if (ts.isCallExpression(e)) return call(L, e, env)
  if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) return { kind: "fn", node: e, env }

  if (ts.isObjectLiteralExpression(e)) {
    const fields = new Map<string, Thunk>()
    for (const p of e.properties) {
      if (ts.isPropertyAssignment(p)) fields.set(propertyKey(p.name), lazy(() => lowerExpr(L, p.initializer, env)))
      else if (ts.isShorthandPropertyAssignment(p)) fields.set(p.name.text, lazy(() => identifier(L, p.name, env)))
      else throw new Unsupported("spreads, methods and accessors in an object literal are not modeled", p)
    }
    return lazyRecord((name) => fields.get(name)?.())
  }
  if (ts.isArrayLiteralExpression(e)) {
    if (e.elements.some((x) => ts.isSpreadElement(x) || ts.isOmittedExpression(x)))
      throw new Unsupported("spreads and holes in an array literal are not modeled", e)
    const items = e.elements.map((x) => lazy(() => lowerExpr(L, x, env)))
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

export const num = (z3: Lowering["u"]["z3"], n: number): Val => ({
  kind: "num",
  cls: z3.Int.val(Number.isNaN(n) ? NUM.nan : n === Infinity ? NUM.posInf : n === -Infinity ? NUM.negInf : NUM.finite),
  real: z3.Real.val(Number.isFinite(n) ? exactRational(n) : 0),
})

const identifier = (L: Lowering, e: ts.Identifier, env: Env): Val => {
  const bound = env.get(e.text)
  if (bound !== undefined) return bound()
  let sym = L.checker.getSymbolAtLocation(e)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = L.checker.getAliasedSymbol(sym)
  if (sym?.name === "undefined" && sym.declarations === undefined) return { kind: "nullish", which: "undefined" }
  if (sym?.name === "undefined" && sym.declarations?.every((d) => d.getSourceFile().isDeclarationFile))
    return { kind: "nullish", which: "undefined" }
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
  throw new Unsupported(`\`${e.text}\` is a binding the verifier cannot see (a \`let\`, a global or a package's)`, e)
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
  if (f.kind !== "fn") throw new Unsupported(`calling a ${f.kind}`, e)
  if (e.arguments.some(ts.isSpreadElement)) throw new Unsupported("spread arguments are not modeled", e)
  const args = e.arguments.map((a) => lowerExpr(L, a, env))
  return lowerCall(L, f.node, f.env, args, e)
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
  const quantify = (q: "exists" | "forall", p: (i: Arith<"main">) => Bool<"main">): Bool<"main"> => {
    if (u.bound !== undefined) {
      // Written out: element k for each k below the bound, counted only where k < length.
      const each = Array.from({ length: u.bound }, (_, k) => {
        const i = z3.Int.val(k)
        return q === "exists" ? z3.And(i.lt(arr.length), p(i)) : z3.Implies(i.lt(arr.length), p(i))
      })
      return q === "exists" ? z3.Or(...each) : z3.And(...each)
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
      if (u.bound !== undefined) {
        count = z3.Sum(
          z3.Int.val(0),
          ...Array.from({ length: u.bound }, (_, k) => z3.If(z3.And(z3.Int.val(k).lt(arr.length), p(z3.Int.val(k))), z3.Int.val(1), z3.Int.val(0))),
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

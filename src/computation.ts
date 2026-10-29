// Computations: a body that runs steps (`yield*` in a generator, `await` in an
// async function), ends in an outcome and calls operations on the way, each
// call recorded in a trace. The same model serves Effect programs, async
// functions and code that throws; an adapter says which form is which.
//
// An outcome is `{ _tag: "Success", value } | { _tag: "Failure", error }`. A
// trace is an array of calls `{ target, op, args, outcome }`, in the order made.
// An operation's outcome is unknown but for its types (and, later, its
// contract): any outcome they allow is covered.
import ts from "typescript"
import type { Arith } from "z3-solver"
import type { Style } from "./adapter.ts"
import { bind, bindParameters, cond, lowerExpr, type Lowering } from "./lower.ts"
import { ite } from "./ops.ts"
import { symbolicOf } from "./symbolic.ts"
import { type Env, type FunctionNode, type Ran, Unsupported, type Val, lazy, lazyRecord } from "./value.ts"

const K = ts.SyntaxKind

const str = (L: Lowering, s: string): Val => ({ kind: "str", term: L.u.z3.String.val(s) })

export const success = (L: Lowering, value: Val): Val =>
  lazyRecord((n) => (n === "_tag" ? str(L, "Success") : n === "value" ? value : undefined))

export const failure = (L: Lowering, error: Val): Val =>
  lazyRecord((n) => (n === "_tag" ? str(L, "Failure") : n === "error" ? error : undefined))

/** A computation's end as a value, so two paths' ends merge as any two values do. */
const ran = (r: Ran): Val => lazyRecord((n) => (n === "outcome" ? r.outcome : n === "trace" ? r.trace : undefined))
const unran = (v: Val): Ran => {
  if (v.kind !== "record") throw new Error("a computation's end is a record")
  return { outcome: v.field("outcome")!, trace: v.field("trace")! }
}

export const emptyTrace = (L: Lowering): Val => ({
  kind: "array",
  length: L.u.z3.Int.val(0),
  size: 0,
  maxSize: 0,
  elem: () => lazyRecord(() => undefined),
})

const appended = (L: Lowering, trace: Val, call: Val, at: ts.Node): Val => {
  if (trace.kind !== "array" || trace.maxSize === undefined) throw new Error("a trace is an array of known bound")
  const z3 = L.u.z3
  const size = trace.size === undefined ? undefined : trace.size + 1
  return {
    kind: "array",
    length: size === undefined ? trace.length.add(1) : z3.Int.val(size),
    ...(size === undefined ? {} : { size }),
    maxSize: trace.maxSize + 1,
    elem: (i: Arith<"main">) => {
      if (trace.size !== undefined && z3.isIntVal(i)) return Number(i.value()) === trace.size ? call : trace.elem(i)
      return ite(L.u, i.eq(trace.length), call, trace.elem(i), at)
    },
  }
}

/**
 * An operation: a function whose call is a computation that records itself and
 * ends in an unknown outcome of its types. `target` names what it is an
 * operation of (a service, a parameter), `op` the method.
 */
export const operation = (
  L: Lowering,
  target: string,
  op: string,
  types: { success: ts.Type; failure: ts.Type | undefined },
  at: ts.Node,
): Val => ({
  kind: "builtin",
  name: `${target}.${op}`,
  call: (args) => ({
    kind: "comp",
    run: (trace) => {
      const z3 = L.u.z3
      const base = [L.u.fresh(`${target}.${op}`)]
      const tag = L.u.leaf([...base, "._tag", "$"], "str", []) as never as ReturnType<typeof z3.String.val>
      const canFail = types.failure !== undefined && !(types.failure.flags & ts.TypeFlags.Never)
      L.u.assume(canFail ? z3.Or(tag.eq(z3.String.val("Success")), tag.eq(z3.String.val("Failure"))) : tag.eq(z3.String.val("Success")))
      const outcome = lazyRecord((n) => {
        if (n === "_tag") return { kind: "str", term: tag }
        if (n === "value") return symbolicOf(L, types.success, [...base, ".value"], [], at)
        if (n === "error") {
          if (types.failure === undefined) throw new Unsupported(`what \`${target}.${op}\` fails with is not declared`, at)
          return symbolicOf(L, types.failure, [...base, ".error"], [], at)
        }
        return undefined
      })
      const argRecord = lazyRecord((n) =>
        n === "length" ? { kind: "int", origin: "count", term: z3.Int.val(args.length) } : /^\d+$/.test(n) ? args[Number(n)] : undefined,
      )
      const call = lazyRecord((n) =>
        n === "target" ? str(L, target) : n === "op" ? str(L, op) : n === "args" ? argRecord : n === "outcome" ? outcome : undefined,
      )
      return { outcome, trace: appended(L, trace, call, at) }
    },
  }),
})

/** A function's call as a computation: running it binds the arguments and runs its body from the trace it is given. */
export const computationCall = (L: Lowering, fn: FunctionNode, style: Style, env: Env, args: ReadonlyArray<Val>, at: ts.Node): Val => ({
  kind: "comp",
  run: (trace) => runBody(L, fn, style, env, args, trace, at),
})

export const runBody = (
  L: Lowering,
  fn: FunctionNode,
  style: Style,
  env: Env,
  args: ReadonlyArray<Val>,
  trace: Val,
  at: ts.Node,
): Ran => {
  if (L.stack.includes(fn)) throw new Unsupported("recursion is not modeled", at)
  L.stack.push(fn)
  try {
    const scope = bindParameters(L, fn, env, args)
    const body = fn.body
    if (body === undefined) throw new Unsupported("a function with no body", fn)
    if (!ts.isBlock(body)) return returning(L, style, body, scope, trace)
    return unran(statements(L, style, body.statements, 0, scope, trace, (t) => ran({ outcome: success(L, { kind: "nullish", which: "undefined" }), trace: t })))
  } finally {
    L.stack.pop()
  }
}

/** The operand of a step, when `e` is one in this style: `yield* x` in a generator, `await x` in an async function. */
const stepOf = (style: Style, e: ts.Expression): ts.Expression | undefined => {
  const x = ts.isParenthesizedExpression(e) ? e.expression : e
  if (style === "gen" && ts.isYieldExpression(x)) {
    if (x.asteriskToken === undefined || x.expression === undefined) throw new Unsupported("a bare `yield` is not modeled; `yield*` is", x)
    return x.expression
  }
  if (style === "async" && ts.isAwaitExpression(x)) return x.expression
  return undefined
}

/** Runs a step's operand from `trace`. */
const step = (L: Lowering, style: Style, operand: ts.Expression, env: Env, trace: Val): Ran => {
  for (const a of L.adapters) {
    const v = a.operand?.(L, operand, env)
    if (v !== undefined) return runValue(L, style, v, trace, operand)
  }
  return runValue(L, style, lowerExpr(L, operand, env), trace, operand)
}

const runValue = (L: Lowering, style: Style, v: Val, trace: Val, at: ts.Node): Ran => {
  if (v.kind === "comp") return v.run(trace)
  if (style === "async") return { outcome: success(L, v), trace } // `await` of a value that is no promise is the value
  throw new Unsupported(`\`yield*\` of a ${v.kind}, which is no computation`, at)
}

/** `return e`: a step's end is the computation's; a value is its success (an async function's promise is awaited). */
const returning = (L: Lowering, style: Style, e: ts.Expression, env: Env, trace: Val): Ran => {
  const operand = stepOf(style, e)
  if (operand !== undefined) return step(L, style, operand, env, trace)
  const v = lowerExpr(L, e, env)
  if (style === "async" && v.kind === "comp") return v.run(trace)
  return { outcome: success(L, v), trace }
}

/** Continues after a step, unless it failed: then its failure is the computation's end. */
const after = (L: Lowering, r: Ran, at: ts.Node, next: (value: Val, trace: Val) => Val): Val => {
  const outcome = r.outcome
  if (outcome.kind !== "record") throw new Error("an outcome is a record")
  const tag = outcome.field("_tag")!
  if (tag.kind !== "str") throw new Error("an outcome's _tag is a string")
  const value = outcome.field("value")
  if (tag.term.sexpr() === '"Failure"') return ran(r)
  if (tag.term.sexpr() === '"Success"' && value !== undefined) return next(value, r.trace)
  const failed = tag.term.eq(L.u.z3.String.val("Failure"))
  return ite(L.u, failed, ran(r), value === undefined ? ran(r) : next(value, r.trace), at)
}

const statements = (
  L: Lowering,
  style: Style,
  stmts: ReadonlyArray<ts.Statement>,
  i: number,
  env: Env,
  trace: Val,
  rest: (trace: Val) => Val,
): Val => {
  if (i === stmts.length) return rest(trace)
  const s = stmts[i]!
  const next = (t: Val, e: Env = env): Val => statements(L, style, stmts, i + 1, e, t, rest)

  if (ts.isVariableStatement(s)) {
    if ((s.declarationList.flags & ts.NodeFlags.Const) === 0) throw new Unsupported("only `const` bindings are modeled", s)
    const decls = s.declarationList.declarations
    const bindFrom = (k: number, scope: Map<string, () => Val>, t: Val): Val => {
      if (k === decls.length) return statements(L, style, stmts, i + 1, scope, t, rest)
      const d = decls[k]!
      if (d.initializer === undefined) throw new Unsupported("a `const` with no value", d)
      const operand = stepOf(style, d.initializer)
      if (operand === undefined) {
        const init = d.initializer
        const inner = new Map(scope)
        bindName(L, d.name, lazy(() => lowerExpr(L, init, inner)), inner)
        return bindFrom(k + 1, inner, t)
      }
      return after(L, step(L, style, operand, scope, t), d, (value, t2) => {
        const inner = new Map(scope)
        bindName(L, d.name, () => value, inner)
        return bindFrom(k + 1, inner, t2)
      })
    }
    return bindFrom(0, new Map(env), trace)
  }
  if (ts.isExpressionStatement(s)) {
    const operand = stepOf(style, s.expression)
    if (operand === undefined) throw new Unsupported("a statement that is no step (`yield*`, `await`) has an effect the verifier does not model", s)
    return after(L, step(L, style, operand, env, trace), s, (_, t) => next(t))
  }
  if (ts.isReturnStatement(s))
    return ran(s.expression === undefined ? { outcome: success(L, { kind: "nullish", which: "undefined" }), trace } : returning(L, style, s.expression, env, trace))
  if (ts.isThrowStatement(s)) {
    if (style === "gen") throw new Unsupported("a `throw` in a generator is a defect, which is not modeled; fail instead", s)
    return ran({ outcome: failure(L, lowerExpr(L, s.expression, env)), trace })
  }
  if (ts.isIfStatement(s)) {
    const c = cond(L, s.expression, env)
    const branch = (b: ts.Statement) => statements(L, style, ts.isBlock(b) ? b.statements : [b], 0, env, trace, (t) => next(t))
    return ite(L.u, c, branch(s.thenStatement), s.elseStatement === undefined ? next(trace) : branch(s.elseStatement), s)
  }
  if (ts.isBlock(s)) return statements(L, style, s.statements, 0, env, trace, (t) => next(t))
  if (ts.isEmptyStatement(s)) return next(trace)
  throw new Unsupported(`a ${K[s.kind]} in a computation is not modeled`, s)
}

const bindName = (L: Lowering, name: ts.BindingName, value: () => Val, scope: Map<string, () => Val>): void => bind(L, name, value, scope)

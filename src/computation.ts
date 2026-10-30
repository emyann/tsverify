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
import type { Arith, Bool } from "z3-solver"
import type { Style } from "./adapter.ts"
import { bind, bindParameters, cond, isLogical, later, lowerExpr, type Lowering, onBranch, stepKey } from "./lower.ts"
import { isNullish, ite, truthy } from "./ops.ts"
import { symbolicOf } from "./symbolic.ts"
import { type Env, type FunctionNode, type Ran, Unsupported, type Val, jsString, lazy, lazyRecord, locate } from "./value.ts"

const K = ts.SyntaxKind

const str = (L: Lowering, s: string): Val => ({ kind: "str", term: jsString(L.u.z3, s) })

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
    elem: (i: Arith) => {
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
      const base = [L.u.given(`${target}.${op}`)]
      L.u.calls.add(base[0]!)
      const tag = L.u.leaf([...base, "._tag", "$"], "str", []) as never as ReturnType<typeof z3.String.val>
      const canFail = types.failure !== undefined && !(types.failure.flags & ts.TypeFlags.Never)
      L.u.assume(canFail ? z3.Or(tag.eq(jsString(z3, "Success")), tag.eq(jsString(z3, "Failure"))) : tag.eq(jsString(z3, "Success")))
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
      // `~root` names this call's root, so a counterexample can tell which calls its run made; no law's type has it.
      const call = lazyRecord((n) =>
        n === "target"
          ? str(L, target)
          : n === "op"
            ? str(L, op)
            : n === "args"
              ? argRecord
              : n === "outcome"
                ? outcome
                : n === "~root"
                  ? str(L, base[0]!)
                  : undefined,
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

export const runBody = (L: Lowering, fn: FunctionNode, style: Style, env: Env, args: ReadonlyArray<Val>, trace: Val, at: ts.Node): Ran => {
  if (L.stack.includes(fn)) throw new Unsupported("recursion is not modeled", at)
  L.stack.push(fn)
  try {
    const scope = bindParameters(L, fn, env, args)
    const body = fn.body
    if (body === undefined) throw new Unsupported("a function with no body", fn)
    if (!ts.isBlock(body)) return unran(stepsIn(L, style, body, scope, trace, (stepped, t) => ran(returning(L, style, body, stepped, t))))
    return unran(
      statements(L, style, body.statements, 0, scope, trace, (t) =>
        ran({ outcome: success(L, { kind: "nullish", which: "undefined" }), trace: t }),
      ),
    )
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

/** `return e`, its steps run: a value is the computation's success (an async function's promise is awaited). */
const returning = (L: Lowering, style: Style, e: ts.Expression, env: Env, trace: Val): Ran => {
  const v = lowerExpr(L, e, env)
  if ((style === "async" || style === "returns") && v.kind === "comp" && stepOf(style, e) === undefined) return v.run(trace)
  return { outcome: success(L, v), trace }
}

/** Whether `n` holds a step of this style, outside any function it defines. */
const holdsStep = (style: Style, n: ts.Node): boolean => {
  if (style === "returns" || ts.isFunctionLike(n) || ts.isClassLike(n)) return false
  const memo = held[style]
  let h = memo.get(n)
  if (h === undefined) {
    h =
      (style === "gen" ? ts.isYieldExpression(n) : ts.isAwaitExpression(n)) ||
      (ts.forEachChild(n, (c) => holdsStep(style, c) || undefined) ?? false)
    memo.set(n, h)
  }
  return h
}
const held = { gen: new WeakMap<ts.Node, boolean>(), async: new WeakMap<ts.Node, boolean>() }

/**
 * Runs the steps in `e`, in the order JavaScript evaluates them, each from the trace the one before left, each value
 * bound under its node for `lowerExpr` to read; then `k`. A step runs only on the paths that reach it: one inside
 * `c ? a : b`, `a && b`, `a || b` or `a ?? b` runs on the paths where its side is evaluated, and the expression's value
 * is bound on each path. A failed step ends the computation there.
 */
const stepsIn = (L: Lowering, style: Style, n: ts.Node, env: Env, trace: Val, k: (env: Env, trace: Val) => Val): Val => {
  if (!holdsStep(style, n)) return k(env, trace)
  const bound = (scope: Env, node: ts.Node, value: () => Val): Env => new Map(scope).set(stepKey(node), lazy(value))
  if (ts.isYieldExpression(n) || ts.isAwaitExpression(n)) {
    const operand = stepOf(style, n)!
    return stepsIn(L, style, operand, env, trace, (env2, t2) =>
      after(L, step(L, style, operand, env2, t2), n, (value, t3) =>
        k(
          bound(env2, n, () => value),
          t3,
        ),
      ),
    )
  }
  if (ts.isConditionalExpression(n) && (holdsStep(style, n.whenTrue) || holdsStep(style, n.whenFalse)))
    return stepsIn(L, style, n.condition, env, trace, (env2, t2) => {
      const arm = (b: ts.Expression) =>
        stepsIn(L, style, b, env2, t2, (env3, t3) =>
          k(
            bound(
              env3,
              n,
              later(L, () => lowerExpr(L, b, env3)),
            ),
            t3,
          ),
        )
      const c = cond(L, n.condition, env2)
      const yes = onBranch(L, c, () => arm(n.whenTrue))
      return ite(
        L.u,
        c,
        yes,
        onBranch(L, L.u.z3.Not(c), () => arm(n.whenFalse)),
        n,
      )
    })
  if (isLogical(n) && holdsStep(style, n.right))
    return stepsIn(L, style, n.left, env, trace, (env2, t2) => {
      const left = lowerExpr(L, n.left, env2)
      const op = n.operatorToken.kind
      const z3 = L.u.z3
      const stops =
        op === K.AmpersandAmpersandToken
          ? z3.Not(truthy(L.u, left))
          : op === K.BarBarToken
            ? truthy(L.u, left)
            : z3.Not(isNullish(L.u, left))
      const right = onBranch(L, z3.Not(stops), () =>
        stepsIn(L, style, n.right, env2, t2, (env3, t3) =>
          k(
            bound(
              env3,
              n,
              later(L, () => lowerExpr(L, n.right, env3)),
            ),
            t3,
          ),
        ),
      )
      return ite(
        L.u,
        stops,
        k(
          bound(env2, n, () => left),
          t2,
        ),
        right,
        n,
      )
    })
  const children: Array<ts.Node> = []
  ts.forEachChild(n, (c) => {
    children.push(c)
  })
  // In a chain after `?.`, all but the head is evaluated only when what came before is present.
  if ((n.flags & ts.NodeFlags.OptionalChain) !== 0 && children.slice(1).some((c) => holdsStep(style, c)))
    throw new Unsupported("a step after `?.` runs only when what is before it is present, which is not modeled: write an `if`", n)
  const each = (i: number, scope: Env, t: Val): Val =>
    i === children.length ? k(scope, t) : stepsIn(L, style, children[i]!, scope, t, (s2, t2) => each(i + 1, s2, t2))
  return each(0, env, trace)
}

/** `c ? a : b` of two computations: one that runs `a` where `c` holds and `b` where it does not. */
export const chosen = (L: Lowering, c: Bool, a: Val, b: Val, at: ts.Node): Val => ({
  kind: "comp",
  run: (trace) =>
    unran(ite(L.u, c, ran(onBranch(L, c, () => runComp(a, trace, at))), ran(onBranch(L, L.u.z3.Not(c), () => runComp(b, trace, at))), at)),
})

/** Runs the computation `v` from `trace`; a value that is none is refused. */
export const runComp = (v: Val, trace: Val, at: ts.Node): Ran => {
  if (v.kind !== "comp") throw new Unsupported(`a ${v.kind} where a computation is expected`, at)
  return v.run(trace)
}

/** `r`, continued by `next` from its success, with its value and the trace so far; a failure ends it as it is. */
export const onSuccess = (L: Lowering, r: Ran, at: ts.Node, next: (value: Val, trace: Val) => Ran): Ran =>
  unran(after(L, r, at, (value, trace) => ran(next(value, trace))))

/** `r`, handled by `handle` from its failure, with its error and the trace so far; a success passes as it is. */
export const onFailure = (L: Lowering, r: Ran, at: ts.Node, handle: (error: Val, trace: Val) => Ran): Ran => {
  const outcome = r.outcome
  if (outcome.kind !== "record") throw new Error("an outcome is a record")
  const tag = outcome.field("_tag")!
  if (tag.kind !== "str") throw new Error("an outcome's _tag is a string")
  if (tag.term.eqIdentity(jsString(L.u.z3, "Success"))) return r
  const error = outcome.field("error")
  if (error === undefined) return r
  if (tag.term.eqIdentity(jsString(L.u.z3, "Failure"))) return handle(error, r.trace)
  const failed = tag.term.eq(jsString(L.u.z3, "Failure"))
  return unran(
    ite(L.u, failed, ran(onBranch(L, failed, () => handle(error, r.trace))), ran({ outcome: asSuccess(outcome), trace: r.trace }), at),
  )
}

/**
 * An outcome seen on the path where it failed, or where it succeeded: the other path's part left out, so the ends of two
 * paths merge field by field (an operation's outcome holds a value of its success type even where it fails).
 */
const asFailure = (o: Val): Val => (o.kind === "record" ? lazyRecord((n) => (n === "value" ? undefined : o.field(n))) : o)
const asSuccess = (o: Val): Val => (o.kind === "record" ? lazyRecord((n) => (n === "error" ? undefined : o.field(n))) : o)

/** Continues after a step, unless it failed: then its failure is the computation's end. */
const after = (L: Lowering, r: Ran, at: ts.Node, next: (value: Val, trace: Val) => Val): Val => {
  const outcome = r.outcome
  if (outcome.kind !== "record") throw new Error("an outcome is a record")
  const tag = outcome.field("_tag")!
  if (tag.kind !== "str") throw new Error("an outcome's _tag is a string")
  const value = outcome.field("value")
  if (tag.term.eqIdentity(jsString(L.u.z3, "Failure"))) return ran(r)
  if (tag.term.eqIdentity(jsString(L.u.z3, "Success")) && value !== undefined) return next(value, r.trace)
  const failed = tag.term.eq(jsString(L.u.z3, "Failure"))
  const rest = value === undefined ? ran(r) : onBranch(L, L.u.z3.Not(failed), () => next(value, r.trace))
  return ite(L.u, failed, ran({ outcome: asFailure(outcome), trace: r.trace }), rest, at)
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
      const init = d.initializer
      if (init === undefined) throw new Unsupported("a `const` with no value", d)
      return stepsIn(L, style, init, scope, t, (stepped, t2) => {
        const inner = new Map(stepped)
        bindName(
          L,
          d.name,
          later(L, () => lowerExpr(L, init, inner)),
          inner,
        )
        return bindFrom(k + 1, inner, t2)
      })
    }
    return bindFrom(0, new Map(env), trace)
  }
  if (ts.isExpressionStatement(s)) {
    if (stepOf(style, s.expression) === undefined)
      throw new Unsupported("a statement that is no step (`yield*`, `await`) has an effect the verifier does not model", s)
    return stepsIn(L, style, s.expression, env, trace, (_, t) => next(t))
  }
  if (ts.isReturnStatement(s)) {
    const e = s.expression
    if (e === undefined) return ran({ outcome: success(L, { kind: "nullish", which: "undefined" }), trace })
    return stepsIn(L, style, e, env, trace, (stepped, t) => ran(returning(L, style, e, stepped, t)))
  }
  if (ts.isThrowStatement(s)) {
    if (style === "gen") throw new Unsupported("a `throw` in a generator is a defect, which is not modeled; fail instead", s)
    return stepsIn(L, style, s.expression, env, trace, (stepped, t) =>
      ran({ outcome: failure(L, lowerExpr(L, s.expression, stepped)), trace: t }),
    )
  }
  if (ts.isIfStatement(s))
    return stepsIn(L, style, s.expression, env, trace, (stepped, t) => {
      const branch = (b: ts.Statement) => statements(L, style, ts.isBlock(b) ? b.statements : [b], 0, stepped, t, (t2) => next(t2))
      const c = cond(L, s.expression, stepped)
      const yes = onBranch(L, c, () => branch(s.thenStatement))
      const no = onBranch(L, L.u.z3.Not(c), () => (s.elseStatement === undefined ? next(t) : branch(s.elseStatement)))
      return ite(L.u, c, yes, no, s)
    })
  if (ts.isForOfStatement(s)) return stepsIn(L, style, s.expression, env, trace, (stepped, t) => forOf(L, style, s, stepped, t, next))
  if (ts.isBlock(s)) return statements(L, style, s.statements, 0, env, trace, (t) => next(t))
  if (ts.isEmptyStatement(s)) return next(trace)
  throw new Unsupported(`a ${K[s.kind]} in a computation is not modeled`, s)
}

/**
 * An outcome no computation ends with: the path ran to the end of a loop's body, or out of the loop. Each iteration and
 * the loop's end are reached once, with the trace of every path that got there merged, so the code after them is read
 * once, not once per path.
 */
const THROUGH = "$through"
const through = (L: Lowering, trace: Val): Val => ran({ outcome: lazyRecord((n) => (n === "_tag" ? str(L, THROUGH) : undefined)), trace })

/** The paths of `v` that went through, continued by `next` from their merged trace; the others ended where they did. */
const whenThrough = (L: Lowering, v: Val, at: ts.Node, next: (trace: Val) => Val): Val => {
  const r = unran(v)
  if (r.outcome.kind !== "record") throw new Error("an outcome is a record")
  const tag = r.outcome.field("_tag")!
  if (tag.kind !== "str") throw new Error("an outcome's _tag is a string")
  const mark = jsString(L.u.z3, THROUGH)
  if (tag.term.eqIdentity(mark)) return next(r.trace)
  const went = tag.term.eq(mark)
  return ite(
    L.u,
    went,
    onBranch(L, went, () => next(r.trace)),
    v,
    at,
  )
}

/** The proof side runs a loop over an array of unknown length at most this many times. */
const TRUNCATE = 4

/**
 * `for (const x of xs) { ... }` over an array: its body run once per element, in order, each iteration from the trace
 * the one before left. An array of known bound (every array of the search side) is run in full. On the proof side an
 * array of unknown length is run at most `TRUNCATE` times, the inputs kept to those it runs no longer: what the proof
 * side then finds is a real run, and what it proves holds of those inputs only.
 */
const forOf = (L: Lowering, style: Style, s: ts.ForOfStatement, env: Env, trace: Val, next: (t: Val) => Val): Val => {
  const z3 = L.u.z3
  if (s.awaitModifier !== undefined) throw new Unsupported("`for await` is not modeled", s)
  const init = s.initializer
  if (!ts.isVariableDeclarationList(init) || (init.flags & ts.NodeFlags.Const) === 0 || init.declarations.length !== 1)
    throw new Unsupported("a `for…of` loop in a computation is modeled with one `const`, `for (const x of xs)`", s)
  const name = init.declarations[0]!.name
  const xs = lowerExpr(L, s.expression, env)
  if (xs.kind !== "array") throw new Unsupported(`a \`for…of\` over a ${xs.kind} is not modeled`, s.expression)
  const known = xs.size ?? xs.maxSize
  const bound = known ?? L.u.bound ?? TRUNCATE
  // Run no further than the inputs go: on the search side, as its arrays do; on the proof side, which then proves nothing.
  if (known === undefined) L.u.assume(xs.length.le(bound))
  if (known === undefined && L.u.bound === undefined)
    L.u.truncated ??= `the proof side runs a loop in a computation at most ${TRUNCATE} times (${locate(s)})`
  const body = ts.isBlock(s.statement) ? s.statement.statements : [s.statement]
  const iteration = (k: number, t: Val): Val => {
    if (k === bound) return through(L, t)
    const scope = new Map(env)
    bindName(L, name, () => xs.elem(z3.Int.val(k)), scope)
    const inBounds = z3.Int.val(k).lt(xs.length)
    const ran = onBranch(L, inBounds, () => statements(L, style, body, 0, scope, t, (t2) => through(L, t2)))
    return ite(
      L.u,
      inBounds,
      onBranch(L, inBounds, () => whenThrough(L, ran, s, (t2) => iteration(k + 1, t2))),
      through(L, t),
      s,
    )
  }
  return whenThrough(L, iteration(0, trace), s, next)
}

const bindName = (L: Lowering, name: ts.BindingName, value: () => Val, scope: Map<string, () => Val>): void => bind(L, name, value, scope)

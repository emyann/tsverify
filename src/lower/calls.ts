// Calls: of a function of the program, of a value that is a function, and of a function a spec declares.
import ts from "typescript"
import { computationCall } from "../computation.ts"
import { truthy } from "../ops.ts"
import { purityOf } from "../purity.ts"
import { symbolicOf } from "../symbolic.ts"
import { type AssumedFn, coveringViews } from "../trust.ts"
import { type Env, type FunctionNode, Unsupported, type Val, identity, termId } from "../value.ts"
import { EMPTY, type Lowering, Unread, inSpec, lowerCall, lowerExpr, member, namespaceMember, optionally } from "../lower.ts"
import { roundedQuotient, standard } from "./library.ts"
import { arrayMethod } from "./arrays.ts"
import { stringMethod } from "./strings.ts"
import { boundArgs, effectsOfValue } from "./closures.ts"

export const call = (L: Lowering, e: ts.CallExpression, env: Env): Val => {
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

export const nameOf = (fn: FunctionNode): string =>
  fn.name?.getText() ?? (ts.isVariableDeclaration(fn.parent) ? fn.parent.name.getText() : "a function")

/** A declared function as a value: calling it is `assumedCall`. */
export const assumedFn = (L: Lowering, a: AssumedFn): Val => ({
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

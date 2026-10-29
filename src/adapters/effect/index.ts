// The Effect 4 adapter: the only place the verifier knows Effect's names.
//
// - `Effect.fn(name)(function* ...)` and `Effect.fn(function* ...)` define a
//   computation whose steps are its `yield*`s.
// - `yield*` of a `Context.Service` key gives the service: its methods that
//   return an Effect are operations of the service, by its name.
// - `Effect.succeed(v)`, `Effect.fail(e)`, `Effect.void`: computations that end
//   at once; `Effect.sync(f)`, one that ends with what `f` returns.
// - `Effect.gen(function* ...)`: a computation, as `Effect.fn` defines one; a
//   function that returns an Effect is a computation too, run when called.
// - `Effect.map`, `flatMap` (continue on success), `catch`, `catchTag` (handle
//   a failure), each with its effect first or last; `x.pipe(f, g)` and
//   `pipe(x, f, g)`, which apply each function to what the last one gave.
// - `Effect.fnUntraced`, read as `Effect.fn`.
// - `new E(fields)` for a class built by `Schema.TaggedError` or
//   `Data.TaggedError`: the record of its fields and its `_tag`.
//
// Pinned to effect 4.0.6. What it does not name (`Effect.try`, `forEach`,
// concurrency, resources, defects) is refused by the core where the code uses
// it, naming the function.
import ts from "typescript"
import { type Adapter, packageExport } from "../../adapter.ts"
import { computationCall, failure, onFailure, onSuccess, runComp, success } from "../../computation.ts"
import type { Lowering } from "../../lower.ts"
import { applyValue, lowerExpr } from "../../lower.ts"
import { ite, strictEq } from "../../ops.ts"
import { symbolicOf } from "../../symbolic.ts"
import { type Env, Unsupported, type Val, lazyRecord } from "../../value.ts"

/**
 * `Effect.fail` for what `node` names in the effect package. A name JavaScript reserves is declared with an underscore
 * and exported without one (`void_ as void`, `catch_ as catch`, `try_ as try`): it is named as written.
 */
const effectName = (checker: ts.TypeChecker, node: ts.Node): string | undefined => {
  const x = packageExport(checker, node)
  return x?.pkg === "effect" ? `${x.module}.${x.name.replace(/_$/, "")}` : undefined
}

/** The generator of `Effect.fn(name)(function* ...)` or `Effect.fn(function* ...)`. */
const generatorOf = (checker: ts.TypeChecker, e: ts.Node): ts.FunctionExpression | undefined => {
  if (!ts.isCallExpression(e)) return undefined
  const isFn = (callee: ts.Expression) => {
    const name = effectName(checker, callee)
    return name === "Effect.fn" || name === "Effect.fnUntraced"
  }
  const gen = e.arguments[0]
  const named = ts.isCallExpression(e.expression) && isFn(e.expression.expression)
  if (!(named || isFn(e.expression)) || gen === undefined || !ts.isFunctionExpression(gen) || gen.asteriskToken === undefined)
    return undefined
  if (e.arguments.length > 1) throw new Unsupported("`Effect.fn` with pipeline arguments after the body is not modeled", e)
  return gen
}

const comp = (run: Extract<Val, { kind: "comp" }>["run"]): Val => ({ kind: "comp", run })
const builtin = (name: string, call: (args: ReadonlyArray<Val>, at: ts.Node) => Val): Val => ({ kind: "builtin", name, call })

/** A function Effect writes both ways, `f(self, g)` and `f(g)(self)`. */
const dual = (name: string, apply: (self: Val, g: Val, at: ts.Node) => Val): Val =>
  builtin(name, (args, at) => {
    if (args.length === 2) return apply(args[0]!, args[1]!, at)
    if (args.length === 1) return builtin(`${name}(f)`, ([self], at2) => apply(self!, args[0]!, at2))
    throw new Unsupported(`\`${name}\` with ${args.length} arguments is not modeled`, at)
  })

/** `self`, its failure with `_tag` equal to `tag` handled by `f`; any other failure passes. */
const caughtTag = (L: Lowering, self: Val, tag: Val, f: Val, at: ts.Node): Val => {
  if (tag.kind !== "str") throw new Unsupported("`Effect.catchTag` of one tag, a string: several tags are not modeled", at)
  return comp((trace) =>
    onFailure(L, runComp(self, trace, at), at, (error, t) => {
      const own = error.kind === "record" ? error.field("_tag") : undefined
      if (own === undefined) throw new Unsupported("`Effect.catchTag` of an error with no `_tag`", at)
      const handled = runComp(applyValue(L, f, [error], at), t, at)
      const passed = { outcome: failure(L, error), trace: t }
      const matched = strictEq(L.u, own, tag, at)
      if (L.u.z3.isTrue(matched)) return handled
      if (L.u.z3.isFalse(matched)) return passed
      const merged = ite(L.u, matched, ranOf(handled), ranOf(passed), at)
      if (merged.kind !== "record") throw new Error("a computation's end is a record")
      return { outcome: merged.field("outcome")!, trace: merged.field("trace")! }
    }),
  )
}
const ranOf = (r: { readonly outcome: Val; readonly trace: Val }): Val =>
  lazyRecord((n) => (n === "outcome" ? r.outcome : n === "trace" ? r.trace : undefined))

/** A class whose `extends` is `Schema.TaggedError<...>()(tag, fields)` or `Data.TaggedError(tag)<...>`. */
const isTaggedErrorClass = (checker: ts.TypeChecker, decl: ts.ClassDeclaration): boolean => {
  let base: ts.Expression | undefined = decl.heritageClauses?.find((h) => h.token === ts.SyntaxKind.ExtendsKeyword)?.types[0]?.expression
  while (base !== undefined && ts.isCallExpression(base)) base = base.expression
  const name = base === undefined ? undefined : effectName(checker, base)
  return name === "Schema.TaggedError" || name === "Data.TaggedError"
}

export const effectAdapter: Adapter = {
  name: "effect",
  computation: (L, e) => {
    const gen = generatorOf(L.checker, e)
    if (gen !== undefined) return { node: gen, style: "gen" }
    // A plain function that returns an Effect: running it runs the Effect it returns.
    if ((ts.isArrowFunction(e) || ts.isFunctionExpression(e) || ts.isFunctionDeclaration(e)) && e.asteriskToken === undefined && e.body !== undefined) {
      const sig = L.checker.getSignatureFromDeclaration(e)
      const returns = sig === undefined ? undefined : L.checker.getReturnTypeOfSignature(sig)
      if (returns !== undefined && effectAdapter.operation?.(L, returns) !== undefined) return { node: e, style: "returns" }
    }
    return undefined
  },
  operation: (L, returns) => {
    const sym = returns.getSymbol()
    const decl = sym?.declarations?.[0]
    if (sym?.name !== "Effect" || decl === undefined || !/\/node_modules\/effect\/dist\/Effect\.d\.ts$/.test(decl.getSourceFile().fileName))
      return undefined
    const [success, failure] = L.checker.getTypeArguments(returns as ts.TypeReference)
    if (success === undefined) return undefined
    return { success, failure }
  },
  operand: (L, operand, _env) => {
    // `yield* Journal`: a service key. Its value is the service, the same each time it is asked.
    const t = L.checker.getTypeAtLocation(operand)
    const service = L.checker.getPropertyOfType(t, "Service")
    const key = L.checker.getPropertyOfType(t, "key")
    const decl = service?.declarations?.[0]
    if (service === undefined || key === undefined || decl === undefined || !/\/node_modules\/effect\/dist\/Context\.d\.ts$/.test(decl.getSourceFile().fileName))
      return undefined
    const name = operand.getText()
    const memo = `service:${name}`
    let handle = L.opaque.get(memo)
    if (handle === undefined) {
      handle = symbolicOf(L, L.checker.getTypeOfSymbolAtLocation(service, operand), [name], [], operand)
      L.opaque.set(memo, handle)
    }
    const h = handle
    return comp((trace) => ({ outcome: success(L, h), trace }))
  },
  expr: (L: Lowering, e: ts.Expression, env: Env) => {
    const gen = generatorOf(L.checker, e)
    if (gen !== undefined) return { kind: "builtin", name: "Effect.fn", call: (args, at) => computationCall(L, gen, "gen", env, args, at) }
    if (ts.isNewExpression(e)) {
      let sym = L.checker.getSymbolAtLocation(e.expression)
      if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = L.checker.getAliasedSymbol(sym)
      const decl = sym?.valueDeclaration
      if (decl === undefined || !ts.isClassDeclaration(decl) || !isTaggedErrorClass(L.checker, decl)) return undefined
      const tag = L.checker.getPropertyOfType(L.checker.getTypeAtLocation(e), "_tag")
      const tagType = tag === undefined ? undefined : L.checker.getTypeOfSymbol(tag)
      if (tagType === undefined || !tagType.isStringLiteral()) throw new Unsupported("a tagged error whose `_tag` is no string literal", e)
      const args = (e.arguments ?? []).map((a) => lowerExpr(L, a, env))
      const fields = args[0]
      if (args.length > 1 || (fields !== undefined && fields.kind !== "record"))
        throw new Unsupported("a tagged error is built from one object of its fields", e)
      const tagValue: Val = { kind: "str", term: L.u.z3.String.val(tagType.value) }
      return lazyRecord((n) => (n === "_tag" ? tagValue : fields?.kind === "record" ? fields.field(n) : undefined))
    }
    if (!ts.isIdentifier(e) && !ts.isPropertyAccessExpression(e)) return undefined
    // `x.pipe(f, g)`: each function applied to what the one before gave, from `x`.
    if (ts.isPropertyAccessExpression(e) && e.name.text === "pipe" && effectName(L.checker, e) === "Pipeable.pipe") {
      const self = lowerExpr(L, e.expression, env)
      return builtin("pipe", (fs, at) => fs.reduce((x, f) => applyValue(L, f, [x], at), self))
    }
    switch (effectName(L.checker, e)) {
      case "Function.pipe":
        return builtin("pipe", ([self, ...fs], at) => fs.reduce((x, f) => applyValue(L, f, [x], at), self ?? { kind: "nullish", which: "undefined" }))
      case "Effect.gen":
        return builtin("Effect.gen", (args, at) => {
          const g = args.at(-1)
          if (args.length !== 1) throw new Unsupported("`Effect.gen` with options is not modeled", at)
          if (g?.kind !== "fn" || !(ts.isFunctionExpression(g.node) && g.node.asteriskToken !== undefined))
            throw new Unsupported("`Effect.gen` of a generator function written in place, `function* () { ... }`", at)
          return computationCall(L, g.node, "gen", g.env, [], at)
        })
      case "Effect.sync":
        return builtin("Effect.sync", ([f], at) => comp((trace) => ({ outcome: success(L, applyValue(L, f!, [], at)), trace })))
      case "Effect.map":
        return dual("Effect.map", (self, f, at) =>
          comp((trace) => onSuccess(L, runComp(self, trace, at), at, (v, t) => ({ outcome: success(L, applyValue(L, f, [v], at)), trace: t }))),
        )
      case "Effect.flatMap":
        return dual("Effect.flatMap", (self, f, at) => comp((trace) => onSuccess(L, runComp(self, trace, at), at, (v, t) => runComp(applyValue(L, f, [v], at), t, at))))
      case "Effect.catch":
        return dual("Effect.catch", (self, f, at) => comp((trace) => onFailure(L, runComp(self, trace, at), at, (err, t) => runComp(applyValue(L, f, [err], at), t, at))))
      case "Effect.catchTag":
        return builtin("Effect.catchTag", (args, at) => {
          const first = args[0]
          const [self, rest] = first?.kind === "comp" ? [first, args.slice(1)] : [undefined, args]
          if (rest.length !== 2) throw new Unsupported("`Effect.catchTag` with a handler for the other errors is not modeled", at)
          const [tag, f] = rest as [Val, Val]
          return self !== undefined ? caughtTag(L, self, tag, f, at) : builtin("Effect.catchTag(tag, f)", ([s], at2) => caughtTag(L, s!, tag, f, at2))
        })
      case "Effect.succeed":
        return { kind: "builtin", name: "Effect.succeed", call: ([v]) => comp((trace) => ({ outcome: success(L, v ?? { kind: "nullish", which: "undefined" }), trace })) }
      case "Effect.fail":
        return { kind: "builtin", name: "Effect.fail", call: ([err]) => comp((trace) => ({ outcome: failure(L, err ?? { kind: "nullish", which: "undefined" }), trace })) }
      case "Effect.void":
        return comp((trace) => ({ outcome: success(L, { kind: "nullish", which: "undefined" }), trace }))
      default:
        return undefined
    }
  },
}

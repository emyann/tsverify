// The Effect 4 adapter: the only place the verifier knows Effect's names.
//
// - `Effect.fn(name)(function* ...)` and `Effect.fn(function* ...)` define a
//   computation whose steps are its `yield*`s.
// - `yield*` of a `Context.Service` key gives the service: its methods that
//   return an Effect are operations of the service, by its name.
// - `Effect.succeed(v)`, `Effect.fail(e)`, `Effect.void`: computations that end
//   at once.
// - `new E(fields)` for a class built by `Schema.TaggedError` or
//   `Data.TaggedError`: the record of its fields and its `_tag`.
//
// Pinned to effect 4.0.6. What it does not name (pipe, map, catch, concurrency,
// resources) is refused by the core where the code uses it.
import ts from "typescript"
import { type Adapter, packageExport } from "../../adapter.ts"
import { computationCall, success, failure } from "../../computation.ts"
import type { Lowering } from "../../lower.ts"
import { lowerExpr } from "../../lower.ts"
import { symbolicOf } from "../../symbolic.ts"
import { type Env, Unsupported, type Val, lazyRecord } from "../../value.ts"

const effectName = (checker: ts.TypeChecker, node: ts.Node): string | undefined => {
  const x = packageExport(checker, node)
  return x?.pkg === "effect" ? `${x.module}.${x.name}` : undefined
}

/** The generator of `Effect.fn(name)(function* ...)` or `Effect.fn(function* ...)`. */
const generatorOf = (checker: ts.TypeChecker, e: ts.Node): ts.FunctionExpression | undefined => {
  if (!ts.isCallExpression(e)) return undefined
  const isFn = (callee: ts.Expression) => effectName(checker, callee) === "Effect.fn"
  const gen = e.arguments[0]
  const named = ts.isCallExpression(e.expression) && isFn(e.expression.expression)
  if (!(named || isFn(e.expression)) || gen === undefined || !ts.isFunctionExpression(gen) || gen.asteriskToken === undefined)
    return undefined
  if (e.arguments.length > 1) throw new Unsupported("`Effect.fn` with pipeline arguments after the body is not modeled", e)
  return gen
}

const comp = (run: Extract<Val, { kind: "comp" }>["run"]): Val => ({ kind: "comp", run })

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
    return gen === undefined ? undefined : { node: gen, style: "gen" }
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
    switch (effectName(L.checker, e)) {
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

// The core's own adapter: what plain TypeScript's runtime gives every program.
//
// - `new Date()` and `Date.now()`: the time, an unknown value per call (any time is covered).
// - `new C(message?)` for a class of the program that extends `Error` and only
//   declares fields with initializers: a record of those fields and `message`.
import ts from "typescript"
import { type Adapter, packageExport } from "../adapter.ts"
import { emptyEnv, later, lowerExpr } from "../lower.ts"
import { Unsupported, type Val, lazyRecord } from "../value.ts"

const isLib = (checker: ts.TypeChecker, node: ts.Node, name: string): boolean => {
  const x = packageExport(checker, node)
  return x?.pkg === "typescript" && x.name === name
}

export const tsAdapter: Adapter = {
  name: "ts",
  expr: (L, e, env) => {
    const z3 = L.u.z3
    const freshStr = (what: string): Val => ({ kind: "str", term: L.u.leaf([L.u.given(what), "$"], "str", []) as never })
    const freshNum = (what: string): Val => {
      const base = L.u.given(what)
      const cls = L.u.leaf([base, "~cls"], "int", []) as never as ReturnType<typeof z3.Int.val>
      L.u.assume(cls.eq(0)) // a time is finite
      return { kind: "num", cls, real: L.u.leaf([base, "$"], "num", []) as never }
    }
    const clock = () => {
      if (L.mode === "spec")
        throw new Unsupported(
          "spec code is deterministic and does not read the clock: read the time in the program and pass it to the law",
          e,
        )
    }
    if (ts.isNewExpression(e) && ts.isIdentifier(e.expression) && isLib(L.checker, e.expression, "Date")) {
      clock()
      if ((e.arguments?.length ?? 0) > 0) throw new Unsupported("`new Date(x)` is not modeled; `new Date()` is", e)
      L.u.notes.add("The time (`new Date()`, `Date.now()`) is an unknown value per call: any time is covered.")
      const builtin = (name: string, v: () => Val): Val => ({ kind: "builtin", name, call: () => v() })
      return lazyRecord((n) =>
        n === "toISOString"
          ? builtin("Date.toISOString", () => freshStr("date.iso"))
          : n === "getTime"
            ? builtin("Date.getTime", () => freshNum("date.ms"))
            : undefined,
      )
    }
    if (
      ts.isCallExpression(e) &&
      ts.isPropertyAccessExpression(e.expression) &&
      e.expression.name.text === "now" &&
      ts.isIdentifier(e.expression.expression) &&
      isLib(L.checker, e.expression.expression, "Date")
    ) {
      clock()
      L.u.notes.add("The time (`new Date()`, `Date.now()`) is an unknown value per call: any time is covered.")
      return freshNum("date.now")
    }
    if (ts.isNewExpression(e)) return errorOf(L, e, env)
    return undefined
  },
}

/** `new C(message?)` for an `Error` subclass of the program whose members are fields with initializers. */
const errorOf = (
  L: Parameters<NonNullable<Adapter["expr"]>>[0],
  e: ts.NewExpression,
  env: Parameters<NonNullable<Adapter["expr"]>>[2],
): Val | undefined => {
  let sym = L.checker.getSymbolAtLocation(e.expression)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = L.checker.getAliasedSymbol(sym)
  const decl = sym?.valueDeclaration
  if (decl === undefined || !ts.isClassDeclaration(decl) || decl.getSourceFile().isDeclarationFile) return undefined
  const base = decl.heritageClauses?.find((h) => h.token === ts.SyntaxKind.ExtendsKeyword)?.types[0]?.expression
  if (base === undefined || !ts.isIdentifier(base) || !isLib(L.checker, base, "Error")) return undefined
  const fields = new Map<string, () => Val>()
  for (const m of decl.members) {
    if (ts.isPropertyDeclaration(m) && m.initializer !== undefined && ts.isIdentifier(m.name)) {
      if (m.modifiers?.some((x) => x.kind === ts.SyntaxKind.StaticKeyword)) continue
      const init = m.initializer
      fields.set(
        m.name.text,
        later(L, () => lowerExpr(L, init, emptyEnv)),
      )
    } else throw new Unsupported("an `Error` subclass is modeled when its members are fields with initializers", m)
  }
  const args = (e.arguments ?? []).map((a) => lowerExpr(L, a, env))
  if (args.length > 1) throw new Unsupported("an `Error` subclass is modeled with a message and nothing else", e)
  return lazyRecord((n) => (n === "message" ? (args[0] ?? { kind: "str", term: L.u.z3.String.val("") }) : fields.get(n)?.()))
}

// What a verification takes on trust: the `assume(...)` declarations in force,
// read from source, and the report of the ones a verification leaned on.
//
// A declaration is in force when its module is part of the program: the spec
// imports it, or imports a pack that holds it (as Verus's `vstd` holds the
// standard library's). A function of the program or of a package that the
// verifier cannot read is refused unless one is in force; one that is in force
// replaces the function's body, read or not (Verus's `external_body`).
import path from "node:path"
import ts from "typescript"
import { packageExport } from "./adapter.ts"
import { CONTRACT_MODULE, type Project, declared, functionOf, unwrap } from "./project.ts"
import { type FunctionNode, Unsupported, locate } from "./value.ts"

/** One `assume(fn, …)`: the view its laws are written for, and the laws. */
export interface View {
  /** `file:line` of the declaration. */
  readonly where: string
  /** The parameter types the laws are written for: a call is covered when its arguments' types are assignable to them. */
  readonly params: ReadonlyArray<ts.Type>
  readonly ensures: ReadonlyArray<{ readonly name: string; readonly law: FunctionNode }>
}

/** A function declared by one or more `assume(...)`. */
export interface AssumedFn {
  readonly symbol: ts.Symbol
  /** `accountOf`, or `uniq (lodash-es)` for a package's. */
  readonly name: string
  /** Its body in the program, when the program has one: where purity is checked. */
  readonly body: FunctionNode | undefined
  readonly pure: boolean
  readonly views: ReadonlyArray<View>
}

export interface Assumptions {
  readonly all: ReadonlyArray<AssumedFn>
  /** The declaration for what `callee` names, if one is in force. */
  readonly of: (callee: ts.Expression) => AssumedFn | undefined
}

/** One entry of a report's trusted base: a declaration a verification leaned on. */
export interface Trusted {
  readonly name: string
  /** Where it is declared, `file:line` each. */
  readonly declared: ReadonlyArray<string>
  /**
   * `checked`: declared pure, and the check read its source and found it so. `unchecked`: declared pure, with no source
   * to read (a package's). `impure`: declared `pure: false`, a fresh result per call.
   */
  readonly purity: "checked" | "unchecked" | "impure"
  /** The laws assumed at its calls, without proof. */
  readonly laws: ReadonlyArray<string>
  /** When the purity check ran: the functions of the program it read. */
  readonly read?: ReadonlyArray<string>
}

export const PURITY_TRUSTS = [
  "a property read runs no getter",
  "a module constant it reads is never changed by other code",
  "it terminates",
] as const

const resolved = (checker: ts.TypeChecker, e: ts.Expression): ts.Symbol | undefined => {
  let x = unwrap(e)
  if (ts.isExpressionWithTypeArguments(x)) x = x.expression
  const at = ts.isPropertyAccessExpression(x) ? x.name : x
  let sym = checker.getSymbolAtLocation(at)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
  return sym
}

const bodyOf = (sym: ts.Symbol): FunctionNode | undefined => {
  const d = sym.valueDeclaration
  if (d === undefined || d.getSourceFile().isDeclarationFile) return undefined
  if (ts.isFunctionDeclaration(d) && d.body !== undefined) return d
  if (ts.isVariableDeclaration(d) && d.initializer !== undefined && (d.parent.flags & ts.NodeFlags.Const) !== 0) {
    const init = unwrap(d.initializer)
    if (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) return init
  }
  return undefined
}

/** The parameter types of the view: `A` of `assume<A, R>`, read from the declaration's resolved type. */
const viewParams = (checker: ts.TypeChecker, call: ts.CallExpression): Array<ts.Type> => {
  const t = checker.getTypeAtLocation(call)
  const fnProp = checker.getPropertyOfType(t, "fn")
  const sig = fnProp === undefined ? undefined : checker.getTypeOfSymbol(fnProp).getCallSignatures()[0]
  if (sig === undefined) throw new Unsupported("an assumption's function has no call signature to read its view from", call)
  const ps = sig.getParameters()
  const rest = ps.length === 1 ? ps[0]!.valueDeclaration : undefined
  if (rest !== undefined && ts.isParameter(rest) && rest.dotDotDotToken !== undefined) {
    const tuple = checker.getTypeOfSymbol(ps[0]!)
    if (checker.isTupleType(tuple)) return [...checker.getTypeArguments(tuple as ts.TypeReference)]
  }
  return ps.map((p) => checker.getTypeOfSymbol(p))
}

/**
 * Every `const x = assume(...)` at the top of a module of the program: a spec's, or a pack's it imports, a package's
 * among them when the package ships the pack as source (tsverify's own, `tsverify/packs/lodash`). A declaration file
 * holds no law to read.
 */
export const readAssumptions = (project: Project): Assumptions => {
  const { checker, program } = project
  const bySymbol = new Map<ts.Symbol, { name: string; body: FunctionNode | undefined; pure: boolean; views: Array<View>; pureAt: string }>()
  for (const sf of program.getSourceFiles()) {
    if (sf.isDeclarationFile) continue
    for (const stmt of sf.statements) {
      if (!ts.isVariableStatement(stmt)) continue
      for (const d of stmt.declarationList.declarations) {
        const init = d.initializer === undefined ? undefined : unwrap(d.initializer)
        if (init === undefined || !ts.isCallExpression(init) || !declared(checker, init.expression, CONTRACT_MODULE, "assume")) continue
        const [fnArg, specArg] = init.arguments
        if (fnArg === undefined || specArg === undefined || !ts.isObjectLiteralExpression(unwrap(specArg)))
          throw new Unsupported("an assumption is `assume(fn, { pure, ensures? })`, written in place", init)
        const sym = resolved(checker, fnArg)
        if (sym === undefined) throw new Unsupported("an assumption names a function the type checker can resolve", fnArg)
        let pure: boolean | undefined
        const ensures: Array<{ name: string; law: FunctionNode }> = []
        for (const p of (unwrap(specArg) as ts.ObjectLiteralExpression).properties) {
          if (!ts.isPropertyAssignment(p) || !ts.isIdentifier(p.name)) throw new Unsupported("an assumption's parts are `pure` and `ensures`, written in place", p)
          if (p.name.text === "pure") {
            const v = unwrap(p.initializer)
            if (v.kind !== ts.SyntaxKind.TrueKeyword && v.kind !== ts.SyntaxKind.FalseKeyword)
              throw new Unsupported("`pure` is `true` or `false`, written in place", p)
            pure = v.kind === ts.SyntaxKind.TrueKeyword
          } else if (p.name.text === "ensures") {
            const laws = unwrap(p.initializer)
            if (!ts.isObjectLiteralExpression(laws)) throw new Unsupported("`ensures` is an object of named laws, written in place", p)
            for (const q of laws.properties) {
              if (ts.isShorthandPropertyAssignment(q)) ensures.push({ name: q.name.text, law: functionOf(checker, q.name) })
              else if (ts.isPropertyAssignment(q) && (ts.isIdentifier(q.name) || ts.isStringLiteral(q.name)))
                ensures.push({ name: q.name.text, law: functionOf(checker, q.initializer) })
              else throw new Unsupported("a law is `name: (args..., result) => boolean`", q)
            }
          } else throw new Unsupported(`an assumption has no part \`${p.name.text}\`; it has \`pure\` and \`ensures\``, p)
        }
        if (pure === undefined) throw new Unsupported("an assumption says whether the function is pure: `pure: true` or `pure: false`", init)
        const where = where_(init)
        const view: View = { where, params: viewParams(checker, init), ensures }
        const known = bySymbol.get(sym)
        if (known !== undefined) {
          if (known.pure !== pure)
            throw new Unsupported(`\`${known.name}\` is declared \`pure: ${known.pure}\` at ${known.pureAt} and \`pure: ${pure}\` here; one function is pure or it is not`, init)
          known.views.push(view)
          continue
        }
        const pkg = packageOf(checker, unwrap(fnArg))
        bySymbol.set(sym, { name: pkg === undefined ? sym.name : `${sym.name} (${pkg})`, body: bodyOf(sym), pure, views: [view], pureAt: where })
      }
    }
  }
  const all: Array<AssumedFn> = [...bySymbol].map(([symbol, a]) => ({ symbol, name: a.name, body: a.body, pure: a.pure, views: a.views }))
  const index = new Map(all.map((a) => [a.symbol, a]))
  return {
    all,
    of: (callee) => {
      const sym = resolved(checker, callee)
      return sym === undefined ? undefined : index.get(sym)
    },
  }
}

/** The package a function is imported from, as the import names it (`lodash-es`), when it is a package's. */
const packageOf = (checker: ts.TypeChecker, e: ts.Expression): string | undefined => {
  const x = ts.isExpressionWithTypeArguments(e) ? e.expression : e
  const at = ts.isPropertyAccessExpression(x) ? x.expression : x
  const first = checker.getSymbolAtLocation(at)?.declarations?.[0]
  let n: ts.Node | undefined = first
  while (n !== undefined && !ts.isImportDeclaration(n)) n = n.parent
  if (n !== undefined && ts.isStringLiteral(n.moduleSpecifier) && !n.moduleSpecifier.text.startsWith(".")) return n.moduleSpecifier.text
  return packageExport(checker, x)?.pkg
}

const where_ = (node: ts.Node): string => {
  const at = locate(node)
  const cwd = process.cwd()
  return at.startsWith(cwd + path.sep) ? at.slice(cwd.length + 1) : at
}

/**
 * The views of `a` that cover a call with `args`: as many arguments as the view has parameters, each assignable to its
 * parameter. A call with fewer may be another form of the function (lodash's `clamp(n, upper)`), which the view's laws
 * do not describe.
 */
export const coveringViews = (checker: ts.TypeChecker, a: AssumedFn, args: ReadonlyArray<ts.Expression>): ReadonlyArray<View> =>
  a.views.filter(
    (v) =>
      args.length === v.params.length &&
      args.every((arg, i) => checker.isTypeAssignableTo(checker.getTypeAtLocation(arg), v.params[i]!)),
  )

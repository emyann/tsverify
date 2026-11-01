// What a verification takes on trust: the `assume(...)` declarations in force,
// read from source, and the report of the ones a verification leaned on.
//
// A declaration is in force when its module is part of the program: the spec
// imports it, or imports a pack that holds it (as Verus's `vstd` holds the
// standard library's). A function of the program or of a package that the
// verifier cannot read is refused unless one is in force; one that is in force
// replaces the function's body, read or not (Verus's `external_body`).
//
// A function that implements a spec is declared by its spec, with no `assume`:
// a call takes its spec's laws where its `requires` holds, as Dafny's callers
// take a method's, and its own verification proves them. Its body is read
// instead where it is not pure, or where it leads back to the function being
// verified, whose proof would then lean on what it proves.
import path from "node:path"
import ts from "typescript"
import { packageExport } from "./adapter.ts"
import { CONTRACT_MODULE, type Project, declared, implementedSpec, isImplementation, lawOf } from "./project.ts"
import { purityOf } from "./purity.ts"
import { functionIn, hasSource, symbolOf, unwrap } from "./resolve.ts"
import { type FunctionNode, Unsupported, locate } from "./value.ts"

/** One `assume(fn, …)`: the view its laws are written for, and the laws. */
export interface View {
  /** `file:line` of the declaration. */
  readonly where: string
  /** The parameter types the laws are written for: a call is covered when its arguments' types are assignable to them. */
  readonly params: ReadonlyArray<ts.Type>
  readonly ensures: ReadonlyArray<{ readonly name: string; readonly law: FunctionNode; readonly description?: string }>
  /**
   * Where the function implements a spec, the spec's `requires`: its laws are what the spec proves of it, so each holds
   * at a call only where this does.
   */
  readonly requires?: FunctionNode
  /** How few arguments a call may give, the rest left `undefined`: all of them when unset. */
  readonly least?: number
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
  /** Where it is declared by the spec it implements, and no `assume`: the spec's name. Its laws are proved on their own. */
  readonly spec?: string
}

export interface Assumptions {
  readonly all: ReadonlyArray<AssumedFn>
  /** The declaration for what `callee` names, if one is in force. */
  readonly of: (callee: ts.Expression) => AssumedFn | undefined
  /**
   * The declarations in force while `target` is verified: a function declared by its spec is read instead, at its
   * calls, where its source leads back to `target`, or where it is not pure.
   */
  readonly forTarget: (target: ts.Node) => Assumptions
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
  /** The laws assumed at its calls: without proof, or, where it is declared by its spec, proved by that spec's verification. */
  readonly laws: ReadonlyArray<string>
  /** Where it is declared by the spec it implements: the spec's name. */
  readonly spec?: string
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
  return symbolOf(checker, ts.isPropertyAccessExpression(x) ? x.name : x)
}

/** The source of a function an assumption declares, where the program has it. */
const bodyOf = (sym: ts.Symbol): FunctionNode | undefined => {
  const d = sym.valueDeclaration
  return d !== undefined && hasSource(d) ? functionIn(d) : undefined
}

/** The parameter types of the view: `A` of `assume<A, R>`, read from the declaration's resolved type. */
const viewParams = (checker: ts.TypeChecker, call: ts.CallExpression): Array<ts.Type> => {
  const t = checker.getTypeAtLocation(call)
  const fnProp = checker.getPropertyOfType(t, "fn")
  const sig = fnProp === undefined ? undefined : checker.getTypeOfSymbol(fnProp).getCallSignatures()[0]
  if (sig === undefined) throw new Unsupported("an assumption's function has no call signature to read its view from", call)
  return paramsOf(checker, sig)
}

/** How few arguments a call of `sig` may give: one past its last parameter that is not optional. Every one, with a rest. */
const leastOf = (checker: ts.TypeChecker, sig: ts.Signature): number | undefined => {
  const ps = sig.getParameters().map((p) => p.valueDeclaration)
  if (ps.some((d) => d !== undefined && ts.isParameter(d) && d.dotDotDotToken !== undefined)) return undefined
  let least = 0
  ps.forEach((d, i) => {
    if (d === undefined || !ts.isParameter(d) || !checker.isOptionalParameter(d)) least = i + 1
  })
  return least
}

/** A signature's parameter types, a rest of a tuple spread into its elements. */
const paramsOf = (checker: ts.TypeChecker, sig: ts.Signature): Array<ts.Type> => {
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
 * among them when the package ships the pack as source (tsverify's own, `@emyann/tsverify/packs/lodash`). A declaration file
 * holds no law to read.
 */
export const readAssumptions = (project: Project): Assumptions => {
  const { checker, program } = project
  const bySymbol = new Map<
    ts.Symbol,
    { name: string; body: FunctionNode | undefined; pure: boolean; views: Array<View>; pureAt: string; spec?: string }
  >()
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
        const ensures: Array<{ name: string; law: FunctionNode; description?: string }> = []
        for (const p of (unwrap(specArg) as ts.ObjectLiteralExpression).properties) {
          if (!ts.isPropertyAssignment(p) || !ts.isIdentifier(p.name))
            throw new Unsupported("an assumption's parts are `pure` and `ensures`, written in place", p)
          if (p.name.text === "pure") {
            const v = unwrap(p.initializer)
            if (v.kind !== ts.SyntaxKind.TrueKeyword && v.kind !== ts.SyntaxKind.FalseKeyword)
              throw new Unsupported("`pure` is `true` or `false`, written in place", p)
            pure = v.kind === ts.SyntaxKind.TrueKeyword
          } else if (p.name.text === "ensures") {
            const laws = unwrap(p.initializer)
            if (!ts.isObjectLiteralExpression(laws)) throw new Unsupported("`ensures` is an object of named laws, written in place", p)
            for (const q of laws.properties) {
              if (ts.isShorthandPropertyAssignment(q)) ensures.push({ name: q.name.text, ...lawOf(checker, q.name) })
              else if (ts.isPropertyAssignment(q) && (ts.isIdentifier(q.name) || ts.isStringLiteral(q.name)))
                ensures.push({ name: q.name.text, ...lawOf(checker, q.initializer) })
              else
                throw new Unsupported(
                  "a law is `name: ({ input: [args...], output }) => boolean`, or `name: { description, condition }`",
                  q,
                )
            }
          } else throw new Unsupported(`an assumption has no part \`${p.name.text}\`; it has \`pure\` and \`ensures\``, p)
        }
        if (pure === undefined)
          throw new Unsupported("an assumption says whether the function is pure: `pure: true` or `pure: false`", init)
        // A function that implements a spec is declared by it: an assumption of it would say again, or more than, what
        // its verification proves. A computation's spec is not taken at a call yet: an assumption of one takes only its
        // laws, each where its `requires` holds.
        const spec = implementedSpec(checker, sym)
        if (spec !== undefined && !spec.computation)
          throw new Unsupported(
            `\`${sym.name}\` implements \`${spec.name}\`, and every call takes what that spec proves of it, where its \`requires\` holds: remove \`${d.name.getText()}\`, and add what a caller needs of it to the spec's \`ensures\``,
            init,
          )
        if (spec !== undefined)
          for (const l of ensures)
            if (!spec.ensures.some((e) => e.law === l.law))
              throw new Unsupported(
                `\`${d.name.getText()}\` assumes \`${l.name}\` of \`${sym.name}\`, which implements \`${spec.name}\` and is proved of its laws alone: name one of them here (the same declaration, in a module both import), or add this law to the spec's \`ensures\``,
                init,
              )
        const where = where_(init)
        const view: View = {
          where,
          params: viewParams(checker, init),
          ensures,
          ...(spec?.requires === undefined ? {} : { requires: spec.requires }),
        }
        const known = bySymbol.get(sym)
        if (known !== undefined) {
          if (known.pure !== pure)
            throw new Unsupported(
              `\`${known.name}\` is declared \`pure: ${known.pure}\` at ${known.pureAt} and \`pure: ${pure}\` here; one function is pure or it is not`,
              init,
            )
          known.views.push(view)
          continue
        }
        const pkg = packageOf(checker, unwrap(fnArg))
        bySymbol.set(sym, {
          name: pkg === undefined ? sym.name : `${sym.name} (${pkg})`,
          body: bodyOf(sym),
          pure,
          views: [view],
          pureAt: where,
        })
      }
    }
  }
  // Every function that implements a spec, declared by it: pure, checked from source, and its spec's laws at a call, each
  // where the spec's `requires` holds. A spec that cannot be read is its own verification's to refuse; its function is
  // read at its calls.
  for (const sf of program.getSourceFiles()) {
    if (sf.isDeclarationFile || sf.fileName.includes("/node_modules/")) continue
    for (const stmt of sf.statements) {
      if (!ts.isVariableStatement(stmt)) continue
      for (const d of stmt.declarationList.declarations) {
        if (!ts.isIdentifier(d.name) || !isImplementation(checker, d)) continue
        const sym = symbolOf(checker, d.name)
        if (sym === undefined || bySymbol.has(sym)) continue
        let spec: ReturnType<typeof implementedSpec>
        try {
          spec = implementedSpec(checker, sym)
        } catch (e) {
          if (e instanceof Unsupported) continue
          throw e
        }
        const sig = checker.getTypeOfSymbol(sym).getCallSignatures()[0]
        if (spec === undefined || spec.computation || sig === undefined) continue
        const where = where_(spec.at)
        const view: View = {
          where,
          params: paramsOf(checker, sig),
          ensures: spec.ensures,
          ...(leastOf(checker, sig) === undefined ? {} : { least: leastOf(checker, sig)! }),
          ...(spec.requires === undefined ? {} : { requires: spec.requires }),
        }
        bySymbol.set(sym, { name: sym.name, body: bodyOf(sym), pure: true, views: [view], pureAt: where, spec: spec.name })
      }
    }
  }
  const all: Array<AssumedFn> = [...bySymbol].map(([symbol, a]) => ({
    symbol,
    name: a.name,
    body: a.body,
    pure: a.pure,
    views: a.views,
    ...(a.spec === undefined ? {} : { spec: a.spec }),
  }))
  const index = new Map(all.map((a) => [a.symbol, a]))
  const of = (callee: ts.Expression): AssumedFn | undefined => {
    const sym = resolved(checker, callee)
    return sym === undefined ? undefined : index.get(sym)
  }
  const reach = new Map<FunctionNode, ReadonlySet<FunctionNode>>()
  /** The functions of the program `fn`'s source may call, through any number of others: what it leads to. */
  const leadsTo = (fn: FunctionNode): ReadonlySet<FunctionNode> => {
    const known = reach.get(fn)
    if (known !== undefined) return known
    const seen = new Set<FunctionNode>()
    const next: Array<ts.Node> = [fn]
    const visit = (n: ts.Node): void => {
      if (ts.isIdentifier(n)) {
        const v = symbolOf(checker, n)?.valueDeclaration
        const f = v !== undefined && hasSource(v) ? functionIn(v) : undefined
        if (f !== undefined && !seen.has(f)) {
          seen.add(f)
          next.push(f)
        }
      }
      ts.forEachChild(n, visit)
    }
    while (next.length > 0) visit(next.pop()!)
    reach.set(fn, seen)
    return seen
  }
  const forTarget = (target: ts.Node): Assumptions => {
    const read = new Map<AssumedFn, boolean>()
    const scoped = (callee: ts.Expression): AssumedFn | undefined => {
      const a = of(callee)
      if (a?.spec === undefined) return a
      let readInstead = read.get(a)
      if (readInstead === undefined) {
        // Taken by its spec while its own purity is read: a function it calls that leads back to it sees it so.
        read.set(a, false)
        readInstead =
          a.body === undefined ||
          a.body === target ||
          leadsTo(a.body).has(target as FunctionNode) ||
          !purityOf(checker, a.body, scoped).pure
        read.set(a, readInstead)
      }
      return readInstead ? undefined : a
    }
    return { all, of: scoped, forTarget }
  }
  return { all, of, forTarget }
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
 * The views of `a` that cover a call with `args`: as many arguments as the view has parameters, or as few as its
 * function requires where it says so (`least`, a spec's), each assignable to its parameter. A call with fewer may be
 * another form of the function (lodash's `clamp(n, upper)`), which the view's laws do not describe.
 */
export const coveringViews = (checker: ts.TypeChecker, a: AssumedFn, args: ReadonlyArray<ts.Expression>): ReadonlyArray<View> =>
  a.views.filter(
    (v) =>
      args.length >= (v.least ?? v.params.length) &&
      args.length <= v.params.length &&
      args.every((arg, i) => checker.isTypeAssignableTo(checker.getTypeAtLocation(arg), v.params[i]!)),
  )

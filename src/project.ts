// The TypeScript side: a program over the spec's files (with any file's text
// replaced, or a file added, in memory: how a planted bug is read), its
// diagnostics, and a contract read from source.
import { existsSync, readFileSync } from "node:fs"
import path from "node:path"
import ts from "typescript"
import { type FunctionNode, Unsupported } from "./value.ts"

export interface Project {
  readonly program: ts.Program
  readonly checker: ts.TypeChecker
}

export const loadProject = (
  files: ReadonlyArray<string>,
  tsconfig: string,
  overrides: ReadonlyMap<string, string> = new Map(),
): Project => {
  const read = ts.readConfigFile(tsconfig, ts.sys.readFile)
  if (read.error !== undefined) throw new Error(ts.flattenDiagnosticMessageText(read.error.messageText, "\n"))
  const options = ts.parseJsonConfigFileContent(read.config, ts.sys, path.dirname(tsconfig)).options
  const host = ts.createCompilerHost(options, true)
  if (overrides.size > 0) {
    const resolved = new Map([...overrides].map(([f, text]) => [path.resolve(f), text]))
    const getSourceFile = host.getSourceFile.bind(host)
    const readFile = host.readFile.bind(host)
    host.getSourceFile = (name, lang, onError, fresh) => {
      const text = resolved.get(path.resolve(name))
      return text === undefined ? getSourceFile(name, lang, onError, fresh) : ts.createSourceFile(name, text, lang, true)
    }
    host.readFile = (name) => resolved.get(path.resolve(name)) ?? readFile(name)
    const fileExists = host.fileExists.bind(host)
    host.fileExists = (name) => resolved.has(path.resolve(name)) || fileExists(name)
  }
  const program = ts.createProgram(files.map((f) => path.resolve(f)), options, host)
  return { program, checker: program.getTypeChecker() }
}

export const sourceFile = (project: Project, file: string): ts.SourceFile => {
  const sf = project.program.getSourceFile(path.resolve(file))
  if (sf === undefined) throw new Error(`${file} is not in the program; pass it to loadProject`)
  return sf
}

/** `tsc --noEmit` for one file: a verification never runs on code that does not type. */
export const diagnostics = (project: Project, file: string): ReadonlyArray<string> => {
  const sf = sourceFile(project, file)
  return [...project.program.getSyntacticDiagnostics(sf), ...project.program.getSemanticDiagnostics(sf)].map((d) => {
    const at = d.file !== undefined && d.start !== undefined ? d.file.getLineAndCharacterOfPosition(d.start) : undefined
    return `${file}${at === undefined ? "" : `:${at.line + 1}:${at.character + 1}`}: ${ts.flattenDiagnosticMessageText(d.messageText, "\n")}`
  })
}

/** The initializer of `export const <name> = ...`. */
export const exportedConst = (project: Project, file: string, name: string): ts.Expression => {
  for (const stmt of sourceFile(project, file).statements) {
    if (!ts.isVariableStatement(stmt) || !stmt.modifiers?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword)) continue
    for (const d of stmt.declarationList.declarations)
      if (ts.isIdentifier(d.name) && d.name.text === name && d.initializer !== undefined) return d.initializer
  }
  throw new Error(`no \`export const ${name}\` in ${file}`)
}

/** A module of tsverify's that a spec imports: `tsverify` and `tsverify/effect`. */
export type OwnModule = "contract" | "adapters/effect/contract"
export const CONTRACT_MODULE: OwnModule = "contract"
const EFFECT_CONTRACT_MODULE: OwnModule = "adapters/effect/contract"

/** The nearest `package.json` above each folder asked of: its folder and its `name`. */
const packages = new Map<string, { readonly root: string; readonly name: unknown } | undefined>()
const packageOf = (dir: string): { readonly root: string; readonly name: unknown } | undefined => {
  if (packages.has(dir)) return packages.get(dir)
  const manifest = path.join(dir, "package.json")
  let found: { readonly root: string; readonly name: unknown } | undefined
  if (existsSync(manifest)) {
    let name: unknown
    try {
      name = (JSON.parse(readFileSync(manifest, "utf8")) as { name?: unknown }).name
    } catch {
      name = undefined
    }
    found = { root: dir, name }
  } else {
    const up = path.dirname(dir)
    found = up === dir ? undefined : packageOf(up)
  }
  packages.set(dir, found)
  return found
}

/**
 * Whether `fileName` is tsverify's module `name`: its source (`src/contract.ts`) or what the build makes of it
 * (`dist/src/contract.d.ts`, `.js`), in whichever copy of the package the program reads — this one, a linked one or
 * one installed under `node_modules`.
 */
export const ownModule = (fileName: string, name: OwnModule): boolean => {
  const file = path.resolve(fileName)
  const pkg = packageOf(path.dirname(file))
  if (pkg?.name !== "tsverify") return false
  const rel = path.relative(pkg.root, file).replaceAll("\\", "/").replace(/\.d\.[cm]?ts$|\.[cm]?[jt]s$/, "")
  return rel === `src/${name}` || rel === `dist/src/${name}`
}

export interface ContractSource {
  readonly name: string
  /**
   * `function`: laws over the arguments and the result. `computation`: over the arguments, the outcome and the calls.
   * `lemma`: a statement over its arguments, its one law `holds`.
   */
  readonly kind: "function" | "computation" | "lemma"
  /**
   * What the contract is about, resolved through the type checker (the contract's link to the code): a function, or
   * the expression that defines a computation (`Effect.fn(...)(function* ...)`), which an adapter reads.
   */
  readonly target: ts.Node
  readonly requires: FunctionNode | undefined
  readonly ensures: ReadonlyArray<{ readonly name: string; readonly law: FunctionNode }>
}

/** What kind of contract `init` writes, when it is a call of this package's `contract`, `computation` or `lemma`. */
const contractKind = (checker: ts.TypeChecker, init: ts.Expression): ContractSource["kind"] | undefined => {
  if (!ts.isCallExpression(init)) return undefined
  if (declared(checker, init.expression, CONTRACT_MODULE, "lemma")) return "lemma"
  if (declared(checker, init.expression, CONTRACT_MODULE, "contract")) return "function"
  if (
    ts.isCallExpression(init.expression) &&
    (declared(checker, init.expression.expression, CONTRACT_MODULE, "computation") ||
      declared(checker, init.expression.expression, EFFECT_CONTRACT_MODULE, "computation"))
  )
    return "computation"
  return undefined
}

/**
 * The names of every contract `file` exports, in order: a spec's implementation (`export const f: Implementation<typeof
 * S> = ...`), a `contract(...)`, a computation's, a lemma.
 */
export const contractsIn = (project: Project, file: string): Array<string> =>
  sourceFile(project, file).statements.flatMap((stmt) =>
    ts.isVariableStatement(stmt) && stmt.modifiers?.some((m) => m.kind === ts.SyntaxKind.ExportKeyword)
      ? stmt.declarationList.declarations.flatMap((d) =>
          ts.isIdentifier(d.name) &&
          d.initializer !== undefined &&
          (isImplementation(project.checker, d) || contractKind(project.checker, unwrap(d.initializer)) !== undefined)
            ? [d.name.text]
            : [],
        )
      : [],
  )

/** Whether `d` is typed `Implementation<...>`, this package's. */
const isImplementation = (checker: ts.TypeChecker, d: ts.VariableDeclaration): boolean =>
  d.type !== undefined && ts.isTypeReferenceNode(d.type) && ts.isIdentifier(d.type.typeName) && declared(checker, d.type.typeName, CONTRACT_MODULE, "Implementation")

/**
 * The spec an implementation is typed by: `const f: Implementation<typeof S>` where `S` is `spec<F>({ ... })` of this
 * package or its Effect adapter; the call, and whether its function is a computation (an Effect program, or a function
 * that returns a promise).
 */
const specOf = (checker: ts.TypeChecker, d: ts.VariableDeclaration): { readonly call: ts.CallExpression; readonly computation: boolean } => {
  const t = d.type as ts.TypeReferenceNode
  const arg = t.typeArguments?.[0]
  if (arg === undefined || !ts.isTypeQueryNode(arg) || !ts.isIdentifier(arg.exprName))
    throw new Unsupported("an implementation names its spec: `Implementation<typeof ChargeSpec>`", t)
  let sym = checker.getSymbolAtLocation(arg.exprName)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
  const decl = sym?.valueDeclaration
  const call = decl !== undefined && ts.isVariableDeclaration(decl) && decl.initializer !== undefined ? unwrap(decl.initializer) : undefined
  const named = arg.exprName.text
  const notASpec = () =>
    new Unsupported(`\`${named}\` is no spec: write \`export const ${named} = spec<F>({ ... })\`, with \`spec\` from "tsverify" (or "tsverify/effect" for an Effect program)`, arg)
  if (call === undefined || !ts.isCallExpression(call)) throw notASpec()
  const effect = declared(checker, call.expression, EFFECT_CONTRACT_MODULE, "spec")
  if (!effect && !declared(checker, call.expression, CONTRACT_MODULE, "spec")) throw notASpec()
  const fnType = call.typeArguments?.[0]
  if (fnType === undefined) throw new Unsupported("a spec names the function's type: `spec<(x: X) => Y>({ ... })`", call)
  const returns = checker.getTypeFromTypeNode(fnType).getCallSignatures()[0]?.getReturnType()
  const promised = returns !== undefined && checker.getPropertyOfType(returns, "then") !== undefined
  return { call, computation: effect || promised }
}

/**
 * Reads, from source, `export const <name> = contract(fn, { requires?, ensures: { law: pred, ... } })` or
 * `computation<Ops>()(fn, { ... })`: every part written in place, the predicates functions, `fn` a function or a
 * computation of the program.
 */
export const readContract = (project: Project, file: string, name: string): ContractSource => {
  const { checker } = project
  const init = unwrap(exportedConst(project, file, name))
  if (ts.isCallExpression(init) && declared(checker, init.expression, CONTRACT_MODULE, "lemma")) {
    const [statementArg, opts] = init.arguments
    if (statementArg === undefined) throw new Unsupported("a lemma states something: `lemma((...) => ...)`", init)
    const statement = functionOf(checker, statementArg)
    let requires: FunctionNode | undefined
    if (opts !== undefined) {
      const o = unwrap(opts)
      if (!ts.isObjectLiteralExpression(o)) throw new Unsupported("a lemma's options are written in place", opts)
      for (const p of o.properties)
        if (ts.isPropertyAssignment(p) && ts.isIdentifier(p.name) && p.name.text === "requires") requires = functionOf(checker, p.initializer)
        else throw new Unsupported("a lemma's one option is `requires`", p)
    }
    return { name, kind: "lemma", target: statement, requires, ensures: [{ name: "holds", law: statement }] }
  }
  const implemented = implementationNamed(project, file, name)
  if (implemented !== undefined) {
    const { call, computation } = specOf(checker, implemented)
    const lawsArg = call.arguments[0]
    if (lawsArg === undefined || !ts.isObjectLiteralExpression(unwrap(lawsArg)))
      throw new Unsupported("a spec is `spec<F>({ requires?, ensures: { ... } })`, written in place", call)
    return { name, kind: computation ? "computation" : "function", target: init, ...lawsOf(checker, lawsArg) }
  }
  const helper = contractKind(checker, init)
  if (helper === undefined || helper === "lemma" || !ts.isCallExpression(init))
    throw new Unsupported(`\`${name}\` is not a \`contract(...)\`, a \`computation<...>()(...)\`, a \`lemma(...)\` or an \`Implementation<typeof S>\` of this package`, init)
  const [fnArg, lawsArg] = init.arguments
  if (fnArg === undefined || lawsArg === undefined || !ts.isObjectLiteralExpression(unwrap(lawsArg)))
    throw new Unsupported("a contract is `contract(fn, { requires?, ensures: { ... } })`, written in place", init)
  return { name, kind: helper, target: targetOf(checker, fnArg), ...lawsOf(checker, lawsArg) }
}

/** `export const <name>: Implementation<...> = ...` in `file`, when it is one. */
const implementationNamed = (project: Project, file: string, name: string): ts.VariableDeclaration | undefined => {
  for (const stmt of sourceFile(project, file).statements)
    if (ts.isVariableStatement(stmt))
      for (const d of stmt.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === name && isImplementation(project.checker, d)) return d
  return undefined
}

/** A contract's or a spec's `{ requires?, ensures: { law: pred, ... } }`, written in place. */
const lawsOf = (checker: ts.TypeChecker, lawsArg: ts.Expression): Pick<ContractSource, "requires" | "ensures"> => {
  let requires: FunctionNode | undefined
  const ensures: Array<{ name: string; law: FunctionNode }> = []
  for (const p of (unwrap(lawsArg) as ts.ObjectLiteralExpression).properties) {
    const value = ts.isPropertyAssignment(p) ? p.initializer : ts.isShorthandPropertyAssignment(p) ? p.name : undefined
    if (value === undefined || !ts.isIdentifier(p.name!)) throw new Unsupported("a contract's parts are `requires` and `ensures`", p)
    if (p.name.text === "requires") requires = functionOf(checker, value)
    else if (p.name.text === "ensures") {
      const laws = unwrap(value)
      if (!ts.isObjectLiteralExpression(laws)) throw new Unsupported("`ensures` is an object of named laws, written in place", p)
      for (const q of laws.properties) {
        if (ts.isShorthandPropertyAssignment(q)) ensures.push({ name: q.name.text, law: functionOf(checker, q.name) })
        else if (ts.isPropertyAssignment(q) && (ts.isIdentifier(q.name) || ts.isStringLiteral(q.name)))
          ensures.push({ name: q.name.text, law: functionOf(checker, q.initializer) })
        else throw new Unsupported("a law is `name: (args..., result) => boolean`", q)
      }
    } else throw new Unsupported(`a contract has no part \`${p.name.text}\``, p)
  }
  return { requires, ensures }
}

export const unwrap = (e: ts.Expression): ts.Expression =>
  ts.isParenthesizedExpression(e) || ts.isSatisfiesExpression(e) ? unwrap(e.expression) : e

/** Whether `e` resolves to the export `name` of tsverify's module `module`. */
export const declared = (checker: ts.TypeChecker, e: ts.Expression, module: OwnModule, name: string): boolean => {
  let sym = checker.getSymbolAtLocation(ts.isPropertyAccessExpression(e) ? e.name : e)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
  const decl = sym?.declarations?.[0]
  return sym?.name === name && decl !== undefined && ownModule(decl.getSourceFile().fileName, module)
}

/** What `fn` names: a function written in place, a function declaration, or the value of a `const` (a function or a computation's definition). */
const targetOf = (checker: ts.TypeChecker, e: ts.Expression): ts.Node => {
  const x = unwrap(e)
  if (!ts.isIdentifier(x)) return x
  let sym = checker.getSymbolAtLocation(x)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
  const decl = sym?.valueDeclaration
  if (decl !== undefined && ts.isFunctionDeclaration(decl) && decl.body !== undefined) return decl
  if (decl !== undefined && ts.isVariableDeclaration(decl) && decl.initializer !== undefined && (decl.parent.flags & ts.NodeFlags.Const) !== 0)
    return unwrap(decl.initializer)
  throw new Unsupported("expected a function or a computation the program declares", e)
}

/** A function written in place, or an identifier resolving to a function declaration or a `const` holding one. */
export const functionOf = (checker: ts.TypeChecker, e: ts.Expression): FunctionNode => {
  const x = unwrap(e)
  if (ts.isArrowFunction(x) || ts.isFunctionExpression(x)) return x
  // A name, or a member of a namespace import (`laws.readsFirst`, from `import * as laws`).
  const name = ts.isIdentifier(x) ? x : ts.isPropertyAccessExpression(x) && ts.isIdentifier(x.expression) ? x.name : undefined
  if (name !== undefined) {
    // In `{ requires }` the name is the property's; the binding it reads is the shorthand's value symbol.
    let sym = ts.isShorthandPropertyAssignment(name.parent) ? checker.getShorthandAssignmentValueSymbol(name.parent) : checker.getSymbolAtLocation(name)
    if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
    const decl = sym?.valueDeclaration
    if (decl !== undefined && ts.isFunctionDeclaration(decl) && decl.body !== undefined) return decl
    if (decl !== undefined && ts.isVariableDeclaration(decl) && decl.initializer !== undefined) {
      const init = unwrap(decl.initializer)
      if ((decl.parent.flags & ts.NodeFlags.Const) !== 0 && (ts.isArrowFunction(init) || ts.isFunctionExpression(init))) return init
    }
  }
  throw new Unsupported("expected a function written in place, or the name of one the program declares", e)
}

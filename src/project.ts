// The TypeScript side: a program over the spec's files (with any file's text
// replaced, or a file added, in memory: how a planted bug is read), its
// diagnostics, and a contract read from source.
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

const CONTRACT_MODULE = path.resolve(import.meta.dirname, "contract.ts")

export interface ContractSource {
  readonly name: string
  /** The function the contract is about, resolved through the type checker: the contract's link to the code. */
  readonly fn: FunctionNode
  readonly requires: FunctionNode | undefined
  readonly ensures: ReadonlyArray<{ readonly name: string; readonly law: FunctionNode }>
}

/**
 * Reads `export const <name> = contract(fn, { requires?, ensures: { law: pred, ... } })`
 * from source: every part written in place, the predicates functions, `fn` a
 * function of the program.
 */
export const readContract = (project: Project, file: string, name: string): ContractSource => {
  const { checker } = project
  const init = unwrap(exportedConst(project, file, name))
  if (!ts.isCallExpression(init) || declarationFile(checker, init.expression) !== CONTRACT_MODULE)
    throw new Unsupported(`\`${name}\` is not a call to \`contract\` from ${CONTRACT_MODULE}`, init)
  const [fnArg, lawsArg] = init.arguments
  if (fnArg === undefined || lawsArg === undefined || !ts.isObjectLiteralExpression(unwrap(lawsArg)))
    throw new Unsupported("a contract is `contract(fn, { requires?, ensures: { ... } })`, written in place", init)
  const fn = functionOf(checker, fnArg)
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
  return { name, fn, requires, ensures }
}

const unwrap = (e: ts.Expression): ts.Expression =>
  ts.isParenthesizedExpression(e) || ts.isSatisfiesExpression(e) ? unwrap(e.expression) : e

const declarationFile = (checker: ts.TypeChecker, e: ts.Expression): string | undefined => {
  let sym = checker.getSymbolAtLocation(ts.isPropertyAccessExpression(e) ? e.name : e)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
  const decl = sym?.declarations?.[0]
  return decl === undefined ? undefined : path.resolve(decl.getSourceFile().fileName)
}

/** A function written in place, or an identifier resolving to a function declaration or a `const` holding one. */
const functionOf = (checker: ts.TypeChecker, e: ts.Expression): FunctionNode => {
  const x = unwrap(e)
  if (ts.isArrowFunction(x) || ts.isFunctionExpression(x)) return x
  if (ts.isIdentifier(x)) {
    // In `{ requires }` the name is the property's; the binding it reads is the shorthand's value symbol.
    let sym = ts.isShorthandPropertyAssignment(x.parent) ? checker.getShorthandAssignmentValueSymbol(x.parent) : checker.getSymbolAtLocation(x)
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

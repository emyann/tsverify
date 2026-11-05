// The values of a TypeScript type, as plain JSON the child turns into generators: read from the checker in the
// verifier's process, sent over ipc. No Z3, no fast-check.

import path from "node:path"
import ts from "typescript"

export type Shape =
  | { readonly kind: "literal"; readonly value: string | number | boolean }
  | { readonly kind: "bigint-literal"; readonly value: string }
  | { readonly kind: "boolean" }
  | { readonly kind: "number" }
  | { readonly kind: "bigint" }
  | { readonly kind: "string" }
  | { readonly kind: "null" }
  | { readonly kind: "undefined" }
  | { readonly kind: "union"; readonly of: ReadonlyArray<Shape> }
  | { readonly kind: "record"; readonly fields: Readonly<Record<string, Shape>>; readonly optional: ReadonlyArray<string> }
  | { readonly kind: "array"; readonly of: Shape }
  | { readonly kind: "tuple"; readonly of: ReadonlyArray<Shape>; readonly rest?: Shape }
  | { readonly kind: "dictionary"; readonly of: Shape }
  | { readonly kind: "map"; readonly key: Shape; readonly value: Shape }
  | { readonly kind: "set"; readonly of: Shape }
  | { readonly kind: "function"; readonly returns: Shape }
  | { readonly kind: "date" }

/** A type no generated value stands for: the run of a contract over it is left to the proof. */
export class NotRunnable extends Error {}

/** Past `MAX_DEPTH` objects deep: a recursive member is dropped where it may be (a union's, an optional field). */
class TooDeep extends NotRunnable {}

/** How many objects deep a shape goes: where a recursive type is cut. */
const MAX_DEPTH = 4

/** The library types a run makes values of; any other class or interface of the library is not run. */
const COLLECTIONS = new Set(["Array", "ReadonlyArray", "Map", "ReadonlyMap", "Set", "ReadonlySet"])

const F = ts.TypeFlags

/** Whether `t` is declared by TypeScript's own library (`lib.*.d.ts`) alone. */
const fromLib = (t: ts.Type): boolean => {
  const decls = t.getSymbol()?.declarations ?? []
  return decls.length > 0 && decls.every((d) => /[\\/]typescript[\\/]lib[\\/]lib\.[^\\/]*\.d\.ts$/.test(d.getSourceFile().fileName))
}

/**
 * The shape of the values of `type`: what a run generates for it. Throws `NotRunnable`, naming the type, for a type no
 * generated value stands for (`unknown`, `any`, a type parameter, a class's instance, a symbol, a `Date`, …).
 */
export const shapeOf = (checker: ts.TypeChecker, type: ts.Type, depth = 0): Shape => {
  const text = () => checker.typeToString(type)
  const refuse = (why: string): never => {
    throw new NotRunnable(`\`${text()}\` is not generated: ${why}`)
  }
  const f = type.flags
  if (f & F.Any) return refuse("it may be anything, unchecked")
  // Any value is one of `unknown`: a run gives it the primitives, which a law must narrow to read.
  if (f & F.Unknown)
    return { kind: "union", of: [{ kind: "undefined" }, { kind: "null" }, { kind: "boolean" }, { kind: "number" }, { kind: "string" }] }
  if (f & F.Never) return refuse("it has no value")
  if (f & F.TypeParameter) return refuse("a type parameter")
  if (f & (F.ESSymbol | F.UniqueESSymbol)) return refuse("a symbol")
  if (f & F.Boolean) return { kind: "boolean" }
  if (f & F.BooleanLiteral) return { kind: "literal", value: (type as { intrinsicName?: string }).intrinsicName === "true" }
  if (type.isStringLiteral() || type.isNumberLiteral()) return { kind: "literal", value: type.value }
  if (f & F.BigIntLiteral) {
    const v = (type as ts.BigIntLiteralType).value
    return { kind: "bigint-literal", value: `${v.negative ? "-" : ""}${v.base10Value}` }
  }
  if (f & F.String) return { kind: "string" }
  if (f & F.Number) return { kind: "number" }
  if (f & F.BigInt) return { kind: "bigint" }
  if (f & F.Null) return { kind: "null" }
  if (f & (F.Undefined | F.Void)) return { kind: "undefined" }
  if (type.isUnion()) {
    const of: Array<Shape> = []
    for (const t of type.types)
      try {
        of.push(shapeOf(checker, t, depth))
      } catch (e) {
        if (!(e instanceof TooDeep)) throw e
      }
    if (of.length === 0) throw new TooDeep(`\`${text()}\` is not generated: it nests itself too deep`)
    return of.length === 1 ? of[0]! : { kind: "union", of }
  }
  if (type.isIntersection()) {
    // A brand: a primitive with a tag only types carry (`string & { readonly __brand: "Id" }`), generated as the primitive.
    const primitive = type.types.find((t) => t.flags & (F.StringLike | F.NumberLike | F.BigIntLike | F.BooleanLike))
    if (primitive !== undefined) return shapeOf(checker, primitive, depth)
  }
  // `object`: an empty one is a value of it.
  if (f & F.NonPrimitive) return { kind: "record", fields: {}, optional: [] }
  if (!(f & F.Object) && !type.isIntersection()) return refuse("no value a run makes")
  if (depth >= MAX_DEPTH) throw new TooDeep(`\`${text()}\` is not generated: it nests itself too deep`)
  const inner = (t: ts.Type) => shapeOf(checker, t, depth + 1)
  if (checker.isTupleType(type)) {
    const ref = type as ts.TupleTypeReference
    const flags = ref.target.elementFlags
    const args = checker.getTypeArguments(ref)
    const of: Array<Shape> = []
    let rest: Shape | undefined
    for (const [i, t] of args.entries()) {
      const fl = flags[i]!
      if (fl & ts.ElementFlags.Variadic) return refuse("a tuple spread of a type parameter")
      if (fl & ts.ElementFlags.Rest) {
        if (i !== args.length - 1) return refuse("a tuple whose rest is not last")
        rest = inner(t)
      } else if (fl & ts.ElementFlags.Optional) of.push({ kind: "union", of: [inner(t), { kind: "undefined" }] })
      else of.push(inner(t))
    }
    return rest === undefined ? { kind: "tuple", of } : { kind: "tuple", of, rest }
  }
  const name = type.getSymbol()?.name
  if (fromLib(type) && name !== undefined && COLLECTIONS.has(name)) {
    const args = checker.getTypeArguments(type as ts.TypeReference)
    if (name === "Array" || name === "ReadonlyArray") {
      try {
        return { kind: "array", of: inner(args[0]!) }
      } catch (e) {
        // A recursive array cut where it nests too deep: empty there.
        if (e instanceof TooDeep) return { kind: "tuple", of: [] }
        throw e
      }
    }
    if (name === "Map" || name === "ReadonlyMap") return { kind: "map", key: inner(args[0]!), value: inner(args[1]!) }
    return { kind: "set", of: inner(args[0]!) }
  }
  if (fromLib(type) && type.getSymbol()?.name === "Date") return { kind: "date" }
  // Any other named interface or class of the library (`RegExp`, `Promise`): no value a run makes. A type the library
  // maps (`Record<string, V>`, `Readonly<T>`) is the object it stands for.
  if (fromLib(type) && (type.getSymbol()!.flags & (ts.SymbolFlags.Interface | ts.SymbolFlags.Class)) !== 0)
    return refuse("an object of the library a run makes none of")
  if ((type.getSymbol()?.flags ?? 0) & ts.SymbolFlags.Class) return refuse("a class's instance")
  if (type.getConstructSignatures().length > 0) return refuse("a constructor")
  const calls = type.getCallSignatures()
  const props = checker.getPropertiesOfType(type)
  if (calls.length > 0) {
    if (props.length > 0) return refuse("a function with properties")
    return { kind: "function", returns: inner(calls[0]!.getReturnType()) }
  }
  const index = checker.getIndexInfosOfType(type)
  if (index.length > 0) {
    if (index.length > 1 || !(index[0]!.keyType.flags & F.String)) return refuse("an object with keys other than strings")
    // Fields beside keys of its own: the fields alone, a value of the type with no other key.
    if (props.length === 0) return { kind: "dictionary", of: inner(index[0]!.type) }
  }
  const fields: Record<string, Shape> = {}
  const optional: Array<string> = []
  for (const p of props) {
    const opt = (p.flags & ts.SymbolFlags.Optional) !== 0
    try {
      fields[p.name] = inner(checker.getTypeOfSymbol(p))
    } catch (e) {
      if (opt && e instanceof TooDeep) continue
      throw e
    }
    if (opt) optional.push(p.name)
  }
  return { kind: "record", fields, optional }
}

/** The strings every pool holds, whatever the program writes. */
const ALWAYS = ["", "a", "b", "c"]

/** The most strings a pool holds. */
const POOL_MAX = 256

/**
 * The string literals of the program's own files `file` reaches through its imports (no package's, no declaration
 * file's), in the order of their paths and positions, each once, at most 256, always with "", "a", "b" and "c": what a
 * run's strings are drawn from, so a key the code looks up is one it is given.
 */
export const poolOf = (project: { readonly program: ts.Program; readonly checker: ts.TypeChecker }, file: string): Array<string> => {
  const { program, checker } = project
  const own = (sf: ts.SourceFile) => !sf.isDeclarationFile && !/[\\/]node_modules[\\/]/.test(sf.fileName)
  const start = program.getSourceFile(path.resolve(file))
  const reached = new Map<string, ts.SourceFile>()
  const visit = (sf: ts.SourceFile) => {
    if (reached.has(sf.fileName) || !own(sf)) return
    reached.set(sf.fileName, sf)
    for (const stmt of sf.statements) {
      const spec =
        (ts.isImportDeclaration(stmt) || ts.isExportDeclaration(stmt)) && stmt.moduleSpecifier !== undefined
          ? stmt.moduleSpecifier
          : undefined
      const target = spec === undefined ? undefined : checker.getSymbolAtLocation(spec)?.valueDeclaration
      if (target !== undefined && ts.isSourceFile(target)) visit(target)
      // A module imported for its effects alone (`import "./x.ts"`) has no symbol: it is found by name.
      if (spec !== undefined && target === undefined && ts.isStringLiteral(spec)) {
        const resolved = ts.resolveModuleName(spec.text, sf.fileName, program.getCompilerOptions(), ts.sys).resolvedModule
        const found = resolved === undefined ? undefined : program.getSourceFile(resolved.resolvedFileName)
        if (found !== undefined) visit(found)
      }
    }
  }
  if (start !== undefined) visit(start)
  const strings = new Set(ALWAYS)
  const files = [...reached.values()].toSorted((a, b) => (a.fileName < b.fileName ? -1 : a.fileName > b.fileName ? 1 : 0))
  for (const sf of files) {
    ts.forEachChild(sf, function scan(n) {
      if (strings.size >= POOL_MAX) return
      const moduleName =
        (n.parent !== undefined &&
          (ts.isImportDeclaration(n.parent) || ts.isExportDeclaration(n.parent)) &&
          n.parent.moduleSpecifier === n) ||
        (n.parent !== undefined && ts.isExternalModuleReference(n.parent)) ||
        (n.parent !== undefined && ts.isLiteralTypeNode(n.parent) && ts.isImportTypeNode(n.parent.parent))
      if ((ts.isStringLiteral(n) || ts.isNoSubstitutionTemplateLiteral(n)) && !moduleName) strings.add(n.text)
      ts.forEachChild(n, scan)
    })
  }
  return [...strings].slice(0, POOL_MAX)
}

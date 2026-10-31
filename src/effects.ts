// What JavaScript's own library does when it is called, as the purity check needs it: which functions and methods
// change nothing, which call the functions they are passed, and which change their receiver and store what they are
// given. Broader than what the lowering reads (`lower/`): a call can be pure and still not be read.
import ts from "typescript"
import { symbolOf } from "./resolve.ts"

const MATH_IMPURE = new Set(["random"])
const PURE_STATICS: Readonly<Record<string, ReadonlySet<string>>> = {
  JSON: new Set(["stringify", "parse"]),
  Object: new Set(["keys", "values", "entries", "fromEntries", "isFrozen", "getPrototypeOf", "hasOwn", "is", "groupBy"]),
  Number: new Set(["isFinite", "isInteger", "isNaN", "isSafeInteger", "parseFloat", "parseInt"]),
  Array: new Set(["isArray", "from", "of"]),
  String: new Set(["fromCharCode", "fromCodePoint", "raw"]),
  Date: new Set(["UTC", "parse"]),
  BigInt: new Set(["asIntN", "asUintN"]),
}
export const PURE_GLOBAL_FNS = new Set([
  "String",
  "Number",
  "Boolean",
  "BigInt",
  "parseInt",
  "parseFloat",
  "isNaN",
  "isFinite",
  "encodeURIComponent",
  "decodeURIComponent",
  "encodeURI",
  "decodeURI",
  "structuredClone",
])
export const FRESH_CONSTRUCTORS = new Set([
  "Map",
  "Set",
  "WeakMap",
  "WeakSet",
  "Array",
  "Date",
  "Error",
  "TypeError",
  "RangeError",
  "SyntaxError",
  "URL",
  "RegExp",
])
const ARRAY_READS = new Set([
  "at",
  "concat",
  "entries",
  "every",
  "filter",
  "find",
  "findIndex",
  "findLast",
  "findLastIndex",
  "flat",
  "flatMap",
  "forEach",
  "includes",
  "indexOf",
  "join",
  "keys",
  "lastIndexOf",
  "map",
  "reduce",
  "reduceRight",
  "slice",
  "some",
  "toReversed",
  "toSorted",
  "toSpliced",
  "values",
  "with",
  "toString",
])
const ARRAY_WRITES = new Set(["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "copyWithin"])
/** Array methods whose result holds the receiver's elements. */
export const ARRAY_ELEMENTS = new Set([
  "at",
  "find",
  "findLast",
  "filter",
  "slice",
  "concat",
  "flat",
  "toReversed",
  "toSorted",
  "toSpliced",
  "with",
  "pop",
  "shift",
  "values",
])
const MAP_READS = new Set(["get", "has", "forEach", "entries", "keys", "values"])
const SET_READS = new Set([
  "has",
  "forEach",
  "entries",
  "keys",
  "values",
  "union",
  "intersection",
  "difference",
  "symmetricDifference",
  "isSubsetOf",
  "isSupersetOf",
  "isDisjointFrom",
])
const COLLECTION_WRITES = new Set(["set", "add", "delete", "clear"])

/** Whether `e` names something TypeScript's own library or `@types/node` declares, and nothing of the program. */
export const isLib = (checker: ts.TypeChecker, e: ts.Node): boolean => {
  const sym = symbolOf(checker, e)
  const decls = sym?.declarations ?? []
  return (
    decls.length > 0 &&
    decls.every(
      (d) =>
        d.getSourceFile().isDeclarationFile &&
        /\/node_modules\/(typescript\/lib|@types\/node)\//.test(d.getSourceFile().fileName.replaceAll("\\", "/")),
    )
  )
}

export const isPrimitive = (checker: ts.TypeChecker, t: ts.Type): boolean =>
  membersOf(checker, t).every(
    (m) =>
      (m.flags &
        (ts.TypeFlags.StringLike |
          ts.TypeFlags.NumberLike |
          ts.TypeFlags.BooleanLike |
          ts.TypeFlags.BigIntLike |
          ts.TypeFlags.EnumLike |
          ts.TypeFlags.ESSymbolLike |
          ts.TypeFlags.Never)) !==
      0,
  )

/** A type's members, null and undefined dropped. */
export const membersOf = (checker: ts.TypeChecker, t: ts.Type): Array<ts.Type> => {
  const nn = checker.getNonNullableType(t)
  return nn.isUnion() ? nn.types : [nn]
}

export const isArrayLike = (checker: ts.TypeChecker, e: ts.Expression): boolean =>
  membersOf(checker, checker.getTypeAtLocation(e)).every((m) => checker.isArrayType(m) || checker.isTupleType(m))

export const isNamed = (checker: ts.TypeChecker, e: ts.Expression, names: ReadonlyArray<string>): boolean =>
  membersOf(checker, checker.getTypeAtLocation(e)).every((m) => names.includes(m.getSymbol()?.name ?? ""))

/** A regular expression without the `g` or `y` flag, written in place or held by a constant: `test` and `exec` leave it as it was. */
const statelessRegExp = (checker: ts.TypeChecker, e: ts.Expression): boolean => {
  let x: ts.Node = e
  if (ts.isIdentifier(x)) {
    const d = symbolOf(checker, x)?.valueDeclaration
    if (d === undefined || !ts.isVariableDeclaration(d) || (d.parent.flags & ts.NodeFlags.Const) === 0 || d.initializer === undefined)
      return false
    x = d.initializer
  }
  return ts.isRegularExpressionLiteral(x) && !/[gy]/.test(x.text.slice(x.text.lastIndexOf("/") + 1))
}

/** What a call of a method of the library does, as the purity check reads it. */
export type LibraryCall =
  /** Changes nothing and calls nothing it is passed. */
  | { readonly does: "nothing" }
  /** Changes nothing, and calls each function it is passed. */
  | { readonly does: "call" }
  /** Changes `target`, storing `stored` in it and copying the fields of each of `copied` into it. */
  | {
      readonly does: "change"
      readonly target: ts.Expression
      readonly stored: ReadonlyArray<ts.Expression>
      readonly copied: ReadonlyArray<ts.Expression>
    }
  /** Something the check does not know to be pure, and why. */
  | { readonly does: "effect"; readonly why: string }

/** What `recv.m(...args)` does, for any method: of the library's statics, of a primitive, an array, a collection, a `Date` or a `RegExp`. */
export const methodCall = (
  checker: ts.TypeChecker,
  callee: ts.PropertyAccessExpression,
  args: ReadonlyArray<ts.Expression>,
): LibraryCall => {
  const m = callee.name.text
  const recv = callee.expression
  if (ts.isIdentifier(recv) && isLib(checker, recv)) {
    if (recv.text === "Math" && !MATH_IMPURE.has(m)) return { does: "nothing" }
    if (PURE_STATICS[recv.text]?.has(m)) return { does: "nothing" }
    if (recv.text === "Object" && (m === "assign" || m === "freeze")) {
      const [target, ...sources] = args
      return target === undefined ? { does: "nothing" } : { does: "change", target, stored: [], copied: sources }
    }
    return { does: "effect", why: `calls \`${recv.text}.${m}\`, which the check does not know to be pure` }
  }
  if (isPrimitive(checker, checker.getNonNullableType(checker.getTypeAtLocation(recv)))) return { does: "nothing" }
  if (isArrayLike(checker, recv)) {
    if (ARRAY_READS.has(m)) return { does: "call" }
    if (ARRAY_WRITES.has(m)) {
      const stored =
        m === "splice" ? args.slice(2) : m === "push" || m === "unshift" || m === "fill" ? args.slice(0, m === "fill" ? 1 : undefined) : []
      return { does: "change", target: recv, stored, copied: [] }
    }
  }
  if (isNamed(checker, recv, ["Map", "ReadonlyMap", "WeakMap"]) && MAP_READS.has(m)) return { does: "call" }
  if (isNamed(checker, recv, ["Set", "ReadonlySet", "WeakSet"]) && SET_READS.has(m)) return { does: "call" }
  if (isNamed(checker, recv, ["Map", "WeakMap", "Set", "WeakSet"]) && COLLECTION_WRITES.has(m))
    return { does: "change", target: recv, stored: args, copied: [] }
  if (isNamed(checker, recv, ["Date"]) && /^(get|to|valueOf)/.test(m)) return { does: "nothing" }
  if (isNamed(checker, recv, ["RegExp"]) && (m === "test" || m === "exec"))
    return statelessRegExp(checker, recv)
      ? { does: "nothing" }
      : { does: "effect", why: `\`${recv.getText()}.${m}\` moves a global or sticky regular expression's \`lastIndex\`` }
  return { does: "effect", why: `calls the method \`${callee.getText()}\`, which the check cannot see into` }
}

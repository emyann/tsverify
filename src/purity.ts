// Whether a function of the program is pure, read from its source: what
// `assume(f, { pure: true })` claims, checked where the source is there.
//
// Pure means: a call changes nothing anyone else can see, and its result
// depends only on its arguments. The check refuses
// - an effect: `await`, `yield`, `this`, a call to anything it does not know
//   to be pure (the clock, `Math.random`, the console, a function it cannot
//   read, a method it cannot see into, a package's function not declared pure),
//   a read or a write of a module's `let`;
// - a change to an object it did not allocate: its arguments, a module's
//   constants, what a callee returned;
// - a cast (`as`) or a type predicate (`x is T`), either of which would hide a
//   value's type from the next rule.
//
// A call to a function it was given is pure where that function is: the check
// names the arguments it calls (`calls`), and a caller passes pure functions
// there, which `assumedCall` asks of each call.
//
// It may change what it allocated itself (a fold builds its state so). The
// hard part is aliasing: a fresh object can hold a value of the caller's, and
// a change made through the fresh object would reach it. The check records
// the types of every value it did not allocate that it stores into one it did,
// and refuses a change to an object whose type one of them, or anything they
// reach, could be (type-based alias analysis). A value stored as `unknown` or
// `object` can be reached only through a narrowing; it is taken as reaching the
// types such narrowings give (an intersection, an index signature, `object`).
//
// What it takes on trust, and the report says: a property read runs no getter;
// a module constant is never changed by other code; the function terminates.
import ts from "typescript"
import { CONTRACT_MODULE, declared as ownExport } from "./project.ts"
import type { AssumedFn } from "./trust.ts"
import { type FunctionNode, locate } from "./value.ts"

export type Purity =
  | {
      readonly pure: true
      readonly read: ReadonlyArray<string>
      /** The arguments it calls, by position: it is pure where each function passed there is. */
      readonly calls: ReadonlyArray<number>
    }
  | { readonly pure: false; readonly why: string }

/** Where a value came from: allocated during the call, the caller's argument `k`, or anything else. */
type Origin = "fresh" | "foreign" | number

interface Summary {
  /** The first effect found, if any. */
  effect: string | undefined
  /** Changes to an argument: which, and the type of the object changed; the first place of each. */
  readonly changed: Map<number, Map<ts.Type, ts.Node>>
  /** Changes to an object allocated during the call: its type. */
  readonly changes: Map<ts.Type, ts.Node>
  /** The types of values not allocated during the call, stored into one that was. */
  readonly stored: Set<ts.Type>
  /** The arguments it calls, by position. */
  readonly calls: Set<number>
}

const K = ts.SyntaxKind

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
const PURE_GLOBAL_FNS = new Set([
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
const FRESH_CONSTRUCTORS = new Set([
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
const ARRAY_ELEMENTS = new Set([
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

/**
 * Checks `fn`: pure, with the functions of the program it read on the way, or not, with the first reason. `assumed`
 * are the declarations in force: a call to a function declared pure is taken as pure.
 */
export const purityOf = (checker: ts.TypeChecker, fn: FunctionNode, assumed: (callee: ts.Expression) => AssumedFn | undefined): Purity => {
  const summaries = new Map<FunctionNode, Summary>()
  const read: Array<string> = []

  const summarise = (f: FunctionNode): Summary => {
    const known = summaries.get(f)
    if (known !== undefined) return known
    const s: Summary = { effect: undefined, changed: new Map(), changes: new Map(), stored: new Set(), calls: new Set() }
    const changeOf = (param: number, type: ts.Type, at: ts.Node) => {
      const m = s.changed.get(param) ?? new Map<ts.Type, ts.Node>()
      if (!m.has(type)) m.set(type, at)
      s.changed.set(param, m)
    }
    const changeFresh = (type: ts.Type, at: ts.Node) => {
      if (!s.changes.has(type)) s.changes.set(type, at)
    }
    // A recursive call sees what is known so far; the caller's summary is complete once its body is read, and a
    // recursive call adds nothing a body does not already show of itself.
    summaries.set(f, s)
    read.push(nameOf(f))
    const own = new Set<ts.Node>()
    ts.forEachChild(f, function mark(n) {
      own.add(n)
      ts.forEachChild(n, mark)
    })
    const params = new Map<ts.Symbol, Set<Origin>>()
    f.parameters.forEach((p, k) => {
      for (const sym of boundSymbols(checker, p.name)) params.set(sym, new Set([k]))
    })
    const effect = (why: string, at: ts.Node) => {
      s.effect ??= `${locate(at)}: ${why}`
    }
    const local = (sym: ts.Symbol): boolean => sym.declarations?.some((d) => own.has(d)) ?? false

    // Every value assigned to a local, so a binding's origins are all of them (the check reads no order).
    const assigned = new Map<ts.Symbol, Array<ts.Expression>>()
    ts.forEachChild(f, function scan(n) {
      if (ts.isBinaryExpression(n) && isAssignment(n.operatorToken.kind) && ts.isIdentifier(n.left)) {
        const sym = symbolOf(checker, n.left)
        if (sym !== undefined) assigned.set(sym, [...(assigned.get(sym) ?? []), n.right])
      }
      ts.forEachChild(n, scan)
    })

    const visiting = new Set<ts.Symbol>()
    const originsOf = (e: ts.Expression): Set<Origin> => {
      if (ts.isParenthesizedExpression(e) || ts.isNonNullExpression(e) || ts.isSatisfiesExpression(e)) return originsOf(e.expression)
      if (ts.isAsExpression(e)) return originsOf(e.expression)
      if (ts.isIdentifier(e)) {
        const sym = symbolOf(checker, e)
        if (sym === undefined) return new Set(["foreign"])
        const p = params.get(sym)
        if (p !== undefined) return p
        if (!local(sym)) return new Set(["foreign"])
        if (visiting.has(sym)) return new Set()
        visiting.add(sym)
        try {
          const out = new Set<Origin>()
          for (const d of sym.declarations ?? []) {
            if (ts.isVariableDeclaration(d) || ts.isBindingElement(d)) {
              const top = declarationOf(d)
              if (ts.isForOfStatement(top.parent.parent) || ts.isForInStatement(top.parent.parent))
                for (const o of originsOf(top.parent.parent.expression)) out.add(o)
              else if (top.initializer !== undefined) for (const o of originsOf(top.initializer)) out.add(o)
            } else if (ts.isFunctionDeclaration(d)) out.add("fresh")
            else out.add("foreign")
          }
          for (const v of assigned.get(sym) ?? []) for (const o of originsOf(v)) out.add(o)
          // A binding with nothing assigned that the check can see (a catch clause's) is taken as the caller's.
          if (out.size === 0) out.add("foreign")
          return out
        } finally {
          visiting.delete(sym)
        }
      }
      if (ts.isPropertyAccessExpression(e) || ts.isElementAccessExpression(e)) return originsOf(e.expression)
      if (ts.isConditionalExpression(e)) return union(originsOf(e.whenTrue), originsOf(e.whenFalse))
      if (ts.isBinaryExpression(e)) {
        const op = e.operatorToken.kind
        if (op === K.QuestionQuestionToken || op === K.BarBarToken || op === K.AmpersandAmpersandToken)
          return union(originsOf(e.left), originsOf(e.right))
        if (isAssignment(op)) return originsOf(e.right)
        if (op === K.CommaToken) return originsOf(e.right)
        return new Set(["fresh"])
      }
      if (ts.isObjectLiteralExpression(e) || ts.isArrayLiteralExpression(e) || ts.isArrowFunction(e) || ts.isFunctionExpression(e))
        return new Set(["fresh"])
      if (ts.isNewExpression(e)) return new Set(["fresh"])
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression)) {
        const m = e.expression.name.text
        const recv = e.expression.expression
        if (isArrayLike(checker, recv) && ARRAY_ELEMENTS.has(m)) return union(originsOf(recv), ...e.arguments.map(originsOf))
        if (isNamed(checker, recv, ["Map", "ReadonlyMap"]) && m === "get") return originsOf(recv)
        if (isGlobal(checker, recv, "Object") && (m === "values" || m === "entries")) return union(...e.arguments.map(originsOf))
      }
      if (
        ts.isCallExpression(e) &&
        ts.isIdentifier(e.expression) &&
        e.expression.text === "structuredClone" &&
        isLib(checker, e.expression)
      )
        return new Set(["fresh"])
      if (isPrimitive(checker, checker.getTypeAtLocation(e))) return new Set(["fresh"])
      return new Set(["foreign"])
    }

    /**
     * Whether `e` is an object this call allocated, itself: a literal, a fresh collection, or a local only ever bound to
     * one. A change to it reaches nothing else, whatever it holds; one to an object read out of it may.
     */
    const allocating = new Set<ts.Symbol>()
    const allocation = (e: ts.Expression): boolean => {
      if (ts.isParenthesizedExpression(e) || ts.isSatisfiesExpression(e)) return allocation(e.expression)
      if (ts.isAsExpression(e)) return freshLiteral(e.expression) && allocation(e.expression)
      if (ts.isArrayLiteralExpression(e) || ts.isObjectLiteralExpression(e)) return true
      if (ts.isNewExpression(e))
        return ts.isIdentifier(e.expression) && isLib(checker, e.expression) && FRESH_CONSTRUCTORS.has(e.expression.text)
      if (!ts.isIdentifier(e)) return false
      const sym = symbolOf(checker, e)
      if (sym === undefined || !local(sym) || params.has(sym)) return false
      if (allocating.has(sym)) return true
      allocating.add(sym)
      try {
        const decls = sym.declarations ?? []
        return (
          decls.length > 0 &&
          decls.every(
            (d) =>
              ts.isVariableDeclaration(d) &&
              ts.isIdentifier(d.name) &&
              !ts.isForOfStatement(d.parent.parent) &&
              !ts.isForInStatement(d.parent.parent) &&
              d.initializer !== undefined &&
              allocation(d.initializer),
          ) &&
          (assigned.get(sym) ?? []).every(allocation)
        )
      } finally {
        allocating.delete(sym)
      }
    }

    /** A change to the object `obj` (a property set or deleted, a mutating method called on it). */
    const change = (obj: ts.Expression, at: ts.Node) => {
      if (allocation(obj)) return
      const type = checker.getTypeAtLocation(obj)
      for (const o of originsOf(obj)) {
        if (o === "fresh") changeFresh(type, at)
        else if (o === "foreign") effect(`changes \`${obj.getText()}\`, which it did not allocate`, at)
        else changeOf(o, type, at)
      }
    }

    /** A value stored into an object: its type recorded when it may be the caller's. */
    const store = (value: ts.Expression) => {
      const t = checker.getTypeAtLocation(value)
      if (isPrimitive(checker, t)) return
      if ([...originsOf(value)].some((o) => o !== "fresh")) s.stored.add(t)
    }
    const storeSpread = (source: ts.Expression) => {
      if (![...originsOf(source)].some((o) => o !== "fresh")) return
      const t = checker.getTypeAtLocation(source)
      for (const part of membersOf(checker, t)) {
        const els = elementsOf(checker, part)
        if (els !== undefined) {
          for (const el of els) if (!isPrimitive(checker, el)) s.stored.add(el)
          continue
        }
        for (const p of checker.getPropertiesOfType(part)) {
          const pt = checker.getTypeOfSymbol(p)
          if (!isPrimitive(checker, pt)) s.stored.add(pt)
        }
      }
    }

    /** A call to another function of the program: its summary, applied to the arguments. */
    const callProgram = (callee: FunctionNode, args: ReadonlyArray<ts.Expression>, at: ts.Node) => {
      const c = summarise(callee)
      if (c.effect !== undefined) effect(`calls \`${nameOf(callee)}\`, which is not pure: ${c.effect}`, at)
      // A function it passes where the callee calls one: called, as if here. Left out, the callee's default is.
      for (const param of c.calls) {
        const arg = args[param]
        if (arg !== undefined) calledValue(arg, `\`${nameOf(callee)}\` calls it`)
      }
      for (const t of c.stored) s.stored.add(t)
      for (const [type, where] of c.changes) changeFresh(type, where)
      for (const [param, types] of c.changed) {
        const arg = args[param]
        if (arg === undefined) continue
        for (const o of originsOf(arg))
          for (const type of types.keys()) {
            if (o === "fresh") changeFresh(type, at)
            else if (o === "foreign")
              effect(`passes \`${arg.getText()}\`, which it did not allocate, to \`${nameOf(callee)}\`, which changes it`, at)
            else changeOf(o, type, at)
          }
      }
    }

    /**
     * A function value the code calls, or hands to something that calls it (`xs.map(f)`, `g(f)`): written here, its
     * body is read where it stands; an argument, it is one this function calls; a function of the program, read.
     */
    const calledValue = (v: ts.Expression, why: string): void => {
      if (ts.isParenthesizedExpression(v)) return calledValue(v.expression, why)
      if (ts.isArrowFunction(v) || ts.isFunctionExpression(v)) return
      if (!ts.isIdentifier(v)) {
        effect(`passes \`${v.getText()}\`, a function it cannot read, and ${why}`, v)
        return
      }
      const declared = assumed(v)
      if (declared !== undefined) {
        if (!declared.pure) effect(`passes \`${declared.name}\`, declared \`pure: false\`, and ${why}`, v)
        return
      }
      if (isLib(checker, v)) {
        if (!PURE_GLOBAL_FNS.has(v.text)) effect(`passes \`${v.text}\`, which the check does not know to be pure, and ${why}`, v)
        return
      }
      const sym = symbolOf(checker, v)
      const target = sym === undefined ? undefined : programFunction(sym)
      if (target !== undefined) {
        if (own.has(target)) return
        const c = summarise(target)
        if (c.effect !== undefined) effect(`passes \`${nameOf(target)}\`, which is not pure: ${c.effect}`, v)
        // What it is called with is not known here: a change to it, or a call of it, may reach anything.
        else if (c.changed.size > 0 || c.calls.size > 0)
          effect(`passes \`${nameOf(target)}\`, which changes or calls what it is given, and ${why}`, v)
        for (const t of c.stored) s.stored.add(t)
        for (const [type, where] of c.changes) changeFresh(type, where)
        return
      }
      const origins = originsOf(v)
      if ([...origins].every((o) => o !== "foreign")) {
        for (const o of origins) if (typeof o === "number") s.calls.add(o)
        return
      }
      effect(`passes \`${v.text}\`, a function it cannot read, and ${why}`, v)
    }

    const call = (e: ts.CallExpression) => {
      const callee = e.expression
      const declared = assumed(callee)
      if (declared !== undefined) {
        if (!declared.pure) effect(`calls \`${declared.name}\`, declared \`pure: false\``, e)
        return
      }
      // A table of the program's functions held by a module constant (`GUARDS[name](state)`): any of them may run.
      if (ts.isPropertyAccessExpression(callee) || ts.isElementAccessExpression(callee)) {
        const table = dispatchTable(callee.expression)
        if (table !== undefined) {
          for (const target of table) callProgram(target, e.arguments, e)
          return
        }
      }
      if (ts.isPropertyAccessExpression(callee)) {
        const m = callee.name.text
        const recv = callee.expression
        if (ts.isIdentifier(recv) && isLib(checker, recv)) {
          if (recv.text === "Math" && !MATH_IMPURE.has(m)) return
          if (PURE_STATICS[recv.text]?.has(m)) return
          if (recv.text === "Object" && (m === "assign" || m === "freeze")) {
            const [target, ...sources] = e.arguments
            if (target !== undefined) change(target, e)
            for (const src of sources) storeSpread(src)
            return
          }
          effect(`calls \`${recv.text}.${m}\`, which the check does not know to be pure`, e)
          return
        }
        const t = checker.getNonNullableType(checker.getTypeAtLocation(recv))
        if (isPrimitive(checker, t)) return
        // A callback given to a read is called by it.
        const callbacks = () => {
          for (const a of e.arguments)
            if (checker.getNonNullableType(checker.getTypeAtLocation(a)).getCallSignatures().length > 0)
              calledValue(a, `\`.${m}\` calls it`)
        }
        if (isArrayLike(checker, recv)) {
          if (ARRAY_READS.has(m)) return callbacks()
          if (ARRAY_WRITES.has(m)) {
            change(recv, e)
            const stored =
              m === "splice"
                ? e.arguments.slice(2)
                : m === "push" || m === "unshift" || m === "fill"
                  ? e.arguments.slice(0, m === "fill" ? 1 : undefined)
                  : []
            for (const a of stored) store(a)
            return
          }
        }
        if (isNamed(checker, recv, ["Map", "ReadonlyMap", "WeakMap"]) && MAP_READS.has(m)) return callbacks()
        if (isNamed(checker, recv, ["Set", "ReadonlySet", "WeakSet"]) && SET_READS.has(m)) return callbacks()
        if (isNamed(checker, recv, ["Map", "WeakMap", "Set", "WeakSet"]) && COLLECTION_WRITES.has(m)) {
          change(recv, e)
          for (const a of e.arguments) store(a)
          return
        }
        if (isNamed(checker, recv, ["Date"]) && /^(get|to|valueOf)/.test(m)) return
        if (isNamed(checker, recv, ["RegExp"]) && (m === "test" || m === "exec")) {
          if (!statelessRegExp(checker, recv))
            effect(`\`${recv.getText()}.${m}\` moves a global or sticky regular expression's \`lastIndex\``, e)
          return
        }
        effect(`calls the method \`${callee.getText()}\`, which the check cannot see into`, e)
        return
      }
      if (ts.isIdentifier(callee)) {
        // The proof code (`invariant`, `assert`) is the verifier's, not the program's: it does nothing when it runs.
        if (ownExport(checker, callee, CONTRACT_MODULE, "invariant") || ownExport(checker, callee, CONTRACT_MODULE, "assert")) return
        if (isLib(checker, callee)) {
          if (!PURE_GLOBAL_FNS.has(callee.text)) effect(`calls \`${callee.text}\`, which the check does not know to be pure`, e)
          return
        }
        const sym = symbolOf(checker, callee)
        const target = sym === undefined ? undefined : programFunction(sym)
        const sig = checker.getResolvedSignature(e)
        if (sig !== undefined && checker.getTypePredicateOfSignature(sig) !== undefined) {
          effect(`narrows by a type predicate (\`${callee.text}\`), a cast the check cannot verify`, e)
          return
        }
        if (target !== undefined) {
          if (own.has(target)) return // a function written inside this one: its body is read where it stands
          callProgram(target, e.arguments, e)
          return
        }
        // A function it was given, or one written here: pure where what it was given is.
        const origins = sym === undefined ? new Set<Origin>(["foreign"]) : originsOf(callee)
        if ([...origins].every((o) => o !== "foreign")) {
          for (const o of origins) if (typeof o === "number") s.calls.add(o)
          return
        }
        effect(`calls \`${callee.text}\`, a function the check cannot read`, e)
        return
      }
      effect(`calls \`${callee.getText()}\`, which the check cannot see into`, e)
    }

    const visit = (n: ts.Node): void => {
      if (n !== f && (ts.isArrowFunction(n) || ts.isFunctionExpression(n) || ts.isFunctionDeclaration(n))) {
        // A callback of an array method reads the receiver's elements; any other function written here, values of
        // its caller's choosing.
        const host =
          ts.isCallExpression(n.parent) &&
          n.parent.arguments.includes(n as ts.Expression) &&
          ts.isPropertyAccessExpression(n.parent.expression)
            ? n.parent
            : undefined
        const recv =
          host !== undefined && isArrayLike(checker, (host.expression as ts.PropertyAccessExpression).expression)
            ? (host.expression as ts.PropertyAccessExpression).expression
            : undefined
        const method = host === undefined ? undefined : (host.expression as ts.PropertyAccessExpression).name.text
        n.parameters.forEach((p, k) => {
          let o: Set<Origin> = new Set(["foreign"])
          if (recv !== undefined && (method === "reduce" || method === "reduceRight")) {
            const init = host!.arguments[1]
            o =
              k === 0 ? (init === undefined ? originsOf(recv) : originsOf(init)) : k === 1 || k === 3 ? originsOf(recv) : new Set(["fresh"])
          } else if (recv !== undefined) o = k === 1 ? new Set(["fresh"]) : originsOf(recv)
          for (const sym of boundSymbols(checker, p.name)) params.set(sym, o)
        })
      }
      if (ts.isAwaitExpression(n) || ts.isYieldExpression(n)) effect("waits on something (`await`, `yield`)", n)
      else if (n.kind === K.ThisKeyword) effect("reads `this`", n)
      else if (ts.isAsExpression(n) && !ts.isConstTypeReference(n.type) && !freshLiteral(n.expression))
        effect("casts (`as`), which hides a value's type from the check", n)
      else if (ts.isTypeAssertionExpression(n)) effect("casts, which hides a value's type from the check", n)
      else if (ts.isTaggedTemplateExpression(n)) effect("calls a tag function", n)
      else if (ts.isIdentifier(n) && isModuleState(checker, n, own))
        effect(`reads or writes \`${n.text}\`, a module's \`let\`, which may change between calls`, n)
      else if (ts.isBinaryExpression(n) && isAssignment(n.operatorToken.kind)) {
        const left = n.left
        if (ts.isPropertyAccessExpression(left) || ts.isElementAccessExpression(left)) {
          change(left.expression, n)
          if (isStoringAssignment(n.operatorToken.kind)) store(n.right)
        } else if (ts.isIdentifier(left)) {
          const sym = symbolOf(checker, left)
          if (sym === undefined || !(local(sym) || params.has(sym))) effect(`assigns \`${left.text}\`, which is not its own`, n)
        } else effect("assigns through a pattern, which the check does not read", n)
      } else if (
        (ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
        (n.operator === K.PlusPlusToken || n.operator === K.MinusMinusToken)
      ) {
        const target = n.operand
        if (ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target)) change(target.expression, n)
        else if (ts.isIdentifier(target)) {
          const sym = symbolOf(checker, target)
          if (sym === undefined || !(local(sym) || params.has(sym))) effect(`changes \`${target.text}\`, which is not its own`, n)
        }
      } else if (ts.isDeleteExpression(n)) {
        const target = n.expression
        if (ts.isPropertyAccessExpression(target) || ts.isElementAccessExpression(target)) change(target.expression, n)
      } else if (ts.isCallExpression(n)) {
        if (n.expression.kind === K.ImportKeyword) effect("imports a module", n)
        else call(n)
      } else if (ts.isNewExpression(n)) {
        const c = n.expression
        if (ts.isIdentifier(c) && isLib(checker, c) && FRESH_CONSTRUCTORS.has(c.text)) {
          if (c.text === "Date" && (n.arguments?.length ?? 0) === 0) effect("reads the clock (`new Date()`)", n)
          for (const a of n.arguments ?? []) store(a)
        } else effect(`constructs \`${c.getText()}\`, whose constructor the check does not read`, n)
      } else if (ts.isObjectLiteralExpression(n)) {
        for (const p of n.properties) {
          if (ts.isPropertyAssignment(p)) store(p.initializer)
          else if (ts.isShorthandPropertyAssignment(p)) store(p.name)
          else if (ts.isSpreadAssignment(p)) storeSpread(p.expression)
          else effect("an object literal with a method or an accessor", p)
        }
      } else if (ts.isArrayLiteralExpression(n)) {
        for (const x of n.elements) {
          if (ts.isSpreadElement(x)) storeSpread(x.expression)
          else store(x)
        }
      }
      ts.forEachChild(n, visit)
    }
    if (f.body !== undefined) visit(f.body)
    for (const p of f.parameters) if (p.initializer !== undefined) visit(p.initializer)
    return s
  }

  /** The functions a module constant's object literal holds, when every value of it is one of the program's. */
  const dispatchTable = (e: ts.Expression): Array<FunctionNode> | undefined => {
    if (!ts.isIdentifier(e)) return undefined
    const d = symbolOf(checker, e)?.valueDeclaration
    if (d === undefined || !ts.isVariableDeclaration(d) || d.initializer === undefined || (d.parent.flags & ts.NodeFlags.Const) === 0)
      return undefined
    if (!ts.isVariableStatement(d.parent.parent) || !ts.isSourceFile(d.parent.parent.parent)) return undefined
    let init = d.initializer
    while (
      ts.isSatisfiesExpression(init) ||
      ts.isParenthesizedExpression(init) ||
      (ts.isAsExpression(init) && ts.isConstTypeReference(init.type))
    )
      init = init.expression
    if (!ts.isObjectLiteralExpression(init)) return undefined
    const out: Array<FunctionNode> = []
    for (const p of init.properties) {
      let fn: FunctionNode | undefined
      if (ts.isShorthandPropertyAssignment(p)) {
        const sym = checker.getShorthandAssignmentValueSymbol(p)
        fn = sym === undefined ? undefined : programFunction(sym.flags & ts.SymbolFlags.Alias ? checker.getAliasedSymbol(sym) : sym)
      } else if (ts.isPropertyAssignment(p)) {
        const v = p.initializer
        if (ts.isArrowFunction(v) || ts.isFunctionExpression(v)) fn = v
        else if (ts.isIdentifier(v)) {
          const sym = symbolOf(checker, v)
          fn = sym === undefined ? undefined : programFunction(sym)
        }
      }
      if (fn === undefined) return undefined
      out.push(fn)
    }
    return out
  }

  const programFunction = (sym: ts.Symbol): FunctionNode | undefined => {
    const d = sym.valueDeclaration
    if (d === undefined || d.getSourceFile().isDeclarationFile) return undefined
    if (ts.isFunctionDeclaration(d) && d.body !== undefined) return d
    if (ts.isVariableDeclaration(d) && d.initializer !== undefined && (d.parent.flags & ts.NodeFlags.Const) !== 0) {
      const init = d.initializer
      if (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) return init
    }
    return undefined
  }

  const s = summarise(fn)
  if (s.effect !== undefined) return { pure: false, why: s.effect }
  for (const [param, types] of s.changed) {
    const at = [...types.values()][0]!
    return { pure: false, why: `${locate(at)}: changes its argument \`${fn.parameters[param]?.name.getText() ?? param}\`` }
  }
  const reach = reachable(checker, s.stored)
  for (const [type, at] of s.changes) {
    const hit = aliasOf(checker, type, reach)
    if (hit !== undefined)
      return {
        pure: false,
        why: `${locate(at)}: changes an object of type \`${checker.typeToString(type)}\`, which may be a value of the caller's it stored (of type \`${checker.typeToString(hit)}\`)`,
      }
  }
  return { pure: true, read, calls: [...s.calls].sort((a, b) => a - b) }
}

/** An object or array literal: a cast of one names the type of what it allocates and hides nothing it was given. */
const freshLiteral = (e: ts.Expression): boolean =>
  ts.isParenthesizedExpression(e) ? freshLiteral(e.expression) : ts.isObjectLiteralExpression(e) || ts.isArrayLiteralExpression(e)

const union = <A>(...sets: ReadonlyArray<ReadonlySet<A>>): Set<A> => new Set(sets.flatMap((x) => [...x]))

const isAssignment = (k: ts.SyntaxKind): boolean => k >= K.FirstAssignment && k <= K.LastAssignment
const isStoringAssignment = (k: ts.SyntaxKind): boolean =>
  k === K.EqualsToken || k === K.QuestionQuestionEqualsToken || k === K.BarBarEqualsToken || k === K.AmpersandAmpersandEqualsToken

const symbolOf = (checker: ts.TypeChecker, e: ts.Node): ts.Symbol | undefined => {
  const at =
    ts.isShorthandPropertyAssignment(e.parent) && e.parent.name === e
      ? checker.getShorthandAssignmentValueSymbol(e.parent)
      : checker.getSymbolAtLocation(e)
  return at !== undefined && at.flags & ts.SymbolFlags.Alias ? checker.getAliasedSymbol(at) : at
}

const boundSymbols = (checker: ts.TypeChecker, name: ts.BindingName): Array<ts.Symbol> => {
  if (ts.isIdentifier(name)) {
    const s = checker.getSymbolAtLocation(name)
    return s === undefined ? [] : [s]
  }
  return name.elements.flatMap((el) => (ts.isOmittedExpression(el) ? [] : boundSymbols(checker, el.name)))
}

const declarationOf = (d: ts.VariableDeclaration | ts.BindingElement): ts.VariableDeclaration => {
  let n: ts.Node = d
  while (!ts.isVariableDeclaration(n)) n = n.parent
  return n
}

const nameOf = (f: FunctionNode): string =>
  f.name?.getText() ?? (ts.isVariableDeclaration(f.parent) ? f.parent.name.getText() : `the function at ${locate(f)}`)

/** Whether `e` names a global of the TypeScript or Node libraries. */
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
const isGlobal = (checker: ts.TypeChecker, e: ts.Expression, name: string): boolean =>
  ts.isIdentifier(e) && e.text === name && isLib(checker, e)

/** Whether `e` reads a module-level `let` or `var` (not one of `own`'s). */
const isModuleState = (checker: ts.TypeChecker, e: ts.Identifier, own: ReadonlySet<ts.Node>): boolean => {
  if (ts.isPropertyAccessExpression(e.parent) && e.parent.name === e) return false
  if (ts.isPropertyAssignment(e.parent) && e.parent.name === e) return false
  const sym = symbolOf(checker, e)
  const d = sym?.valueDeclaration
  if (d === undefined || !ts.isVariableDeclaration(d) || own.has(d) || d.getSourceFile().isDeclarationFile) return false
  return (
    (d.parent.flags & (ts.NodeFlags.Const | ts.NodeFlags.Using)) === 0 &&
    ts.isVariableStatement(d.parent.parent) &&
    ts.isSourceFile(d.parent.parent.parent)
  )
}

const isPrimitive = (checker: ts.TypeChecker, t: ts.Type): boolean =>
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
const membersOf = (checker: ts.TypeChecker, t: ts.Type): Array<ts.Type> => {
  const nn = checker.getNonNullableType(t)
  return nn.isUnion() ? nn.types : [nn]
}

/** An array's or a tuple's element types; `undefined` for any other type. */
const elementsOf = (checker: ts.TypeChecker, t: ts.Type): ReadonlyArray<ts.Type> | undefined =>
  checker.isArrayType(t) || checker.isTupleType(t) ? checker.getTypeArguments(t as ts.TypeReference) : undefined

const isArrayLike = (checker: ts.TypeChecker, e: ts.Expression): boolean =>
  membersOf(checker, checker.getTypeAtLocation(e)).every((m) => checker.isArrayType(m) || checker.isTupleType(m))

const isNamed = (checker: ts.TypeChecker, e: ts.Expression, names: ReadonlyArray<string>): boolean =>
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

/** Every object type a value of `types` can hold, itself included, to a depth of six. */
const reachable = (checker: ts.TypeChecker, types: ReadonlySet<ts.Type>): Set<ts.Type> => {
  const out = new Set<ts.Type>()
  const go = (t: ts.Type, depth: number) => {
    for (const m of membersOf(checker, t)) {
      if (out.has(m) || isPrimitive(checker, m)) continue
      out.add(m)
      if (depth === 0) continue
      const els = elementsOf(checker, m)
      if (els !== undefined) {
        for (const el of els) go(el, depth - 1)
        continue
      }
      for (const p of checker.getPropertiesOfType(m)) go(checker.getTypeOfSymbol(p), depth - 1)
      for (const info of checker.getIndexInfosOfType(m)) go(info.type, depth - 1)
    }
  }
  for (const t of types) go(t, 6)
  return out
}

/** A type a narrowing of `unknown` or `object` gives: `object`, `{}`, an intersection, a type with an index signature. */
const opaqueLike = (checker: ts.TypeChecker, t: ts.Type): boolean =>
  (t.flags & (ts.TypeFlags.Unknown | ts.TypeFlags.Any | ts.TypeFlags.NonPrimitive)) !== 0 ||
  (!checker.isArrayType(t) && !checker.isTupleType(t) && checker.getIndexInfosOfType(t).length > 0) ||
  t.isIntersection() ||
  ((t.flags & ts.TypeFlags.Object) !== 0 && checker.getPropertiesOfType(t).length === 0)

/** A type of `reach` an object of type `changed` may be, if any. */
const aliasOf = (checker: ts.TypeChecker, changed: ts.Type, reach: ReadonlySet<ts.Type>): ts.Type | undefined => {
  for (const r of reach) {
    if (r.flags & ts.TypeFlags.Any) return r
    for (const m of membersOf(checker, changed)) {
      if (m.flags & ts.TypeFlags.Any) return r
      if (opaqueLike(checker, r) && !(r.flags & ts.TypeFlags.Any)) {
        if (opaqueLike(checker, m)) return r
        continue
      }
      // A value reaches an expression of a wider type by assignment (r to m) and of a narrower one by a narrowing (m to
      // r). No narrowing but a type predicate or a cast, both refused, turns a read-only array into a mutable one.
      const arrays = (t: ts.Type) => checker.isArrayType(t) || checker.isTupleType(t)
      if (checker.isTypeAssignableTo(r, m) || (!(arrays(r) && arrays(m)) && checker.isTypeAssignableTo(m, r))) return r
    }
  }
  return undefined
}

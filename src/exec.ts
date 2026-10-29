// Statements, run: the part of the lowering where code has state.
//
// A function's body is run statement by statement over a state: the path
// condition that reaches the statement, the bindings in scope, and a store of
// cells, one per variable, each holding its current value (lazily, as all
// values here). An assignment, a field set or a `push` makes a new store; an
// `if`, a `switch` and a loop's iterations merge their paths' stores, value by
// value, under their conditions. Nothing changes in place, so a value read
// earlier keeps what it was.
//
// Objects are values here. That is JavaScript's meaning only while each object
// the function allocated has one owner, as in Rust:
// - a `const` may borrow a part of an object (`const a = s.attempts.find(...)`),
//   and a change through the borrow is a change to that part; so may a
//   function's parameter, when the argument is a variable or a part of one;
// - an object stored into another is moved: its variable is not read again;
// - a part is never stored in a second place, nor replaced while borrowed;
// - only what the function allocated changes: never an argument it was given
//   by value, nor anything it did not build.
// The executor refuses what breaks these rules.
//
// Loops. Where an array's bound is known (an array the code built, every array
// on the search side), a `for…of` is unrolled, exactly. A `for` or `while` loop
// is unrolled on the search side up to a limit; longer runs are not searched.
// On the proof side, a loop over an array of unknown length, and any `for` or
// `while`, is read through its invariants (`invariant(...)`, first in its
// body): they must hold on entry and be kept by an iteration from any state
// that satisfies them (obligations, proved apart), and after the loop the
// variables it changes are any values that satisfy them.
import ts from "typescript"
import type { Arith, Bool } from "z3-solver"
import { type Lowering, arithmetic, cond as condOf, firstIndex, inSpec, later, lowerCall, lowerExpr, member, propertyKey } from "./lower.ts"
import { ite, nullishOr, strictEq, truthy } from "./ops.ts"
import { CONTRACT_MODULE, declared, functionOf, ownModule, unwrap } from "./project.ts"
import { symbolicOf } from "./symbolic.ts"
import { type Env, type FunctionNode, type Thunk, UNDEFINED, Unsupported, type Val, lazy, lazyRecord, locate, memoElems } from "./value.ts"

const K = ts.SyntaxKind

/** What the proof code asks proved: true wherever `cond` holds. */
export interface Obligation {
  /** The same obligation on both sides and in every instance (a loop inlined twice): kind, place and phase. */
  readonly key: string
  readonly kind: "invariant" | "assert" | "requires"
  /** The claim as written. */
  readonly text: string
  /** `file:line:col`. */
  readonly at: string
  /** An invariant on entry, or kept by an iteration; an assert or a lemma's precondition, here. */
  readonly phase: "entry" | "kept" | "here"
  readonly cond: Bool<"main">
  readonly goal: Bool<"main">
  /** How many of the lowering's hints were made before it: those it may be proved with. */
  readonly hints: number
  /** For an invariant the verifier guessed, the law it restates. */
  readonly guessed?: string
}

/** A lemma the proof code called: proved apart, as a contract is. */
export interface LemmaUse {
  readonly file: string
  readonly name: string
}

/** A variable's root, or an argument passed by reference, and a path into it. */
export interface Place {
  readonly cell: number
  readonly steps: ReadonlyArray<Step>
  readonly text: string
}
type Step = { readonly kind: "field"; readonly name: string } | { readonly kind: "index"; readonly index: Arith<"main"> }

type Binding =
  /** A value fixed for the scope: what a closure captured, a value the caller gave. */
  | { readonly kind: "value"; readonly thunk: Thunk }
  | { readonly kind: "cell"; readonly cell: number }
  /** A borrow: reads and changes go through to the place. `isUndefined` when it may be none (`.find`). */
  | { readonly kind: "place"; readonly place: Place; readonly isUndefined?: Bool<"main"> }

interface Cell {
  readonly thunk: Thunk
  /** Allocated by the function: it may change. */
  readonly owned: boolean
  readonly name: string
  /** Its declared type: what a loop's havoc draws from. */
  readonly type: ts.Type | undefined
}

export interface State {
  readonly cond: Bool<"main">
  readonly vars: ReadonlyMap<string, Binding>
  readonly store: ReadonlyMap<number, Cell>
  /** Cells moved into another object, with where: never read again. */
  readonly dead: ReadonlyMap<number, string>
  /** The borrows the callers hold: a place none of them may see replaced. */
  readonly outer: ReadonlyArray<{ readonly name: string; readonly place: Place }>
}

interface Exits {
  readonly normal: State | undefined
  readonly returns: ReadonlyArray<{ readonly state: State; readonly value: Thunk; readonly owned: boolean }>
  readonly breaks: ReadonlyArray<State>
  readonly continues: ReadonlyArray<State>
}

/** An argument: a value, or a place the parameter borrows. */
export type Arg = { readonly kind: "value"; readonly thunk: Thunk; readonly owned: boolean } | { readonly kind: "place"; readonly place: Place }

/** The methods that change the array, map or set they are called on. */
const MUTATORS: ReadonlySet<string> = new Set(["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill", "copyWithin", "set", "add", "delete", "clear"])

/** How many times a `for` or `while` loop is unrolled on the search side. */
const UNROLL = 10

let nextCell = 0

const NONE: Exits = { normal: undefined, returns: [], breaks: [], continues: [] }

// ——— Running a function ———

/**
 * Runs `fn` with `args`. With no `caller`, on a store of its own: a call read as a value. With one, on the caller's
 * state, so a change made through a parameter that borrows a caller's place is the caller's: `after` is its state then.
 */
export const runFunction = (
  L: Lowering,
  fn: FunctionNode,
  closure: Env,
  args: ReadonlyArray<Arg>,
  caller: State | undefined,
  at: ts.Node,
): { readonly value: Thunk; readonly owned: boolean; readonly after: State | undefined } => {
  const z3 = L.u.z3
  const vars = new Map<string, Binding>()
  for (const [name, thunk] of closure) vars.set(name, { kind: "value", thunk })
  let st: State = {
    cond: caller?.cond ?? z3.Bool.val(true),
    vars,
    store: caller?.store ?? new Map(),
    dead: caller?.dead ?? new Map(),
    outer: caller === undefined ? [] : [...borrowsOf(caller), ...caller.outer],
  }
  fn.parameters.forEach((p, i) => {
    if (p.dotDotDotToken !== undefined) throw new Unsupported("rest parameters are not modeled", p)
    const arg = args[i]
    const type = L.checker.getTypeAtLocation(p)
    if (arg?.kind === "place" && ts.isIdentifier(p.name)) {
      st = bindVar(st, p.name.text, { kind: "place", place: { ...arg.place, text: p.name.text } })
      return
    }
    const now = st
    const thunk: Thunk =
      arg !== undefined
        ? (arg as Extract<Arg, { kind: "value" }>).thunk
        : p.initializer !== undefined
          ? later(L, () => lowerExpr(L, p.initializer!, envOf(L, now)))
          : () => UNDEFINED
    st = bindName(L, st, p.name, thunk, arg?.kind === "value" ? arg.owned : false, type)
  })
  const body = fn.body!
  if (!ts.isBlock(body)) {
    const now = st
    return { value: later(L, () => lowerExpr(L, body, envOf(L, now))), owned: fresh(body), after: caller === undefined ? undefined : { ...caller, store: st.store } }
  }
  const x = statements(L, body.statements, st)
  const results = [...x.returns, ...(x.normal === undefined ? [] : [{ state: x.normal, value: (() => UNDEFINED) as Thunk, owned: true }])]
  if (results.length === 0) throw new Unsupported("a function that never returns", fn)
  const last = results[results.length - 1]!
  const value = lazy(() => results.slice(0, -1).reduceRight((acc, r) => ite(L.u, r.state.cond, r.value(), acc, at), last.value()))
  if (caller === undefined) return { value, owned: results.every((r) => r.owned), after: undefined }
  const merged = merge(L, results.map((r) => r.state), at)!
  return { value, owned: results.every((r) => r.owned), after: { ...caller, store: merged.store, dead: merged.dead } }
}

// ——— Bindings, cells and places ———

const bindVar = (st: State, name: string, b: Binding): State => {
  const vars = new Map(st.vars)
  vars.set(name, b)
  return { ...st, vars }
}

const newCell = (L: Lowering, st: State, name: string, thunk: Thunk, owned: boolean, type: ts.Type | undefined): State => {
  const cell = nextCell++
  const store = new Map(st.store)
  store.set(cell, { thunk, owned, name, type })
  return bindVar({ ...st, store }, name, { kind: "cell", cell })
}

/** Binds a name, or each name of an object pattern, to a cell holding the value (or its field). */
const bindName = (L: Lowering, st: State, name: ts.BindingName, thunk: Thunk, owned: boolean, type: ts.Type | undefined): State => {
  if (ts.isIdentifier(name)) return newCell(L, st, name.text, thunk, owned, type)
  if (!ts.isObjectBindingPattern(name)) throw new Unsupported("array destructuring is not modeled", name)
  let out = st
  for (const el of name.elements) {
    if (el.dotDotDotToken !== undefined || el.initializer !== undefined) throw new Unsupported("rest and default values in destructuring are not modeled", el)
    const key = el.propertyName === undefined ? (el.name as ts.Identifier).text : propertyKey(el.propertyName)
    out = bindName(L, out, el.name, later(L, () => member(L, thunk(), key, el, type)), false, L.checker.getTypeAtLocation(el))
  }
  return out
}

/** The bindings as values, for reading expressions: each read from the store as it is in this state. */
const envs = new WeakMap<State, Env>()
const envOf = (L: Lowering, st: State): Env => {
  let env = envs.get(st)
  if (env !== undefined) return env
  const m = new Map<string, Thunk>()
  for (const [name, b] of st.vars) {
    if (b.kind === "value") m.set(name, b.thunk)
    else if (b.kind === "cell") m.set(name, () => readCell(st, b.cell, name))
    else
      m.set(name, () => {
        const v = readPlace(L, st, b.place)
        return b.isUndefined === undefined ? v : { kind: "maybe", isNull: L.u.z3.Bool.val(false), isUndefined: b.isUndefined, value: v }
      })
  }
  env = m
  envs.set(st, env)
  return env
}

const readCell = (st: State, cell: number, name: string): Val => {
  const moved = st.dead.get(cell)
  if (moved !== undefined) throw new Unsupported(`\`${name}\` was stored in ${moved}; read it from there`)
  return st.store.get(cell)!.thunk()
}

/** A value present: a borrow is read where the type checker has shown it present. */
const present = (v: Val): Val => (v.kind === "maybe" ? (v.value ?? UNDEFINED) : v)

const readPlace = (L: Lowering, st: State, p: Place): Val => {
  let v = readCell(st, p.cell, p.text)
  for (const s of p.steps) {
    v = present(v)
    if (s.kind === "field") {
      if (v.kind !== "record") throw new Unsupported(`\`${p.text}\`: a field of a ${v.kind}`)
      v = v.field(s.name) ?? UNDEFINED
    } else {
      if (v.kind !== "array") throw new Unsupported(`\`${p.text}\`: an element of a ${v.kind}`)
      v = v.elem(s.index)
    }
  }
  return v
}

/**
 * `v` with the value at `steps` replaced by `f` of it: a new value, every other part shared. `absent`: the last field is
 * deleted, so the object no longer holds its key.
 */
const update = (L: Lowering, v: Val, steps: ReadonlyArray<Step>, f: (old: Val) => Val, at: ts.Node, absent: boolean): Val => {
  const [s, ...rest] = steps
  if (s === undefined) return f(v)
  const z3 = L.u.z3
  const o = present(v)
  if (s.kind === "field") {
    if (o.kind !== "record") throw new Unsupported(`a field set on a ${o.kind}`, at)
    const gone = absent && rest.length === 0
    return lazyRecord(
      (name) => (name === s.name ? update(L, o.field(name) ?? UNDEFINED, rest, f, at, absent) : o.field(name)),
      undefined,
      o.has === undefined ? undefined : (name) => (name === s.name ? z3.Bool.val(!gone) : o.has!(name)),
    )
  }
  if (o.kind !== "array") throw new Unsupported(`an element set on a ${o.kind}`, at)
  return {
    kind: "array",
    length: o.length,
    ...(o.size === undefined ? {} : { size: o.size }),
    ...(o.maxSize === undefined ? {} : { maxSize: o.maxSize }),
    elem: memoElems((j) => {
      if (j === s.index || j.eqIdentity(s.index)) return update(L, o.elem(j), rest, f, at, absent)
      if (z3.isIntVal(j) && z3.isIntVal(s.index)) return o.elem(j)
      return ite(L.u, j.eq(s.index), update(L, o.elem(j), rest, f, at, absent), o.elem(j), at)
    }),
  }
}

const writePlace = (L: Lowering, st: State, p: Place, f: (old: Val) => Val, at: ts.Node, absent = false): State => {
  const old = st.store.get(p.cell)!
  const store = new Map(st.store)
  const before = st
  store.set(p.cell, { ...old, thunk: later(L, () => update(L, readCell(before, p.cell, p.text), p.steps, f, at, absent)) })
  return { ...st, store }
}

/** `a` is a prefix of `b`, or may be: two indices not known to differ may be the same. */
const prefix = (a: Place, b: Place): boolean =>
  a.cell === b.cell &&
  a.steps.length <= b.steps.length &&
  a.steps.every((s, i) => {
    const t = b.steps[i]!
    return s.kind === "field" ? t.kind === "field" && t.name === s.name : t.kind === "index"
  })

const borrowsOf = (st: State): Array<{ name: string; place: Place }> =>
  [...st.vars].flatMap(([name, b]) => (b.kind === "place" ? [{ name, place: b.place }] : []))

/** The place `e` names, when it names one: a variable, a field or element of one, what `.find` or `.at` found in one. */
const placeOf = (L: Lowering, st: State, e: ts.Expression): { readonly place: Place; readonly isUndefined?: Bool<"main"> } | undefined => {
  const z3 = L.u.z3
  const x = unwrap(e)
  if (ts.isIdentifier(x)) {
    const b = st.vars.get(x.text)
    if (b?.kind === "cell") return { place: { cell: b.cell, steps: [], text: x.text } }
    if (b?.kind === "place") return { place: b.place, ...(b.isUndefined === undefined ? {} : { isUndefined: b.isUndefined }) }
    return undefined
  }
  if (ts.isPropertyAccessExpression(x) && x.questionDotToken === undefined && !(x.flags & ts.NodeFlags.OptionalChain)) {
    const base = placeOf(L, st, x.expression)
    return base === undefined ? undefined : { place: extend(base.place, { kind: "field", name: x.name.text }, x.getText()) }
  }
  if (ts.isElementAccessExpression(x) && ts.isNumericLiteral(x.argumentExpression) && /^\d+$/.test(x.argumentExpression.text)) {
    const base = placeOf(L, st, x.expression)
    return base === undefined ? undefined : { place: extend(base.place, { kind: "index", index: z3.Int.val(Number(x.argumentExpression.text)) }, x.getText()) }
  }
  if (ts.isCallExpression(x) && ts.isPropertyAccessExpression(x.expression) && x.arguments.length === 1) {
    const method = x.expression.name.text
    if (method !== "find" && method !== "at") return undefined
    const base = placeOf(L, st, x.expression.expression)
    if (base === undefined) return undefined
    const arr = present(readPlace(L, st, base.place))
    if (arr.kind !== "array") return undefined
    if (method === "at") {
      const a = x.arguments[0]!
      const k = ts.isNumericLiteral(a) ? BigInt(a.text) : ts.isPrefixUnaryExpression(a) && a.operator === K.MinusToken && ts.isNumericLiteral(a.operand) ? -BigInt(a.operand.text) : undefined
      if (k === undefined) return undefined
      const index = k < 0n ? arr.length.add(z3.Int.val(k)) : z3.Int.val(k)
      return { place: extend(base.place, { kind: "index", index }, x.getText()), isUndefined: z3.Or(index.lt(0), index.ge(arr.length)) }
    }
    const f = lowerExpr(L, x.arguments[0]!, envOf(L, st))
    if (f.kind !== "fn") return undefined
    const { found, k } = firstIndex(
      L,
      arr,
      (i) => truthy(L.u, lowerCall(L, f.node, f.env, [arr.elem(i), { kind: "int", origin: "count", term: i }], x)),
      x,
    )
    return { place: extend(base.place, { kind: "index", index: k }, x.getText()), isUndefined: z3.Not(found) }
  }
  return undefined
}

const extend = (p: Place, s: Step, text: string): Place => ({ cell: p.cell, steps: [...p.steps, s], text })

/** Whether an object-typed value is read here: a borrow is made only of one, a primitive is copied. */
const isObjectTyped = (L: Lowering, e: ts.Node): boolean => {
  const t = L.checker.getNonNullableType(L.checker.getTypeAtLocation(e))
  return (t.isUnion() ? t.types : [t]).some((m) => (m.flags & (ts.TypeFlags.Object | ts.TypeFlags.NonPrimitive | ts.TypeFlags.Intersection)) !== 0)
}

/** An expression that allocates: a literal, an object or an array the code builds here. */
const fresh = (e: ts.Expression): boolean => {
  const x = unwrap(e)
  return ts.isObjectLiteralExpression(x) || ts.isArrayLiteralExpression(x) || ts.isNewExpression(x)
}

/** A change may be made through `p`: its root is the function's own, and no one borrows into what it replaces. */
const changeable = (L: Lowering, st: State, p: Place, replaces: boolean, at: ts.Node): void => {
  const cell = st.store.get(p.cell)!
  if (!cell.owned) throw new Unsupported(`changes \`${p.text}\`, which the function did not allocate (an argument given by value, or what it was given)`, at)
  const moved = st.dead.get(p.cell)
  if (moved !== undefined) throw new Unsupported(`\`${cell.name}\` was stored in ${moved}; change it there`, at)
  if (!replaces) return
  for (const b of [...borrowsOf(st), ...st.outer])
    if (b.place !== p && prefix(p, b.place) && b.place.steps.length > p.steps.length)
      throw new Unsupported(`replaces \`${p.text}\` while \`${b.name}\` refers into it`, at)
}

/**
 * What storing `e` into `target` does to ownership: a variable that holds an object of the function's is moved (no
 * longer read); a part of one stored in a second place is refused, unless it is the very place being written.
 */
const storing = (L: Lowering, st: State, e: ts.Expression, target: Place | undefined, where: string, at: ts.Node): State => {
  let out = st
  const visit = (x: ts.Expression): void => {
    const y = unwrap(x)
    if (ts.isConditionalExpression(y)) return (visit(y.whenTrue), visit(y.whenFalse))
    if (ts.isBinaryExpression(y) && [K.QuestionQuestionToken, K.BarBarToken, K.AmpersandAmpersandToken].includes(y.operatorToken.kind))
      return (visit(y.left), visit(y.right))
    if (ts.isObjectLiteralExpression(y)) {
      for (const p of y.properties)
        if (ts.isPropertyAssignment(p)) visit(p.initializer)
        else if (ts.isShorthandPropertyAssignment(p)) visit(p.name)
        else if (ts.isSpreadAssignment(p)) spread(p.expression)
      return
    }
    if (ts.isArrayLiteralExpression(y)) {
      for (const el of y.elements) if (ts.isSpreadElement(el)) spread(el.expression)
        else visit(el)
      return
    }
    if (!isObjectTyped(L, y)) return
    if (ts.isIdentifier(y)) {
      const b = out.vars.get(y.text)
      if (b?.kind === "cell" && out.store.get(b.cell)!.owned) {
        const dead = new Map(out.dead)
        dead.set(b.cell, where)
        out = { ...out, dead }
        return
      }
    }
    const p = placeOf(L, out, y)
    if (p !== undefined && out.store.get(p.place.cell)!.owned && !(target !== undefined && samePlace(p.place, target)))
      throw new Unsupported(`stores \`${y.getText()}\`, a part of an object the function holds, in a second place (${where})`, at)
  }
  /** A spread copies the parts of what it spreads: of one of the function's objects, only its primitive parts may be copied elsewhere. */
  const spread = (x: ts.Expression): void => {
    const y = unwrap(x)
    if (ts.isBinaryExpression(y) && y.operatorToken.kind === K.QuestionQuestionToken) return (spread(y.left), spread(y.right))
    if (ts.isConditionalExpression(y)) return (spread(y.whenTrue), spread(y.whenFalse))
    const p = placeOf(L, out, y)
    if (p === undefined || !out.store.get(p.place.cell)!.owned || (target !== undefined && samePlace(p.place, target))) return
    const t = L.checker.getNonNullableType(L.checker.getTypeAtLocation(y))
    const parts = L.checker.isArrayType(t) ? [L.checker.getTypeArguments(t as ts.TypeReference)[0]!] : L.checker.getPropertiesOfType(t).map((s) => L.checker.getTypeOfSymbol(s))
    if (parts.some((pt) => isObjectType(L, pt))) throw new Unsupported(`spreads \`${y.getText()}\`, whose parts are objects the function holds, into a second place (${where})`, at)
  }
  visit(e)
  return out
}

const isObjectType = (L: Lowering, t: ts.Type): boolean => {
  const n = L.checker.getNonNullableType(t)
  return (n.isUnion() ? n.types : [n]).some((m) => (m.flags & (ts.TypeFlags.Object | ts.TypeFlags.NonPrimitive | ts.TypeFlags.Intersection)) !== 0)
}

const samePlace = (a: Place, b: Place): boolean =>
  a.cell === b.cell &&
  a.steps.length === b.steps.length &&
  a.steps.every((s, i) => {
    const t = b.steps[i]!
    return s.kind === "field" ? t.kind === "field" && t.name === s.name : t.kind === "index" && t.index.eqIdentity(s.index)
  })

// ——— Merging paths ———

/** The state after paths that rejoin: under the condition of each, its values. Paths whose condition is false are dropped. */
const merge = (L: Lowering, states: ReadonlyArray<State | undefined>, at: ts.Node): State | undefined => {
  const z3 = L.u.z3
  const live = states.filter((s): s is State => s !== undefined && !z3.isFalse(s.cond))
  if (live.length <= 1) return live[0]
  return live.reduce((a, b) => {
    const store = new Map(a.store)
    for (const [cell, cb] of b.store) {
      const ca = a.store.get(cell)
      if (ca === undefined) store.set(cell, cb)
      else if (ca.thunk !== cb.thunk) {
        const ta = ca.thunk
        const tb = cb.thunk
        const c = a.cond
        store.set(cell, { ...ca, owned: ca.owned && cb.owned, thunk: lazy(() => ite(L.u, c, ta(), tb(), at)) })
      }
    }
    const vars = new Map<string, Binding>()
    for (const [name, x] of a.vars) if (b.vars.get(name) === x) vars.set(name, x)
    const dead = new Map([...a.dead, ...b.dead])
    return { cond: z3.Or(a.cond, b.cond), vars, store, dead, outer: a.outer }
  })
}

const withCond = (st: State, cond: Bool<"main">): State => ({ ...st, cond })

/** Each exit of a block, with the bindings it declared out of scope. */
const scoped = (x: Exits, vars: ReadonlyMap<string, Binding>): Exits => {
  const out = (s: State): State => ({ ...s, vars })
  return {
    normal: x.normal === undefined ? undefined : out(x.normal),
    returns: x.returns,
    breaks: x.breaks.map(out),
    continues: x.continues.map(out),
  }
}

const join = (...xs: ReadonlyArray<Exits>): Pick<Exits, "returns" | "breaks" | "continues"> => ({
  returns: xs.flatMap((x) => x.returns),
  breaks: xs.flatMap((x) => x.breaks),
  continues: xs.flatMap((x) => x.continues),
})

// ——— Statements ———

const statements = (L: Lowering, stmts: ReadonlyArray<ts.Statement>, st: State): Exits => {
  let cur: State | undefined = st
  const returns: Array<Exits["returns"][number]> = []
  const breaks: Array<State> = []
  const continues: Array<State> = []
  for (const s of stmts) {
    if (cur === undefined || L.u.z3.isFalse(cur.cond)) break
    const x = statement(L, s, cur)
    returns.push(...x.returns)
    breaks.push(...x.breaks)
    continues.push(...x.continues)
    cur = x.normal
  }
  return { normal: cur, returns, breaks, continues }
}

const block = (L: Lowering, s: ts.Statement, st: State): Exits => scoped(statements(L, ts.isBlock(s) ? s.statements : [s], st), st.vars)

const normal = (st: State): Exits => ({ ...NONE, normal: st })

const statement = (L: Lowering, s: ts.Statement, st: State): Exits => {
  const z3 = L.u.z3
  if (ts.isBlock(s)) return block(L, s, st)
  if (ts.isEmptyStatement(s)) return normal(st)
  if (ts.isVariableStatement(s)) return normal(declare(L, s.declarationList, st))
  if (ts.isFunctionDeclaration(s)) {
    if (s.name === undefined || s.body === undefined) throw new Unsupported("a function declaration with no name or body", s)
    return normal(bindVar(st, s.name.text, { kind: "value", thunk: () => ({ kind: "fn", node: s, env: envOf(L, st) }) }))
  }
  if (ts.isExpressionStatement(s)) return normal(expressionStatement(L, s.expression, st))
  if (ts.isReturnStatement(s)) {
    if (s.expression === undefined) return { ...NONE, returns: [{ state: st, value: () => UNDEFINED, owned: true }] }
    const r = valueOf(L, s.expression, st)
    if (isObjectTyped(L, s.expression)) {
      const p = placeOf(L, r.state, s.expression)
      if (p !== undefined && isCallerPlace(r.state, p.place))
        throw new Unsupported("returns a reference into an argument it borrows; return a copy, or change it in place", s)
    }
    return { ...NONE, returns: [{ state: r.state, value: r.value, owned: r.owned }] }
  }
  if (ts.isIfStatement(s)) {
    const c = condOf(L, s.expression, envOf(L, st))
    const yes = z3.isFalse(c) ? NONE : block(L, s.thenStatement, withCond(st, z3.And(st.cond, c)))
    const no = z3.isTrue(c) ? NONE : s.elseStatement === undefined ? normal(withCond(st, z3.And(st.cond, z3.Not(c)))) : block(L, s.elseStatement, withCond(st, z3.And(st.cond, z3.Not(c))))
    return { normal: merge(L, [yes.normal, no.normal], s), ...join(yes, no) }
  }
  if (ts.isSwitchStatement(s)) return switchStatement(L, s, st)
  if (ts.isBreakStatement(s)) {
    if (s.label !== undefined) throw new Unsupported("a labelled `break` is not modeled", s)
    return { ...NONE, breaks: [st] }
  }
  if (ts.isContinueStatement(s)) {
    if (s.label !== undefined) throw new Unsupported("a labelled `continue` is not modeled", s)
    return { ...NONE, continues: [st] }
  }
  if (ts.isForOfStatement(s)) return forOf(L, s, st)
  if (ts.isForStatement(s) || ts.isWhileStatement(s)) return guarded(L, s, st)
  throw new Unsupported(`a ${K[s.kind]} is not modeled`, s)
}

/** `const`/`let` declarations: a borrow, a call run for its effects, or a value read when first used. */
const declare = (L: Lowering, list: ts.VariableDeclarationList, st: State): State => {
  const isConst = (list.flags & ts.NodeFlags.Const) !== 0
  if (!isConst && (list.flags & ts.NodeFlags.Let) === 0) throw new Unsupported("`var` is not modeled; use `const` or `let`", list)
  let out = st
  for (const d of list.declarations) {
    const type = L.checker.getTypeAtLocation(d.name)
    if (d.initializer === undefined) {
      if (isConst) throw new Unsupported("a `const` with no value", d)
      out = bindName(L, out, d.name, () => UNDEFINED, true, type)
      continue
    }
    const init = d.initializer
    if (ts.isIdentifier(d.name) && isObjectTyped(L, init) && !fresh(init)) {
      const p = placeOf(L, out, init)
      const borrowed = ts.isIdentifier(unwrap(init)) ? out.vars.get((unwrap(init) as ts.Identifier).text)?.kind === "place" : true
      if (p !== undefined && borrowed) {
        if (!isConst) throw new Unsupported(`a \`let\` that refers into an object the function holds is not modeled; use \`const\``, d)
        out = bindVar(out, d.name.text, { kind: "place", place: { ...p.place, text: d.name.text }, ...(p.isUndefined === undefined ? {} : { isUndefined: p.isUndefined }) })
        continue
      }
      if (p !== undefined && out.store.get(p.place.cell)?.owned)
        throw new Unsupported(`\`${d.name.text}\` would be a second name for \`${init.getText()}\`, which the function holds; use \`${init.getText()}\``, d)
    }
    const r = valueOf(L, init, out)
    out = bindName(L, r.state, d.name, r.value, r.owned, type)
  }
  return out
}

/**
 * An expression's value in this state. A call of one of the program's functions that borrows a place is run now, on
 * this state, so its changes are made; anything else is read when first used.
 */
const valueOf = (L: Lowering, e: ts.Expression, st: State): { readonly state: State; readonly value: Thunk; readonly owned: boolean } => {
  const x = unwrap(e)
  if (ts.isCallExpression(x)) {
    const run = runInline(L, x, st, false)
    if (run !== undefined) return run
  }
  return { state: st, value: later(L, () => lowerExpr(L, e, envOf(L, st))), owned: fresh(e) }
}

/** Whether a place belongs to a caller: its cell is no binding of this frame's. */
const isCallerPlace = (st: State, p: Place): boolean => ![...st.vars.values()].some((b) => b.kind === "cell" && b.cell === p.cell)

/**
 * A call of a function of the program run on this state, its parameters borrowing the places its arguments name: when
 * one does (or `always`). `undefined` when it is no such call, or borrows nothing and need not run now.
 */
const runInline = (
  L: Lowering,
  e: ts.CallExpression,
  st: State,
  always: boolean,
): { readonly state: State; readonly value: Thunk; readonly owned: boolean } | undefined => {
  const target = programFunction(L, e, st)
  if (target === undefined) return undefined
  const places = e.arguments.map((a) => (isObjectTyped(L, a) && !fresh(a) ? placeOf(L, st, a) : undefined))
  if (!always && !places.some((p) => p !== undefined && st.store.get(p.place.cell)?.owned)) return undefined
  if (L.stack.includes(target.node)) throw new Unsupported("recursion is not modeled", e)
  const args: Array<Arg> = e.arguments.map((a, i) => {
    if (ts.isSpreadElement(a)) throw new Unsupported("spread arguments are not modeled", a)
    const p = places[i]
    if (p !== undefined) {
      if (p.isUndefined !== undefined) {
        const t = L.checker.getTypeAtLocation(a)
        if ((t.isUnion() ? t.types : [t]).some((m) => m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)))
          throw new Unsupported(`passes \`${a.getText()}\`, which may be undefined here, to a function that may change it`, a)
      }
      return { kind: "place", place: p.place }
    }
    return { kind: "value", thunk: later(L, () => lowerExpr(L, a, envOf(L, st))), owned: fresh(a) }
  })
  L.stack.push(target.node)
  try {
    const r = runFunction(L, target.node, target.env, args, st, e)
    return { state: { ...r.after!, vars: st.vars, outer: st.outer, cond: st.cond }, value: r.value, owned: r.owned }
  } finally {
    L.stack.pop()
  }
}

/** The program's function a call names, read from its source: not a declared one, nor an adapter's, nor a hint. */
const programFunction = (L: Lowering, e: ts.CallExpression, st: State): { readonly node: FunctionNode; readonly env: Env } | undefined => {
  const callee = e.expression
  if (!ts.isIdentifier(callee)) return undefined
  if (L.trust.assumptions.of(callee) !== undefined) return undefined
  const b = st.vars.get(callee.text)
  if (b?.kind === "value" || b?.kind === "cell") {
    const v = b.kind === "value" ? b.thunk() : readCell(st, b.cell, callee.text)
    return v.kind === "fn" ? { node: v.node, env: v.env } : undefined
  }
  if (b !== undefined) return undefined
  let sym = L.checker.getSymbolAtLocation(callee)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = L.checker.getAliasedSymbol(sym)
  const d = sym?.valueDeclaration
  if (d === undefined || d.getSourceFile().isDeclarationFile || d.getSourceFile().fileName.includes("/node_modules/")) return undefined
  if (ownModule(d.getSourceFile().fileName, CONTRACT_MODULE)) return undefined
  if (ts.isFunctionDeclaration(d) && d.body !== undefined) return { node: d, env: new Map() }
  if (ts.isVariableDeclaration(d) && d.initializer !== undefined && (d.parent.flags & ts.NodeFlags.Const) !== 0) {
    const init = unwrap(d.initializer)
    if ((ts.isArrowFunction(init) || ts.isFunctionExpression(init)) && init.asteriskToken === undefined && !init.modifiers?.some((m) => m.kind === K.AsyncKeyword))
      return { node: init, env: new Map() }
  }
  return undefined
}

const ASSIGN_OPS: ReadonlyMap<ts.SyntaxKind, ts.SyntaxKind> = new Map([
  [K.PlusEqualsToken, K.PlusToken],
  [K.MinusEqualsToken, K.MinusToken],
  [K.AsteriskEqualsToken, K.AsteriskToken],
])

/** A statement that is an expression: an assignment, a change, a call run for what it changes, or a hint. */
const expressionStatement = (L: Lowering, e: ts.Expression, st: State): State => {
  const u = L.u
  const x = unwrap(e)
  if (ts.isBinaryExpression(x) && x.operatorToken.kind >= K.FirstAssignment && x.operatorToken.kind <= K.LastAssignment) {
    const op = x.operatorToken.kind
    const env = envOf(L, st)
    const rhs = later(L, () => lowerExpr(L, x.right, env))
    const compute = (old: Val): Val => {
      if (op === K.EqualsToken) return rhs()
      if (op === K.QuestionQuestionEqualsToken) return nullishOr(u, old, rhs, x)
      if (op === K.BarBarEqualsToken) return ite(u, truthy(u, old), old, rhs(), x)
      if (op === K.AmpersandAmpersandEqualsToken) return ite(u, truthy(u, old), rhs(), old, x)
      const base = ASSIGN_OPS.get(op)
      if (base === undefined) throw new Unsupported(`operator ${ts.tokenToString(op)} is not modeled`, x.operatorToken)
      return arithmetic(L, base, old, rhs(), x)
    }
    return assign(L, st, x.left, compute, x.right, x)
  }
  if ((ts.isPrefixUnaryExpression(x) || ts.isPostfixUnaryExpression(x)) && (x.operator === K.PlusPlusToken || x.operator === K.MinusMinusToken)) {
    const op = x.operator === K.PlusPlusToken ? K.PlusToken : K.MinusToken
    return assign(L, st, x.operand, (old) => {
      if (old.kind === "int" && old.origin === "bigint") return { ...old, term: op === K.PlusToken ? old.term.add(1) : old.term.sub(1) }
      throw new Unsupported(`\`${ts.tokenToString(x.operator)}\` on a ${old.kind}: arithmetic on \`number\` rounds, which the model of numbers does not see: use \`bigint\` where the values are whole, or move it into a function the spec declares with \`assume\``, x)
    }, undefined, x)
  }
  if (ts.isDeleteExpression(x)) return assign(L, st, x.expression, () => UNDEFINED, undefined, x, true)
  if (ts.isCallExpression(x)) return callStatement(L, x, st)
  throw new Unsupported(`an expression statement (${K[x.kind]}) has no effect the verifier models`, x)
}

/** `target op= …`: a variable's cell, or a place in an object the function holds, set to `compute(old)`. */
const assign = (
  L: Lowering,
  st: State,
  target: ts.Expression,
  compute: (old: Val) => Val,
  rhs: ts.Expression | undefined,
  at: ts.Node,
  deleting = false,
): State => {
  const t = unwrap(target)
  if (ts.isIdentifier(t)) {
    const b = st.vars.get(t.text)
    if (b?.kind !== "cell") throw new Unsupported(`assigns \`${t.text}\`, which is ${b?.kind === "place" ? "a reference into an object; change its fields" : "not a variable of this function (a closure's capture, or a global)"}`, at)
    const cell = st.store.get(b.cell)!
    if (rhs !== undefined && isObjectTyped(L, rhs) && !fresh(rhs)) {
      const p = placeOf(L, st, rhs)
      if (p !== undefined && st.store.get(p.place.cell)?.owned)
        throw new Unsupported(`\`${t.text}\` would be a second name for \`${rhs.getText()}\`, which the function holds`, at)
    }
    const next = rhs === undefined ? st : storing(L, st, rhs, undefined, `\`${t.text}\``, at)
    const store = new Map(next.store)
    const before = st
    store.set(b.cell, { ...cell, owned: rhs === undefined ? cell.owned : fresh(rhs) || (cell.owned && !isObjectTyped(L, rhs)), thunk: later(L, () => compute(readCell(before, b.cell, t.text))) })
    return { ...next, store }
  }
  if (!ts.isPropertyAccessExpression(t) && !ts.isElementAccessExpression(t))
    throw new Unsupported("an assignment to a pattern is not modeled", at)
  const objType = L.checker.getTypeAtLocation(t.expression)
  if ((objType.isUnion() ? objType.types : [objType]).some((m) => m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)))
    throw new Unsupported(`changes \`${t.expression.getText()}\`, which the type checker has not shown present here`, at)
  const base = placeOf(L, st, t.expression)
  if (base === undefined) throw new Unsupported(`changes \`${t.expression.getText()}\`, which is no variable of this function nor part of one`, at)
  const step: Step = ts.isPropertyAccessExpression(t)
    ? { kind: "field", name: t.name.text }
    : ts.isNumericLiteral(t.argumentExpression) && /^\d+$/.test(t.argumentExpression.text)
      ? { kind: "index", index: L.u.z3.Int.val(Number(t.argumentExpression.text)) }
      : (() => {
          throw new Unsupported("an element set `a[i] = …` is modeled for a literal index", at)
        })()
  const place = extend(base.place, step, t.getText())
  changeable(L, st, place, true, at)
  const next = rhs === undefined ? st : storing(L, st, rhs, place, `\`${t.getText()}\``, at)
  return writePlace(L, next, place, compute, at, deleting)
}

/** A call made for what it does: a hint, a `push`, or one of the program's functions run on this state. */
const callStatement = (L: Lowering, e: ts.CallExpression, st: State): State => {
  const u = L.u
  const z3 = u.z3
  const callee = e.expression
  if (declared(L.checker, callee, CONTRACT_MODULE, "invariant"))
    throw new Unsupported("an invariant goes first in a loop's body, before any other statement", e)
  if (declared(L.checker, callee, CONTRACT_MODULE, "assert")) {
    const goal = claim(L, st, e, undefined)
    obligate(L, "assert", e, "here", st.cond, goal)
    // Proof code is for proofs: the search side, which runs the code exactly, checks a hint and never leans on it.
    if (u.bound === undefined) L.hints.push(z3.Implies(st.cond, goal))
    return st
  }
  const lem = lemmaOf(L, callee)
  if (lem !== undefined) {
    const env = envOf(L, st)
    const args = e.arguments.map((a) => lowerExpr(L, a, env))
    L.lemmas.set(`${lem.file}#${lem.name}`, { file: lem.file, name: lem.name })
    if (lem.requires !== undefined) {
      const req = inSpec(L, () => truthy(u, lowerCall(L, lem.requires!, new Map(), args, e)))
      obligate(L, "requires", e, "here", st.cond, req, `${lem.name}: ${lem.requires.getText()}`)
    }
    if (u.bound === undefined) L.hints.push(z3.Implies(st.cond, inSpec(L, () => truthy(u, lowerCall(L, lem.statement, new Map(), args, e)))))
    return st
  }
  if (ts.isPropertyAccessExpression(callee)) {
    const method = callee.name.text
    const recv = placeOf(L, st, callee.expression)
    if (recv !== undefined && method === "push") {
      changeable(L, st, recv.place, false, e)
      let next = st
      for (const a of e.arguments) {
        if (ts.isSpreadElement(a)) throw new Unsupported("`push(...xs)` is not modeled", a)
        next = storing(L, next, a, undefined, `\`${callee.expression.getText()}\``, e)
      }
      const env = envOf(L, st)
      const items = e.arguments.map((a) => later(L, () => lowerExpr(L, a, env)))
      return writePlace(L, next, recv.place, (old) => appended(L, old, items, e), e)
    }
    if (recv !== undefined && MUTATORS.has(method))
      throw new Unsupported(`\`.${method}\` is not modeled; \`.push\` is`, e)
  }
  const run = runInline(L, e, st, true)
  if (run !== undefined) return run.state
  if (L.trust.assumptions.of(callee) !== undefined) {
    // A declared function changes nothing: read now, so a refusal (a call no declaration covers) is not missed.
    lowerExpr(L, e, envOf(L, st))
    return st
  }
  throw new Unsupported(`a call whose result is unused (\`${callee.getText()}\`) has an effect the verifier does not model`, e)
}

/** `arr` with `items` after its elements. */
const appended = (L: Lowering, v: Val, items: ReadonlyArray<Thunk>, at: ts.Node): Val => {
  const arr = present(v)
  if (arr.kind !== "array") throw new Unsupported(`\`.push\` on a ${arr.kind}`, at)
  const z3 = L.u.z3
  const n = items.length
  const bound = arr.maxSize ?? arr.size ?? L.u.bound
  return {
    kind: "array",
    length: arr.length.add(n),
    ...(arr.size === undefined ? {} : { size: arr.size + n }),
    ...(bound === undefined ? {} : { maxSize: bound + n }),
    elem: memoElems((j) => {
      let out = arr.elem(j)
      for (let k = n - 1; k >= 0; k--) {
        const at_ = arr.length.add(k)
        if (z3.isIntVal(j) && z3.isIntVal(at_)) {
          if (j.value() === at_.value()) return items[k]!()
          continue
        }
        out = ite(L.u, j.eq(at_), items[k]!(), out, at)
      }
      return out
    }),
  }
}

/** `switch`: the first case whose test is `===` the value, or `default`, and on through the cases after it until a `break`. */
const switchStatement = (L: Lowering, s: ts.SwitchStatement, st: State): Exits => {
  const z3 = L.u.z3
  const env = envOf(L, st)
  const d = later(L, () => lowerExpr(L, s.expression, env))
  const clauses = s.caseBlock.clauses
  const tests = clauses.map((c) => (ts.isCaseClause(c) ? strictEq(L.u, d(), lowerExpr(L, c.expression, env), c) : undefined))
  const anyMatch = z3.Or(z3.Bool.val(false), ...tests.filter((t): t is Bool<"main"> => t !== undefined))
  let fall: State | undefined
  let before: Bool<"main"> = z3.Bool.val(false)
  const returns: Array<Exits["returns"][number]> = []
  const leaving: Array<State> = []
  const continues: Array<State> = []
  clauses.forEach((c, i) => {
    const t = tests[i]
    const entryCond = t === undefined ? z3.And(st.cond, z3.Not(anyMatch)) : z3.And(st.cond, z3.Not(before), t)
    if (t !== undefined) before = z3.Or(before, t)
    const start = merge(L, [fall, withCond(st, entryCond)], c)
    if (start === undefined) {
      fall = undefined
      return
    }
    const x = statements(L, c.statements, start)
    returns.push(...x.returns)
    leaving.push(...x.breaks)
    continues.push(...x.continues)
    fall = x.normal
  })
  const noDefault = !clauses.some(ts.isDefaultClause)
  const out = scoped(
    { normal: merge(L, [fall, ...leaving, noDefault ? withCond(st, z3.And(st.cond, z3.Not(anyMatch))) : undefined], s), returns, breaks: [], continues },
    st.vars,
  )
  return out
}

// ——— Loops ———

/** The leading `invariant(...)` calls of a loop's body, and the rest of it. */
const invariantsOf = (L: Lowering, body: ts.Statement): { readonly invariants: ReadonlyArray<ts.CallExpression>; readonly rest: ReadonlyArray<ts.Statement> } => {
  const stmts = ts.isBlock(body) ? body.statements : [body]
  const invariants: Array<ts.CallExpression> = []
  let i = 0
  for (; i < stmts.length; i++) {
    const s = stmts[i]!
    if (!ts.isExpressionStatement(s) || !ts.isCallExpression(s.expression) || !declared(L.checker, s.expression.expression, CONTRACT_MODULE, "invariant")) break
    invariants.push(s.expression)
  }
  return { invariants, rest: stmts.slice(i) }
}

/** An invariant's, or an assert's, claim in a state: the callback written in place, run as spec code. */
const claim = (L: Lowering, st: State, call: ts.CallExpression, i: Arith<"main"> | undefined): Bool<"main"> => {
  const f = call.arguments[0]
  if (f === undefined || !(ts.isArrowFunction(unwrap(f)) || ts.isFunctionExpression(unwrap(f)))) throw new Unsupported("a hint takes a function written in place", call)
  const fn = unwrap(f) as ts.ArrowFunction | ts.FunctionExpression
  if (fn.parameters.length > 0 && i === undefined)
    throw new Unsupported("only a `for…of` loop's invariant takes `i`; a `for` or `while` loop's names its own variables", fn)
  return inSpec(L, () => truthy(L.u, lowerCall(L, fn, envOf(L, st), i === undefined ? [] : [{ kind: "int", origin: "count", term: i }], call)))
}

/**
 * A loop invariant as the loop reads it: one written first in its body, or one the verifier guessed (`Lowering.guess`).
 * Either is an obligation on entry and kept by each iteration, and a hint once proved.
 */
interface LoopClaim {
  readonly law?: string
  readonly key: string
  readonly at: string
  readonly text: string
  readonly claim: (st: State, i: Arith<"main">) => Bool<"main">
}

const writtenClaim = (L: Lowering, call: ts.CallExpression): LoopClaim => ({
  key: `invariant@${locate(call)}`,
  at: locate(call),
  text: call.arguments[0]?.getText() ?? call.getText(),
  claim: (st, i) => claim(L, st, call, i),
})

const obligateClaim = (L: Lowering, inv: LoopClaim, phase: "entry" | "kept", cond: Bool<"main">, goal: Bool<"main">): void => {
  L.obligations.push({
    key: `${inv.key}#${phase}`,
    kind: "invariant",
    text: inv.text,
    at: inv.at,
    phase,
    cond,
    goal,
    hints: L.hints.length,
    ...(inv.law === undefined ? {} : { guessed: inv.law }),
  })
}

const obligate = (L: Lowering, kind: Obligation["kind"], node: ts.CallExpression, phase: Obligation["phase"], cond: Bool<"main">, goal: Bool<"main">, text?: string): void => {
  const at = locate(node)
  const what = text ?? node.arguments[0]?.getText() ?? node.getText()
  L.obligations.push({ key: `${kind}@${at}#${phase}`, kind, text: what, at, phase, cond, goal, hints: L.hints.length })
}

/** The outer cells a loop may change: assigned, changed through, or lent to a call that may change them. */
const changedBy = (L: Lowering, st: State, nodes: ReadonlyArray<ts.Node>, inner: ts.Node): Set<number> => {
  const out = new Set<number>()
  const root = (x: ts.Expression): void => {
    let y = unwrap(x)
    for (;;) {
      if (ts.isPropertyAccessExpression(y) || ts.isElementAccessExpression(y)) y = unwrap(y.expression)
      else if (ts.isCallExpression(y) && ts.isPropertyAccessExpression(y.expression)) y = unwrap(y.expression.expression)
      else break
    }
    if (!ts.isIdentifier(y)) return
    const d = L.checker.getSymbolAtLocation(y)?.valueDeclaration
    if (d !== undefined && d.pos >= inner.pos && d.end <= inner.end) return
    const b = st.vars.get(y.text)
    if (b?.kind === "cell") out.add(b.cell)
    else if (b?.kind === "place") out.add(b.place.cell)
  }
  const visit = (n: ts.Node): void => {
    if (ts.isFunctionLike(n) && !ts.isArrowFunction(n) && !ts.isFunctionExpression(n)) return
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= K.FirstAssignment && n.operatorToken.kind <= K.LastAssignment) root(n.left)
    else if ((ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) && (n.operator === K.PlusPlusToken || n.operator === K.MinusMinusToken)) root(n.operand)
    else if (ts.isDeleteExpression(n)) root(n.expression)
    else if (ts.isCallExpression(n)) {
      if (ts.isPropertyAccessExpression(n.expression) && MUTATORS.has(n.expression.name.text)) root(n.expression.expression)
      // A function of the program may change what it is lent; a method of a value, or a builtin, is read for what it returns.
      if (ts.isIdentifier(n.expression)) for (const a of n.arguments) if (!ts.isArrowFunction(a) && !ts.isFunctionExpression(a)) root(a)
    }
    ts.forEachChild(n, visit)
  }
  for (const n of nodes) visit(n)
  return out
}

/** A state whose `cells` hold any values of their types: what is known of them is what the caller then assumes. */
const havoc = (L: Lowering, st: State, cells: ReadonlySet<number>, tag: string, at: ts.Node): State => {
  if (cells.size === 0) return st
  const store = new Map(st.store)
  for (const c of cells) {
    const cell = st.store.get(c)!
    if (cell.type === undefined) throw new Unsupported(`\`${cell.name}\` changes in a loop, and its type is unknown`, at)
    const type = cell.type
    store.set(c, { ...cell, thunk: lazy(() => symbolicOf(L, type, [L.u.fresh(`${cell.name}@${tag}`)], [], at)) })
  }
  L.u.abstracted = true
  L.u.approximations.add(
    `the loop at ${locate(at)} is read through its invariants alone, and none rules this run out: write one that does, first in its body (\`invariant((i) => ...)\`)`,
  )
  return { ...st, store }
}

/** `for (const x of xs)`. */
const forOf = (L: Lowering, s: ts.ForOfStatement, st: State): Exits => {
  const u = L.u
  const z3 = u.z3
  if (s.awaitModifier !== undefined) throw new Unsupported("`for await` is not modeled", s)
  const init = s.initializer
  if (!ts.isVariableDeclarationList(init) || init.declarations.length !== 1 || !ts.isIdentifier(init.declarations[0]!.name))
    throw new Unsupported("a `for…of` loop is modeled with one variable, `for (const x of xs)`", s)
  const name = (init.declarations[0]!.name as ts.Identifier).text
  const iterPlace = placeOf(L, st, s.expression)
  const iterated = present(iterPlace !== undefined ? readPlace(L, st, iterPlace.place) : lowerExpr(L, s.expression, envOf(L, st)))
  if (iterated.kind !== "array") throw new Unsupported(`a \`for…of\` over a ${iterated.kind} is not modeled`, s.expression)
  const arr = iterated
  const { invariants: written, rest } = invariantsOf(L, s.statement)
  for (const inv of written) noElement(L, inv, init.declarations[0]!.name as ts.Identifier)
  // What is written, then the verifier's guesses, if it makes any for this loop, each read in the loop's state: when
  // nothing is written, or beside what is (`verify`'s second round, for a law what is written leaves unproved).
  if (written.length > 0) L.wrote = true
  const guessed = L.guess !== undefined && (written.length === 0 || L.guessBeside === true) ? L.guess(s) : []
  const invariants: ReadonlyArray<LoopClaim> = [
    ...written.map((call) => writtenClaim(L, call)),
    ...guessed.map((g) => ({ ...g, claim: (at: State, i: Arith<"main">) => g.claim(envOf(L, at), i) })),
  ]
  const changed = changedBy(L, st, [s.statement], s.statement)
  if (iterPlace !== undefined && changed.has(iterPlace.place.cell)) throw new Unsupported(`changes \`${s.expression.getText()}\` while iterating it`, s)
  const elementType = L.checker.getTypeAtLocation(init.declarations[0]!.name)
  const bindElement = (head: State, i: Arith<"main">): State => {
    if (iterPlace !== undefined && isObjectType(L, elementType))
      return bindVar(head, name, { kind: "place", place: extend(iterPlace.place, { kind: "index", index: i }, name) })
    return newCell(L, head, name, () => arr.elem(i), false, elementType)
  }
  const bound = arr.maxSize ?? arr.size ?? u.bound
  const results = { returns: [] as Array<Exits["returns"][number]>, leaving: [] as Array<State> }
  if (bound !== undefined) {
    let head: State | undefined = st
    for (let k = 0; head !== undefined; k++) {
      const atK: State = head
      for (const inv of invariants) obligateClaim(L, inv, k === 0 ? "entry" : "kept", atK.cond, inv.claim(atK, z3.Int.val(k)))
      if (k === bound) {
        results.leaving.push(atK)
        break
      }
      const inLoop = z3.Int.val(k).lt(arr.length)
      results.leaving.push(withCond(atK, z3.And(atK.cond, z3.Not(inLoop))))
      const x = scoped(statements(L, rest, withCond(bindElement(atK, z3.Int.val(k)), z3.And(atK.cond, inLoop))), st.vars)
      results.returns.push(...x.returns)
      results.leaving.push(...x.breaks)
      head = merge(L, [x.normal, ...x.continues], s)
    }
    return { normal: merge(L, results.leaving, s), returns: results.returns, breaks: [], continues: [] }
  }
  // Proof side, unknown length: through the invariants.
  for (const inv of invariants) obligateClaim(L, inv, "entry", st.cond, inv.claim(st, z3.Int.val(0)))
  const i = u.leaf([u.fresh("i"), "$"], "int", [], "count") as never as Arith<"main">
  const step = havoc(L, st, changed, "step", s)
  const hyp = z3.And(st.cond, i.ge(0), i.lt(arr.length), ...invariants.map((inv) => inv.claim(step, i)))
  const x = scoped(statements(L, rest, withCond(bindElement(step, i), hyp)), st.vars)
  const next = merge(L, [x.normal, ...x.continues], s)
  if (next !== undefined) for (const inv of invariants) obligateClaim(L, inv, "kept", next.cond, inv.claim(next, i.add(1)))
  const after = havoc(L, st, changed, "after", s)
  if (invariants.length === 0 && changed.size > 0)
    u.notes.add("A loop with no invariant leaves what it changes unknown on the proof side; the search side runs it.")
  return leave(L, st, x, after, z3.And(z3.Bool.val(true), ...invariants.map((inv) => inv.claim(after, arr.length))), s)
}

/**
 * How the proof side leaves a loop it reads through its invariants, a choice the solver makes. Either the loop ran to its
 * end, and what holds there (`atEnd`: the invariants, and a `while`'s guard false) is known; or the iteration read at the
 * solver's count and state left it by a `return` or a `break`, and that iteration is one that does. What holds at the
 * end is never known on the second way: a loop that returns early never reaches it.
 */
const leave = (L: Lowering, st: State, x: Exits, after: State, atEnd: Bool<"main">, at: ts.Node): Exits => {
  const z3 = L.u.z3
  const exits = [...x.returns.map((r) => r.state.cond), ...x.breaks.map((b) => b.cond)]
  if (exits.length === 0) {
    L.hints.push(z3.Implies(st.cond, atEnd))
    return { normal: withCond(after, st.cond), returns: [], breaks: [], continues: [] }
  }
  const ran = z3.Bool.const(L.u.fresh("loop.ran"))
  L.u.assume(z3.Implies(z3.And(st.cond, z3.Not(ran)), z3.Or(...exits)))
  L.hints.push(z3.Implies(z3.And(st.cond, ran), atEnd))
  const early = (c: Bool<"main">) => z3.And(c, z3.Not(ran))
  return {
    normal: merge(L, [withCond(after, z3.And(st.cond, ran)), ...x.breaks.map((b) => withCond(b, early(b.cond)))], at),
    returns: x.returns.map((r) => ({ ...r, state: withCond(r.state, early(r.state.cond)) })),
    breaks: [],
    continues: [],
  }
}

/** An invariant states what holds between iterations: the current element is not one of its words. */
const noElement = (L: Lowering, inv: ts.CallExpression, element: ts.Identifier): void => {
  const sym = L.checker.getSymbolAtLocation(element)
  const visit = (n: ts.Node): void => {
    if (ts.isIdentifier(n) && L.checker.getSymbolAtLocation(n) === sym)
      throw new Unsupported(`an invariant holds between iterations, where there is no \`${element.text}\`: state it with \`i\`, the count done`, n)
    ts.forEachChild(n, visit)
  }
  visit(inv)
}

/** `for (init; guard; step)` and `while (guard)`. */
const guarded = (L: Lowering, s: ts.ForStatement | ts.WhileStatement, st0: State): Exits => {
  const u = L.u
  const z3 = u.z3
  let st = st0
  if (ts.isForStatement(s) && s.initializer !== undefined)
    st = ts.isVariableDeclarationList(s.initializer) ? declare(L, s.initializer, st) : expressionStatement(L, s.initializer, st)
  const guardExpr = ts.isForStatement(s) ? s.condition : s.expression
  const guard = (x: State): Bool<"main"> => (guardExpr === undefined ? z3.Bool.val(true) : condOf(L, guardExpr, envOf(L, x)))
  const incr = (x: State | undefined): State | undefined =>
    x === undefined || !ts.isForStatement(s) || s.incrementor === undefined ? x : expressionStatement(L, s.incrementor, x)
  const { invariants, rest } = invariantsOf(L, s.statement)
  const returns: Array<Exits["returns"][number]> = []
  const leaving: Array<State> = []
  if (u.bound !== undefined) {
    let head: State | undefined = st
    for (let k = 0; head !== undefined; k++) {
      const atK: State = head
      for (const inv of invariants) obligate(L, "invariant", inv, k === 0 ? "entry" : "kept", atK.cond, claim(L, atK, inv, undefined))
      const g = guard(atK)
      if (k === UNROLL) {
        // Longer runs are not searched: the search side's inputs are those that leave the loop within the limit.
        u.assume(z3.Not(z3.And(atK.cond, g)))
        u.notes.add(`The search side runs a \`for\` or \`while\` loop at most ${UNROLL} times; inputs that run it longer are not searched.`)
        leaving.push(atK)
        break
      }
      leaving.push(withCond(atK, z3.And(atK.cond, z3.Not(g))))
      const x = scoped(statements(L, rest, withCond(atK, z3.And(atK.cond, g))), st.vars)
      returns.push(...x.returns)
      leaving.push(...x.breaks)
      head = incr(merge(L, [x.normal, ...x.continues], s))
    }
    return scoped({ normal: merge(L, leaving, s), returns, breaks: [], continues: [] }, st0.vars)
  }
  for (const inv of invariants) obligate(L, "invariant", inv, "entry", st.cond, claim(L, st, inv, undefined))
  const changed = changedBy(L, st, ts.isForStatement(s) && s.incrementor !== undefined ? [s.statement, s.incrementor] : [s.statement], s.statement)
  const step = havoc(L, st, changed, "step", s)
  const hyp = z3.And(st.cond, guard(step), ...invariants.map((inv) => claim(L, step, inv, undefined)))
  const x = scoped(statements(L, rest, withCond(step, hyp)), st.vars)
  const next = incr(merge(L, [x.normal, ...x.continues], s))
  if (next !== undefined) for (const inv of invariants) obligate(L, "invariant", inv, "kept", next.cond, claim(L, next, inv, undefined))
  const after = havoc(L, st, changed, "after", s)
  u.notes.add("A `for` or `while` loop is assumed to end: an invariant proves what holds if it does.")
  return scoped(leave(L, st, x, after, z3.And(z3.Not(guard(after)), ...invariants.map((inv) => claim(L, after, inv, undefined))), s), st0.vars)
}

// ——— Lemmas ———

/** The lemma a callee names: `const name = lemma(statement, { requires })`, read from source. */
export const lemmaOf = (
  L: Lowering,
  callee: ts.Expression,
): { readonly file: string; readonly name: string; readonly statement: FunctionNode; readonly requires: FunctionNode | undefined } | undefined => {
  if (!ts.isIdentifier(callee)) return undefined
  let sym = L.checker.getSymbolAtLocation(callee)
  if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = L.checker.getAliasedSymbol(sym)
  const d = sym?.valueDeclaration
  if (d === undefined || !ts.isVariableDeclaration(d) || d.initializer === undefined) return undefined
  const init = unwrap(d.initializer)
  if (!ts.isCallExpression(init) || !declared(L.checker, init.expression, CONTRACT_MODULE, "lemma")) return undefined
  const [statementArg, opts] = init.arguments
  if (statementArg === undefined) throw new Unsupported("a lemma states something: `lemma((...) => ...)`", init)
  let requires: FunctionNode | undefined
  if (opts !== undefined) {
    const o = unwrap(opts)
    if (!ts.isObjectLiteralExpression(o)) throw new Unsupported("a lemma's options are written in place", opts)
    for (const p of o.properties) {
      if (ts.isPropertyAssignment(p) && ts.isIdentifier(p.name) && p.name.text === "requires") requires = functionOf(L.checker, p.initializer)
      else throw new Unsupported("a lemma's one option is `requires`", p)
    }
  }
  return { file: d.getSourceFile().fileName, name: (d.name as ts.Identifier).text, statement: functionOf(L.checker, statementArg), requires }
}


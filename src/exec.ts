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
import type { Arith, Bool, Expr } from "z3-solver"
import {
  type Lowering,
  cond as condOf,
  exactSpec,
  inSpec,
  later,
  lowerCall,
  lowerExpr,
  shownPresent,
  member,
  oblige,
  onBranch,
  quietly,
  under,
} from "./lower.ts"
import { arithmetic, asNumber, exactly } from "./lower/numbers.ts"
import { atIndex, indexOf, shown } from "./lower/strings.ts"
import { defaulted, patternElement, patternRest, patternKeys, restOf } from "./lower/patterns.ts"
import { elementwise, firstIndex, flatExact } from "./lower/arrays.ts"
import { countAsNum, isNullish, isWhole, ite, nullishOr, strictEq, truthy } from "./ops.ts"
import { CONTRACT_MODULE, declared, functionOf, ownModule } from "./project.ts"
import { functionIn, inProgram, symbolOf, unwrap } from "./resolve.ts"
import { symbolicOf } from "./symbolic.ts"
import { elementsOf, tableMethods } from "./collections.ts"
import { isDictionaryType } from "./lower/records.ts"
import {
  type LoopEffect,
  type LoopWrites,
  type MapKind,
  type Table,
  type Write,
  emptyTable,
  givenTable,
  keyedTable,
  loopTable,
  lookup,
  mapValue,
  building,
  markerTable,
  pushedArray,
  pushedItems,
  tableOf,
  written,
  writesSince,
} from "./maps.ts"
import {
  type Env,
  type FunctionNode,
  NUM,
  type Thunk,
  UNDEFINED,
  Unsupported,
  type Val,
  identity,
  jsString,
  lazy,
  lazyRecord,
  locate,
  memoElems,
  termId,
} from "./value.ts"

const K = ts.SyntaxKind

/** What the proof code asks proved: true wherever `cond` holds. */
export interface Obligation {
  /** The same obligation on both sides and in every instance (a loop inlined twice): kind, place and phase. */
  readonly key: string
  /**
   * Proof code's (`invariant`, `assert`, a lemma's `requires`), or the model's: a `division` whose divisor is not 0n, a
   * `write` that lands inside its array, `exact` arithmetic on `number`. A law is judged on the runs where the model's
   * hold; a write and arithmetic are leaned on besides, since the runs where they fail go on, with a value not modeled.
   */
  readonly kind: "invariant" | "assert" | "requires" | "division" | "write" | "exact" | "key"
  /** The claim as written. */
  readonly text: string
  /** `file:line:col`. */
  readonly at: string
  /** An invariant on entry, or kept by an iteration; an assert or a lemma's precondition, here. */
  readonly phase: "entry" | "kept" | "here"
  readonly cond: Bool
  readonly goal: Bool
  /** How many of the lowering's hints were made before it: those it may be proved with. */
  readonly hints: number
  /** For an invariant the verifier guessed, the law it restates. */
  readonly guessed?: string
}

/** The obligations of the model, which say what runs it reads exactly, rather than what the proof code asked. */
export const MODELS: ReadonlySet<string> = new Set<Obligation["kind"]>(["division", "write", "exact", "key"])

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
type Step =
  | { readonly kind: "field"; readonly name: string }
  | { readonly kind: "index"; readonly index: Arith }
  /** A key of a map the code built (`out[key]`, `out.team`): `named` where the code writes it as a name. */
  | { readonly kind: "key"; readonly key: Val; readonly named?: string }

type Binding =
  /** A value fixed for the scope: what a closure captured, a value the caller gave. */
  | { readonly kind: "value"; readonly thunk: Thunk }
  | { readonly kind: "cell"; readonly cell: number }
  /** A borrow: reads and changes go through to the place. `isUndefined` when it may be none (`.find`). */
  | { readonly kind: "place"; readonly place: Place; readonly isUndefined?: Bool }

interface Cell {
  readonly thunk: Thunk
  /** Allocated by the function: it may change. */
  readonly owned: boolean
  readonly name: string
  /** Its declared type: what a loop's havoc draws from. */
  readonly type: ts.Type | undefined
}

export interface State {
  readonly cond: Bool
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
export type Arg =
  | { readonly kind: "value"; readonly thunk: Thunk; readonly owned: boolean }
  | { readonly kind: "place"; readonly place: Place }

/** The methods that change the array, map or set they are called on. */
const MUTATORS: ReadonlySet<string> = new Set([
  "push",
  "pop",
  "shift",
  "unshift",
  "splice",
  "sort",
  "reverse",
  "fill",
  "copyWithin",
  "set",
  "add",
  "delete",
  "clear",
])

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
  const vars = new Map<string, Binding>()
  for (const [name, thunk] of closure) vars.set(name, { kind: "value", thunk })
  // A body entered from an expression runs under that expression's branch.
  let st: State = {
    cond: caller?.cond ?? L.guard,
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
    // A default is taken where the argument is `undefined`: left out, or given as one.
    const thunk: Thunk = defaulted(
      L,
      arg !== undefined ? (arg as Extract<Arg, { kind: "value" }>).thunk : () => UNDEFINED,
      p.initializer === undefined ? undefined : later(L, () => lowerExpr(L, p.initializer!, envOf(L, now)), now.cond),
      p,
    )
    st = bindName(L, st, p.name, thunk, arg?.kind === "value" ? arg.owned : false, type)
  })
  const body = fn.body!
  if (!ts.isBlock(body)) {
    const now = st
    return {
      value: later(L, () => lowerExpr(L, body, envOf(L, now)), now.cond),
      owned: fresh(body),
      after: caller === undefined ? undefined : { ...caller, store: st.store },
    }
  }
  const x = statements(L, body.statements, st)
  const results = [...x.returns, ...(x.normal === undefined ? [] : [{ state: x.normal, value: (() => UNDEFINED) as Thunk, owned: true }])]
  if (results.length === 0) throw new Unsupported("a function that never returns", fn)
  const last = results[results.length - 1]!
  const value = lazy(() => results.slice(0, -1).reduceRight((acc, r) => ite(L.u, r.state.cond, r.value(), acc, at), last.value()))
  if (caller === undefined) return { value, owned: results.every((r) => r.owned), after: undefined }
  const merged = merge(
    L,
    results.map((r) => r.state),
    at,
  )!
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
  if (ts.isArrayBindingPattern(name)) {
    let out = st
    name.elements.forEach((el, k) => {
      if (ts.isOmittedExpression(el)) return
      const now = out
      const elType = L.checker.getTypeAtLocation(el)
      if (el.dotDotDotToken !== undefined) {
        out = bindName(
          L,
          out,
          el.name,
          later(L, () => patternRest(L, thunk(), k, el)),
          owned,
          elType,
        )
        return
      }
      out = bindName(
        L,
        out,
        el.name,
        defaulted(
          L,
          later(L, () => patternElement(L, thunk(), k, el)),
          el.initializer === undefined ? undefined : later(L, () => lowerExpr(L, el.initializer!, envOf(L, now)), now.cond),
          el,
        ),
        false,
        elType,
      )
    })
    return out
  }
  const { keys, rest } = patternKeys(name)
  const objType = L.checker.getTypeAtLocation(name)
  const whole = (): Val => shownPresent(thunk(), objType)
  let out = st
  for (const { key, el } of keys) {
    const now = out
    out = bindName(
      L,
      out,
      el.name,
      defaulted(
        L,
        later(L, () => member(L, whole(), key, el, type, L.checker.getTypeAtLocation(el))),
        el.initializer === undefined ? undefined : later(L, () => lowerExpr(L, el.initializer!, envOf(L, now)), now.cond),
        el,
      ),
      false,
      L.checker.getTypeAtLocation(el),
    )
  }
  if (rest !== undefined)
    out = bindName(
      L,
      out,
      rest.name,
      later(L, () =>
        restOf(
          L,
          whole(),
          keys.map((k) => k.key),
          rest,
        ),
      ),
      owned,
      L.checker.getTypeAtLocation(rest),
    )
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
    } else if (s.kind === "key") {
      throw new Unsupported(`\`${p.text}\`: a key of a map is read as a value, not referred into`)
    } else if (v.kind === "record" && L.u.z3.isIntVal(s.index)) {
      // A tuple's element at a literal index (a call's `args[0]`): its field.
      v = v.field(String(s.index.value())) ?? UNDEFINED
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
const update = (L: Lowering, v: Val, steps: ReadonlyArray<Step>, f: (old: Val) => Val, at: ts.Node, absent: boolean, guard: Bool): Val => {
  const [s, ...rest] = steps
  // A field is read when a law reads it, long after the write: `f` runs under the branch of the write.
  if (s === undefined) return under(L, guard, () => f(v))
  const z3 = L.u.z3
  const o = present(v)
  if (s.kind === "key") {
    const t = tableOf(o)
    if (t === undefined) throw new Unsupported("a key set on what is no map the code built", at)
    if (rest.length > 0)
      throw new Unsupported(
        "changes a map's value in place: a value a map holds is replaced (`out[k] = { ...out[k], x }`), never changed",
        at,
      )
    if (absent) return mapValue(written(t, guard, s.key, false, UNDEFINED, at, s.named), tableMethods)
    // The value it replaces, for `??=` and the like; a pass of a loop read whole only writes with `=`, and reads nothing.
    const old = building(t) ? undefined : lookup(t, s.key, at)
    const before: Val =
      old === undefined
        ? UNDEFINED
        : old.value.kind === "maybe"
          ? { ...old.value, isUndefined: z3.Or(z3.Not(old.found), old.value.isUndefined), isNull: z3.And(old.found, old.value.isNull) }
          : { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(old.found), value: old.value }
    return mapValue(
      written(
        t,
        guard,
        s.key,
        true,
        under(L, guard, () => f(before)),
        at,
        s.named,
      ),
      tableMethods,
    )
  }
  if (s.kind === "field") {
    if (o.kind !== "record") throw new Unsupported(`a field set on a ${o.kind}`, at)
    const gone = absent && rest.length === 0
    return lazyRecord(
      (name) => (name === s.name ? update(L, o.field(name) ?? UNDEFINED, rest, f, at, absent, guard) : o.field(name)),
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
      if (j === s.index || j.eqIdentity(s.index)) return update(L, o.elem(j), rest, f, at, absent, guard)
      if (z3.isIntVal(j) && z3.isIntVal(s.index)) return o.elem(j)
      return ite(L.u, j.eq(s.index), update(L, o.elem(j), rest, f, at, absent, guard), o.elem(j), at)
    }),
  }
}

const writePlace = (L: Lowering, st: State, p: Place, f: (old: Val) => Val, at: ts.Node, absent = false): State => {
  const old = st.store.get(p.cell)!
  const store = new Map(st.store)
  const before = st
  store.set(p.cell, { ...old, thunk: later(L, () => update(L, readCell(before, p.cell, p.text), p.steps, f, at, absent, L.guard)) })
  return { ...st, store }
}

/** `a` is a prefix of `b`, or may be: two indices not known to differ may be the same. */
const prefix = (a: Place, b: Place): boolean =>
  a.cell === b.cell &&
  a.steps.length <= b.steps.length &&
  a.steps.every((s, i) => {
    const t = b.steps[i]!
    return s.kind === "field" ? t.kind === "field" && t.name === s.name : t.kind === s.kind
  })

const borrowsOf = (st: State): Array<{ name: string; place: Place }> =>
  [...st.vars].flatMap(([name, b]) => (b.kind === "place" ? [{ name, place: b.place }] : []))

/** The place `e` names, when it names one: a variable, a field or element of one, what `.find` or `.at` found in one. */
const placeOf = (L: Lowering, st: State, e: ts.Expression): { readonly place: Place; readonly isUndefined?: Bool } | undefined => {
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
  if (ts.isElementAccessExpression(x)) {
    const base = placeOf(L, st, x.expression)
    if (base === undefined) return undefined
    const literal = ts.isNumericLiteral(x.argumentExpression) && /^\d+$/.test(x.argumentExpression.text)
    // A tuple's element at a literal index: its field, which its type says is there. Told apart from an array by its
    // type, before its value is read: a call's `args`, read only once its `op` narrows it.
    if (!isArrayTyped(L, x.expression))
      return literal
        ? { place: extend(base.place, { kind: "index", index: z3.Int.val(Number(x.argumentExpression.text)) }, x.getText()) }
        : undefined
    const container = present(readPlace(L, st, base.place))
    if (container.kind !== "array") return undefined
    // An array's element: missing wherever the index is no whole number inside the array. A literal stays one.
    const { term, whole } = literal
      ? { term: z3.Int.val(Number(x.argumentExpression.text)), whole: z3.Bool.val(true) }
      : indexOf(L, lowerExpr(L, x.argumentExpression, envOf(L, st)), x.argumentExpression)
    return {
      place: extend(base.place, { kind: "index", index: term }, x.getText()),
      isUndefined: z3.Not(z3.And(whole, term.ge(0), term.lt(container.length))),
    }
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
      const k = ts.isNumericLiteral(a)
        ? BigInt(a.text)
        : ts.isPrefixUnaryExpression(a) && a.operator === K.MinusToken && ts.isNumericLiteral(a.operand)
          ? -BigInt(a.operand.text)
          : undefined
      // A literal index stays a literal, which reads that one element exactly (a call of the trace, as it was made).
      if (k !== undefined) {
        const index = k < 0n ? arr.length.add(z3.Int.val(k)) : z3.Int.val(k)
        return { place: extend(base.place, { kind: "index", index }, x.getText()), isUndefined: z3.Or(index.lt(0), index.ge(arr.length)) }
      }
      const { index, isUndefined } = atIndex(L, arr, lowerExpr(L, a, envOf(L, st)), a)
      return { place: extend(base.place, { kind: "index", index }, x.getText()), isUndefined }
    }
    const f = lowerExpr(L, x.arguments[0]!, envOf(L, st))
    if (f.kind !== "fn") return undefined
    const { found, k } = firstIndex(L, arr, (i) =>
      truthy(L.u, lowerCall(L, f.node, f.env, [arr.elem(i), { kind: "int", origin: "count", term: i }], x)),
    )
    return { place: extend(base.place, { kind: "index", index: k }, x.getText()), isUndefined: z3.Not(found) }
  }
  return undefined
}

const extend = (p: Place, s: Step, text: string): Place => ({ cell: p.cell, steps: [...p.steps, s], text })

/** Whether `e`'s type is an array's (`T[]`, `ReadonlyArray<T>`), and not a tuple's or a record's. */
const isArrayTyped = (L: Lowering, e: ts.Expression): boolean => {
  const t = L.checker.getNonNullableType(L.checker.getTypeAtLocation(e))
  return (t.isUnion() ? t.types : [t]).every((m) => L.checker.isArrayType(m))
}

/** Whether an object-typed value is read here: a borrow is made only of one, a primitive is copied. */
const isObjectTyped = (L: Lowering, e: ts.Node): boolean => {
  const t = L.checker.getNonNullableType(L.checker.getTypeAtLocation(e))
  return (t.isUnion() ? t.types : [t]).some(
    (m) => (m.flags & (ts.TypeFlags.Object | ts.TypeFlags.NonPrimitive | ts.TypeFlags.Intersection)) !== 0,
  )
}

/** An expression that allocates: a literal, an object or an array the code builds here. */
const fresh = (e: ts.Expression): boolean => {
  const x = unwrap(e)
  return ts.isObjectLiteralExpression(x) || ts.isArrayLiteralExpression(x) || ts.isNewExpression(x)
}

/** A change may be made through `p`: its root is the function's own, and no one borrows into what it replaces. */
const changeable = (L: Lowering, st: State, p: Place, replaces: boolean, at: ts.Node): void => {
  const cell = st.store.get(p.cell)!
  if (!cell.owned)
    throw new Unsupported(
      `changes \`${p.text}\`, which the function did not allocate (an argument given by value, or what it was given)`,
      at,
    )
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
      for (const el of y.elements)
        if (ts.isSpreadElement(el)) spread(el.expression)
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
    const parts = L.checker.isArrayType(t)
      ? [L.checker.getTypeArguments(t as ts.TypeReference)[0]!]
      : L.checker.getPropertiesOfType(t).map((s) => L.checker.getTypeOfSymbol(s))
    if (parts.some((pt) => isObjectType(L, pt)))
      throw new Unsupported(`spreads \`${y.getText()}\`, whose parts are objects the function holds, into a second place (${where})`, at)
  }
  visit(e)
  return out
}

const isObjectType = (L: Lowering, t: ts.Type): boolean => {
  const n = L.checker.getNonNullableType(t)
  return (n.isUnion() ? n.types : [n]).some(
    (m) => (m.flags & (ts.TypeFlags.Object | ts.TypeFlags.NonPrimitive | ts.TypeFlags.Intersection)) !== 0,
  )
}

const samePlace = (a: Place, b: Place): boolean =>
  a.cell === b.cell &&
  a.steps.length === b.steps.length &&
  a.steps.every((s, i) => {
    const t = b.steps[i]!
    if (s.kind === "field") return t.kind === "field" && t.name === s.name
    if (s.kind === "key") return t.kind === "key" && identity(t.key) !== undefined && identity(t.key) === identity(s.key)
    return t.kind === "index" && t.index.eqIdentity(s.index)
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

const withCond = (st: State, cond: Bool): State => ({ ...st, cond })

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
    // What the statement lowers runs under the branch that reached it.
    const at: State = cur
    const x: Exits = under(L, at.cond, () => statement(L, s, at))
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
    const no = z3.isTrue(c)
      ? NONE
      : s.elseStatement === undefined
        ? normal(withCond(st, z3.And(st.cond, z3.Not(c))))
        : block(L, s.elseStatement, withCond(st, z3.And(st.cond, z3.Not(c))))
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
        out = bindVar(out, d.name.text, {
          kind: "place",
          place: { ...p.place, text: d.name.text },
          ...(p.isUndefined === undefined ? {} : { isUndefined: p.isUndefined }),
        })
        continue
      }
      if (p !== undefined && out.store.get(p.place.cell)?.owned)
        throw new Unsupported(
          `\`${d.name.text}\` would be a second name for \`${init.getText()}\`, which the function holds; use \`${init.getText()}\``,
          d,
        )
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
  const d = symbolOf(L.checker, callee)?.valueDeclaration
  if (d === undefined || !inProgram(d) || ownModule(d.getSourceFile().fileName, CONTRACT_MODULE)) return undefined
  const fn = functionIn(d)
  // A generator or an async function a `const` holds is a computation, read where it is run.
  if (
    fn === undefined ||
    (!ts.isFunctionDeclaration(fn) && (fn.asteriskToken !== undefined || fn.modifiers?.some((m) => m.kind === K.AsyncKeyword)))
  )
    return undefined
  return { node: fn, env: new Map() }
}

const ASSIGN_OPS: ReadonlyMap<ts.SyntaxKind, ts.SyntaxKind> = new Map([
  [K.PlusEqualsToken, K.PlusToken],
  [K.MinusEqualsToken, K.MinusToken],
  [K.AsteriskEqualsToken, K.AsteriskToken],
  [K.SlashEqualsToken, K.SlashToken],
  [K.PercentEqualsToken, K.PercentToken],
  [K.BarEqualsToken, K.BarToken],
  [K.AmpersandEqualsToken, K.AmpersandToken],
  [K.CaretEqualsToken, K.CaretToken],
  [K.LessThanLessThanEqualsToken, K.LessThanLessThanToken],
  [K.GreaterThanGreaterThanEqualsToken, K.GreaterThanGreaterThanToken],
  [K.GreaterThanGreaterThanGreaterThanEqualsToken, K.GreaterThanGreaterThanGreaterThanToken],
])

/** A statement that is an expression: an assignment, a change, a call run for what it changes, or a hint. */
const expressionStatement = (L: Lowering, e: ts.Expression, st: State): State => {
  const u = L.u
  const x = unwrap(e)
  if (ts.isBinaryExpression(x) && x.operatorToken.kind >= K.FirstAssignment && x.operatorToken.kind <= K.LastAssignment) {
    const op = x.operatorToken.kind
    const env = envOf(L, st)
    const rhs = later(L, () => lowerExpr(L, x.right, env))
    // `??=`, `||=` and `&&=` run their right side only on the branch that assigns.
    const rhsWhere = (c: Bool): Val => onBranch(L, c, () => lowerExpr(L, x.right, env))
    const compute = (old: Val): Val => {
      if (op === K.EqualsToken) return rhs()
      if (op === K.QuestionQuestionEqualsToken)
        return nullishOr(u, old, () => rhsWhere(old.kind === "maybe" ? isNullish(u, old) : u.z3.Bool.val(true)), x)
      if (op === K.BarBarEqualsToken) return ite(u, truthy(u, old), old, rhsWhere(u.z3.Not(truthy(u, old))), x)
      if (op === K.AmpersandAmpersandEqualsToken) return ite(u, truthy(u, old), rhsWhere(truthy(u, old)), old, x)
      const base = ASSIGN_OPS.get(op)
      if (base === undefined) throw new Unsupported(`operator ${ts.tokenToString(op)} is not modeled`, x.operatorToken)
      return arithmetic(L, base, old, rhs(), x)
    }
    return assign(L, st, x.left, compute, x.right, x)
  }
  if (
    (ts.isPrefixUnaryExpression(x) || ts.isPostfixUnaryExpression(x)) &&
    (x.operator === K.PlusPlusToken || x.operator === K.MinusMinusToken)
  ) {
    const op = x.operator === K.PlusPlusToken ? K.PlusToken : K.MinusToken
    return assign(
      L,
      st,
      x.operand,
      (old) => {
        if (old.kind === "int" && old.origin === "bigint") return { ...old, term: op === K.PlusToken ? old.term.add(1) : old.term.sub(1) }
        const n = old.kind === "num" ? old : old.kind === "int" && old.origin === "count" ? countAsNum(u, old.term) : undefined
        if (n !== undefined)
          return exactly(L, op, n, { kind: "num", cls: u.z3.Int.val(NUM.finite), real: u.z3.Real.val(1), whole: u.z3.Bool.val(true) }, x)
        throw new Unsupported(
          `\`${ts.tokenToString(x.operator)}\` on a ${old.kind}: arithmetic on \`number\` rounds, which the model of numbers does not see: use \`bigint\` where the values are whole, or move it into a function the spec declares with \`assume\``,
          x,
        )
      },
      undefined,
      x,
    )
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
    if (b?.kind !== "cell")
      throw new Unsupported(
        `assigns \`${t.text}\`, which is ${b?.kind === "place" ? "a reference into an object; change its fields" : "not a variable of this function (a closure's capture, or a global)"}`,
        at,
      )
    const cell = st.store.get(b.cell)!
    if (rhs !== undefined && isObjectTyped(L, rhs) && !fresh(rhs)) {
      const p = placeOf(L, st, rhs)
      if (p !== undefined && st.store.get(p.place.cell)?.owned)
        throw new Unsupported(`\`${t.text}\` would be a second name for \`${rhs.getText()}\`, which the function holds`, at)
    }
    const next = rhs === undefined ? st : storing(L, st, rhs, undefined, `\`${t.text}\``, at)
    const store = new Map(next.store)
    const before = st
    store.set(b.cell, {
      ...cell,
      owned: rhs === undefined ? cell.owned : fresh(rhs) || (cell.owned && !isObjectTyped(L, rhs)),
      thunk: later(L, () => compute(readCell(before, b.cell, t.text))),
    })
    return { ...next, store }
  }
  if (!ts.isPropertyAccessExpression(t) && !ts.isElementAccessExpression(t))
    throw new Unsupported("an assignment to a pattern is not modeled", at)
  const objType = L.checker.getTypeAtLocation(t.expression)
  if ((objType.isUnion() ? objType.types : [objType]).some((m) => m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)))
    throw new Unsupported(`changes \`${t.expression.getText()}\`, which the type checker has not shown present here`, at)
  const base = placeOf(L, st, t.expression)
  if (base === undefined)
    throw new Unsupported(`changes \`${t.expression.getText()}\`, which is no variable of this function nor part of one`, at)
  const step: Step = isDictionaryType(L.checker, L.checker.getNonNullableType(objType))
    ? keyStep(L, st, t)
    : ts.isPropertyAccessExpression(t)
      ? { kind: "field", name: t.name.text }
      : elementStep(L, st, base.place, t)
  const place = extend(base.place, step, t.getText())
  changeable(L, st, place, true, at)
  const next = rhs === undefined ? st : storing(L, st, rhs, place, `\`${t.getText()}\``, at)
  return writePlace(L, next, place, compute, at, deleting)
}

/** The key `t` writes in a dictionary the code built: `out[key]`, a key it computes, or `out.team`, a name. */
const keyStep = (L: Lowering, st: State, t: ts.PropertyAccessExpression | ts.ElementAccessExpression): Step => {
  const z3 = L.u.z3
  if (ts.isPropertyAccessExpression(t)) return { kind: "key", key: { kind: "str", term: jsString(z3, t.name.text) }, named: t.name.text }
  const k = t.argumentExpression
  if (ts.isStringLiteralLike(k)) return { kind: "key", key: { kind: "str", term: jsString(z3, k.text) }, named: k.text }
  const key = shown(L, lowerExpr(L, k, envOf(L, st)), k)
  if (key.kind !== "str") throw new Unsupported(`a key of a record that is a ${key.kind}: the code writes it at a string`, k)
  return { kind: "key", key }
}

/**
 * The element `t` sets, `a[i] = …`: one inside the array. JavaScript grows the array to reach one past its end, with
 * holes between, which the model does not hold: each write is an obligation that its index is a whole number within
 * the array's length.
 */
const elementStep = (L: Lowering, st: State, base: Place, t: ts.ElementAccessExpression): Step => {
  const z3 = L.u.z3
  if (!isArrayTyped(L, t.expression)) throw new Unsupported("an element set on what is no array", t)
  const container = present(readPlace(L, st, base))
  if (container.kind !== "array") throw new Unsupported(`an element set on a ${container.kind}`, t)
  const { term, whole } = indexOf(L, lowerExpr(L, t.argumentExpression, envOf(L, st)), t.argumentExpression)
  const at = locate(t)
  oblige(L, {
    key: `write@${at}#here`,
    kind: "write",
    text: t.getText(),
    at,
    phase: "here",
    cond: st.cond,
    goal: z3.And(whole, term.ge(0), term.lt(container.length)),
    hints: L.hints.length,
  })
  return { kind: "index", index: term }
}

/** A call made for what it does: a hint, a `push`, or one of the program's functions run on this state. */
const callStatement = (L: Lowering, e: ts.CallExpression, st: State): State => {
  const u = L.u
  const z3 = u.z3
  const callee = e.expression
  if (declared(L.checker, callee, CONTRACT_MODULE, "invariant"))
    throw new Unsupported("an invariant goes first in a loop's body, before any other statement", e)
  if (declared(L.checker, callee, CONTRACT_MODULE, "assert")) {
    obligate(L, "assert", e, "here", st.cond, claim(L, st, e, undefined, "asserted"))
    // Proof code is for proofs: the search side, which runs the code exactly, checks a hint and never leans on it.
    if (u.bound === undefined) L.hints.push(z3.Implies(st.cond, claim(L, st, e, undefined, "assumed")))
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
    if (u.bound === undefined)
      L.hints.push(
        z3.Implies(
          st.cond,
          inSpec(L, () => truthy(u, lowerCall(L, lem.statement, new Map(), args, e))),
        ),
      )
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
    if (recv !== undefined && CHANGES.has(method) && isCollectionTyped(L, callee.expression)) {
      changeable(L, st, recv.place, false, e)
      let next = st
      for (const a of e.arguments) {
        if (ts.isSpreadElement(a)) throw new Unsupported(`\`.${method}(...xs)\` is not modeled`, a)
        next = storing(L, next, a, undefined, `\`${callee.expression.getText()}\``, e)
      }
      const env = envOf(L, st)
      const args = e.arguments.map((a) => lowerExpr(L, a, env))
      return writePlace(L, next, recv.place, (old) => changed(L, old, method, args, e), e)
    }
    if (recv !== undefined && MUTATORS.has(method)) throw new Unsupported(`\`.${method}\` is not modeled; \`.push\` is`, e)
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

/** The methods that change a `Map` or a `Set` the code built, read as statements. */
const CHANGES: ReadonlySet<string> = new Set(["set", "add", "delete", "clear"])

/** Whether `e`'s type is a `Map`'s or a `Set`'s. */
const isCollectionTyped = (L: Lowering, e: ts.Expression): boolean => {
  const t = L.checker.getNonNullableType(L.checker.getTypeAtLocation(e))
  const name = t.getSymbol()?.getName()
  return name === "Map" || name === "Set"
}

/** A `Map` or a `Set` after `m.set(k, v)`, `s.add(k)`, `x.delete(k)` or `x.clear()`, made under the branch being lowered. */
const changed = (L: Lowering, v: Val, method: string, args: ReadonlyArray<Val>, at: ts.CallExpression): Val => {
  const t = tableOf(present(v))
  if (t === undefined || t.kind === "object") throw new Unsupported(`\`.${method}\` of a collection the code did not build here`, at)
  const want = method === "set" ? 2 : method === "clear" ? 0 : 1
  if (args.length !== want || (method === "set" && t.kind !== "Map") || (method === "add" && t.kind !== "Set"))
    throw new Unsupported(`\`.${method}\` of a \`${t.kind}\` with ${args.length} argument${args.length === 1 ? "" : "s"}`, at)
  if (method === "clear") return mapValue(emptyTable(L, t.kind, at), tableMethods)
  const [key, value] = args as [Val, Val | undefined]
  return mapValue(written(t, L.guard, key, method !== "delete", value ?? UNDEFINED, at), tableMethods)
}

/** `arr` with `items` after its elements. */
const appended = (L: Lowering, v: Val, items: ReadonlyArray<Thunk>, at: ts.Node): Val => {
  const arr = present(v)
  if (arr.kind !== "array") throw new Unsupported(`\`.push\` on a ${arr.kind}`, at)
  // An array a loop builds, as one pass sees it: what it pushes, under the branch that does (`summarized`).
  if (arr.pushes !== undefined)
    return pushedArray(L.u, arr.pushes.base, [...arr.pushes.items, ...items.map((item) => ({ cond: L.guard, value: item() }))], at)
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
  const anyMatch = z3.Or(z3.Bool.val(false), ...tests.filter((t): t is Bool => t !== undefined))
  let fall: State | undefined
  let before: Bool = z3.Bool.val(false)
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
    {
      normal: merge(L, [fall, ...leaving, noDefault ? withCond(st, z3.And(st.cond, z3.Not(anyMatch))) : undefined], s),
      returns,
      breaks: [],
      continues,
    },
    st.vars,
  )
  return out
}

// ——— Loops ———

/** The leading `invariant(...)` calls of a loop's body, and the rest of it. */
const invariantsOf = (
  L: Lowering,
  body: ts.Statement,
): { readonly invariants: ReadonlyArray<ts.CallExpression>; readonly rest: ReadonlyArray<ts.Statement> } => {
  const stmts = ts.isBlock(body) ? body.statements : [body]
  const invariants: Array<ts.CallExpression> = []
  let i = 0
  for (; i < stmts.length; i++) {
    const s = stmts[i]!
    if (
      !ts.isExpressionStatement(s) ||
      !ts.isCallExpression(s.expression) ||
      !declared(L.checker, s.expression.expression, CONTRACT_MODULE, "invariant")
    )
      break
    invariants.push(s.expression)
  }
  return { invariants, rest: stmts.slice(i) }
}

/** An invariant's, or an assert's, claim in a state: the callback written in place, run as spec code. */
const claim = (L: Lowering, st: State, call: ts.CallExpression, i: Arith | undefined, role: "asserted" | "assumed"): Bool => {
  const f = call.arguments[0]
  if (f === undefined || !(ts.isArrowFunction(unwrap(f)) || ts.isFunctionExpression(unwrap(f))))
    throw new Unsupported("a hint takes a function written in place", call)
  const fn = unwrap(f) as ts.ArrowFunction | ts.FunctionExpression
  if (fn.parameters.length > 0 && i === undefined)
    throw new Unsupported("only a `for…of` loop's invariant takes `i`; a `for` or `while` loop's names its own variables", fn)
  return exactSpec(
    L,
    () =>
      inSpec(L, () =>
        truthy(L.u, lowerCall(L, fn, envOf(L, st), i === undefined ? [] : [{ kind: "int", origin: "count", term: i }], call)),
      ),
    role,
  )
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
  readonly claim: (st: State, i: Arith, role: "asserted" | "assumed") => Bool
}

const writtenClaim = (L: Lowering, call: ts.CallExpression): LoopClaim => ({
  key: `invariant@${locate(call)}`,
  at: locate(call),
  text: call.arguments[0]?.getText() ?? call.getText(),
  claim: (st, i, role) => claim(L, st, call, i, role),
})

const obligateClaim = (L: Lowering, inv: LoopClaim, phase: "entry" | "kept", cond: Bool, goal: Bool): void => {
  oblige(L, {
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

const obligate = (
  L: Lowering,
  kind: Obligation["kind"],
  node: ts.CallExpression,
  phase: Obligation["phase"],
  cond: Bool,
  goal: Bool,
  text?: string,
): void => {
  const at = locate(node)
  const what = text ?? node.arguments[0]?.getText() ?? node.getText()
  oblige(L, { key: `${kind}@${at}#${phase}`, kind, text: what, at, phase, cond, goal, hints: L.hints.length })
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
    else if (
      (ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
      (n.operator === K.PlusPlusToken || n.operator === K.MinusMinusToken)
    )
      root(n.operand)
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

/**
 * What a loop keeps of each counter it steps, by construction: a `let` of the state before it that the loop changes only
 * by `++`, `--`, `+= k` or `-= k` (`k` a whole literal), and only one way, stays a whole number where it starts as one,
 * and never goes below where it started (above, stepping down). It holds of the model's values, which are JavaScript's
 * wherever every step was exact: an obligation of each step, so on the runs a law is judged on. Dafny knows as much of
 * an `int`, from its type. A counter that starts at a value whole as written (`let i = 0`) is `whole`, the cells the loop's
 * states then hold as integers (`havoc`): a fact the solver would have to bring into every quantifier is then no fact.
 */
const counterFacts = (
  L: Lowering,
  st: State,
  nodes: ReadonlyArray<ts.Node>,
  inner: ts.Node,
): { readonly facts: (x: State) => Bool; readonly whole: ReadonlySet<number> } => {
  const z3 = L.u.z3
  const way = new Map<string, "up" | "down" | "no">()
  // An array the loop changes only through its elements (`b[i] = …`, `b[i].f = …`) keeps its length: each such write
  // lands inside it, an obligation (`elementStep`). Anything else that changes it says nothing of its length.
  const lengths = new Map<string, boolean>()
  const outer = (y: ts.Identifier): boolean => {
    const decl = L.checker.getSymbolAtLocation(y)?.valueDeclaration
    return decl === undefined || decl.pos < inner.pos || decl.end > inner.end
  }
  const note = (target: ts.Expression, d: "up" | "down" | "no"): void => {
    const y = unwrap(target)
    if (!ts.isIdentifier(y)) {
      let r: ts.Expression = y
      let first: ts.Expression | undefined
      while (ts.isPropertyAccessExpression(r) || ts.isElementAccessExpression(r)) {
        first = r
        r = unwrap(r.expression)
      }
      if (ts.isIdentifier(r) && outer(r))
        lengths.set(r.text, (lengths.get(r.text) ?? true) && first !== undefined && ts.isElementAccessExpression(first))
      return
    }
    if (!outer(y)) return
    lengths.set(y.text, false)
    const prev = way.get(y.text)
    way.set(y.text, prev === undefined || prev === d ? d : "no")
  }
  const changedOtherwise = (x: ts.Expression): void => {
    let r = unwrap(x)
    while (ts.isPropertyAccessExpression(r) || ts.isElementAccessExpression(r)) r = unwrap(r.expression)
    if (ts.isIdentifier(r) && outer(r)) lengths.set(r.text, false)
  }
  const wholeLiteral = (x: ts.Expression): boolean => ts.isNumericLiteral(x) && /^\d+$/.test(x.text)
  const visit = (n: ts.Node): void => {
    if (ts.isBinaryExpression(n) && n.operatorToken.kind >= K.FirstAssignment && n.operatorToken.kind <= K.LastAssignment) {
      const op = n.operatorToken.kind
      note(
        n.left,
        op === K.PlusEqualsToken && wholeLiteral(n.right) ? "up" : op === K.MinusEqualsToken && wholeLiteral(n.right) ? "down" : "no",
      )
    } else if (
      (ts.isPrefixUnaryExpression(n) || ts.isPostfixUnaryExpression(n)) &&
      (n.operator === K.PlusPlusToken || n.operator === K.MinusMinusToken)
    )
      note(n.operand, n.operator === K.PlusPlusToken ? "up" : "down")
    else if (ts.isDeleteExpression(n)) changedOtherwise(n.expression)
    else if (ts.isCallExpression(n)) {
      // As `changedBy` reads a call: a method that changes its receiver, or a function of the program lent a value.
      if (ts.isPropertyAccessExpression(n.expression) && MUTATORS.has(n.expression.name.text)) changedOtherwise(n.expression.expression)
      if (ts.isIdentifier(n.expression))
        for (const a of n.arguments) if (!ts.isArrowFunction(a) && !ts.isFunctionExpression(a)) changedOtherwise(a)
    }
    ts.forEachChild(n, visit)
  }
  for (const n of nodes) visit(n)
  const counters = [...way].filter(([name, d]) => d !== "no" && st.vars.get(name)?.kind === "cell")
  const kept = [...lengths].filter(([name, only]) => only && st.vars.get(name)?.kind === "cell").map(([name]) => name)
  if (counters.length === 0 && kept.length === 0) return { facts: () => z3.Bool.val(true), whole: new Set() }
  const arrayIn = (x: State, name: string) => {
    const v = envOf(L, x).get(name)?.()
    const p = v === undefined ? undefined : present(v)
    return p?.kind === "array" ? p : undefined
  }
  const valueIn = (x: State, name: string) => {
    const v = envOf(L, x).get(name)?.()
    return v === undefined ? undefined : asNumber(L, v)
  }
  const whole = (v: Extract<Val, { kind: "num" }>) => z3.And(v.cls.eq(NUM.finite), isWhole(L.u, v))
  const wholeCells = new Set<number>()
  for (const [name] of counters) {
    const b = st.vars.get(name)
    const v = b?.kind === "cell" ? present(envOf(L, st).get(name)!()) : undefined
    // Not `-0`, which an integer does not hold: `let i = -0` is no counter.
    const signless = v?.kind === "num" && (v.negZero === undefined || z3.isFalse(v.negZero))
    if (
      b?.kind === "cell" &&
      v?.kind === "num" &&
      signless &&
      v.cls.eqIdentity(z3.Int.val(NUM.finite)) &&
      v.whole !== undefined &&
      z3.isTrue(v.whole)
    )
      wholeCells.add(b.cell)
  }
  const facts = (x: State) =>
    z3.And(
      z3.Bool.val(true),
      ...counters.flatMap(([name, d]) => {
        const a = valueIn(st, name)
        const b = valueIn(x, name)
        if (a === undefined || b === undefined) return []
        return [z3.Implies(whole(a), z3.And(whole(b), d === "up" ? b.real.ge(a.real) : b.real.le(a.real)))]
      }),
      ...kept.flatMap((name) => {
        const a = arrayIn(st, name)
        const b = arrayIn(x, name)
        return a === undefined || b === undefined ? [] : [b.length.eq(a.length)]
      }),
    )
  return { facts, whole: wholeCells }
}

/**
 * A state whose `cells` hold any values of their types: what is known of them is what the caller then assumes. A cell
 * of `whole` holds any integer, a counter's (`counterFacts`).
 */
const havoc = (
  L: Lowering,
  st: State,
  cells: ReadonlySet<number>,
  tag: string,
  at: ts.Node,
  whole: ReadonlySet<number> = new Set(),
): State => {
  if (cells.size === 0) return st
  const z3 = L.u.z3
  const store = new Map(st.store)
  for (const c of cells) {
    const cell = st.store.get(c)!
    if (cell.type === undefined) throw new Unsupported(`\`${cell.name}\` changes in a loop, and its type is unknown`, at)
    const type = cell.type
    const integer = (): Val => {
      const k = z3.Int.const(L.u.fresh(`${cell.name}@${tag}~k`))
      return { kind: "num", cls: z3.Int.val(NUM.finite), real: z3.ToReal(k), whole: z3.Bool.val(true), int: k }
    }
    // A map the code built stays one: any table of its type, which the code may go on writing.
    const any = (): Val => {
      const v = symbolicOf(L, type, [L.u.fresh(`${cell.name}@${tag}`)], [], at)
      return builtKind(L, type) === "object" && v.kind === "record" && v.entries !== undefined
        ? mapValue(givenTable(L, v, at), tableMethods)
        : v
    }
    store.set(c, { ...cell, thunk: lazy(() => (whole.has(c) ? integer() : any())) })
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
  if (!ts.isVariableDeclarationList(init) || init.declarations.length !== 1)
    throw new Unsupported("a `for…of` loop is modeled with one declaration, `for (const x of xs)` or `for (const [k, v] of pairs)`", s)
  const head = init.declarations[0]!.name
  const name = ts.isIdentifier(head) ? head.text : undefined
  const iterPlace = placeOf(L, st, s.expression)
  const read = present(iterPlace !== undefined ? readPlace(L, st, iterPlace.place) : lowerExpr(L, s.expression, envOf(L, st)))
  // A `Map` or a `Set` the code built gives its elements, values of their own (`elementsOf`).
  const map = read.kind === "record" ? read.table : undefined
  const iterated = map !== undefined ? elementsOf(L, map, s.expression) : read
  if (iterated.kind !== "array") throw new Unsupported(`a \`for…of\` over a ${iterated.kind} is not modeled`, s.expression)
  const arr = iterated
  const elementPlace = map === undefined ? iterPlace : undefined
  const { invariants: written, rest } = invariantsOf(L, s.statement)
  for (const inv of written) for (const n of namesIn(head)) noElement(L, inv, n)
  const changed = changedBy(L, st, [s.statement], s.statement)
  // A loop whose passes only build what it changes is read whole on the proof side (`summarized`): it needs no
  // invariant, and none is guessed for it, on either side.
  const builds = written.length === 0 && buildsOnly(L, st, s.statement, changed)
  // What is written, then the verifier's guesses, if it makes any for this loop, each read in the loop's state: when
  // nothing is written, or beside what is (`verify`'s second round, for a law what is written leaves unproved).
  if (written.length > 0) L.wrote = true
  const guessed = !builds && L.guess !== undefined && (written.length === 0 || L.guessBeside === true) ? L.guess(s) : []
  const invariants: ReadonlyArray<LoopClaim> = [
    ...written.map((call) => writtenClaim(L, call)),
    ...guessed.map((g) => ({ ...g, claim: (at: State, i: Arith) => g.claim(envOf(L, at), i) })),
  ]
  if (iterPlace !== undefined && changed.has(iterPlace.place.cell))
    throw new Unsupported(`changes \`${s.expression.getText()}\` while iterating it`, s)
  const elementType = L.checker.getTypeAtLocation(head)
  const bindElement = (at: State, i: Arith): State => {
    // A pattern takes the element apart, each name a value of it, as a `const` pattern does.
    if (name === undefined) return bindName(L, at, head, () => arr.elem(i), false, elementType)
    if (elementPlace !== undefined && isObjectType(L, elementType))
      return bindVar(at, name, { kind: "place", place: extend(elementPlace.place, { kind: "index", index: i }, name) })
    return newCell(L, at, name, () => arr.elem(i), false, elementType)
  }
  const bound = arr.maxSize ?? arr.size ?? u.bound
  const results = { returns: [] as Array<Exits["returns"][number]>, leaving: [] as Array<State> }
  if (bound !== undefined) {
    let head: State | undefined = st
    for (let k = 0; head !== undefined; k++) {
      const atK: State = head
      for (const inv of invariants) obligateClaim(L, inv, k === 0 ? "entry" : "kept", atK.cond, inv.claim(atK, z3.Int.val(k), "asserted"))
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
  // A key the loop is read at, bound as its element is: a value of its own, where the element is not an object.
  const bindKey =
    name !== undefined && !(elementPlace !== undefined && isObjectType(L, elementType))
      ? (at: State, k: Val): State => newCell(L, at, name, () => k, false, elementType)
      : undefined
  if (builds) return summarized(L, s, st, arr, rest, bindElement, changed, bindKey)
  // Proof side, unknown length: through the invariants.
  for (const inv of invariants) obligateClaim(L, inv, "entry", st.cond, inv.claim(st, z3.Int.val(0), "asserted"))
  const i = u.leaf([u.fresh("i"), "$"], "int", [], "count") as never as Arith
  const counted = counterFacts(L, st, [s.statement], s.statement)
  const step = havoc(L, st, changed, "step", s, counted.whole)
  const hyp = z3.And(st.cond, i.ge(0), i.lt(arr.length), counted.facts(step), ...invariants.map((inv) => inv.claim(step, i, "assumed")))
  const x = scoped(statements(L, rest, withCond(bindElement(step, i), hyp)), st.vars)
  const next = merge(L, [x.normal, ...x.continues], s)
  if (next !== undefined) for (const inv of invariants) obligateClaim(L, inv, "kept", next.cond, inv.claim(next, i.add(1), "asserted"))
  const after = havoc(L, st, changed, "after", s, counted.whole)
  if (invariants.length === 0 && changed.size > 0)
    u.notes.add("A loop with no invariant leaves what it changes unknown on the proof side; the search side runs it.")
  return leave(L, st, x, after, z3.And(counted.facts(after), ...invariants.map((inv) => inv.claim(after, arr.length, "assumed"))), s)
}

/** What a loop builds in a variable, by its type: a map the code built (a dictionary, a `Map`, a `Set`), or an array. */
const builtKind = (L: Lowering, type: ts.Type | undefined): MapKind | "array" | undefined => {
  if (type === undefined) return undefined
  const t = L.checker.getNonNullableType(type)
  if (t !== type) return undefined
  if (L.checker.isArrayType(t)) return "array"
  if (isDictionaryType(L.checker, t)) return "object"
  const name = t.getSymbol()?.getName()
  return name === "Map" || name === "Set" ? name : undefined
}

/**
 * Whether a loop's passes only build what it changes: each variable it changes is a map the code built or an array,
 * named in its body only where the body writes it (`out[k] = v`, `out.k = v`, `delete out[k]`, `xs.push(v)`,
 * `m.set(k, v)`, `s.add(k)`, `m.delete(k)`), and a pass ends at its end or at a `continue`. Its other statements declare
 * a name, or choose with `if`.
 */
const buildsOnly = (L: Lowering, st: State, body: ts.Statement, changed: ReadonlySet<number>): boolean => {
  if (changed.size === 0) return false
  for (const c of changed) {
    const cell = st.store.get(c)
    if (cell === undefined || !cell.owned || builtKind(L, cell.type) === undefined) return false
  }
  // The names of what it builds: every binding of the cells it changes.
  const names = new Map<string, number>()
  for (const [n, b] of st.vars) {
    if (b.kind === "cell" && changed.has(b.cell)) names.set(n, b.cell)
    if (b.kind === "place" && changed.has(b.place.cell)) return false
  }
  const built = (e: ts.Expression): number | undefined => {
    const x = unwrap(e)
    if (!ts.isIdentifier(x)) return undefined
    const d = L.checker.getSymbolAtLocation(x)?.valueDeclaration
    if (d !== undefined && d.pos >= body.pos && d.end <= body.end) return undefined
    return names.get(x.text)
  }
  let ok = true
  // Any other mention of what it builds is a read of it.
  const reads = (n: ts.Node): void => {
    if (!ok) return
    if (ts.isIdentifier(n) && built(n) !== undefined) ok = false
    else ts.forEachChild(n, reads)
  }
  const kindOf = (e: ts.Expression) => builtKind(L, st.store.get(built(e)!)!.type)
  const write = (e: ts.Expression): boolean => {
    const x = unwrap(e)
    if (ts.isBinaryExpression(x) && x.operatorToken.kind === K.EqualsToken) {
      const t = unwrap(x.left)
      if ((ts.isElementAccessExpression(t) || ts.isPropertyAccessExpression(t)) && built(t.expression) !== undefined) {
        if (kindOf(t.expression) !== "object") return false
        if (ts.isElementAccessExpression(t)) reads(t.argumentExpression)
        reads(x.right)
        return true
      }
      return false
    }
    if (ts.isDeleteExpression(x)) {
      const t = unwrap(x.expression)
      if ((ts.isElementAccessExpression(t) || ts.isPropertyAccessExpression(t)) && built(t.expression) !== undefined) {
        if (kindOf(t.expression) !== "object") return false
        if (ts.isElementAccessExpression(t)) reads(t.argumentExpression)
        return true
      }
      return false
    }
    if (ts.isCallExpression(x) && ts.isPropertyAccessExpression(x.expression) && built(x.expression.expression) !== undefined) {
      const kind = kindOf(x.expression.expression)
      const method = x.expression.name.text
      const allowed =
        kind === "array" ? ["push"] : kind === "Map" ? ["set", "delete"] : kind === "Set" ? ["add", "delete"] : ([] as Array<string>)
      if (!allowed.includes(method) || x.arguments.some(ts.isSpreadElement)) return false
      if (method === "push" && x.arguments.length !== 1) return false
      x.arguments.forEach(reads)
      return true
    }
    return false
  }
  const statement = (n: ts.Statement): void => {
    if (!ok) return
    if (ts.isBlock(n)) n.statements.forEach(statement)
    else if (ts.isIfStatement(n)) {
      reads(n.expression)
      statement(n.thenStatement)
      if (n.elseStatement !== undefined) statement(n.elseStatement)
    } else if (ts.isVariableStatement(n)) reads(n.declarationList)
    else if (ts.isContinueStatement(n)) ok = n.label === undefined
    else if (ts.isExpressionStatement(n)) ok = write(n.expression)
    else if (!ts.isEmptyStatement(n)) ok = false
  }
  statement(body)
  return ok
}

/**
 * A loop over an array of unknown length whose passes only build what it changes (`buildsOnly`), read whole on the proof
 * side, exactly. A pass writes a map at keys it computes, and pushes onto an array, from its element and from what the
 * loop does not change: no pass sees another's. So each key of a map holds what the last pass that wrote it wrote, or
 * what it held before (`loopEntry`, in `maps.ts`); an array holds what it held, then what each pass pushed, in order
 * (`flatExact`). A pass is read once at an index the quantifiers bind, for what every pass obliges and writes, then again
 * at each index a read asks about: the last pass that wrote a key, the pass an element comes from.
 */
const summarized = (
  L: Lowering,
  s: ts.ForOfStatement,
  st: State,
  arr: Extract<Val, { kind: "array" }>,
  rest: ReadonlyArray<ts.Statement>,
  bindElement: (at: State, i: Arith) => State,
  changed: ReadonlySet<number>,
  bindKey: ((at: State, k: Val) => State) | undefined,
): Exits => {
  const u = L.u
  const z3 = u.z3
  const n = arr.length
  const bounds = u.openBounds()
  // What each pass starts from: the loop's state, each thing it builds a marker that is written, never read.
  type Built =
    | { readonly kind: MapKind; readonly table: Table }
    | { readonly kind: "array"; readonly base: Extract<Val, { kind: "array" }> }
  const built = new Map<number, Built>()
  const store = new Map(st.store)
  for (const c of changed) {
    const cell = st.store.get(c)!
    const kind = builtKind(L, cell.type)!
    const reads = (): never => {
      throw new Unsupported(`reads \`${cell.name}\` in the loop that builds it, which is read only where each pass writes it`, s)
    }
    if (kind === "array") {
      const base: Extract<Val, { kind: "array" }> = { kind: "array", length: z3.Int.const(u.fresh(`${cell.name}.before`)), elem: reads }
      const start: Val = { ...base, pushes: { base, items: [] } }
      built.set(c, { kind, base })
      store.set(c, { ...cell, thunk: () => start })
    } else {
      const table = markerTable(L, kind, cell.name, s)
      const start = mapValue(table, tableMethods)
      built.set(c, { kind, table })
      store.set(c, { ...cell, thunk: () => start })
    }
  }
  const start: State = { ...st, store }
  interface Pass {
    readonly writes: ReadonlyMap<number, ReadonlyArray<Write>>
    readonly pushes: ReadonlyMap<number, ReadonlyArray<{ readonly cond: Bool; readonly value: Val }>>
  }
  const run = (from: State): Pass => {
    const x = scoped(statements(L, rest, from), st.vars)
    if (x.returns.length > 0 || x.breaks.length > 0) throw new Error("a pass of a loop read whole leaves it early")
    const next = merge(L, [x.normal, ...x.continues], s)
    const writes = new Map<number, ReadonlyArray<Write>>()
    const pushes = new Map<number, ReadonlyArray<{ readonly cond: Bool; readonly value: Val }>>()
    for (const [c, b] of built) {
      const v = next === undefined ? undefined : present(readCell(next, c, st.store.get(c)!.name))
      if (b.kind === "array") {
        if (v?.kind === "array" && v.pushes?.base === b.base) pushes.set(c, v.pushes.items)
        else if (v === undefined || (v.kind === "array" && v.length === b.base.length)) pushes.set(c, [])
        else throw new Error("a pass of a loop read whole builds its array otherwise than by pushes")
      } else {
        const t2 = tableOf(v)
        const ws = v === undefined ? [] : t2 === undefined ? undefined : writesSince(t2, b.table)
        if (ws === undefined) throw new Error("a pass of a loop read whole builds its map otherwise than by writes")
        writes.set(c, ws)
      }
    }
    return { writes, pushes }
  }
  const pass = (t: Arith): Pass => run(withCond(bindElement(start, t), z3.And(st.cond, t.ge(0), t.lt(n))))
  // Over a list of keys, each once, a map each pass writes at its element alone is read key by key: a key's entry is
  // the pass's at that key, where the list holds it (`keyedTable`), and no function of the pass's index is made for it.
  const keyed = arr.keyed !== undefined && bindKey !== undefined ? arr.keyed : undefined
  const byKey = new Set<number>()
  // Every pass, at an index the quantifiers bind: what it obliges, and each of its writes, by the pass's index: whether
  // the pass makes it, at which key, with which value, each a function of the index the pass defines; and that every
  // pass that makes it at a key is at most the last that does (`loopEntry` says that the last does).
  const i = z3.Int.const(u.fresh("pass"))
  const inRange = z3.And(i.ge(0), i.lt(n))
  const effects = new Map<number, Array<LoopEffect>>()
  const every = elementwise(
    L,
    i,
    inRange,
    () => {
      const each = pass(i)
      const facts: Array<Bool> = []
      const element = keyed === undefined ? undefined : identity(arr.elem(i))
      for (const [c, all] of each.writes) {
        if (element !== undefined && all.length > 0 && all.every((w) => identity(w.key) === element)) {
          byKey.add(c)
          continue
        }
        const name = st.store.get(c)!.name
        const made: Array<LoopEffect> = []
        for (const w of sameKeyMerged(L, all, s)) {
          const key = packed(L, w.key, s, name)
          const value = packed(L, w.value, s, name)
          const k = key.terms[0]
          if (key.terms.length !== 1 || k === undefined || !["str", "int", "bool"].includes(w.key.kind))
            throw new Unsupported(
              `a loop that writes \`${name}\` at a key that is a ${w.key.kind}: of a string, a bigint or a boolean it is read whole`,
              s,
            )
          const fn = u.fresh(`${name}.wrote`)
          const ints = [...bounds.map(() => z3.Int.sort()), z3.Int.sort()]
          const cond = z3.Function.declare(`${fn}.cond`, ...ints, z3.Bool.sort())
          const keyAt = z3.Function.declare(`${fn}.key`, ...ints, k.sort)
          const valueAt = value.terms.map((v, p) => z3.Function.declare(`${fn}.value${p}`, ...ints, v.sort))
          const heldAt = w.present === undefined ? undefined : z3.Function.declare(`${fn}.held`, ...ints, z3.Bool.sort())
          const has = z3.Function.declare(fn, ...bounds.map(() => z3.Int.sort()), k.sort, z3.Bool.sort())
          const last = z3.Function.declare(`${fn}.last`, ...bounds.map(() => z3.Int.sort()), k.sort, z3.Int.sort())
          const at = (t: Arith) => [...bounds, t]
          facts.push(
            cond.call(...at(i)).eq(w.cond),
            z3.Implies(
              w.cond,
              z3.And(
                (keyAt.call(...at(i)) as Expr).eq(k),
                ...value.terms.map((v, p) => (valueAt[p]!.call(...at(i)) as Expr).eq(v)),
                ...(heldAt === undefined ? [] : [heldAt.call(...at(i)).eq(w.present!)]),
                has.call(...bounds, k),
                i.le(last.call(...bounds, k)),
              ),
            ),
          )
          made.push({
            held: (t) => (heldAt === undefined ? z3.Bool.val(w.set) : heldAt.call(...at(t))),
            cond: (t) => cond.call(...at(t)),
            key: (t) => key.build([keyAt.call(...at(t))]),
            value: (t) => value.build(valueAt.map((f) => f.call(...at(t)))),
            has,
            last,
          })
        }
        effects.set(c, made)
      }
      return z3.And(z3.Bool.val(true), ...facts)
    },
    true,
  )
  u.assume(z3.ForAll([i], z3.Implies(z3.And(inRange, ...every.facts), every.result)), bounds)
  // What a pass pushes is read again at each index a read asks about, quietly: what it obliges is obliged above.
  const passes = new Map<string, Pass>()
  const passAt = (t: Arith): Pass => {
    const key = termId(t)
    let p = passes.get(key)
    if (p === undefined) {
      p = quietly(L, () => pass(t))
      passes.set(key, p)
    }
    return p
  }
  const after = new Map(st.store)
  for (const [c, b] of built) {
    const cell = st.store.get(c)!
    const before = (): Val => present(readCell(st, c, cell.name))
    if (b.kind === "array") {
      after.set(c, {
        ...cell,
        thunk: later(L, () => {
          const pushed = flatExact(L, n, (t) => pushedItems(L, passAt(t).pushes.get(c)!, s))
          const was = before()
          if (was.kind !== "array") throw new Unsupported(`\`${cell.name}\` is a ${was.kind} before the loop that builds it`, s)
          return joined(L, was, pushed, s)
        }),
      })
      continue
    }
    if (byKey.has(c) && keyed !== undefined && bindKey !== undefined) {
      const list = { ...arr, keyed }
      const passes = new Map<string, Pass>()
      const writesAt = (k: Val): ReadonlyArray<Write> => {
        const id = identity(k)
        let p = id === undefined ? undefined : passes.get(id)
        if (p === undefined) {
          p = quietly(L, () => run(withCond(bindKey(start, k), z3.And(st.cond, keyed.member(k)))))
          if (id !== undefined) passes.set(id, p)
        }
        const ws = p.writes.get(c) ?? []
        if (ws.some((w) => identity(w.key) !== id)) throw new Error("a pass read at a key writes another")
        return ws
      }
      after.set(c, {
        ...cell,
        thunk: later(L, () => {
          const prev = tableOf(before())
          if (prev === undefined) throw new Unsupported(`\`${cell.name}\` is no map the code built before the loop that writes it`, s)
          return mapValue(keyedTable(prev, list, writesAt, s), tableMethods)
        }),
      })
      continue
    }
    const loop: LoopWrites = { n, bounds, effects: effects.get(c) ?? [] }
    after.set(c, {
      ...cell,
      thunk: later(L, () => {
        const prev = tableOf(before())
        if (prev === undefined) throw new Unsupported(`\`${cell.name}\` is no map the code built before the loop that writes it`, s)
        return mapValue(loopTable(prev, loop, s), tableMethods)
      }),
    })
  }
  u.notes.add(
    "A loop whose passes only write a map the code built, or push onto an array, is read whole on the proof side: each key holds what the last pass that wrote it wrote, and the array what each pass pushed, in order.",
  )
  return { normal: { ...st, store: after }, returns: [], breaks: [], continues: [] }
}

/**
 * A pass's writes, those at one key term made one, in order: a later write over an earlier where its branch holds. A
 * pass that sets or deletes `edit.key` on two branches writes one key, read once.
 */
const sameKeyMerged = (
  L: Lowering,
  ws: ReadonlyArray<Write>,
  at: ts.Node,
): Array<{ readonly cond: Bool; readonly key: Val; readonly set: boolean; readonly value: Val; readonly present?: Bool }> => {
  const z3 = L.u.z3
  const out: Array<{ cond: Bool; key: Val; set: boolean; value: Val; present?: Bool }> = []
  for (const w of ws) {
    const k = identity(w.key)
    const prior = k === undefined ? undefined : out.find((o) => identity(o.key) === k)
    if (prior === undefined) {
      out.push({ ...w })
      continue
    }
    // Whether the key is held after the two, and its value where it is.
    const heldBefore = prior.present ?? z3.Bool.val(prior.set)
    prior.present = z3.If(w.cond, z3.Bool.val(w.set), heldBefore)
    prior.value = w.set ? (prior.set ? ite(L.u, w.cond, w.value, prior.value, at) : w.value) : prior.value
    prior.set = prior.set || w.set
    prior.cond = z3.Or(prior.cond, w.cond)
  }
  return out
}

/**
 * A value a loop's pass writes, as the terms that make it and how to make it again of other terms: of a string, a
 * boolean, a bigint, a number (its class, its value, whether it is `-0`), and of one of those that may be missing.
 */
const packed = (
  L: Lowering,
  v: Val,
  at: ts.Node,
  name: string,
): { readonly terms: ReadonlyArray<Expr>; readonly build: (terms: ReadonlyArray<Expr>) => Val } => {
  const z3 = L.u.z3
  switch (v.kind) {
    case "str":
    case "bool":
    case "int":
      return { terms: [v.term], build: ([t]) => ({ ...v, term: t }) as Val }
    case "num":
      return {
        terms: [v.cls, v.real, v.negZero ?? z3.Bool.val(false)],
        build: ([cls, real, negZero]) => ({ kind: "num", cls: cls as Arith, real: real as Arith, negZero: negZero as Bool }),
      }
    case "nullish":
      return { terms: [], build: () => v }
    case "maybe": {
      const inner = v.value === undefined ? undefined : packed(L, v.value, at, name)
      return {
        terms: [v.isNull, v.isUndefined, ...(inner?.terms ?? [])],
        build: ([isNull, isUndefined, ...rest]) => ({
          kind: "maybe",
          isNull: isNull as Bool,
          isUndefined: isUndefined as Bool,
          value: inner?.build(rest),
        }),
      }
    }
    default:
      throw new Unsupported(
        `a loop that writes \`${name}\` a ${v.kind}: a map a loop builds is read whole where it holds strings, numbers, booleans or bigints`,
        at,
      )
  }
}

/** `a` followed by `b`, as `[...a, ...b]` is. */
const joined = (L: Lowering, a: Extract<Val, { kind: "array" }>, b: Extract<Val, { kind: "array" }>, at: ts.Node): Val => {
  if (a.size === 0) return b
  return {
    kind: "array",
    length: a.length.add(b.length),
    elem: memoElems((j) => ite(L.u, j.lt(a.length), a.elem(j), b.elem(j.sub(a.length)), at)),
  }
}

/**
 * How the proof side leaves a loop it reads through its invariants, a choice the solver makes. Either the loop ran to its
 * end, and what holds there (`atEnd`: the invariants, and a `while`'s guard false) is known; or the iteration read at the
 * solver's count and state left it by a `return` or a `break`, and that iteration is one that does. What holds at the
 * end is never known on the second way: a loop that returns early never reaches it.
 */
const leave = (L: Lowering, st: State, x: Exits, after: State, atEnd: Bool, at: ts.Node): Exits => {
  const z3 = L.u.z3
  const exits = [...x.returns.map((r) => r.state.cond), ...x.breaks.map((b) => b.cond)]
  if (exits.length === 0) {
    L.hints.push(z3.Implies(st.cond, atEnd))
    return { normal: withCond(after, st.cond), returns: [], breaks: [], continues: [] }
  }
  const ran = z3.Bool.const(L.u.fresh("loop.ran"))
  L.u.assume(z3.Implies(z3.And(st.cond, z3.Not(ran)), z3.Or(...exits)))
  L.hints.push(z3.Implies(z3.And(st.cond, ran), atEnd))
  const early = (c: Bool) => z3.And(c, z3.Not(ran))
  return {
    normal: merge(L, [withCond(after, z3.And(st.cond, ran)), ...x.breaks.map((b) => withCond(b, early(b.cond)))], at),
    returns: x.returns.map((r) => ({ ...r, state: withCond(r.state, early(r.state.cond)) })),
    breaks: [],
    continues: [],
  }
}

/** An invariant states what holds between iterations: the current element is not one of its words. */
/** The names a binding declares, a pattern's every one. */
const namesIn = (n: ts.BindingName): Array<ts.Identifier> =>
  ts.isIdentifier(n) ? [n] : n.elements.flatMap((el) => (ts.isOmittedExpression(el) ? [] : namesIn(el.name)))

const noElement = (L: Lowering, inv: ts.CallExpression, element: ts.Identifier): void => {
  const sym = L.checker.getSymbolAtLocation(element)
  const visit = (n: ts.Node): void => {
    if (ts.isIdentifier(n) && L.checker.getSymbolAtLocation(n) === sym)
      throw new Unsupported(
        `an invariant holds between iterations, where there is no \`${element.text}\`: state it with \`i\`, the count done`,
        n,
      )
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
  // The guard and the step run under what holds where they run, as a statement does: an obligation of theirs (`i + 1`
  // exact) is asked there, on the proof side with the loop's hypotheses at its head.
  const guard = (x: State, where: Bool = x.cond): Bool =>
    guardExpr === undefined ? z3.Bool.val(true) : under(L, where, () => condOf(L, guardExpr, envOf(L, x)))
  const incr = (x: State | undefined): State | undefined =>
    x === undefined || !ts.isForStatement(s) || s.incrementor === undefined
      ? x
      : under(L, x.cond, () => expressionStatement(L, s.incrementor!, x))
  const { invariants, rest } = invariantsOf(L, s.statement)
  const returns: Array<Exits["returns"][number]> = []
  const leaving: Array<State> = []
  if (u.bound !== undefined) {
    let head: State | undefined = st
    for (let k = 0; head !== undefined; k++) {
      const atK: State = head
      for (const inv of invariants)
        obligate(L, "invariant", inv, k === 0 ? "entry" : "kept", atK.cond, claim(L, atK, inv, undefined, "asserted"))
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
  for (const inv of invariants) obligate(L, "invariant", inv, "entry", st.cond, claim(L, st, inv, undefined, "asserted"))
  const changed = changedBy(
    L,
    st,
    ts.isForStatement(s) && s.incrementor !== undefined ? [s.statement, s.incrementor] : [s.statement],
    s.statement,
  )
  const counted = counterFacts(
    L,
    st,
    ts.isForStatement(s) && s.incrementor !== undefined ? [s.statement, s.incrementor] : [s.statement],
    s.statement,
  )
  const step = havoc(L, st, changed, "step", s, counted.whole)
  const head = z3.And(st.cond, counted.facts(step), ...invariants.map((inv) => claim(L, step, inv, undefined, "assumed")))
  const hyp = z3.And(head, guard(step, head))
  const x = scoped(statements(L, rest, withCond(step, hyp)), st.vars)
  const next = incr(merge(L, [x.normal, ...x.continues], s))
  if (next !== undefined)
    for (const inv of invariants) obligate(L, "invariant", inv, "kept", next.cond, claim(L, next, inv, undefined, "asserted"))
  const after = havoc(L, st, changed, "after", s, counted.whole)
  u.notes.add("A `for` or `while` loop is assumed to end: an invariant proves what holds if it does.")
  return scoped(
    leave(
      L,
      st,
      x,
      after,
      (() => {
        const atEnd = z3.And(st.cond, counted.facts(after), ...invariants.map((inv) => claim(L, after, inv, undefined, "assumed")))
        return z3.And(z3.Not(guard(after, atEnd)), atEnd)
      })(),
      s,
    ),
    st0.vars,
  )
}

// ——— Lemmas ———

/** The lemma a callee names: `const name = lemma(statement, { requires })`, read from source. */
export const lemmaOf = (
  L: Lowering,
  callee: ts.Expression,
):
  | { readonly file: string; readonly name: string; readonly statement: FunctionNode; readonly requires: FunctionNode | undefined }
  | undefined => {
  if (!ts.isIdentifier(callee)) return undefined
  const d = symbolOf(L.checker, callee)?.valueDeclaration
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
      if (ts.isPropertyAssignment(p) && ts.isIdentifier(p.name) && p.name.text === "requires")
        requires = functionOf(L.checker, p.initializer)
      else throw new Unsupported("a lemma's one option is `requires`", p)
    }
  }
  return {
    file: d.getSourceFile().fileName,
    name: (d.name as ts.Identifier).text,
    statement: functionOf(L.checker, statementArg),
    requires,
  }
}

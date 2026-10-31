// JavaScript's own functions the verifier reads: `Math`, `Number`, `Object` and `Date`.
import ts from "typescript"
import type { Arith, Bool, FuncDecl } from "z3-solver"
import { compare, countAsNum, intOf, isNegZero, isNullish, isWhole, ite, sameValue, strictEq } from "../ops.ts"
import { isLib } from "../effects.ts"
import { MAX_TIME } from "../symbolic.ts"
import type { Universe } from "../universe.ts"
import { type Env, NUM, UNDEFINED, Unsupported, type Val, locate, memoElems } from "../value.ts"
import { type Lowering, bool, lowerExpr, num } from "../lower.ts"
import { TWO_52, TWO_53, asNumber, unwrapParens } from "./numbers.ts"
import { shown } from "./strings.ts"
import { ownOf, tupleOf } from "./records.ts"

const K = ts.SyntaxKind

/**
 * A function of JavaScript's own `Math`, `Number` or `Object` the model reads: what a double makes of it, exactly.
 * `floor`, `trunc` and `ceil` give an integral double, which the double holds, `-0` where JavaScript gives it; `max` and
 * `min` are `NaN` where an argument is, and tell `-0` from `0`; the `Number` checks read the class and the value; and
 * `Object.is` is SameValue.
 */
export const standard = (L: Lowering, callee: ts.PropertyAccessExpression): Val | undefined => {
  const o = callee.expression
  if (!ts.isIdentifier(o) || !["Math", "Number", "Object", "Date"].includes(o.text) || !isLib(L.checker, o)) return undefined
  const z3 = L.u.z3
  const name = `${o.text}.${callee.name.text}`
  const one = (f: (v: Val, at: ts.Node) => Val): Val => ({
    kind: "builtin",
    name,
    call: ([v], at) => {
      if (v === undefined) throw new Unsupported(`\`${name}\` of no argument`, at)
      return f(v, at)
    },
  })
  type Num = Extract<Val, { kind: "num" }>
  const asNum = (v: Val, at: ts.Node): Num => {
    const n = asNumber(L, v)
    if (n === undefined) throw new Unsupported(`\`${name}\` of a ${v.kind}`, at)
    return n
  }
  /**
   * `f` of a fraction; and `toZero` where a fraction rounds to `-0`: between -1 and 0 for `ceil` and `trunc`, from -0.5
   * for `round`.
   */
  const rounded = (f: (r: Arith) => Arith, toZero?: (r: Arith) => Bool) =>
    one((v, at) => {
      if (v.kind === "int" && v.origin === "count") return v
      if (v.kind !== "num") throw new Unsupported(`\`${name}\` of a ${v.kind}`, at)
      const finite = v.cls.eq(NUM.finite)
      // A whole number rounds to itself; a fraction, by `f`.
      const r = z3.If(isWhole(L.u, v), intOf(L.u, v), f(v.real))
      return {
        kind: "num",
        cls: v.cls,
        real: z3.If(finite, z3.ToReal(r), v.real),
        whole: z3.If(finite, z3.Bool.val(true), isWhole(L.u, v)),
        int: z3.If(finite, r, intOf(L.u, v)),
        negZero:
          toZero === undefined
            ? isNegZero(L.u, v)
            : z3.Or(isNegZero(L.u, v), z3.And(finite, z3.Not(isWhole(L.u, v)), toZero(v.real), v.real.lt(0))),
      }
    })
  /** `Math.max` (`largest`) or `Math.min` of any number of numbers: `NaN` where one is; of two zeros, `0` and `-0`. */
  const extreme = (largest: boolean): Val => ({
    kind: "builtin",
    name,
    call: (args, at) => {
      const ns = args.map((v) => asNum(v, at))
      const nan = num(z3, Number.NaN) as Num
      const pair = (a: Num, b: Num): Num => {
        const picked = ite(L.u, compare(L.u, b, a, largest ? ">" : "<", at), b, a, at) as Num
        const zeros = z3.And(a.cls.eq(NUM.finite), b.cls.eq(NUM.finite), a.real.eq(0), b.real.eq(0))
        const sign = largest ? z3.And(isNegZero(L.u, a), isNegZero(L.u, b)) : z3.Or(isNegZero(L.u, a), isNegZero(L.u, b))
        const signed: Num = { ...picked, negZero: z3.If(zeros, sign, isNegZero(L.u, picked)) }
        return ite(L.u, z3.Or(a.cls.eq(NUM.nan), b.cls.eq(NUM.nan)), nan, signed, at) as Num
      }
      const [first, ...rest] = ns
      return first === undefined ? num(z3, largest ? -Infinity : Infinity) : rest.reduce(pair, first)
    },
  })
  // A `Number` check: of a number, what `f` says; of a value that may be missing, that it is there and a number `f`
  // holds of; of anything else (a string, a boolean), false, as JavaScript gives it.
  const check = (f: (v: Extract<Val, { kind: "num" }>) => Bool) => {
    const of = (v: Val, at: ts.Node): Bool => {
      if (v.kind === "num") return f(v)
      if (v.kind === "int" && v.origin === "count") return f(countAsNum(L.u, v.term))
      if (v.kind === "maybe") return v.value === undefined ? z3.Bool.val(false) : z3.And(z3.Not(isNullish(L.u, v)), of(v.value, at))
      if (v.kind === "opaque" || v.kind === "builtin" || v.kind === "fn" || v.kind === "comp")
        throw new Unsupported(`\`${name}\` of a ${v.kind} is not modeled`, at)
      return z3.Bool.val(false)
    }
    return one((v, at) => bool(of(v, at)))
  }
  const whole = (v: Extract<Val, { kind: "num" }>) => z3.And(v.cls.eq(NUM.finite), isWhole(L.u, v))
  switch (name) {
    case "Math.floor":
      return rounded((r) => z3.ToInt(r))
    case "Math.ceil":
      return rounded(
        (r) => z3.ToInt(r.neg()).neg(),
        (r) => r.gt(-1),
      )
    case "Math.trunc":
      return rounded(
        (r) => z3.If(r.ge(0), z3.ToInt(r), z3.ToInt(r.neg()).neg()),
        (r) => r.gt(-1),
      )
    case "Math.round":
      // Half way rounds up, toward +Infinity: 2.5 to 3, -2.5 to -2, and -0.5 to -0.
      return rounded(
        (r) => z3.ToInt(r.add(z3.Real.val("1/2"))),
        (r) => r.ge(z3.Real.val("-1/2")),
      )
    case "Math.max":
      return extreme(true)
    case "Math.min":
      return extreme(false)
    case "Math.abs":
      return one((v, at) => {
        if (v.kind === "int" && v.origin === "count") return v
        const n = asNum(v, at)
        const negative = n.real.lt(0)
        return {
          kind: "num",
          cls: z3.If(n.cls.eq(NUM.negInf), z3.Int.val(NUM.posInf), n.cls),
          real: z3.If(negative, n.real.neg(), n.real),
          ...(n.whole === undefined ? {} : { whole: n.whole }),
          ...(n.int === undefined ? {} : { int: z3.If(n.int.lt(0), n.int.neg(), n.int) }),
        }
      })
    case "Object.is":
      return {
        kind: "builtin",
        name,
        call: (args, at) => {
          const [a, b] = args
          if (args.length !== 2 || a === undefined || b === undefined) throw new Unsupported("`Object.is` of other than two values", at)
          const na = asNumber(L, a)
          const nb = asNumber(L, b)
          if (na !== undefined && nb !== undefined) return bool(sameValue(L.u, na, nb))
          // Of two values neither a number nor an object, SameValue is `===`.
          const plain = (v: Val) =>
            v.kind === "str" || v.kind === "bool" || v.kind === "nullish" || (v.kind === "int" && v.origin === "bigint")
          if (plain(a) && plain(b)) return bool(strictEq(L.u, a, b, at))
          throw new Unsupported(
            "`Object.is` is modeled of two numbers, or of two values neither of which is a number or an object: an object's identity is not",
            at,
          )
        },
      }
    case "Date.parse":
      // A function of its string the verifier does not compute: the same string, the same time, which is `NaN` or a
      // whole number of milliseconds within `MAX_TIME` of 1970. A counterexample leans on that and on nothing more.
      return one((given, at) => {
        const arg = ts.isCallExpression(at) ? at.arguments[0] : undefined
        const v = arg === undefined ? given : shown(L, given, arg)
        if (v.kind !== "str") throw new Unsupported(`\`Date.parse\` of a ${v.kind}: of a string it is read`, at)
        const f = parsing(L.u)
        const ms = f.ms.call(v.term) as Arith
        const cls = f.cls.call(v.term) as Arith
        // What every string's time is, said of this one: `NaN`, or a whole number of milliseconds within `MAX_TIME`.
        L.u.assume(z3.And(z3.Or(cls.eq(NUM.nan), cls.eq(NUM.finite)), ms.le(MAX_TIME), ms.ge(-MAX_TIME)), L.u.openBounds())
        L.u.opaqueCalls.add("Date.parse")
        L.u.notes.add(
          "`Date.parse` is read as some function of its string: the same string gives the same time, `NaN` or a whole number of milliseconds; which time, the verifier does not compute.",
        )
        return { kind: "num", cls, real: z3.ToReal(ms), whole: z3.Bool.val(true), int: ms }
      })
    case "Object.keys":
      return one((v, at) => ownOf(L, v, name, at).keys)
    case "Object.values":
      return one((v, at) => ownOf(L, v, name, at).values)
    case "Object.entries":
      return one((v, at) => {
        const { keys, values } = ownOf(L, v, name, at)
        if (keys.kind !== "array" || values.kind !== "array") throw new Unsupported(`\`${name}\` of a value whose keys are not a list`, at)
        return {
          kind: "array",
          length: keys.length,
          elem: memoElems((i) => tupleOf(L, [() => keys.elem(i), () => values.elem(i)], () => UNDEFINED, at)),
          ...(keys.maxSize === undefined ? {} : { maxSize: keys.maxSize }),
          ...(keys.size === undefined ? {} : { size: keys.size }),
        }
      })
    case "Object.hasOwn":
      return {
        kind: "builtin",
        name,
        call: (args, at) => {
          const [o, key] = args
          const d = o?.kind === "maybe" ? o.value : o
          if (args.length !== 2 || d?.kind !== "record" || d.entries === undefined || key === undefined)
            throw new Unsupported("`Object.hasOwn` is read of a record keyed by any string (`Record<string, T>`) and a key", at)
          return bool(d.entries(key, at).found)
        },
      }
    case "Number.isInteger":
      return check(whole)
    case "Number.isSafeInteger":
      return check((v) => z3.And(whole(v), v.real.le(TWO_53 - 1), v.real.ge(1 - TWO_53)))
    case "Number.isFinite":
      return check((v) => v.cls.eq(NUM.finite))
    case "Number.isNaN":
      return check((v) => v.cls.eq(NUM.nan))
    default:
      return undefined
  }
}

const ROUNDING = new Set(["Math.floor", "Math.ceil", "Math.trunc", "Math.round"])

/**
 * `Math.floor(a / b)`, and `ceil`, `trunc` and `round`, of two whole numbers: the quotient's real value rounded, which
 * is what JavaScript gives while `a` is within 2^52 of 0. A quotient that is not whole is no exact double, but it lies
 * at least `1 / |b|` from a whole number and half that from a half, more than the double it rounds to strays from it,
 * so rounding the double and rounding the real agree. What that needs of `a` and `b` is an obligation, as an exact
 * operation's is. Undefined where the argument is no quotient of two numbers, which reads as the call does.
 */
export const roundedQuotient = (L: Lowering, f: Val, e: ts.CallExpression, env: Env): Val | undefined => {
  const quotient = e.arguments.length === 1 ? unwrapParens(e.arguments[0]!) : undefined
  if (f.kind !== "builtin" || !ROUNDING.has(f.name) || quotient === undefined || !ts.isBinaryExpression(quotient)) return undefined
  if (quotient.operatorToken.kind !== K.SlashToken) return undefined
  const numberTyped = (x: ts.Expression) => (L.checker.getTypeAtLocation(x).flags & ts.TypeFlags.NumberLike) !== 0
  if (!numberTyped(quotient.left) || !numberTyped(quotient.right)) return undefined
  const z3 = L.u.z3
  const a = asNumber(L, lowerExpr(L, quotient.left, env))
  const b = asNumber(L, lowerExpr(L, quotient.right, env))
  if (a === undefined || b === undefined) throw new Unsupported("a quotient of values that are no numbers", quotient)
  const wholeFinite = (v: Extract<Val, { kind: "num" }>) => z3.And(v.cls.eq(NUM.finite), isWhole(L.u, v))
  const goal = z3.And(wholeFinite(a), wholeFinite(b), z3.Not(b.real.eq(0)), a.real.le(TWO_52), a.real.ge(-TWO_52))
  if (L.mode === "spec") L.exact?.push(z3.Implies(L.guard, goal))
  else {
    const where = locate(quotient)
    L.obligations.push({
      key: `exact@${where}#here`,
      kind: "exact",
      text: e.getText(),
      at: where,
      phase: "here",
      cond: L.guard,
      goal,
      hints: L.hints.length,
    })
  }
  const r = a.real.div(b.real)
  const negative = (v: Extract<Val, { kind: "num" }>) => z3.Or(v.real.lt(0), isNegZero(L.u, v))
  const q: Val = {
    kind: "num",
    cls: z3.Int.val(NUM.finite),
    real: r,
    whole: z3.IsInt(r),
    negZero: z3.And(r.eq(0), z3.Not(negative(a).eq(negative(b)))),
  }
  return f.call([q], e)
}

/** `Date.parse` of a universe, one function of the string for its class and one for its milliseconds. */
const PARSING = new WeakMap<Universe, { readonly cls: FuncDecl; readonly ms: FuncDecl }>()
const parsing = (u: Universe): { readonly cls: FuncDecl; readonly ms: FuncDecl } => {
  let f = PARSING.get(u)
  if (f === undefined) {
    const z3 = u.z3
    f = {
      cls: z3.Function.declare("Date.parse~cls", z3.String.sort(), z3.Int.sort()),
      ms: z3.Function.declare("Date.parse~ms", z3.String.sort(), z3.Int.sort()),
    }
    PARSING.set(u, f)
  }
  return f
}

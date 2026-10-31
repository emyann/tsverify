// Numbers: arithmetic on `number` where it is exact, on `bigint` as JavaScript computes it, and the bitwise operators
// on 32-bit integers.
import ts from "typescript"
import type { Arith } from "z3-solver"
import { countAsNum, intOf, isNegZero, isWhole } from "../ops.ts"
import { NUM, Unsupported, type Val, locate } from "../value.ts"
import type { Lowering } from "../lower.ts"

const K = ts.SyntaxKind

export const arithmetic = (L: Lowering, op: ts.SyntaxKind, l: Val, r: Val, e: ts.BinaryExpression): Val => {
  if (BITWISE.has(op)) return bitwise(L, op, l, r, e)
  if (l.kind === "int" && r.kind === "int" && l.origin === "bigint" && r.origin === "bigint") {
    if (op === K.PlusToken) return { ...l, term: l.term.add(r.term) }
    if (op === K.MinusToken) return { ...l, term: l.term.sub(r.term) }
    if (op === K.AsteriskToken) return { ...l, term: l.term.mul(r.term) }
    if (op === K.SlashToken || op === K.PercentToken) return divided(L, op, l, r, e)
    throw new Unsupported(`bigint \`${ts.tokenToString(op)}\` is not modeled`, e.operatorToken)
  }
  const a = asNumber(L, l)
  const b = asNumber(L, r)
  if (a !== undefined && b !== undefined) {
    if (op === K.PercentToken) throw new Unsupported("`%` on `number` is not modeled: `bigint` where the values are whole", e.operatorToken)
    // A count plus or minus a count or a small whole literal (`b.length + c.length`, `i - 1`) is exact whatever the
    // input, a whole number below 2^34: nothing to oblige.
    const small = (x: ts.Expression, v: Val) =>
      (v.kind === "int" && v.origin === "count") || (ts.isNumericLiteral(x) && /^\d{1,9}$/.test(x.text))
    const known = (op === K.PlusToken || op === K.MinusToken) && small(e.left, l) && small(e.right, r)
    if (L.mode === "spec") {
      // Spec code has no runs to hold an obligation: elsewhere than a law, a `requires` or proof code it reads only
      // what is exact whatever the input.
      if (known) return exactly(L, op, a, b, e, true)
      // A law, a `requires` and proof code say where it is exact as part of what they say (`exactSpec`).
      if (L.exact !== undefined) return exactly(L, op, a, b, e)
      throw new Unsupported(
        "here (a declaration's laws, a guessed invariant) arithmetic on `number` is read only on counts and small whole literals (`i - 1`): its rounding is not modeled. Compute the value in the program, or use `bigint`",
        e.operatorToken,
      )
    }
    return exactly(L, op, a, b, e, known)
  }
  if (op === K.PlusToken && l.kind === "str" && r.kind === "str") return { kind: "str", term: l.term.concat(r.term) }
  throw new Unsupported(`${ts.tokenToString(op)} between a ${l.kind} and a ${r.kind} is not modeled`, e)
}

/** `v` as a `number`: itself, or a count (a length, an index), which a double holds exactly. */
export const asNumber = (L: Lowering, v: Val): Extract<Val, { kind: "num" }> | undefined =>
  v.kind === "num" ? v : v.kind === "int" && v.origin === "count" ? countAsNum(L.u, v.term) : undefined

export const TWO_53 = 9007199254740992
export const TWO_52 = 4503599627370496
const TWO_32 = 4294967296
const TWO_31 = 2147483648

const BITWISE: ReadonlySet<ts.SyntaxKind> = new Set([
  K.BarToken,
  K.AmpersandToken,
  K.CaretToken,
  K.LessThanLessThanToken,
  K.GreaterThanGreaterThanToken,
  K.GreaterThanGreaterThanGreaterThanToken,
])

/** The number a literal, a negated one, or a `**` of two of them is, as JavaScript computes it; else `undefined`. */
export const constantOf = (e: ts.Expression): number | bigint | undefined => {
  const x = unwrapParens(e)
  if (ts.isNumericLiteral(x)) return Number(x.text)
  if (ts.isBigIntLiteral(x)) return BigInt(x.text.slice(0, -1))
  if (ts.isPrefixUnaryExpression(x) && x.operator === K.MinusToken) {
    const c = constantOf(x.operand)
    return c === undefined ? undefined : -c
  }
  if (ts.isBinaryExpression(x) && x.operatorToken.kind === K.AsteriskAsteriskToken) {
    const a = constantOf(x.left)
    const b = constantOf(x.right)
    if (typeof a === "number" && typeof b === "number") return a ** b
    if (typeof a === "bigint" && typeof b === "bigint" && b >= 0n) return a ** b
  }
  return undefined
}

/** Methods that give a new array, which nothing else holds. */
const FRESH = new Set(["slice", "map", "filter", "flatMap", "concat", "toReversed", "toSorted"])

/** Whether the receiver of the method `e` calls is an array made right there: a literal, or one a method gave anew. */
export const fresh = (e: ts.CallExpression): boolean => {
  if (!ts.isPropertyAccessExpression(e.expression)) return false
  const r = unwrapParens(e.expression.expression)
  return (
    ts.isArrayLiteralExpression(r) ||
    (ts.isCallExpression(r) && ts.isPropertyAccessExpression(r.expression) && FRESH.has(r.expression.name.text))
  )
}

export const unwrapParens = (e: ts.Expression): ts.Expression => (ts.isParenthesizedExpression(e) ? unwrapParens(e.expression) : e)

/** The results of `x >> 31` (a count of 31 mod 32): a sign mask, 0 or -1 by construction. */
const MASKS = new WeakSet<Arith>()

/** Whether `v` is a sign mask, made by `>> 31`. */
const isMask = (v: Val): boolean => v.kind === "num" && v.int !== undefined && MASKS.has(v.int)

/** A whole number the code made as an integer (a bitwise result): finite, never `-0`. */
export const integral = (L: Lowering, t: Arith): Val => ({
  kind: "num",
  cls: L.u.z3.Int.val(NUM.finite),
  real: L.u.z3.ToReal(t),
  whole: L.u.z3.Bool.val(true),
  int: t,
})

/** The first step of `ToInt32` and `ToUint32`: 0 of `NaN`, the infinities and the zeros; else truncated toward 0. */
export const truncatedOf = (L: Lowering, v: Extract<Val, { kind: "num" }>): Arith => {
  const z3 = L.u.z3
  const t = z3.If(isWhole(L.u, v), intOf(L.u, v), z3.If(v.real.ge(0), z3.ToInt(v.real), z3.ToInt(v.real.neg()).neg()))
  return z3.If(v.cls.eq(NUM.finite), t, z3.Int.val(0))
}

/** `t` as a signed 32-bit integer (`ToInt32`): `t` mod 2^32, from -2^31. */
export const int32 = (L: Lowering, t: Arith): Arith => {
  const z3 = L.u.z3
  const m = t.mod(TWO_32)
  return z3.If(m.ge(TWO_31), m.sub(TWO_32), m)
}

/**
 * A bitwise operator on two numbers, as JavaScript computes it: each operand made a 32-bit integer (`ToInt32`, and
 * `ToUint32` for `>>>`), the result one too, so exact and never `-0`. Shifts are arithmetic, by 2^(count mod 32); `|`,
 * `&` and `^` go through 32-bit vectors, but for `x | 0`, `x ^ 0` and `x & (2^k - 1)`, which are arithmetic too.
 */
const bitwise = (L: Lowering, op: ts.SyntaxKind, l: Val, r: Val, e: ts.BinaryExpression): Val => {
  const z3 = L.u.z3
  const a = asNumber(L, l)
  const b = asNumber(L, r)
  if (a === undefined || b === undefined)
    throw new Unsupported(
      `\`${ts.tokenToString(op)}\` between a ${l.kind} and a ${r.kind} is not modeled: bitwise operators are read on \`number\``,
      e.operatorToken,
    )
  const x = truncatedOf(L, a)
  const y = truncatedOf(L, b)
  const k = constantOf(e.right)
  const literal = typeof k === "number" && Number.isInteger(k) ? k : undefined
  const x32 = int32(L, x)
  const y32 = int32(L, y)
  const vector = (
    f: (p: ReturnType<typeof z3.Int2BV<32>>, q: ReturnType<typeof z3.Int2BV<32>>) => ReturnType<typeof z3.Int2BV<32>>,
  ): Arith => {
    L.u.vectors = true
    return z3.BV2Int(f(z3.Int2BV(x, 32), z3.Int2BV(y, 32)), true)
  }
  // Of 0 or -1, a sign mask (`x >> 31`), each of `|`, `&` and `^` is arithmetic: the vectors are left to other operands.
  const ones = z3.Int.val(-1)
  const zero = z3.Int.val(0)
  // An operand that is a sign mask by construction leaves no other case, and no vectors at all.
  const masked = isMask(r) ? { mask: y32, other: x32 } : isMask(l) ? { mask: x32, other: y32 } : undefined
  if (masked !== undefined && (op === K.BarToken || op === K.AmpersandToken || op === K.CaretToken)) {
    const { mask, other } = masked
    const isZero = mask.eq(zero)
    return integral(
      L,
      op === K.BarToken
        ? z3.If(isZero, other, ones)
        : op === K.AmpersandToken
          ? z3.If(isZero, zero, other)
          : z3.If(isZero, other, other.neg().sub(1)),
    )
  }
  // 2^(count mod 32): a constant of a literal count, else one of the 32.
  const power = (): Arith => {
    if (literal !== undefined) return z3.Int.val(2 ** (((literal % 32) + 32) % 32))
    const c = y.mod(32)
    let p: Arith = z3.Int.val(2 ** 31)
    for (let j = 30; j >= 0; j--) p = z3.If(c.eq(j), z3.Int.val(2 ** j), p)
    return p
  }
  switch (op) {
    case K.BarToken:
      return integral(
        L,
        literal === 0
          ? x32
          : z3.If(
              z3.Or(x32.eq(ones), y32.eq(ones)),
              ones,
              z3.If(
                x32.eq(zero),
                y32,
                z3.If(
                  y32.eq(zero),
                  x32,
                  vector((p, q) => p.or(q)),
                ),
              ),
            ),
      )
    case K.CaretToken:
      return integral(
        L,
        literal === 0
          ? x32
          : z3.If(
              x32.eq(zero),
              y32,
              z3.If(
                y32.eq(zero),
                x32,
                z3.If(
                  x32.eq(ones),
                  y32.neg().sub(1),
                  z3.If(
                    y32.eq(ones),
                    x32.neg().sub(1),
                    vector((p, q) => p.xor(q)),
                  ),
                ),
              ),
            ),
      )
    case K.AmpersandToken: {
      // A mask of the low bits keeps the 32-bit value's remainder: never negative, below the mask.
      const mask = literal !== undefined && literal >= 0 && literal < TWO_31 && Number.isInteger(Math.log2(literal + 1))
      return integral(
        L,
        mask
          ? x.mod(TWO_32).mod(literal + 1)
          : z3.If(
              z3.Or(x32.eq(zero), y32.eq(zero)),
              zero,
              z3.If(
                x32.eq(ones),
                y32,
                z3.If(
                  y32.eq(ones),
                  x32,
                  vector((p, q) => p.and(q)),
                ),
              ),
            ),
      )
    }
    case K.LessThanLessThanToken:
      return integral(L, int32(L, int32(L, x).mul(power())))
    case K.GreaterThanGreaterThanToken: {
      const shifted = int32(L, x).div(power())
      if (literal !== undefined && ((literal % 32) + 32) % 32 === 31) MASKS.add(shifted)
      return integral(L, shifted)
    }
    default:
      return integral(L, x.mod(TWO_32).div(power()))
  }
}

/**
 * `a op b` on doubles, read where it is exact: both finite (and the divisor not 0), the exact result a whole number or
 * a half within 2^53, which a double holds. A double operation rounds its exact result, so there it gives that result.
 * Elsewhere it may round, which the model does not see: each operation is an obligation that it is exact, proved, or
 * broken by an input where it may not be. A law is judged on the runs where every operation is exact, and is proved
 * only once each is (`MODELS`). Where it is `known` exact whatever the input (a count plus a count), it obliges nothing.
 */
export const exactly = (
  L: Lowering,
  op: ts.SyntaxKind,
  a: Extract<Val, { kind: "num" }>,
  b: Extract<Val, { kind: "num" }>,
  at: ts.Node,
  known = false,
): Val => {
  const z3 = L.u.z3
  const r =
    op === K.PlusToken
      ? a.real.add(b.real)
      : op === K.MinusToken
        ? a.real.sub(b.real)
        : op === K.AsteriskToken
          ? a.real.mul(b.real)
          : op === K.SlashToken
            ? a.real.div(b.real)
            : undefined
  if (r === undefined) throw new Unsupported(`\`${ts.tokenToString(op)}\` on \`number\` is not modeled`, at)
  // Whether the result is whole, in terms the solver reasons with: of two whole numbers, a sum, a difference and a
  // product are; `IsInt` beside, for the rest (0.5 + 0.5). Twice a half of a whole number is that number.
  const both = z3.And(isWhole(L.u, a), isWhole(L.u, b))
  const whole = op === K.SlashToken ? z3.IsInt(r) : z3.Or(both, z3.IsInt(r))
  const ia = intOf(L.u, a)
  const ib = intOf(L.u, b)
  const int = op === K.PlusToken ? ia.add(ib) : op === K.MinusToken ? ia.sub(ib) : op === K.AsteriskToken ? ia.mul(ib) : undefined
  const intOfResult = int === undefined ? z3.ToInt(r) : z3.If(both, int, z3.ToInt(r))
  const halfOfTwo = op === K.SlashToken && b.real.eqIdentity(z3.Real.val(2))
  const twiceWhole = halfOfTwo ? isWhole(L.u, a) : op === K.SlashToken ? z3.IsInt(r.mul(2)) : z3.Or(both, z3.IsInt(r.mul(2)))
  const bounded = (x: Arith) => z3.And(x.le(TWO_53), x.ge(-TWO_53))
  const finite = z3.And(a.cls.eq(NUM.finite), b.cls.eq(NUM.finite), op === K.SlashToken ? z3.Not(b.real.eq(0)) : z3.Bool.val(true))
  const goal = z3.And(finite, z3.Or(z3.And(whole, bounded(r)), z3.And(twiceWhole, bounded(r.mul(2)))))
  if (known) {
    // Exact by construction: no condition to say, nor to oblige.
  } else if (L.mode === "spec") L.exact?.push(z3.Implies(L.guard, goal))
  else {
    const where = locate(at)
    L.obligations.push({
      key: `exact@${where}#here`,
      kind: "exact",
      text: at.getText(),
      at: where,
      phase: "here",
      cond: L.guard,
      goal,
      hints: L.hints.length,
    })
  }
  // Its sign where it is 0, as IEEE 754 gives it: `-0 + -0` and `-0 - 0` are `-0`, any other sum or difference that is 0
  // is `0`; a product or quotient that is 0 is `-0` where exactly one operand is negative, `-0` among them.
  const negative = (v: Extract<Val, { kind: "num" }>) => z3.Or(v.real.lt(0), isNegZero(L.u, v))
  const negZero =
    op === K.PlusToken
      ? z3.And(isNegZero(L.u, a), isNegZero(L.u, b))
      : op === K.MinusToken
        ? z3.And(isNegZero(L.u, a), b.real.eq(0), z3.Not(isNegZero(L.u, b)))
        : z3.And(r.eq(0), z3.Not(negative(a).eq(negative(b))))
  return { kind: "num", cls: z3.Int.val(NUM.finite), real: r, whole, int: intOfResult, ...(known ? {} : { negZero }) }
}

/**
 * A bigint `/` or `%`, as JavaScript computes it: the quotient truncated toward zero, the remainder with the dividend's
 * sign. A divisor of 0n throws a RangeError, so wherever the division runs (`L.guard`) its divisor must be another: in
 * the program, an obligation, proved, or broken by the input that throws; in a law or a `requires`, part of what it says.
 */
const divided = (L: Lowering, op: ts.SyntaxKind, l: Val & { kind: "int" }, r: Val & { kind: "int" }, e: ts.BinaryExpression): Val => {
  const z3 = L.u.z3
  // A divisor that is a literal other than 0n never throws: nothing to oblige, and the quotient and remainder are Z3's
  // own, truncated toward 0 as JavaScript's are, which read inside a quantifier as well as out.
  if (z3.isIntVal(r.term) && r.term.value() !== 0n) {
    const d = r.term.value()
    const negative = l.term.lt(0)
    const size = z3.If(negative, l.term.neg(), l.term)
    if (op === K.SlashToken) {
      const q = z3.If(negative, size.div(d < 0n ? -d : d).neg(), size.div(d < 0n ? -d : d))
      return { ...l, term: d < 0n ? q.neg() : q }
    }
    const m = size.mod(d < 0n ? -d : d)
    return { ...l, term: z3.If(negative, m.neg(), m) }
  }
  // Inside a quantifier the element is any index's, read or not, so the obligation would ask more than the code needs.
  if (L.u.openBounds().length > 0)
    throw new Unsupported(
      `a bigint \`${ts.tokenToString(op)}\` by a value the code computes, inside \`.some\`, \`.every\`, \`.find\`, \`.filter\`, \`.map\` or \`.flatMap\`, is not modeled: divide in a \`for…of\` over the elements, or outside the callback`,
      e.operatorToken,
    )
  const nonZero = z3.Not(r.term.eq(0))
  if (L.mode === "spec" && L.defined !== undefined) L.defined.push(z3.Implies(L.guard, nonZero))
  else {
    const at = locate(e.right)
    L.obligations.push({
      key: `division@${at}#here`,
      kind: "division",
      text: e.right.getText(),
      at,
      phase: "here",
      cond: L.guard,
      goal: nonZero,
      hints: L.hints.length,
    })
  }
  // JavaScript truncates: the quotient rounds toward 0, and the remainder takes the dividend's sign. Each is a fresh
  // integer, defined where the divisor is not 0n by what the two are together: the dividend is the divisor times the
  // quotient plus the remainder, which is smaller than the divisor and has the dividend's sign, or is 0n. That is one
  // pair, so the two are exact; and a law as plain as `a === b * (a / b) + a % b` is a fact, not a search.
  const abs = (t: Arith): Arith => z3.If(t.ge(0), t, t.neg())
  const q = z3.Int.const(L.u.fresh("div.q"))
  const m = z3.Int.const(L.u.fresh("div.r"))
  L.u.assume(z3.Implies(nonZero, z3.And(l.term.eq(r.term.mul(q).add(m)), abs(m).lt(abs(r.term)), z3.Or(m.eq(0), m.lt(0).eq(l.term.lt(0))))))
  return { ...l, term: op === K.SlashToken ? q : m }
}

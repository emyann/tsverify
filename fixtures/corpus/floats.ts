// Doubles: rounding, NaN, the infinities and the sign of zero. Arithmetic on `number` is read where it is exact, an
// obligation of each operation; where it may round, a law leaning on it is bounded, never judged. What compares alone
// is judged.
import { contract } from "../../src/contract.ts"
import type { Case } from "./cases.ts"

// fp-point1-plus-point2
export function add(a: number, b: number): number {
  return a + b
}
export const pointOnePlusPointTwo = contract(add, {
  requires: (a, b) => a === 0.1 && b === 0.2,
  ensures: { isPointThree: (_a, _b, out) => out === 0.3, isExact: (_a, _b, out) => out === 0.30000000000000004 },
})
// fp-add-assoc
export function add3(a: number, b: number, c: number): number {
  return a + b + c
}
export const additionAssociates = contract(add3, {
  requires: (a, b, c) => Number.isFinite(a) && Number.isFinite(b) && Number.isFinite(c),
  ensures: { assoc: (a, b, c, out) => out === a + (b + c) },
})
// fp-add-absorbs
export function succ(n: number): number {
  return n + 1
}
export const successorGrows = contract(succ, {
  requires: (n) => Number.isInteger(n) && n >= 0,
  ensures: { grows: (n, out) => out > n },
})
// fp-nan: `===` is IEEE equality, which NaN fails.
export function same(x: number): boolean {
  return x === x
}
export const selfEqual = contract(same, {
  ensures: { always: (_x, out) => out, unlessNaN: (x, out) => out === !Number.isNaN(x) },
})
export function trichotomy(a: number, b: number): boolean {
  return a < b || a > b || a === b
}
export const ordered = contract(trichotomy, { ensures: { always: (_a, _b, out) => out } })
export function max2(a: number, b: number): number {
  return Math.max(a, b)
}
export const maxOfTwo = contract(max2, { ensures: { upper: (a, b, out) => out >= a && out >= b, picks: (a, b, out) => out === a || out === b } })
// fp-signed-zero: `0 === -0`, but they are two values.
export function strictEq(x: number, y: number): boolean {
  return x === y
}
export const equalIsSameValue = contract(strictEq, { ensures: { sameAsIs: (x, y, out) => out === Object.is(x, y) } })
export function recipEq(x: number, y: number): boolean {
  return 1 / x === 1 / y
}
export const reciprocalsOfEquals = contract(recipEq, { ensures: { congruent: (x, y, out) => x !== y || out } })
// fp-min-signed-zero
export function min2(a: number, b: number): number {
  return Math.min(a, b)
}
export const minOfZeros = contract(min2, {
  ensures: {
    negZeroWins: (a, b, out) => !(a === 0 && b === 0 && (Object.is(a, -0) || Object.is(b, -0))) || Object.is(out, -0),
    isPlusZero: (a, b, out) => !(a === 0 && b === 0) || Object.is(out, 0),
  },
})
// fp-nan-producing
export function timesZero(x: number): number {
  return x * 0
}
export const timesZeroIsZero = contract(timesZero, { ensures: { zero: (_x, out) => out === 0 } })
// fp-sub-zero-iff-equal
export function diffIsZero(x: number, y: number): boolean {
  return x - y === 0
}
export const differenceZeroIffEqual = contract(diffIsZero, {
  requires: (x, y) => Number.isFinite(x) && Number.isFinite(y),
  ensures: { iffEqual: (x, y, out) => out === (x === y) },
})
// zg-kinematics
export function displacement(vi: number, a: number, t: number): number {
  return vi * t + (a * t * t) / 2
}
export const kinematics = contract(displacement, {
  requires: (vi, a, t) => vi === 0 && a === 6 && t === 4.1,
  ensures: { exact: (_vi, _a, _t, out) => out === 50.43, asDoubles: (_vi, _a, _t, out) => out === 50.42999999999999 },
})
// zg-div-by-zero-real
export function divZero(a: number): number {
  return a / 0
}
export const divisionByZero = contract(divZero, { ensures: { neverTen: (_a, out) => out !== 10 } })
// zg-nonlinear-unsat
export function sys(x: number, y: number, z: number): boolean {
  return x * x === x + 2 && x * y === x && (y - 1) * z === 1
}
export const nonlinearSystem = contract(sys, { ensures: { noSolution: (_x, _y, _z, out) => !out } })

const DOUBLES = [0, -0, 1, -1, 0.1, 0.2, 0.5, 2 ** 53, Number.MAX_VALUE, Infinity, -Infinity, NaN]
const pairs = DOUBLES.flatMap((a) => DOUBLES.map((b) => [a, b]))
export const cases: Readonly<Record<string, Case>> = {
  pointOnePlusPointTwo: {
    source: "https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html",
    laws: { isPointThree: ["invalid", "bounded"], isExact: ["valid", "bounded"] },
    samples: [[0.1, 0.2]],
    witnesses: { isPointThree: [0.1, 0.2] },
  },
  additionAssociates: {
    source: "https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html",
    laws: { assoc: ["invalid", "unknown"] },
    samples: [],
    witnesses: { assoc: [0.1, 0.2, 0.3] },
  },
  successorGrows: {
    source: "https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html",
    laws: { grows: ["invalid", "bounded"] },
    samples: [],
    witnesses: { grows: [2 ** 53] },
  },
  selfEqual: {
    source: "https://smt-lib.org/theories-FloatingPoint.shtml",
    laws: { always: "invalid", unlessNaN: "valid" },
    samples: DOUBLES.map((x) => [x]),
    witnesses: { always: [NaN] },
  },
  ordered: {
    source: "https://smt-lib.org/theories-FloatingPoint.shtml",
    laws: { always: "invalid" },
    samples: [],
    witnesses: { always: [NaN, 0] },
  },
  maxOfTwo: {
    source: "https://smt-lib.org/theories-FloatingPoint.shtml",
    laws: { upper: ["invalid", "refused"], picks: ["invalid", "refused"] },
    samples: [],
    witnesses: { upper: [NaN, 0], picks: [NaN, 0] },
  },
  equalIsSameValue: {
    source: "https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is",
    laws: { sameAsIs: ["invalid", "refused"] },
    samples: [],
    witnesses: { sameAsIs: [0, -0] },
  },
  reciprocalsOfEquals: {
    source: "https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html",
    laws: { congruent: ["invalid", "unknown"] },
    samples: [],
    witnesses: { congruent: [0, -0] },
  },
  minOfZeros: {
    source: "https://smt-lib.org/theories-FloatingPoint.shtml",
    laws: { negZeroWins: ["valid", "refused"], isPlusZero: ["invalid", "refused"] },
    samples: pairs,
    witnesses: { isPlusZero: [0, -0] },
  },
  timesZeroIsZero: {
    source: "https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html",
    laws: { zero: ["invalid", "bounded"] },
    samples: [],
    witnesses: { zero: [Infinity] },
  },
  differenceZeroIffEqual: {
    source: "https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html",
    laws: { iffEqual: ["valid", "bounded"] },
    samples: pairs,
  },
  kinematics: {
    source: "https://microsoft.github.io/z3guide/docs/theories/Arithmetic",
    laws: { exact: ["invalid", "bounded"], asDoubles: ["valid", "bounded"] },
    samples: [[0, 6, 4.1]],
    witnesses: { exact: [0, 6, 4.1] },
  },
  divisionByZero: {
    source: "https://microsoft.github.io/z3guide/docs/theories/Arithmetic",
    laws: { neverTen: ["valid", "bounded"] },
    samples: DOUBLES.map((x) => [x]),
  },
  nonlinearSystem: {
    source: "https://microsoft.github.io/z3guide/docs/theories/Arithmetic",
    laws: { noSolution: ["invalid", "bounded"] },
    samples: [],
    witnesses: { noSolution: [Infinity, 2, 1] },
  },
}

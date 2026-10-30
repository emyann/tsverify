// 32-bit (and 8- and 4-bit) arithmetic: as JavaScript writes it, with `| 0`, `>>>` and `^` on `number`, and in `bigint`
// with C's wrap-around written out with `%`.
import { contract, invariant } from "../../src/contract.ts"
import type { Case } from "./cases.ts"

// --- As JavaScript writes it, on `number`.
// bv-abs
export function absAddXor(v: number): number {
  const m = v >> 31
  return (v + m) ^ m
}
export const branchlessAbs = contract(absAddXor, {
  requires: (v) => v === (v | 0),
  ensures: { isAbs: (v, out) => out === (v > 0 ? v : -v) },
})
// bv-pow2
export function isPow2(x: number): boolean {
  return x !== 0 && (x & (x - 1)) === 0
}
export const powerOfTwoIsPositive = contract(isPow2, {
  requires: (x) => x === (x | 0),
  ensures: { positive: (x, out) => !out || x > 0 },
})
// js-ushr
export function toU32(x: number): number {
  return x >>> 0
}
export const unsignedShift = contract(toU32, {
  ensures: { inRange: (_x, out) => out >= 0 && out <= 4294967295, sameAsI32: (x, out) => out === (x | 0) },
})
// vf-bloch-midpoint, as JavaScript writes it.
export function midpoint(lo: number, hi: number): number {
  return (lo + hi) >>> 1
}
export const midpointInRange = contract(midpoint, {
  requires: (lo, hi) => Number.isInteger(lo) && Number.isInteger(hi) && 0 <= lo && lo <= hi && hi <= 2 ** 32 - 2,
  ensures: { between: (lo, hi, out) => lo <= out && out <= hi },
})

// --- In `bigint`, C's wrap-around written out.
const I32 = 4294967296n
/** `x` wrapped to a signed 32-bit integer, as C and Java do. */
const i32 = (x: bigint): bigint => ((((x + 2147483648n) % I32) + I32) % I32) - 2147483648n
const isI32 = (x: bigint): boolean => -2147483648n <= x && x <= 2147483647n

// ssbe-add-overflow: `a + b` wraps, and compiler-rt's test tells exactly when.
export function add32(a: bigint, b: bigint) {
  const s = i32(a + b)
  return { s, overflow: b >= 0n ? s < a : s > a }
}
export const signedAddition = contract(add32, {
  requires: (a, b) => isI32(a) && isI32(b),
  ensures: { noWrap: (a, b, out) => out.s === a + b, detects: (a, b, out) => out.overflow === (out.s !== a + b) },
})
// ssbe-mul1024-overflow: `a * 1024` before `malloc`.
export function times1024(a: bigint): bigint {
  return i32(a * 1024n)
}
export const mul1024Unchecked = contract(times1024, { requires: (a) => isI32(a), ensures: { noOverflow: (a, out) => out === a * 1024n } })
export const mul1024BelowHundred = contract(times1024, {
  requires: (a) => isI32(a) && a < 100n,
  ensures: { noOverflow: (a, out) => out === a * 1024n },
})
export const mul1024PositiveBelowHundred = contract(times1024, {
  requires: (a) => isI32(a) && a > 0n && a < 100n,
  ensures: { noOverflow: (a, out) => out === a * 1024n },
})
// vf-bloch-midpoint: Java's `(low + high) / 2`, and its fix.
export function midJava(lo: bigint, hi: bigint): bigint {
  return i32(lo + hi) / 2n
}
export const javaMidpoint = contract(midJava, {
  requires: (lo, hi) => 0n <= lo && lo <= hi && hi <= 2147483647n,
  ensures: { between: (lo, hi, out) => lo <= out && out <= hi },
})
export function midFixed(lo: bigint, hi: bigint): bigint {
  return i32(lo + i32(hi - lo) / 2n)
}
export const fixedMidpoint = contract(midFixed, {
  requires: (lo, hi) => 0n <= lo && lo <= hi && hi <= 2147483647n,
  ensures: { between: (lo, hi, out) => lo <= out && out <= hi },
})
// vf-verus-octuple: on `i8`, right only for -16 <= x < 16.
const I8 = 256n
const i8 = (x: bigint): bigint => ((((x + 128n) % I8) + I8) % I8) - 128n
export function octuple(x: bigint): bigint {
  const x2 = i8(x + x)
  const x4 = i8(x2 + x2)
  return i8(x4 + x4)
}
export const octupleInRange = contract(octuple, { requires: (x) => -16n <= x && x < 16n, ensures: { eightTimes: (x, out) => out === 8n * x } })
export const octupleWider = contract(octuple, { requires: (x) => -64n <= x && x < 64n, ensures: { eightTimes: (x, out) => out === 8n * x } })
// pz3-bmc-counter: a 4-bit counter stepping by 3 reaches 10; unbounded, it never does.
export function counter4(n: bigint): bigint {
  let x = 0n
  for (let i = 0n; i < n; i = i + 1n) x = (x + 3n) % 16n
  return x
}
export const fourBitCounter = contract(counter4, { requires: (n) => n >= 0n, ensures: { never10: (_n, out) => out !== 10n } })
export function counter(n: bigint): bigint {
  let x = 0n
  for (let i = 0n; i < n; i = i + 1n) {
    invariant(() => x % 3n === 0n)
    x = x + 3n
  }
  return x
}
export const unboundedCounter = contract(counter, { requires: (n) => n >= 0n, ensures: { never10: (_n, out) => out !== 10n } })
// ssbe-swap: the add/sub swap, valid on integers.
export function swapAddSub(x: bigint, y: bigint) {
  const a = x + y
  const b = a - y
  return { x: a - b, y: b }
}
export const addSubSwap = contract(swapAddSub, { ensures: { swapped: (x, y, out) => out.x === y && out.y === x } })
// bv-div-by-constant: dividing by 10 as a multiply by 0xCCCCCCCCCCCCCCCD and a shift by 67, on 64-bit inputs.
export function div10(x: bigint): bigint {
  return (x * 0xcccccccccccccccdn) / 147573952589676412928n
}
export const divideByTen = contract(div10, { requires: (x) => 0n <= x && x < 18446744073709551616n, ensures: { isTenth: (x, out) => out === x / 10n } })
export const divideByTenAnySize = contract(div10, { requires: (x) => 0n <= x, ensures: { isTenth: (x, out) => out === x / 10n } })
// ssbe-school-equation over 32-bit words: four solutions where the integers have one.
export function school32(c: bigint, s: bigint, t: bigint): boolean {
  return i32(c + c) === 10n && i32(i32(c * s) + s) === 12n && i32(i32(c * s) - i32(t * c)) === c
}
// The circle fixed at 5, which the first equation allows (with 5 + 2^31): the products are then linear. Left free, the
// search takes 16 s alone, and times out under a suite's load.
export const schoolEquation32 = contract(school32, {
  requires: (c, s, t) => c === 5n && isI32(s) && isI32(t),
  ensures: { onlyFiveTwoOne: (c, s, t, out) => !out || (c === 5n && s === 2n && t === 1n) },
})

const BIG32 = [-2147483648n, -1n, 0n, 1n, 99n, 2097152n, 1073741824n, 2147483647n]
export const cases: Readonly<Record<string, Case>> = {
  branchlessAbs: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-bit-vectors",
    laws: { isAbs: "invalid" },
    samples: [],
    witnesses: { isAbs: [-2147483648] },
  },
  powerOfTwoIsPositive: {
    source: "https://microsoft.github.io/z3guide/docs/theories/Bitvectors",
    laws: { positive: "invalid" },
    samples: [],
    witnesses: { positive: [-2147483648] },
  },
  unsignedShift: {
    source: "https://tc39.es/ecma262/#sec-unsigned-right-shift-operator",
    laws: { inRange: "valid", sameAsI32: "invalid" },
    samples: [[0], [-1], [1.5], [NaN], [Infinity], [2 ** 32], [-(2 ** 31)]],
    witnesses: { sameAsI32: [-1] },
  },
  midpointInRange: {
    source: "https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/",
    laws: { between: "invalid" },
    samples: [],
    witnesses: { between: [2 ** 31, 2 ** 31] },
  },
  signedAddition: {
    source: "https://smt.st/current_tree/",
    laws: { noWrap: "invalid", detects: "valid" },
    samples: BIG32.flatMap((a) => BIG32.map((b) => [a, b])),
    witnesses: { noWrap: [1n, 2147483647n] },
  },
  mul1024Unchecked: {
    source: "https://smt.st/current_tree/",
    laws: { noOverflow: "invalid" },
    samples: [],
    witnesses: { noOverflow: [2097152n] },
  },
  mul1024BelowHundred: {
    source: "https://smt.st/current_tree/",
    laws: { noOverflow: "invalid" },
    samples: [],
    witnesses: { noOverflow: [-2147483648n] },
  },
  mul1024PositiveBelowHundred: {
    source: "https://smt.st/current_tree/",
    laws: { noOverflow: "valid" },
    samples: [[1n], [50n], [99n]],
  },
  javaMidpoint: {
    source: "https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/",
    laws: { between: "invalid" },
    samples: [],
    witnesses: { between: [1073741824n, 1073741824n] },
  },
  fixedMidpoint: {
    source: "https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/",
    laws: { between: "valid" },
    samples: [[0n, 0n], [0n, 1n], [1073741824n, 1073741824n], [0n, 2147483647n], [2147483646n, 2147483647n]],
  },
  octupleInRange: {
    source: "https://verus-lang.github.io/verus/guide/integers.html",
    laws: { eightTimes: "valid" },
    samples: [[-16n], [-1n], [0n], [15n]],
  },
  octupleWider: {
    source: "https://verus-lang.github.io/verus/guide/integers.html",
    laws: { eightTimes: "invalid" },
    samples: [],
    witnesses: { eightTimes: [32n] },
  },
  fourBitCounter: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-bounded-model-checking",
    laws: { never10: ["invalid", "bounded"] },
    samples: [],
    witnesses: { never10: [14n] },
  },
  unboundedCounter: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-bounded-model-checking",
    laws: { never10: "valid" },
    samples: [[0n], [1n], [3n], [4n], [14n]],
  },
  addSubSwap: {
    source: "https://smt.st/current_tree/",
    laws: { swapped: "valid" },
    samples: BIG32.flatMap((a) => BIG32.map((b) => [a, b])),
  },
  divideByTen: {
    source: "https://smt.st/current_tree/",
    laws: { isTenth: "valid" },
    samples: [[0n], [9n], [10n], [99n], [18446744073709551615n]],
  },
  divideByTenAnySize: {
    source: "https://smt.st/current_tree/",
    laws: { isTenth: "invalid" },
    samples: [],
    witnesses: { isTenth: [73786976294838206469n] },
  },
  schoolEquation32: {
    source: "https://smt.st/current_tree/equations/CBMC_eq/main_EN.tex",
    laws: { onlyFiveTwoOne: "invalid" },
    samples: [],
    witnesses: { onlyFiveTwoOne: [5n, -2147483646n, -2147483647n] },
  },
}

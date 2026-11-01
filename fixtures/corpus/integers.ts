// Integers (`bigint`): programs and classic puzzles. A puzzle is a law that says no solution exists, whose
// counterexample is the solution, and one that says the known solution is the only one.
import { contract, invariant } from "../../src/contract.ts"
import { type Case, grid, INTS } from "./cases.ts"

const abs = (x: bigint): bigint => (x < 0n ? -x : x)
/** The Euclidean remainder, SMT-LIB's `mod`: never negative. */
export const emod = (a: bigint, b: bigint): bigint => (a % b + abs(b)) % abs(b)

// zg-div-mod-rem: JavaScript's `/` and `%` truncate; SMT-LIB's `div` and `mod` are Euclidean, Z3's `rem` signs by the divisor.
export function divmod(a: bigint, b: bigint) {
  return { q: a / b, r: a % b }
}
export const divisionAsJavaScript = contract(divmod, {
  requires: ({ input: [, b] }) => b !== 0n,
  ensures: {
    truncates: ({ input: [a, b], output }) => a === b * output.q + output.r && abs(output.r) < abs(b) && (output.r === 0n || output.r < 0n === a < 0n),
    euclid: ({ input: [a, b], output }) => a === b * output.q + output.r && 0n <= output.r && output.r < abs(b),
    remLikeZ3: ({ input: [a, b], output }) => output.r === (b > 0n ? emod(a, b) : -emod(a, b)),
  },
})
export const euclideanRemainder = contract(emod, {
  requires: ({ input: [, b] }) => b !== 0n,
  ensures: { isEuclid: ({ input: [a, b], output }) => 0n <= output && output < abs(b) && (a - output) % b === 0n },
})

// vf-dafny-compute-fib: the iterative Fibonacci meets the recursive one, and fails at 0 without its guard.
export function fib(n: bigint): bigint {
  return n <= 0n ? 0n : n === 1n ? 1n : fib(n - 1n) + fib(n - 2n)
}
export function computeFib(n: bigint): bigint {
  if (n === 0n) return 0n
  let i = 1n
  let a = 0n
  let b = 1n
  while (i < n) {
    const next = a + b
    a = b
    b = next
    i = i + 1n
  }
  return b
}
export const fibMeetsItsDefinition = contract(computeFib, {
  requires: ({ input: [n] }) => n >= 0n,
  ensures: { isFib: ({ input: [n], output }) => output === fib(n) },
})
export function computeFibUnguarded(n: bigint): bigint {
  let i = 1n
  let a = 0n
  let b = 1n
  while (i < n) {
    const next = a + b
    a = b
    b = next
    i = i + 1n
  }
  return b
}
export const fibUnguarded = contract(computeFibUnguarded, {
  requires: ({ input: [n] }) => n >= 0n,
  ensures: { zeroAtZero: ({ input: [n], output }) => n !== 0n || output === 0n },
})

// pz3-mc91: McCarthy's 91 function, as a loop, meets its closed form.
export function mc91(n: bigint): bigint {
  let m = n
  let c = 1n
  while (c !== 0n) {
    // What is left to compute: the closed form applied `c` times to `m`, which is `m - 10c`, or 91 once that is below.
    invariant(() => c >= 0n && (c === 0n ? m : m - 10n * c > 91n ? m - 10n * c : 91n) === (n <= 101n ? 91n : n - 10n))
    if (m > 100n) {
      m = m - 10n
      c = c - 1n
    } else {
      m = m + 11n
      c = c + 1n
    }
  }
  return m
}
export const mc91ClosedForm = contract(mc91, {
  ensures: { closedForm: ({ input: [n], output }) => output === (n <= 101n ? 91n : n - 10n) },
})

// zg-dog-cat-mouse: 100 animals for 100 dollars, in cents.
export function buys(dog: bigint, cat: bigint, mouse: bigint): boolean {
  return dog >= 1n && cat >= 1n && mouse >= 1n && dog + cat + mouse === 100n && 1500n * dog + 100n * cat + 25n * mouse === 10000n
}
export const dogCatMouse = contract(buys, {
  ensures: {
    noSolution: ({ output }) => !output,
    unique: ({ input: [d, c, m], output }) => !output || (d === 3n && c === 41n && m === 56n),
  },
})

// ssbe-send-more-money: SEND+MORE=MONEY; without M ≠ 0 there are 24 more solutions.
const digit = (x: bigint): boolean => x >= 0n && x <= 9n
export function sendMoreMoney(s: bigint, e: bigint, n: bigint, d: bigint, m: bigint, o: bigint, r: bigint, y: bigint): boolean {
  const xs = [s, e, n, d, m, o, r, y]
  return (
    xs.every((x) => digit(x)) &&
    xs.every((x) => xs.filter((z) => z === x).length === 1) &&
    1000n * s + 100n * e + 10n * n + d + (1000n * m + 100n * o + 10n * r + e) === 10000n * m + 1000n * o + 100n * n + 10n * e + y
  )
}
const classic = (s: bigint, e: bigint, n: bigint, d: bigint, m: bigint, o: bigint, r: bigint, y: bigint) =>
  s === 9n && e === 5n && n === 6n && d === 7n && m === 1n && o === 0n && r === 8n && y === 2n
export const sendMoreMoneyAnyM = contract(sendMoreMoney, {
  ensures: { onlyTheClassic: ({ input: [s, e, n, d, m, o, r, y], output }) => !output || classic(s, e, n, d, m, o, r, y) },
})
export const sendMoreMoneyMNotZero = contract(sendMoreMoney, {
  requires: ({ input: [, , , , m] }) => m !== 0n,
  ensures: {
    noSolution: ({ output }) => !output,
    onlyTheClassic: ({ input: [s, e, n, d, m, o, r, y], output }) => !output || classic(s, e, n, d, m, o, r, y),
  },
})

// pz3-stamps: with 5- and 7-cent stamps every amount from 24 cents on can be paid, and 23 cannot.
export function stamps(x: bigint, y: bigint): bigint {
  return 5n * x + 7n * y
}
export const stampAmounts = contract(stamps, {
  requires: ({ input: [x, y] }) => x >= 0n && y >= 0n,
  ensures: { never23: ({ output }) => output !== 23n, never22: ({ output }) => output !== 22n },
})
/** How many of each stamp pay `n`: as many 7s as `n`'s remainder by 5 needs, then 5s. */
export function changeFor(n: bigint) {
  const r = n % 5n
  const sevens = r === 0n ? 0n : r === 1n ? 3n : r === 2n ? 1n : r === 3n ? 4n : 2n
  return { fives: (n - 7n * sevens) / 5n, sevens }
}
export const changeFrom24 = contract(changeFor, {
  requires: ({ input: [n] }) => n >= 24n,
  ensures: { pays: ({ input: [n], output }) => 5n * output.fives + 7n * output.sevens === n && output.fives >= 0n && output.sevens >= 0n },
})
export const changeFrom23 = contract(changeFor, {
  requires: ({ input: [n] }) => n >= 23n,
  ensures: { pays: ({ input: [n], output }) => 5n * output.fives + 7n * output.sevens === n && output.fives >= 0n && output.sevens >= 0n },
})

// ssbe-xkcd287: appetizers for $15.05, in cents: two orders.
export function total(a: bigint, b: bigint, c: bigint, d: bigint, e: bigint, f: bigint): bigint {
  return 215n * a + 275n * b + 335n * c + 355n * d + 420n * e + 580n * f
}
export const xkcd287 = contract(total, {
  requires: ({ input: [a, b, c, d, e, f] }) => a >= 0n && b >= 0n && c >= 0n && d >= 0n && e >= 0n && f >= 0n,
  ensures: {
    twoOrders: ({ input: [a, b, c, d, e, f], output }) =>
      output !== 1505n ||
      (a === 7n && b === 0n && c === 0n && d === 0n && e === 0n && f === 0n) ||
      (a === 1n && b === 0n && c === 0n && d === 2n && e === 0n && f === 1n),
    oneOrder: ({ input: [a, b, c, d, e, f], output }) => output !== 1505n || (a === 1n && b === 0n && c === 0n && d === 2n && e === 0n && f === 1n),
  },
})

// ssbe-school-equation: one solution over the integers.
export function school(circle: bigint, square: bigint, triangle: bigint): boolean {
  return circle + circle === 10n && circle * square + square === 12n && circle * square - triangle * circle === circle
}
export const schoolEquation = contract(school, {
  ensures: { onlyFiveTwoOne: ({ input: [c, s, t], output }) => !output || (c === 5n && s === 2n && t === 1n) },
})

// zg-install-problem: a forced profile, and none once g is wanted too.
export function installable(a: boolean, b: boolean, c: boolean, d: boolean, e: boolean, f: boolean, g: boolean, z: boolean): boolean {
  return (!a || (b && c && z)) && (!b || d) && (!c || ((d || e) && (f || g))) && !(d && e) && !(d && g)
}
export const installProblem = contract(installable, {
  ensures: {
    forced: ({ input: [a, b, c, d, e, f, g, z], output }) => !(output && a && z) || (b && c && d && f && !e && !g),
    notWithG: ({ input: [a, , , , , , g, z], output }) => !(output && a && z && g),
    noProfile: ({ input: [a, , , , , , , z], output }) => !(output && a && z),
  },
})

const BOOLS = [true, false]
const DIGITS = [0n, 1n, 2n, 5n, 6n, 7n, 8n, 9n]
const SMALL = [0n, 1n, 2n, 3n, 7n]
export const cases: Readonly<Record<string, Case>> = {
  divisionAsJavaScript: {
    source: "https://microsoft.github.io/z3guide/docs/theories/Arithmetic#division",
    laws: { truncates: "valid", euclid: "invalid", remLikeZ3: "invalid" },
    samples: grid(INTS, INTS),
    witnesses: { euclid: [-10n, 4n], remLikeZ3: [10n, -4n] },
  },
  euclideanRemainder: {
    source: "https://smt-lib.org/theories-Ints.shtml",
    laws: { isEuclid: "valid" },
    samples: grid(INTS, INTS),
  },
  fibMeetsItsDefinition: {
    source: "https://dafny.org/latest/OnlineTutorial/guide",
    laws: { isFib: ["valid", "refused"] },
    samples: grid([0n, 1n, 2n, 3n, 10n, 20n]),
  },
  fibUnguarded: {
    source: "https://dafny.org/latest/OnlineTutorial/guide",
    laws: { zeroAtZero: "invalid" },
    samples: grid([0n, 1n, 2n, 3n, 10n]),
    witnesses: { zeroAtZero: [0n] },
  },
  mc91ClosedForm: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-horn-clause-solver",
    laws: { closedForm: "valid" },
    samples: grid([-50n, 0n, 89n, 90n, 91n, 100n, 101n, 102n, 111n, 299n]),
  },
  dogCatMouse: {
    source: "https://ericpony.github.io/z3py-tutorial/guide-examples.htm",
    laws: { noSolution: "invalid", unique: "valid" },
    samples: [[3n, 41n, 56n], [1n, 1n, 98n], [2n, 50n, 48n], [0n, 0n, 100n], ...grid(SMALL, SMALL, SMALL)],
    witnesses: { noSolution: [3n, 41n, 56n] },
  },
  sendMoreMoneyAnyM: {
    source: "https://smt.st/current_tree/puzzles/alphametics/main_EN.tex",
    laws: { onlyTheClassic: "invalid" },
    samples: [[9n, 5n, 6n, 7n, 1n, 0n, 8n, 2n], [2n, 8n, 1n, 7n, 0n, 3n, 6n, 5n]],
    witnesses: { onlyTheClassic: [2n, 8n, 1n, 7n, 0n, 3n, 6n, 5n] },
  },
  sendMoreMoneyMNotZero: {
    source: "https://smt.st/current_tree/puzzles/alphametics/main_EN.tex",
    laws: { noSolution: "invalid", onlyTheClassic: "valid" },
    samples: [[9n, 5n, 6n, 7n, 1n, 0n, 8n, 2n], [9n, 5n, 6n, 7n, 1n, 0n, 8n, 3n], [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n]],
    witnesses: { noSolution: [9n, 5n, 6n, 7n, 1n, 0n, 8n, 2n] },
  },
  stampAmounts: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-qsat",
    laws: { never23: "valid", never22: "invalid" },
    samples: grid([0n, 1n, 2n, 3n, 4n, 5n], [0n, 1n, 2n, 3n, 4n]),
    witnesses: { never22: [3n, 1n] },
  },
  changeFrom24: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-qsat",
    laws: { pays: "valid" },
    samples: grid([24n, 25n, 26n, 27n, 28n, 29n, 100n, 1001n]),
  },
  changeFrom23: {
    source: "https://z3prover.github.io/papers/programmingz3.html#sec-qsat",
    laws: { pays: "invalid" },
    samples: grid([23n, 24n, 25n]),
    witnesses: { pays: [23n] },
  },
  xkcd287: {
    source: "https://smt.st/current_tree/equations/xkcd287/main_EN.tex",
    laws: { twoOrders: "valid", oneOrder: "invalid" },
    samples: [[7n, 0n, 0n, 0n, 0n, 0n], [1n, 0n, 0n, 2n, 0n, 1n], [0n, 1n, 1n, 1n, 1n, 1n], [1n, 1n, 1n, 1n, 1n, 1n]],
    witnesses: { oneOrder: [7n, 0n, 0n, 0n, 0n, 0n] },
  },
  schoolEquation: {
    source: "https://smt.st/current_tree/basics/SMT/eq2.tex",
    laws: { onlyFiveTwoOne: "valid" },
    samples: [[5n, 2n, 1n], [5n, -2147483646n, -2147483647n], ...grid(DIGITS, DIGITS.slice(0, 4), DIGITS.slice(0, 4))],
  },
  installProblem: {
    source: "https://ericpony.github.io/z3py-tutorial/guide-examples.htm",
    laws: { forced: "valid", notWithG: "valid", noProfile: "invalid" },
    samples: grid(BOOLS, BOOLS, BOOLS, BOOLS, BOOLS, BOOLS, BOOLS, BOOLS),
    witnesses: { noProfile: [true, true, true, true, false, true, false, true] },
  },
}

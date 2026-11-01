// Declarations and the contracts that lean on them: each rule of what the
// verifier takes on trust, one case each. `test/trust.test.ts` asks each.
import { clamp, compact, uniq } from "lodash-es"
import "../packs/lodash.ts"
import { assume, contract } from "../src/contract.ts"

const always = () => true

/** A score the verifier does not read (it loops): declared pure, which is checked, and never negative, which is not. */
export function score(word: string): number {
  let n = 0
  for (const c of word) if (c === "a") n++
  return n
}
export const scoreIsPure = assume(score, {
  pure: true,
  ensures: { nonNegative: { description: "A score is never negative", condition: ({ output }) => output >= 0 } },
})

/** The law of `score` holds of every element inside a quantifier: one call per element, not one for them all. */
export const everyScoreNonNegative = contract((words: ReadonlyArray<string>) => words.every((w) => score(w) >= 0), {
  ensures: { always: ({ output }) => output },
})
export const everyScorePositive = contract((words: ReadonlyArray<string>) => words.every((w) => score(w) > 0), {
  ensures: { always: ({ output }) => output },
})

/** A function the verifier cannot read (it takes square roots, which round) and nobody declared. */
export function total(xs: ReadonlyArray<number>): number {
  let t = 0
  for (const x of xs) t += Math.sqrt(x)
  return t
}
export const undeclared = contract((xs: ReadonlyArray<number>) => total(xs), { ensures: { always } })

/** Declared pure, and it changes its argument. */
export function stamp(log: string[]): number {
  log.push("stamped")
  return log.length
}
export const stampIsPure = assume(stamp, { pure: true })
export const stamped = contract((log: string[]) => stamp(log), { ensures: { always } })

/** Declared not pure: a fresh result per call, and no law may call it. */
export function nowMs(): number {
  return Date.now()
}
export const nowIsNotPure = assume(nowMs, { pure: false, ensures: { aNumber: ({ output }) => output === output } })
export const twoReadsAgree = contract(() => nowMs() === nowMs(), { ensures: { always: ({ output }) => output } })
export const lawReadsTheClockThroughADeclaration = contract((x: string) => x, { ensures: { late: () => nowMs() > 0 } })
export const lawReadsTheClock = contract((x: string) => x, { ensures: { late: () => Date.now() > 0 } })

/** A law that runs a computation. */
export const fetchOne = async (x: string): Promise<string> => x
export const lawRunsAComputation = contract((x: string) => x, { ensures: { runs: ({ input: [x] }) => fetchOne(x) !== undefined } })

/** The program may read the clock where a law reads the result: a binding keeps the mode of the code that wrote it. */
export const stampedNow = contract((x: string) => ({ x, at: Date.now() }), { ensures: { keeps: ({ input: [x], output }) => output.x === x && output.at === output.at } })

/** Pure where the function it is given is: it applies it. */
export function applied(f: (x: number) => number, x: number): number {
  return f(x)
}
export const appliedIsPure = assume(applied, { pure: true })
let ticks = 0
const tick = (x: number): number => {
  ticks++
  return x + ticks
}
/** Given a function that counts its calls, `applied` is not pure. */
export const appliedToATick = contract((x: number) => applied(tick, x), { ensures: { always } })
/** Given one that changes nothing, written twice alike, it is one call: one result. */
export const appliedTwice = contract((x: number) => Object.is(applied((y) => y + 1, x), applied((y) => y + 1, x)), {
  ensures: { same: ({ output }) => output },
})

/** `uniq` is declared on strings; on numbers no declaration covers it. */
export const uncovered = contract((xs: ReadonlyArray<number>) => uniq(xs).length, { ensures: { always } })

/** `clamp(n, upper)`, lodash's two-argument form, which the pack's three-argument laws do not describe. */
export const otherForm = contract((n: number) => clamp(n, 10), { ensures: { always } })

/** `compact` is lodash's, and nothing declares it. */
export const undeclaredPackage = contract((xs: ReadonlyArray<string>) => compact(xs).length, { ensures: { always } })

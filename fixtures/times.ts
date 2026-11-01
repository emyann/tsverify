// Time and rounding: a `Date` the code is given, read through `getTime()`; a time `Date.parse` reads off a string,
// which the verifier takes as some function of it; `Math.round`; a quotient of two whole numbers rounded, which is
// exact; and `Number.isInteger` of a value that may be missing. `test/times.test.ts` asks each.
import { contract } from "../src/contract.ts"

/** Whole seconds from `since` to `now`, rounded: what a stopwatch shows. */
export function secondsSince(since: string, now: Date): number {
  return Math.round((now.getTime() - Date.parse(since)) / 1000)
}

/** A moment as a log stamps one: whole milliseconds, after 1970 and before 2^52 of them. */
const stamped = (ms: number): boolean => Number.isInteger(ms) && ms >= 0 && ms <= 2 ** 52

export const secondsShown = contract(secondsSince, {
  requires: ({ input: [since, now] }) => stamped(Date.parse(since)) && stamped(now.getTime()),
  ensures: {
    whole: ({ output }) => Number.isInteger(output),
    noneAtOnce: ({ input: [since, now], output }) => now.getTime() !== Date.parse(since) || output === 0,
    aSecondIsOne: ({ input: [since, now], output }) => now.getTime() - Date.parse(since) !== 1000 || output === 1,
    halfRoundsUp: ({ input: [since, now], output }) => now.getTime() - Date.parse(since) !== 1500 || output === 2,
    signed: ({ input: [since, now], output }) => now.getTime() >= Date.parse(since) || output <= 0,
  },
})

/** Whether a run is past its deadline, which is optional, in whole seconds. */
export function overdue(ranForMs: number, deadlineSeconds: number | undefined): boolean {
  return deadlineSeconds !== undefined && ranForMs > deadlineSeconds * 1000
}

export const overdueOnlyPastIt = contract(overdue, {
  requires: ({ input: [ranForMs, deadlineSeconds] }) =>
    stamped(ranForMs) && (deadlineSeconds === undefined || (Number.isInteger(deadlineSeconds) && deadlineSeconds >= 0 && deadlineSeconds <= 2 ** 31)),
  ensures: {
    neverWithout: ({ input: [, deadline], output }) => deadline !== undefined || !output,
    pastIt: ({ input: [ran, deadline], output }) => deadline === undefined || output === ran > deadline * 1000,
  },
})

/** The middle of a range, rounded down: `Math.floor` of a quotient of whole numbers. */
export function middle(lo: number, hi: number): number {
  return Math.floor((lo + hi) / 2)
}

export const middleBetween = contract(middle, {
  requires: ({ input: [lo, hi] }) => Number.isInteger(lo) && Number.isInteger(hi) && lo >= 0 && lo <= hi && hi <= 2 ** 40,
  ensures: {
    notBelow: ({ input: [lo], output }) => output >= lo,
    notAbove: ({ input: [, hi], output }) => output <= hi,
    whole: ({ output }) => Number.isInteger(output),
  },
})

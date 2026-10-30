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
  requires: (since, now) => stamped(Date.parse(since)) && stamped(now.getTime()),
  ensures: {
    whole: (_since, _now, out) => Number.isInteger(out),
    noneAtOnce: (since, now, out) => now.getTime() !== Date.parse(since) || out === 0,
    aSecondIsOne: (since, now, out) => now.getTime() - Date.parse(since) !== 1000 || out === 1,
    halfRoundsUp: (since, now, out) => now.getTime() - Date.parse(since) !== 1500 || out === 2,
    signed: (since, now, out) => now.getTime() >= Date.parse(since) || out <= 0,
  },
})

/** Whether a run is past its deadline, which is optional, in whole seconds. */
export function overdue(ranForMs: number, deadlineSeconds: number | undefined): boolean {
  return deadlineSeconds !== undefined && ranForMs > deadlineSeconds * 1000
}

export const overdueOnlyPastIt = contract(overdue, {
  requires: (ranForMs, deadlineSeconds) =>
    stamped(ranForMs) && (deadlineSeconds === undefined || (Number.isInteger(deadlineSeconds) && deadlineSeconds >= 0 && deadlineSeconds <= 2 ** 31)),
  ensures: {
    neverWithout: (_ran, deadline, out) => deadline !== undefined || !out,
    pastIt: (ran, deadline, out) => deadline === undefined || out === ran > deadline * 1000,
  },
})

/** The middle of a range, rounded down: `Math.floor` of a quotient of whole numbers. */
export function middle(lo: number, hi: number): number {
  return Math.floor((lo + hi) / 2)
}

export const middleBetween = contract(middle, {
  requires: (lo, hi) => Number.isInteger(lo) && Number.isInteger(hi) && lo >= 0 && lo <= hi && hi <= 2 ** 40,
  ensures: {
    notBelow: (lo, _hi, out) => out >= lo,
    notAbove: (_lo, hi, out) => out <= hi,
    whole: (_lo, _hi, out) => Number.isInteger(out),
  },
})

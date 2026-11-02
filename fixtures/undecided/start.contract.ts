// Laws that leave a result open between two kinds at some input: code could answer either, and every law proved says
// nothing of which. The verdict names the part left open and an input where both results keep every law.
import { contract } from "@emyann/tsverify"

export type Refusal = { readonly reason: "not-filed" | "out-of-order"; readonly message: string }

export function start(filed: boolean, attempt: bigint, started: bigint): Refusal | undefined {
  if (!filed) return { reason: "not-filed", message: "file the task first" }
  if (attempt !== started + 1n) return { reason: "out-of-order", message: `start attempt ${started + 1n}` }
  return undefined
}

/** Laws that say when a start is refused, and never when one is taken: a refusal of every start keeps them too. */
export const refusesOnly = contract(start, {
  ensures: {
    unfiledIsRefused: ({ input: [filed], output }) => filed || output?.reason === "not-filed",
    outOfOrderIsRefused: ({ input: [filed, attempt, started], output }) => !(filed && attempt !== started + 1n) || output?.reason === "out-of-order",
  },
})

/** The same laws, and the one that says when a start is taken: every input decided. */
export const bothSides = contract(start, {
  ensures: {
    unfiledIsRefused: ({ input: [filed], output }) => filed || output?.reason === "not-filed",
    outOfOrderIsRefused: ({ input: [filed, attempt, started], output }) => !(filed && attempt !== started + 1n) || output?.reason === "out-of-order",
    inOrderIsTaken: ({ input: [filed, attempt, started], output }) => !(filed && attempt === started + 1n) || output === undefined,
  },
})

/** Laws that decide whether a start is taken, and leave which reason a refusal gives open: a choice named as the code's. */
export const reasonLeftOpen = contract(start, {
  ensures: {
    refusedUnlessInOrder: ({ input: [filed, attempt, started], output }) => (output === undefined) === (filed && attempt === started + 1n),
  },
  open: ["output.reason"],
})

/** The same law, the choice not named: the reason is undecided. */
export const reasonUnsaid = contract(start, {
  ensures: {
    refusedUnlessInOrder: ({ input: [filed, attempt, started], output }) => (output === undefined) === (filed && attempt === started + 1n),
  },
})

/** Laws of what is never done, the result left to the code on purpose. */
export const safetyOnly = contract(start, {
  ensures: {
    unfiledIsRefused: ({ input: [filed], output }) => filed || output !== undefined,
  },
  open: true,
})

export function phase(settled: boolean, failed: boolean): "running" | "done" | "failed" {
  return !settled ? "running" : failed ? "failed" : "done"
}

/** A union of strings the laws do not settle once a task has settled without failing. */
export const phaseLeftOpen = contract(phase, {
  ensures: {
    runningUntilSettled: ({ input: [settled], output }) => settled === (output !== "running"),
  },
})

/** A hole only outside `requires` is no hole: every input the callers may pass is decided. */
export const holeOutsideRequires = contract(phase, {
  requires: ({ input: [settled] }) => !settled,
  ensures: {
    runningUntilSettled: ({ input: [settled], output }) => settled === (output !== "running"),
  },
})

export function labelled(n: bigint): { readonly sign: "negative" | "zero" | "positive"; readonly label: string } {
  return { sign: n < 0n ? "negative" : n === 0n ? "zero" : "positive", label: `${n}` }
}

/** A free string beside a decided closed field: two results that differ only in the string are of one kind. */
export const freeLabel = contract(labelled, {
  ensures: {
    signDecided: ({ input: [n], output }) => output.sign === (n < 0n ? "negative" : n === 0n ? "zero" : "positive"),
  },
})

// Records read by key and values of more than one kind: a dictionary (`Record<string, T>`) read at a key, `in` and
// `Object.hasOwn` of it; a record read at a key its type holds to a few names; a value that is a boolean or a name,
// told apart by `typeof`; `trim`, `Boolean(x)`; a field read once a check has shown its object present; a value
// written before a search and first read inside it; and the same search made twice, by the code and by a law, with a
// function declared pure called on what it found; a dictionary's keys and entries (`Object.keys`, `Object.entries`),
// each key once, and a literal's in the order JavaScript gives them; and `typeof` of an `unknown`.
// `test/records.test.ts` asks each.
import { assume, contract } from "../src/contract.ts"

export type Steps = Readonly<Record<string, { readonly taskId: string | null }>>

/** The task a step was filed as: `null` where it was not filed, or where the record has no such step. */
export function filedAs(steps: Steps, name: string): string | null {
  const record = steps[name]
  return record === undefined ? null : record.taskId
}

export const filedAsItsRecordSays = contract(filedAs, {
  /** A step's name is no name of `Object.prototype`'s: `steps["toString"]` finds Object's own function. */
  requires: ({ input: [steps, name] }) => Object.hasOwn(steps, name) || (name !== "toString" && name !== "constructor" && name.startsWith("s")),
  ensures: {
    itsRecords: ({ input: [steps, name], output }) => !Object.hasOwn(steps, name) || output === steps[name]?.taskId,
    noneWithoutOne: ({ input: [steps, name], output }) => Object.hasOwn(steps, name) || output === null,
    aStepIsIn: ({ input: [steps, name], output }) => output === null || name in steps,
  },
})

/** Refused nowhere, and broken: a key may be a name `Object.prototype` holds, which `steps[name]` finds. */
export const anyNameRead = contract(filedAs, { ensures: { always: () => true } })
/** False: a counterexample reads the dictionary back as a plain object. */
export const neverFiled = contract(filedAs, {
  requires: ({ input: [steps, name] }) => Object.hasOwn(steps, name),
  ensures: { never: ({ output }) => output === null },
})

export type Phase = "waiting" | "running" | "done"
const WORDS: Partial<Record<Phase, string>> = { waiting: "not filed", running: "still running" }

/** What a phase says to a person; a phase with no words of its own, "other". */
export function said(phase: Phase): string {
  return WORDS[phase] ?? "other"
}

export const saidOfEachPhase = contract(said, {
  ensures: {
    waiting: ({ input: [p], output }) => p !== "waiting" || output === "not filed",
    running: ({ input: [p], output }) => p !== "running" || output === "still running",
    done: ({ input: [p], output }) => p !== "done" || output === "other",
  },
})

/** A setting given as a switch or a mode's name. */
export function modeOf(setting: boolean | "strict" | "loose"): string {
  if (typeof setting === "string") return setting
  return setting ? "strict" : "off"
}

export const modeOfASetting = contract(modeOf, {
  ensures: {
    aNameIsItself: ({ input: [s], output }) => typeof s !== "string" || output === s,
    onIsStrict: ({ input: [s], output }) => s !== true || output === "strict",
    offIsOff: ({ input: [s], output }) => s !== false || output === "off",
  },
})

/** False: a counterexample gives a switch or a name, as JavaScript holds it. */
export const neverStrict = contract(modeOf, { ensures: { never: ({ output }) => output !== "strict" } })

/** What kind of value a field holds, as `typeof` says it. */
export function kindOf(v: string | number | undefined | null): string {
  return typeof v
}

export const kindOfAField = contract(kindOf, {
  ensures: {
    aMissingOne: ({ input: [v], output }) => v !== undefined || output === "undefined",
    nullIsAnObject: ({ input: [v], output }) => v !== null || output === "object",
    aNumber: ({ input: [v], output }) => typeof v !== "number" || output === "number",
  },
})

/** Whether words given are empty, spaces and line ends alone. */
export function blank(message: string | undefined): boolean {
  return message !== undefined && !message.trim()
}

export const blankWords = contract(blank, {
  ensures: {
    emptyIsBlank: ({ input: [m], output }) => m !== "" || output,
    spacesAreBlank: ({ input: [m], output }) => m !== " \t\n" || output,
    aLetterIsNot: ({ input: [m], output }) => m === undefined || !m.includes("a") || !output,
    noneIsNot: ({ input: [m], output }) => m !== undefined || !output,
  },
})

/** Whether a list was given and names "a". */
export function listsA(xs: ReadonlyArray<string> | undefined): boolean {
  return Boolean(xs?.includes("a"))
}

export const listsAWhenGiven = contract(listsA, {
  ensures: { exactly: ({ input: [xs], output }) => output === (xs !== undefined && xs.includes("a")) },
})

export type Run = { readonly id: string; readonly pruned?: { readonly at: string; readonly files: number } }

/** When a run was pruned, read from its record once it is shown pruned. */
export function prunedAt(run: Run): string {
  if (!run.pruned) return "never"
  const { at } = run.pruned
  return at
}

export const prunedAtItsTime = contract(prunedAt, {
  ensures: { itsTime: ({ input: [run], output }) => run.pruned === undefined || output === run.pruned.at },
})

/** The try a step is on, from 1: one past the tries its record keeps. */
const tryOf = (steps: Readonly<Record<string, { readonly tries?: ReadonlyArray<string> }>>, name: string): number =>
  (steps[name]?.tries?.length ?? 0) + 1

/** Whether the try after the next one is asked for: a count written before the search, read first inside it. */
export function askedPast(
  steps: Readonly<Record<string, { readonly tries?: ReadonlyArray<string> }>>,
  name: string,
  asks: ReadonlyArray<{ readonly step: string; readonly try: number }>,
): boolean {
  const n = tryOf(steps, name)
  return asks.find((a) => a.step === name && a.try === n + 1) !== undefined
}

export const askedPastTheNext = contract(askedPast, {
  requires: ({ input: [steps, name] }) => Object.hasOwn(steps, name),
  ensures: {
    thatTry: ({ input: [steps, name, asks], output }) => output === asks.some((a) => a.step === name && a.try === (steps[name]?.tries?.length ?? 0) + 2),
  },
})

export type Job = { readonly id: string; readonly size: number }

/** A job's price by some table: read where it is declared, not from its body. */
export function priceOf(job: Job, weigh: (job: Job) => number = () => 1): number {
  return weigh(job) * 2
}
export const pricesArePure = assume(priceOf, { pure: true })

/** The price of the job of an id, 0 where there is none. */
export function quote(jobs: ReadonlyArray<Job>, id: string, weigh?: (job: Job) => number): number {
  const job = jobs.find((j) => j.id === id)
  return job === undefined ? 0 : priceOf(job, weigh)
}

export const quotedAtItsPrice = contract(quote, {
  ensures: {
    itsPrice: ({ input: [jobs, id, weigh], output }) => {
      const job = jobs.find((j) => j.id === id)
      return job === undefined ? output === 0 : Object.is(output, priceOf(job, weigh ?? (() => 1)))
    },
  },
})

/** The names of a dictionary: each its own key, none twice, and array positions first. */
export function namesOf(steps: Steps): ReadonlyArray<string> {
  return Object.keys(steps)
}

export const namesOfItsOwn = contract(namesOf, {
  ensures: {
    itsOwn: ({ input: [steps], output }) => output.every((k) => Object.hasOwn(steps, k)),
    eachOnce: ({ output }) => output.every((k, i) => output.every((j, m) => m === i || j !== k)),
    /** An array position comes first, ascending: none is less than "0". */
    zeroFirst: ({ output }) => output.every((k, i) => k !== "0" || i === 0),
  },
})

/** The steps filed, by name: an entry's key beside its value. */
export function filedSteps(steps: Steps): ReadonlyArray<string> {
  return Object.entries(steps)
    .filter(([, s]) => s.taskId !== null)
    .map(([name]) => name)
}

export const filedStepsAreFiled = contract(filedSteps, {
  ensures: { filed: ({ input: [steps], output }) => output.every((n) => Object.hasOwn(steps, n) && steps[n]?.taskId !== null) },
})

/** A literal's keys and values: positions first, ascending, then names as they were written. */
export function written(): ReadonlyArray<string> {
  const o = { b: "w", 2: "x", a: "y", 1: "z" }
  return [...Object.keys(o), ...Object.values(o)]
}

export const writtenInOrder = contract(written, {
  ensures: {
    keysThenValues: ({ output }) =>
      output.length === 8 &&
      output[0] === "1" &&
      output[1] === "2" &&
      output[2] === "b" &&
      output[3] === "a" &&
      output[4] === "z" &&
      output[5] === "x" &&
      output[6] === "w" &&
      output[7] === "y",
  },
})

/** What kind of value anything is, as `typeof` says it. */
export function kindOfAnything(v: unknown): string {
  const kind = typeof v
  return kind
}

export const kindOfAnythingIsJavaScripts = contract(kindOfAnything, {
  ensures: {
    oneOfEight: ({ output }) =>
      output === "undefined" ||
      output === "object" ||
      output === "boolean" ||
      output === "number" ||
      output === "bigint" ||
      output === "string" ||
      output === "symbol" ||
      output === "function",
    aFunctionIsOne: ({ input: [v], output }) => typeof v !== "function" || output === "function",
  },
})

/** False: a counterexample gives a function, read back as one. */
export const neverAFunction = contract(kindOfAnything, { ensures: { never: ({ output }) => output !== "function" } })

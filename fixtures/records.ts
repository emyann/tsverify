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
  requires: (steps, name) => Object.hasOwn(steps, name) || (name !== "toString" && name !== "constructor" && name.startsWith("s")),
  ensures: {
    itsRecords: (steps, name, out) => !Object.hasOwn(steps, name) || out === steps[name]?.taskId,
    noneWithoutOne: (steps, name, out) => Object.hasOwn(steps, name) || out === null,
    aStepIsIn: (steps, name, out) => out === null || name in steps,
  },
})

/** Refused nowhere, and broken: a key may be a name `Object.prototype` holds, which `steps[name]` finds. */
export const anyNameRead = contract(filedAs, { ensures: { always: () => true } })
/** False: a counterexample reads the dictionary back as a plain object. */
export const neverFiled = contract(filedAs, {
  requires: (steps, name) => Object.hasOwn(steps, name),
  ensures: { never: (_steps, _name, out) => out === null },
})

export type Phase = "waiting" | "running" | "done"
const WORDS: Partial<Record<Phase, string>> = { waiting: "not filed", running: "still running" }

/** What a phase says to a person; a phase with no words of its own, "other". */
export function said(phase: Phase): string {
  return WORDS[phase] ?? "other"
}

export const saidOfEachPhase = contract(said, {
  ensures: {
    waiting: (p, out) => p !== "waiting" || out === "not filed",
    running: (p, out) => p !== "running" || out === "still running",
    done: (p, out) => p !== "done" || out === "other",
  },
})

/** A setting given as a switch or a mode's name. */
export function modeOf(setting: boolean | "strict" | "loose"): string {
  if (typeof setting === "string") return setting
  return setting ? "strict" : "off"
}

export const modeOfASetting = contract(modeOf, {
  ensures: {
    aNameIsItself: (s, out) => typeof s !== "string" || out === s,
    onIsStrict: (s, out) => s !== true || out === "strict",
    offIsOff: (s, out) => s !== false || out === "off",
  },
})

/** False: a counterexample gives a switch or a name, as JavaScript holds it. */
export const neverStrict = contract(modeOf, { ensures: { never: (_s, out) => out !== "strict" } })

/** What kind of value a field holds, as `typeof` says it. */
export function kindOf(v: string | number | undefined | null): string {
  return typeof v
}

export const kindOfAField = contract(kindOf, {
  ensures: {
    aMissingOne: (v, out) => v !== undefined || out === "undefined",
    nullIsAnObject: (v, out) => v !== null || out === "object",
    aNumber: (v, out) => typeof v !== "number" || out === "number",
  },
})

/** Whether words given are empty, spaces and line ends alone. */
export function blank(message: string | undefined): boolean {
  return message !== undefined && !message.trim()
}

export const blankWords = contract(blank, {
  ensures: {
    emptyIsBlank: (m, out) => m !== "" || out,
    spacesAreBlank: (m, out) => m !== " \t\n" || out,
    aLetterIsNot: (m, out) => m === undefined || !m.includes("a") || !out,
    noneIsNot: (m, out) => m !== undefined || !out,
  },
})

/** Whether a list was given and names "a". */
export function listsA(xs: ReadonlyArray<string> | undefined): boolean {
  return Boolean(xs?.includes("a"))
}

export const listsAWhenGiven = contract(listsA, {
  ensures: { exactly: (xs, out) => out === (xs !== undefined && xs.includes("a")) },
})

export type Run = { readonly id: string; readonly pruned?: { readonly at: string; readonly files: number } }

/** When a run was pruned, read from its record once it is shown pruned. */
export function prunedAt(run: Run): string {
  if (!run.pruned) return "never"
  const { at } = run.pruned
  return at
}

export const prunedAtItsTime = contract(prunedAt, {
  ensures: { itsTime: (run, out) => run.pruned === undefined || out === run.pruned.at },
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
  requires: (steps, name) => Object.hasOwn(steps, name),
  ensures: {
    thatTry: (steps, name, asks, out) => out === asks.some((a) => a.step === name && a.try === (steps[name]?.tries?.length ?? 0) + 2),
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
    itsPrice: (jobs, id, weigh, out) => {
      const job = jobs.find((j) => j.id === id)
      return job === undefined ? out === 0 : Object.is(out, priceOf(job, weigh ?? (() => 1)))
    },
  },
})

/** The names of a dictionary: each its own key, none twice, and array positions first. */
export function namesOf(steps: Steps): ReadonlyArray<string> {
  return Object.keys(steps)
}

export const namesOfItsOwn = contract(namesOf, {
  ensures: {
    itsOwn: (steps, out) => out.every((k) => Object.hasOwn(steps, k)),
    eachOnce: (_steps, out) => out.every((k, i) => out.every((j, m) => m === i || j !== k)),
    /** An array position comes first, ascending: none is less than "0". */
    zeroFirst: (_steps, out) => out.every((k, i) => k !== "0" || i === 0),
  },
})

/** The steps filed, by name: an entry's key beside its value. */
export function filedSteps(steps: Steps): ReadonlyArray<string> {
  return Object.entries(steps)
    .filter(([, s]) => s.taskId !== null)
    .map(([name]) => name)
}

export const filedStepsAreFiled = contract(filedSteps, {
  ensures: { filed: (steps, out) => out.every((n) => Object.hasOwn(steps, n) && steps[n]?.taskId !== null) },
})

/** A literal's keys and values: positions first, ascending, then names as they were written. */
export function written(): ReadonlyArray<string> {
  const o = { b: "w", 2: "x", a: "y", 1: "z" }
  return [...Object.keys(o), ...Object.values(o)]
}

export const writtenInOrder = contract(written, {
  ensures: {
    keysThenValues: (out) =>
      out.length === 8 &&
      out[0] === "1" &&
      out[1] === "2" &&
      out[2] === "b" &&
      out[3] === "a" &&
      out[4] === "z" &&
      out[5] === "x" &&
      out[6] === "w" &&
      out[7] === "y",
  },
})

/** What kind of value anything is, as `typeof` says it. */
export function kindOfAnything(v: unknown): string {
  const kind = typeof v
  return kind
}

export const kindOfAnythingIsJavaScripts = contract(kindOfAnything, {
  ensures: {
    oneOfEight: (_v, out) =>
      out === "undefined" ||
      out === "object" ||
      out === "boolean" ||
      out === "number" ||
      out === "bigint" ||
      out === "string" ||
      out === "symbol" ||
      out === "function",
    aFunctionIsOne: (v, out) => typeof v !== "function" || out === "function",
  },
})

/** False: a counterexample gives a function, read back as one. */
export const neverAFunction = contract(kindOfAnything, { ensures: { never: (_v, out) => out !== "function" } })

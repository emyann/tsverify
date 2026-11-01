// Collections and keys: the elements a `.filter` keeps, a `Map` and a `Set` the code is given or builds and reads
// through `has` and `get`, a copy turned around, a `.slice` of positions counted from the end, and `in`, of an object
// the code built and of a union it is given. `test/collections.test.ts` asks each.
import { contract } from "../src/contract.ts"

export interface Job {
  readonly id: string
  readonly done: boolean
  readonly turn?: number
}

/** The first job not done, and the last. */
export function pending(jobs: ReadonlyArray<Job>): { readonly first: Job | undefined; readonly last: Job | undefined } {
  const open = jobs.filter((j) => !j.done)
  return { first: open[0], last: open.at(-1) }
}

export const pendingOnes = contract(pending, {
  ensures: {
    firstNotDone: ({ output }) => output.first === undefined || !output.first.done,
    lastNotDone: ({ output }) => output.last === undefined || !output.last.done,
    noneWhenAllDone: ({ input: [jobs], output }) => !jobs.every((j) => j.done) || output.first === undefined,
    someWhenOneOpen: ({ input: [jobs], output }) => !jobs.some((j) => !j.done) || output.first !== undefined,
  },
})

/** A job's owner, as the table says; "nobody" where it has none. */
export function ownerOf(owners: ReadonlyMap<string, string>, job: Job): string {
  return owners.get(job.id) ?? "nobody"
}

export const ownedOrNobody = contract(ownerOf, {
  ensures: {
    theTables: ({ input: [owners, job], output }) => !owners.has(job.id) || output === owners.get(job.id),
    nobodyOtherwise: ({ input: [owners, job], output }) => owners.has(job.id) || output === "nobody",
  },
})

const TERMINAL = new Set(["done", "failed"])

/** Whether a state is one a job ends in, or one a person said to skip. */
export function finished(state: string, skipped: ReadonlySet<string>): boolean {
  return TERMINAL.has(state) || skipped.has(state)
}

export const finishedStates = contract(finished, {
  ensures: {
    doneIs: ({ input: [state], output }) => state !== "done" || output,
    failedIs: ({ input: [state], output }) => state !== "failed" || output,
    skippedIs: ({ input: [state, skipped], output }) => !skipped.has(state) || output,
    nothingElse: ({ input: [state, skipped], output }) => !output || state === "done" || state === "failed" || skipped.has(state),
  },
})

/** The last job that has a turn, read from the end. */
export function lastWithTurn(jobs: ReadonlyArray<Job>): Job | undefined {
  return [...jobs].reverse().find((j) => j.turn !== undefined)
}

export const lastWithATurn = contract(lastWithTurn, {
  ensures: {
    hasATurn: ({ output }) => output === undefined || output.turn !== undefined,
    theLastWhenItHasOne: ({ input: [jobs], output }) => jobs.at(-1)?.turn === undefined || output?.id === jobs.at(-1)?.id,
    foundWhenOneHas: ({ input: [jobs], output }) => !jobs.some((j) => j.turn !== undefined) || output !== undefined,
  },
})

/** The last `n` ids, positions counted from the end. */
export function lastIds(ids: ReadonlyArray<string>, n: number): ReadonlyArray<string> {
  return ids.slice(-n)
}

export const lastIdsKept = contract(lastIds, {
  requires: ({ input: [, n] }) => Number.isInteger(n) && n >= 1 && n <= 3,
  ensures: {
    atMostN: ({ input: [, n], output }) => output.length <= n,
    allWhenFewer: ({ input: [ids, n], output }) => ids.length > n || output.length === ids.length,
    endsTheSame: ({ input: [ids], output }) => output.length === 0 || output.at(-1) === ids.at(-1),
  },
})

export type Moved = { readonly to: string; readonly note: string } | { readonly refused: string }

/** What a move says: where it went, or why it was refused. */
export function said(moved: Moved): string {
  return "refused" in moved ? `refused: ${moved.refused}` : moved.to
}

export const saidOfAMove = contract(said, {
  ensures: { theDestination: ({ input: [moved], output }) => "refused" in moved || output === moved.to },
})

/** A record the code builds holds the keys it wrote: `in` asks it. */
export function tagged(withNote: boolean): boolean {
  const o = withNote ? { id: "a", note: "n" } : { id: "a" }
  return "note" in o
}

export const taggedWhenAsked = contract(tagged, {
  ensures: { exactlyWhenAsked: ({ input: [withNote], output }) => output === withNote },
})

/** A label for an id, from a naming function the caller gives: the id itself where it names nothing. */
export function labelOf(id: string, name: (id: string) => string): string {
  const given = name(id)
  return given === "" ? id : given
}

export const labelNeverEmpty = contract(labelOf, {
  ensures: { notEmptyOfAnId: ({ input: [id], output }) => id === "" || output !== "" },
})

export type Step = { readonly kind: "even"; readonly half: bigint } | { readonly kind: "odd" } | { readonly kind: "never" }

/** A step of a count: half of it where it is even. A union told apart by `kind`, one member of which is never made. */
export function stepOf(n: bigint): Step {
  return n % 2n === 0n ? { kind: "even", half: n / 2n } : { kind: "odd" }
}

export const stepsOfACount = contract(stepOf, {
  ensures: { halfOfAnEven: ({ input: [n], output }) => output.kind !== "even" || output.half * 2n === n },
})

/** Refused: `.reverse()` turns around the array it is called on, here the caller's. */
export function reversedInPlace(xs: Array<string>): Array<string> {
  return xs.reverse()
}
export const reversedRefused = contract(reversedInPlace, { ensures: { same: ({ input: [xs], output }) => output.length === xs.length } })

/** Refused: an optional key's presence, which `in` asks and an absent key and one holding `undefined` do not tell. */
export function hasNote(job: { readonly id: string; readonly note?: string }): boolean {
  return "note" in job
}
export const optionalKeyRefused = contract(hasNote, { ensures: { any: ({ output }) => output || !output } })

/** Refused: a `Map`'s size, which counts its keys, not its entries. */
export function owners(table: ReadonlyMap<string, string>): number {
  return table.size
}
export const sizeRefused = contract(owners, { ensures: { counted: ({ output }) => output >= 0 } })

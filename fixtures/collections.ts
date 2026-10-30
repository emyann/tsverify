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
    firstNotDone: (_jobs, out) => out.first === undefined || !out.first.done,
    lastNotDone: (_jobs, out) => out.last === undefined || !out.last.done,
    noneWhenAllDone: (jobs, out) => !jobs.every((j) => j.done) || out.first === undefined,
    someWhenOneOpen: (jobs, out) => !jobs.some((j) => !j.done) || out.first !== undefined,
  },
})

/** A job's owner, as the table says; "nobody" where it has none. */
export function ownerOf(owners: ReadonlyMap<string, string>, job: Job): string {
  return owners.get(job.id) ?? "nobody"
}

export const ownedOrNobody = contract(ownerOf, {
  ensures: {
    theTables: (owners, job, out) => !owners.has(job.id) || out === owners.get(job.id),
    nobodyOtherwise: (owners, job, out) => owners.has(job.id) || out === "nobody",
  },
})

const TERMINAL = new Set(["done", "failed"])

/** Whether a state is one a job ends in, or one a person said to skip. */
export function finished(state: string, skipped: ReadonlySet<string>): boolean {
  return TERMINAL.has(state) || skipped.has(state)
}

export const finishedStates = contract(finished, {
  ensures: {
    doneIs: (state, _skipped, out) => state !== "done" || out,
    failedIs: (state, _skipped, out) => state !== "failed" || out,
    skippedIs: (state, skipped, out) => !skipped.has(state) || out,
    nothingElse: (state, skipped, out) => !out || state === "done" || state === "failed" || skipped.has(state),
  },
})

/** The last job that has a turn, read from the end. */
export function lastWithTurn(jobs: ReadonlyArray<Job>): Job | undefined {
  return [...jobs].reverse().find((j) => j.turn !== undefined)
}

export const lastWithATurn = contract(lastWithTurn, {
  ensures: {
    hasATurn: (_jobs, out) => out === undefined || out.turn !== undefined,
    theLastWhenItHasOne: (jobs, out) => jobs.at(-1)?.turn === undefined || out?.id === jobs.at(-1)?.id,
    foundWhenOneHas: (jobs, out) => !jobs.some((j) => j.turn !== undefined) || out !== undefined,
  },
})

/** The last `n` ids, positions counted from the end. */
export function lastIds(ids: ReadonlyArray<string>, n: number): ReadonlyArray<string> {
  return ids.slice(-n)
}

export const lastIdsKept = contract(lastIds, {
  requires: (_ids, n) => Number.isInteger(n) && n >= 1 && n <= 3,
  ensures: {
    atMostN: (_ids, n, out) => out.length <= n,
    allWhenFewer: (ids, n, out) => ids.length > n || out.length === ids.length,
    endsTheSame: (ids, _n, out) => out.length === 0 || out.at(-1) === ids.at(-1),
  },
})

export type Moved = { readonly to: string; readonly note: string } | { readonly refused: string }

/** What a move says: where it went, or why it was refused. */
export function said(moved: Moved): string {
  return "refused" in moved ? `refused: ${moved.refused}` : moved.to
}

export const saidOfAMove = contract(said, {
  ensures: { theDestination: (moved, out) => "refused" in moved || out === moved.to },
})

/** A record the code builds holds the keys it wrote: `in` asks it. */
export function tagged(withNote: boolean): boolean {
  const o = withNote ? { id: "a", note: "n" } : { id: "a" }
  return "note" in o
}

export const taggedWhenAsked = contract(tagged, {
  ensures: { exactlyWhenAsked: (withNote, out) => out === withNote },
})

/** A label for an id, from a naming function the caller gives: the id itself where it names nothing. */
export function labelOf(id: string, name: (id: string) => string): string {
  const given = name(id)
  return given === "" ? id : given
}

export const labelNeverEmpty = contract(labelOf, {
  ensures: { notEmptyOfAnId: (id, _name, out) => id === "" || out !== "" },
})

export type Step = { readonly kind: "even"; readonly half: bigint } | { readonly kind: "odd" } | { readonly kind: "never" }

/** A step of a count: half of it where it is even. A union told apart by `kind`, one member of which is never made. */
export function stepOf(n: bigint): Step {
  return n % 2n === 0n ? { kind: "even", half: n / 2n } : { kind: "odd" }
}

export const stepsOfACount = contract(stepOf, {
  ensures: { halfOfAnEven: (n, out) => out.kind !== "even" || out.half * 2n === n },
})

/** Refused: `.reverse()` turns around the array it is called on, here the caller's. */
export function reversedInPlace(xs: Array<string>): Array<string> {
  return xs.reverse()
}
export const reversedRefused = contract(reversedInPlace, { ensures: { same: (xs, out) => out.length === xs.length } })

/** Refused: an optional key's presence, which `in` asks and an absent key and one holding `undefined` do not tell. */
export function hasNote(job: { readonly id: string; readonly note?: string }): boolean {
  return "note" in job
}
export const optionalKeyRefused = contract(hasNote, { ensures: { any: (_job, out) => out || !out } })

/** Refused: a `Map`'s size, which counts its keys, not its entries. */
export function owners(table: ReadonlyMap<string, string>): number {
  return table.size
}
export const sizeRefused = contract(owners, { ensures: { counted: (_t, out) => out >= 0 } })

// Functions for the purity check: each impure one for one reason, then pure
// ones it must accept. None is verified; `test/purity.test.ts` asks each.

// Impure.

export function changesArgument(xs: string[]): number {
  xs.push("x")
  return xs.length
}

export const readsClock = (): number => Date.now()

export const rolls = (): number => Math.random()

let calls = 0
export const counts = (): number => {
  calls++
  return calls
}

export const logs = (x: string): string => {
  console.log(x)
  return x
}

/** A fresh box holding the caller's list: a change made through the box reaches the caller. */
export const changesThroughABox = (p: { readonly list: string[] }): number => {
  const box = { inner: p.list }
  box.inner.push("x")
  return box.inner.length
}

/** The same, the box filled by a helper and changed by another. */
const fill = (box: { inner: string[] }, from: string[]): void => {
  box.inner = from
}
const grow = (list: string[]): void => {
  list.push("y")
}
export const changesThroughHelpers = (from: string[]): number => {
  const box = { inner: [] as string[] }
  fill(box, from)
  grow(box.inner)
  return box.inner.length
}

/** A value of the caller's stored as `unknown`, narrowed back and changed. */
export const changesANarrowedUnknown = (p: { readonly v: unknown }): number => {
  const box: { v: unknown } = { v: p.v }
  const x = box.v
  if (typeof x === "object" && x !== null && "k" in x) x.k = 1
  return 0
}

export const passesItsArgumentOn = (xs: string[]): number => {
  grow(xs)
  return 1
}

export const callsTheClockThroughAHelper = (): number => readsClock() + 1

export const casts = (x: unknown): number => (x as { a: number }).a

/** A callback a read calls: one that reads the clock, the console's, one that changes what it is given. */
const stampOf = (_x: number): number => Date.now()
export const passesTheClock = (xs: ReadonlyArray<number>): ReadonlyArray<number> => xs.map(stampOf)
export const logsEach = (xs: ReadonlyArray<string>): void => xs.forEach(console.log)
export const passesWhatChangesIt = (xs: ReadonlyArray<string[]>): void => xs.forEach(changesArgument)

// Pure where the functions it is given are: it calls them, or hands them to what does.

export const appliesWhatItIsGiven = (f: (x: number) => number, x: number): number => f(x)
export const mapsWithWhatItIsGiven = (xs: ReadonlyArray<number>, f: (x: number) => number): ReadonlyArray<number> => xs.map(f)
export const passesItOn = (g: (x: number) => number): number => appliesWhatItIsGiven(g, 1)
export const defaultsIt = (x: number, f: (x: number) => number = (y) => y): number => f(x)

// Pure.

/** Fills two lists it made, one with values it was given as `unknown`: a change to either reaches nothing of the caller's. */
export const sortsUnknowns = (xs: ReadonlyArray<unknown>): number => {
  const lists: unknown[] = []
  const others: string[] = []
  for (const x of xs) {
    if (Array.isArray(x)) lists.push(x)
    else others.push(typeof x)
  }
  return lists.length + others.length
}

/** Builds a fresh list and fills it: a change to what it allocated. */
export const copies = (xs: ReadonlyArray<number>): number => {
  const out: number[] = []
  for (const x of xs) out.push(x)
  return out.length
}

/** A state folded from events, as a fold builds one: the caller's values stored, the fresh parts changed. */
type Item = { readonly name: string; readonly tags: ReadonlyArray<string> }
type Folded = { names: string[]; last: Item | undefined; count: number }
export const folds = (items: ReadonlyArray<Item>): Folded => {
  const s: Folded = { names: [], last: undefined, count: 0 }
  for (const it of items) {
    s.names.push(it.name)
    s.last = it
    s.count += 1
  }
  return s
}

/** A table of functions held by a constant, called by name. */
const isEmpty = (xs: ReadonlyArray<string>): boolean => xs.length === 0
const isFull = (xs: ReadonlyArray<string>): boolean => xs.length > 8
const TESTS = { isEmpty, isFull }
export const asks = (which: keyof typeof TESTS, xs: ReadonlyArray<string>): boolean => TESTS[which](xs)

export const reduces = (xs: ReadonlyArray<number>): number => xs.reduce((acc, x) => Math.max(acc, x), 0)

export function recurses(n: number): number {
  return n <= 0 ? 0 : recurses(n - 1)
}

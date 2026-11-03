// A map the code builds at keys it computes: Nemia's `inheritedLabels` (agent-orchestrator, src/labels/labels.ts, at
// d77e7c7), copied as it is written. `test/maps.test.ts` asks each law, and plants a bug for each.
import { contract } from "../src/contract.ts"

/** A person's labels: a key to its value, Kubernetes' `map[string]string`. */
export type Labels = Readonly<Record<string, string>>

/** One edit of a map, as kubectl spells it: `key=value` sets the key, `key-` removes it. */
export type LabelEdit =
  | { readonly key: string; readonly op: "set"; readonly value: string }
  | { readonly key: string; readonly op: "remove" }

/** A run a start names, `--after` or `--from`, and the labels it carries. */
export type ParentLabels = { readonly run: string; readonly labels: Labels }

/** A key a start leaves out, since the runs it names give it different values: the key, and each run with its value. */
export type LeftOut = { readonly key: string; readonly values: readonly { readonly run: string; readonly value: string }[] }

/** What a start copies: the labels, and each key two of its runs disagree on, which is not inherited. */
export type Inherited = { readonly labels: Labels; readonly leftOut: readonly LeftOut[] }

/**
 * The labels a run or a card is created with, copied once: every key the runs it names (`parents`) agree on, then the card's own
 * labels over them, then the start's typed edits over those — `key=value` sets, `key-` drops an inherited one. A key two runs give
 * different values that neither the card nor the start sets is left out, and named in `leftOut`. Pure.
 */
export function inheritedLabels(input: {
  readonly parents: readonly ParentLabels[]
  readonly card?: Labels
  readonly edits?: readonly LabelEdit[]
}): Inherited {
  const card = input.card ?? {}
  const edits = input.edits ?? []
  const named = (key: string): boolean => Object.hasOwn(card, key) || edits.some((e) => e.key === key)
  const out: Record<string, string> = {}
  const leftOut: LeftOut[] = []
  const keys = [...new Set(input.parents.flatMap((p) => Object.keys(p.labels)))].sort()
  for (const key of keys) {
    if (named(key)) continue
    const values = input.parents.flatMap((p) => {
      const value = Object.hasOwn(p.labels, key) ? p.labels[key] : undefined
      return value === undefined ? [] : [{ run: p.run, value }]
    })
    const first = values[0]
    if (first === undefined) continue
    if (values.every((v) => v.value === first.value)) out[key] = first.value
    else leftOut.push({ key, values })
  }
  for (const [key, value] of Object.entries(card)) out[key] = value
  for (const edit of edits) {
    if (edit.op === "set") out[edit.key] = edit.value
    else delete out[edit.key]
  }
  return { labels: out, leftOut }
}

type Start = Parameters<typeof inheritedLabels>[0]

/** Whether `map` carries `key` itself: `constructor` is a label like any other. */
const carries = (map: Labels, key: string): boolean => Object.hasOwn(map, key)
const cardOf = (start: Start): Labels => start.card ?? {}
const editsOf = (start: Start): readonly LabelEdit[] => start.edits ?? []
/** Whether the card or an edit names `key`. */
const named = (start: Start, key: string): boolean => carries(cardOf(start), key) || editsOf(start).some((e) => e.key === key)
/** Whether edit `i` is the last that names its key. */
const lastOfItsKey = (start: Start, i: number, key: string): boolean => !editsOf(start).some((f, j) => j > i && f.key === key)
/** Whether every run that carries `key` gives it `value`. */
const allGive = (start: Start, key: string, value: string): boolean =>
  start.parents.every((p) => !carries(p.labels, key) || p.labels[key] === value)
/** Whether two runs give `key` different values. */
const disagree = (start: Start, key: string): boolean =>
  start.parents.some((p) => start.parents.some((q) => carries(p.labels, key) && carries(q.labels, key) && p.labels[key] !== q.labels[key]))
/** Whether `labels` holds `key` at `value`. */
const holds = (labels: Labels, key: string, value: string): boolean => carries(labels, key) && labels[key] === value
/**
 * No run, card or edit names `__proto__`, which a person's label never is (`labelKeyRefusal`): written to a plain object,
 * it sets no key, so the map the start builds never holds it.
 */
const noProto = (start: Start): boolean =>
  start.parents.every((p) => !carries(p.labels, "__proto__")) &&
  !carries(cardOf(start), "__proto__") &&
  editsOf(start).every((e) => e.key !== "__proto__")

export const inheritedLabelsLaws = contract(inheritedLabels, {
  requires: ({ input: [start] }) => noProto(start),
  ensures: {
    typedWins: {
      description: "A key typed key=value at the start has that value, over the card and the runs",
      condition: ({ input: [start], output }) =>
        editsOf(start).every((e, i) => e.op !== "set" || !lastOfItsKey(start, i, e.key) || holds(output.labels, e.key, e.value)),
    },
    droppedAtStart: {
      description: "A key typed key- is absent, whatever the card or the runs say",
      condition: ({ input: [start], output }) =>
        editsOf(start).every((e, i) => e.op === "set" || !lastOfItsKey(start, i, e.key) || !carries(output.labels, e.key)),
    },
    cardOverRuns: {
      description: "The card's value is taken over the runs', where no edit names its key",
      condition: ({ input: [start], output }) =>
        Object.entries(cardOf(start)).every(([key, value]) => editsOf(start).some((e) => e.key === key) || holds(output.labels, key, value)),
    },
    agreedInherited: {
      description: "A key every run carrying it gives one value has that value, where neither the card nor an edit names it",
      condition: ({ input: [start], output }) =>
        start.parents.every((p) =>
          Object.entries(p.labels).every(
            ([key, value]) => named(start, key) || !allGive(start, key, value) || holds(output.labels, key, value),
          ),
        ),
    },
    disagreedLeftOut: {
      description: "A key two runs give different values is absent and left out, where neither the card nor an edit names it",
      condition: ({ input: [start], output }) =>
        start.parents.every((p) =>
          Object.keys(p.labels).every(
            (key) =>
              named(start, key) ||
              !disagree(start, key) ||
              (!carries(output.labels, key) && output.leftOut.some((l) => l.key === key)),
          ),
        ),
    },
    leftOutOnlyDisagreed: {
      description: "A key left out is one two runs disagree on, and neither the card nor an edit names",
      condition: ({ input: [start], output }) => output.leftOut.every((l) => !named(start, l.key) && disagree(start, l.key)),
    },
    leftOutNamesEachRun: {
      description: "A key left out is named with each run that carries it and its value, and no other",
      condition: ({ input: [start], output }) =>
        output.leftOut.every(
          (l) =>
            l.values.every((v) => start.parents.some((p) => p.run === v.run && holds(p.labels, l.key, v.value))) &&
            start.parents.every((p) => !carries(p.labels, l.key) || l.values.some((v) => v.run === p.run && v.value === p.labels[l.key])),
        ),
    },
    nothingElse: {
      description: "Every key the start has is typed, the card's own, or one the runs agree on, with that value",
      condition: ({ input: [start], output }) =>
        Object.entries(output.labels).every(
          ([key, value]) =>
            editsOf(start).some((e, i) => e.key === key && lastOfItsKey(start, i, key) && e.op === "set" && e.value === value) ||
            (!editsOf(start).some((e) => e.key === key) &&
              (holds(cardOf(start), key, value) ||
                (!carries(cardOf(start), key) && start.parents.some((p) => carries(p.labels, key)) && allGive(start, key, value)))),
        ),
    },
  },
})

/**
 * Two laws that do not hold, a canary for the round that reads the first loop's writes as unknown: what a key typed
 * key=value holds, and what a key the runs agree on holds, are both written, so neither is ever absent.
 */
export const inheritedLabelsWrong = contract(inheritedLabels, {
  requires: ({ input: [start] }) => noProto(start),
  ensures: {
    typedNeverHeld: ({ input: [start], output }) => editsOf(start).every((e) => e.op !== "set" || !carries(output.labels, e.key)),
    agreedNeverHeld: ({ input: [start], output }) =>
      start.parents.every((p) => Object.keys(p.labels).every((key) => named(start, key) || !carries(output.labels, key))),
  },
})

// ——— Each construct on its own, run against JavaScript (test/maps.test.ts) ———

/** Writes at computed keys in a loop over a list given, a write and a delete after: the value `k` holds, or "-". */
export function written(keys: readonly string[], gone: string, k: string): string {
  const out: Record<string, string> = {}
  for (const key of keys) out[key] = gone
  out[gone] = "set"
  delete out[gone]
  return Object.hasOwn(out, k) ? (out[k] ?? "?") : "-"
}
export const writtenRun = contract(written, { ensures: { goneIsAbsent: ({ input: [, gone, k], output }) => k !== gone || output === "-" } })

/** The keys an object holds, in JavaScript's order: array positions first, by number; a key deleted and set again, last. */
export function listed(keys: readonly string[], again: string): string {
  const out: Record<string, string> = {}
  for (const key of keys) out[key] = key
  delete out[again]
  out[again] = again
  return Object.keys(out).join(",")
}
export const listedRun = contract(listed, { ensures: { againIsListed: ({ input: [, again], output }) => output.includes(again) } })

/** How many keys an object holds after writes and a delete. */
export function counted(keys: readonly string[], gone: string): number {
  const out: Record<string, string> = {}
  for (const key of keys) out[key] = key
  delete out[gone]
  return Object.keys(out).length
}
export const countedRun = contract(counted, { ensures: { atMostEach: ({ input: [keys], output }) => output <= keys.length } })

/** A list's strings, each once, sorted. */
export function sortedOnce(xs: readonly string[]): string {
  return [...new Set(xs)].sort().join(",")
}
export const sortedOnceRun = contract(sortedOnce, { ensures: { noneGiven: ({ input: [xs], output }) => xs.length > 0 || output === "" } })

/** How many strings a list holds, each once. */
export function distinct(xs: readonly string[]): number {
  return [...new Set(xs)].length
}
export const distinctRun = contract(distinct, { ensures: { atMostEach: ({ input: [xs], output }) => output <= xs.length } })

/** Each string twice, an empty one left out. */
export function doubled(xs: readonly string[]): string {
  return xs.flatMap((x) => (x === "" ? [] : [x, x])).join(",")
}
export const doubledRun = contract(doubled, { ensures: { noneGiven: ({ input: [xs], output }) => xs.length > 0 || output === "" } })

/** A `Map` the code fills, then changes: the value at `k` where it holds it, else "-". */
export function mappedAt(xs: readonly string[], k: string): string {
  const m = new Map<string, string>()
  for (const x of xs) m.set(x, x + "=")
  m.delete("z")
  return m.has(k) ? (m.get(k) ?? "?") : "-"
}
export const mappedAtRun = contract(mappedAt, { ensures: { zIsGone: ({ input: [, k], output }) => k !== "z" || output === "-" } })

/** How many keys a `Map` the code fills, then changes, holds. */
export function mappedSize(xs: readonly string[]): number {
  const m = new Map<string, string>()
  for (const x of xs) m.set(x, x)
  m.delete("z")
  return m.size
}
export const mappedSizeRun = contract(mappedSize, { ensures: { atMostEach: ({ input: [xs], output }) => output <= xs.length } })

/** A `Set` the code fills, then changes, listed in insertion order. */
export function members(xs: readonly string[], gone: string): string {
  const s = new Set<string>()
  for (const x of xs) s.add(x)
  s.delete(gone)
  const out: string[] = []
  for (const x of s) out.push(x)
  return out.join(",")
}
export const membersRun = contract(members, { ensures: { noneGiven: ({ input: [xs], output }) => xs.length > 0 || output === "" } })

/** Whether a `Set` the code fills, then changes, holds `k`. */
export function holdsOf(xs: readonly string[], gone: string, k: string): boolean {
  const s = new Set<string>()
  for (const x of xs) s.add(x)
  s.delete(gone)
  return s.has(k)
}
export const holdsOfRun = contract(holdsOf, { ensures: { goneIsGone: ({ input: [, gone, k], output }) => k !== gone || !output } })

/** How many strings a `Set` the code fills, then changes, holds. */
export function setSize(xs: readonly string[], gone: string): number {
  const s = new Set<string>()
  for (const x of xs) s.add(x)
  s.delete(gone)
  return s.size
}
export const setSizeRun = contract(setSize, { ensures: { atMostEach: ({ input: [xs], output }) => output <= xs.length } })

/** How many strings each twice, an empty one left out, make. */
export function doubledCount(xs: readonly string[]): number {
  return xs.flatMap((x) => (x === "" ? [] : [x, x])).length
}
export const doubledCountRun = contract(doubledCount, { ensures: { even: ({ output }) => output % 2 === 0 } })

/** A loop over a list's strings, each once, that writes a map at each but the empty one: the value `q` holds, or "-". */
export function keyedAt(xs: readonly string[], q: string): string {
  const out: Record<string, string> = {}
  for (const k of new Set(xs)) {
    if (k === "") continue
    out[k] = k + "!"
  }
  return Object.hasOwn(out, q) ? (out[q] ?? "?") : "-"
}
export const keyedAtRun = contract(keyedAt, { ensures: { emptyIsAbsent: ({ input: [, q], output }) => q !== "" || output === "-" } })

/** How many keys that loop writes. */
export function keyedCount(xs: readonly string[]): number {
  const out: Record<string, string> = {}
  for (const k of new Set(xs)) {
    if (k === "") continue
    out[k] = k + "!"
  }
  return Object.keys(out).length
}
export const keyedCountRun = contract(keyedCount, { ensures: { atMostEach: ({ input: [xs], output }) => output <= xs.length } })

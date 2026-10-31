// State: variables, changes to what a function allocated, borrows, `switch`.
// The first contracts are read and proved; the rest each break one rule of
// ownership and are refused for it. `test/loops.test.ts` asks each.
import { contract } from "../src/contract.ts"

const always = () => true

/** A helper changes a part of an object it is lent; the change is the caller's. */
function bump(c: { n: bigint }): void {
  c.n += 1n
}
export function twice(): bigint {
  const s = { c: { n: 0n } }
  bump(s.c)
  bump(s.c)
  return s.c.n
}
export const twiceIsTwo = contract(twice, { ensures: { two: (out) => out === 2n } })

/** A change through what `.find` found. */
export function mark(id: bigint): boolean {
  const items = [
    { id: 1n, done: false },
    { id: 2n, done: false },
  ]
  const it = items.find((x) => x.id === id)
  if (it) it.done = true
  return items.some((x) => x.done)
}
export const markedWhenFound = contract(mark, { ensures: { found: (id, out) => out === (id === 1n || id === 2n) } })

/** `switch`, cases that share a body, a fall-through and a `break`. */
export function kindOf(k: "a" | "b" | "c" | "d"): bigint {
  let n = 0n
  switch (k) {
    case "a":
    case "b":
      n = 1n
      break
    case "c":
      n = 2n
    // falls through
    default:
      n += 10n
  }
  return n
}
export const kinds = contract(kindOf, { ensures: { each: (k, out) => out === (k === "a" || k === "b" ? 1n : k === "c" ? 12n : 10n) } })

/** An optional field set, deleted, and set again only when absent (`??=`). */
export function stamps(at: string): string | undefined {
  const s: { at?: string; seen?: string } = {}
  s.at = at
  delete s.at
  s.seen ??= at
  s.seen ??= "later"
  return s.at ?? s.seen
}
export const stampKept = contract(stamps, { ensures: { first: (at, out) => out === at } })

/** A closure kept for later over a value that what runs before its call only reads: a part passed, or the whole to a pure function. */
function sizeOf(c: { xs: ReadonlyArray<bigint>; name: string }): number {
  return c.xs.length
}
function counted(c: { xs: ReadonlyArray<bigint> }, has: (x: bigint) => boolean): number {
  return c.xs.filter((x) => has(x)).length
}
export function keptOverRead(
  c: { xs: ReadonlyArray<bigint>; name: string },
  has: (x: bigint) => boolean,
  named: (name: string) => boolean,
): { same: boolean; named: boolean } {
  const f = () => c.xs.length
  const known = named(c.name)
  return { same: counted(c, has) >= 0 && f() === sizeOf(c), named: known }
}
export const readOnly = contract(keptOverRead, {
  ensures: { same: (_c, _has, _named, out) => out.same },
})

// Refused.

export function changesItsArgument(xs: Array<bigint>): number {
  xs.push(1n)
  return xs.length
}
export const argument = contract(changesItsArgument, { ensures: { always } })

export function twoNames(): bigint {
  const a = { n: 1n }
  const b = a
  b.n = 2n
  return a.n
}
export const secondName = contract(twoNames, { ensures: { always } })

export function storedTwice(): bigint {
  const s = { a: { n: 1n }, b: { n: 2n } }
  s.b = s.a
  return s.b.n
}
export const twice_ = contract(storedTwice, { ensures: { always } })

export function readAfterMove(): bigint {
  const item = { n: 1n }
  const list: Array<{ n: bigint }> = []
  list.push(item)
  return item.n
}
export const moved = contract(readAfterMove, { ensures: { always } })

export function replacedWhileBorrowed(): bigint {
  const s = { xs: [{ n: 1n }] }
  const a = s.xs.at(0)
  s.xs = []
  if (a) a.n = 2n
  return 0n
}
export const borrowed = contract(replacedWhileBorrowed, { ensures: { always } })

export function keptClosure(): bigint {
  let n = 0n
  const f = () => n
  n = 1n
  return f()
}
export const closure = contract(keptClosure, { ensures: { always } })

export function keptShorthand(): bigint {
  let n = 0n
  const f = () => ({ n })
  n = 1n
  return f().n
}
// Runs to 1n: a closure is read with what it captures where it is written, so this would read as 0n.
export const shorthand = contract(keptShorthand, { ensures: { isZero: (r) => r === 0n } })

export function keptOverLent(): bigint {
  const s = { n: 0n }
  const f = () => s.n
  bump(s)
  return f()
}
export const lent = contract(keptOverLent, { ensures: { always } })

/** Pure where the function it is handed is: handed one that changes what it is passed, the whole call changes `s`. */
function applied(c: { n: bigint }, g: (c: { n: bigint }) => void): void {
  g(c)
}
export function keptOverHanded(): bigint {
  const s = { n: 0n }
  const f = () => s.n
  applied(s, bump)
  return f()
}
export const handed = contract(keptOverHanded, { ensures: { always } })

/**
 * A callback's parameter is no function the caller is given: here it is `bump`, which changes `s`. The closure check
 * would not take it for one; that `applied` then changes what it is passed refuses it first.
 */
export function keptOverACallback(): bigint {
  const s = { n: 0n }
  const f = () => s.n
  const done = [bump].map((g) => applied(s, g))
  return done.length > 0 ? f() : 0n
}
export const callback = contract(keptOverACallback, { ensures: { always } })

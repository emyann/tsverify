# Loops and proof code

A law over a loop needs to know what the loop keeps true while it runs: its *invariant*. The verifier guesses one from
each law, and most loops need nothing written. Where a guess is not enough, the code says what the loop keeps, in a call
that does nothing when it runs. This page is about both, and about the other proof code: `assert` and lemmas.

## Invariants the verifier guesses

The largest element of an array, and a spec of it:

<!-- file: src/largest.contract.ts -->
```ts
import { type Implementation, spec } from "@emyann/tsverify"

const largestSpec = spec<(xs: ReadonlyArray<bigint>) => bigint>({
  ensures: {
    noneLarger: ({ input: [xs], output }) => xs.every((x) => x <= output),
    oneOfThem: ({ input: [xs], output }) => xs.length === 0 || xs.includes(output),
  },
})
export type Largest = Implementation<typeof largestSpec>
```

<!-- file: src/largest.ts -->
```ts
import type { Largest } from "./largest.contract.ts"

export const largest: Largest = (xs) => {
  let best = xs.at(0) ?? 0n
  for (const x of xs) if (x > best) best = x
  return best
}
```

<!-- run, exits 1 -->
```text
$ npx tsverify src/largest.ts
src/largest.ts
  ~ largest  1 bounded, 1 proved · 2 obligations  (857 ms)
    ✓ noneLarger  (23 ms)
    ~ oneOfThem  (47 ms)
      not proved: the loop at src/largest.ts:5:3 is read through its invariants alone, and none rules this run out: write one that does, first in its body (`invariant((i) => ...)`); no counterexample with arrays of at most 4 elements
    proof code:
      ✓ invariant on entry: noneLarger, of the elements gone through  (src/largest.ts:5:3)
      ✓ invariant kept by each iteration: noneLarger, of the elements gone through  (src/largest.ts:5:3)

~ 1 bounded
✓ 1 law, 2 obligations proved
  1 contract in 1 file · 1.6 s
```

For a `for…of` loop over one of the function's parameters, the function returning a variable after it, the verifier
restates each law for the elements the loop has gone through: `xs` read as `xs.slice(0, i)`, the result as `best`. Each
restatement is a candidate invariant. It keeps those proved true before the first iteration and kept by every one, all of
them assumed at its start, and drops the rest, round after round until those left hold together. Houdini, the
annotation assistant of ESC/Java (Flanagan and Leino, 2001), works so.

`noneLarger`'s restatement holds: every element gone through is at most `best`. `oneOfThem`'s, that `best` is among the
elements gone through, is not kept: it says nothing of `best` while none has been gone through, so it cannot show that
`best`, left as it was by a first element no larger, is among them after it. So the loop is read without it, and the law
is `bounded`: no array of up to 4 elements breaks it, and nothing proves it. What the guess misses is that `best` is one
of `xs` from the start.

A guess is an obligation like any other, so a wrong one is dropped, never trusted. A fold's laws are often its
invariants: `examples/account/account.ts` folds a ledger in a loop of seven kinds of entry, and with its five written
invariants taken out (`test/account.test.ts`), its five laws are still proved.

## Writing an invariant

`invariant(pred)`, from `@emyann/tsverify`, first in the loop's body, says what the loop keeps. Here, that `best` is always one of
`xs`:

<!-- file: src/largest.ts -->
```ts
import { invariant } from "@emyann/tsverify"
import type { Largest } from "./largest.contract.ts"

export const largest: Largest = (xs) => {
  let best = xs.at(0) ?? 0n
  for (const x of xs) {
    invariant(() => xs.length === 0 || xs.includes(best))
    if (x > best) best = x
  }
  return best
}
```

<!-- run -->
```text
$ npx tsverify src/largest.ts
src/largest.ts
  ✓ largest  2 laws · 4 obligations  (2218 ms)
    ✓ noneLarger  (20 ms)
    ✓ oneOfThem  (19 ms)
    proof code:
      ✓ invariant on entry: () => xs.length === 0 || xs.includes(best)  (src/largest.ts:7:5)
      ✓ invariant on entry: noneLarger, of the elements gone through  (src/largest.ts:6:3)
      ✓ invariant kept by each iteration: () => xs.length === 0 || xs.includes(best)  (src/largest.ts:7:5)
      ✓ invariant kept by each iteration: noneLarger, of the elements gone through  (src/largest.ts:6:3)

✓ 2 laws, 4 obligations proved
  1 contract in 1 file · 2.9 s
```

- **An invariant is proved twice:** true before the first iteration (*on entry*), and kept by each one, from any state
  where it holds (*kept*). Then it is known when the loop ends.
- **`invariant((i) => ...)`** names `i`, how many elements the loop has gone through: `xs.slice(0, i)` is what it has
  seen. An invariant may not name the loop's element. In a `for` or `while` loop, write `invariant(() => ...)` over the
  loop's own variables.
- **Writing one never loses a guess.** When what is written leaves a law unproved, the verifier guesses again beside it:
  `noneLarger` is still guessed here.
- **The call does nothing when it runs**, but it is a call, and it imports `@emyann/tsverify` into the code: the one trace of the
  verifier in code verified through a spec. Prefer the guess; write an invariant where a law needs one.

### How a loop is read

- The **search side** unrolls it: as many iterations as its array has elements (up to 4), or up to 10 passes of a `for`
  or `while`. Every run it finds is real.
- The **proof side** reads it through its invariants: it forgets what the body changes, assumes the invariants, checks
  that one pass keeps them, and knows them after the loop, on the paths that reach its end. A loop left early, by a
  `return` or a `break`, is left by an iteration of the solver's choosing that keeps the invariants, and what holds at the
  end is not known there.
- Besides its invariants, the proof side keeps what the body's own text settles, so an invariant need not say it: a
  variable the body only counts up (`++`, `+= 1`) stays whole if it starts whole and never falls below where it started,
  one only counted down never rises above, and an array the body changes only through its elements keeps its length.

A loop is taken to end. An invariant proves what holds *if* the loop ends; a `for…of` over an array always does, and a
`while` loop's ending is not proved.

### State

A loop is only useful if the code changes something, so the verifier reads `let`, assignment, compound operators (`+=`,
`??=`, `||=`, `&&=`), `++` and `--` on bigints and numbers, `delete`, `push`, `switch` with fallthrough, and writes
through fields, elements at any index and what `.find` or `.at` found. It reads them as Rust's borrow checker would, which keeps aliasing out of the
solver:

- a variable owns what it allocated, and only what is owned changes;
- an argument, and anything reached from one, is borrowed: a change to it is refused;
- a part of an object has one name at a time, so a second is refused;
- a value stored into another object is moved: its old name is dead;
- a value cannot be replaced while something borrows it.

## `assert`

`assert(() => ...)` says what holds where it is written. The verifier proves it there, then knows it after:

<!-- file: src/total.ts -->
```ts
import { assert } from "@emyann/tsverify"

/** The price of `count` items at `each`, less a `discount` no larger than the price. */
export function total(each: bigint, count: bigint, discount: bigint): bigint {
  const price = each * count
  assert(() => price >= discount)
  return price - discount
}
```

<!-- file: src/total.contract.ts -->
```ts
import { contract } from "@emyann/tsverify"
import { total } from "./total.ts"

export const totalNotNegative = contract(total, {
  requires: ({ input: [each, count, discount] }) => each >= 0n && count >= 0n && discount >= 0n && discount <= each * count,
  ensures: { notNegative: ({ output }) => output >= 0n },
})
```

<!-- run -->
```text
$ npx tsverify src/total.contract.ts
src/total.contract.ts
  ✓ totalNotNegative  1 law · 1 obligation  (177 ms)
    ✓ notNegative  (24 ms)
    proof code:
      ✓ assert: () => price >= discount  (src/total.ts:6:3)

✓ 1 law, 1 obligation proved
  1 contract in 1 file · 0.9 s
```

Each obligation is proved with only the proof code written before it, so no `assert` proves itself.

## Lemmas

A lemma is a fact proved once, for every argument its `requires` admits, then known wherever it is called.
`lemma(statement, { requires? })` declares it; the command verifies it as it verifies a contract, its one law `holds`:

<!-- file: src/area.contract.ts -->
```ts
import { type Implementation, lemma, spec } from "@emyann/tsverify"

/** A product of two numbers not below zero is not below zero: proved once, then known where it is called. */
export const productNotNegative = lemma((a: bigint, b: bigint) => a * b >= 0n, { requires: (a, b) => a >= 0n && b >= 0n })

const areaSpec = spec<(width: bigint, height: bigint) => bigint>({
  requires: ({ input: [width, height] }) => width >= 0n && height >= 0n,
  ensures: { notNegative: ({ output }) => output >= 0n },
})
export type Area = Implementation<typeof areaSpec>
```

<!-- file: src/area.ts -->
```ts
import { type Area, productNotNegative } from "./area.contract.ts"

export const area: Area = (width, height) => {
  productNotNegative(width, height)
  return width * height
}
```

<!-- run -->
```text
$ npx tsverify src/area.ts src/area.contract.ts
src/area.contract.ts
  ✓ productNotNegative  1 law  (106 ms)
src/area.ts
  ✓ area  1 law · 2 obligations  (60 ms)

✓ 2 laws, 2 obligations proved
  2 contracts in 2 files · 1.0 s
```

A call proves the lemma's `requires` where it is made, and then knows its statement: `area`'s two obligations, which
`npx tsverify src/area.ts` lists. A lemma may not lean on itself.

Z3 proves many such facts alone: `width * height >= 0n` is proved here without the lemma too. A lemma is for a fact worth
naming and proving once, used in many places, and for one the solver does not find in time where it is needed. The code
imports the lemma at run time, where a call of it does nothing.

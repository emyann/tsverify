# Writing a spec

A spec is what a function must do, written before the function: its type, what a caller promises, and its laws. The
code takes the spec as its type, so a spec is also where the code's signature comes from.

## The spec, then the code

`spec<F>({ requires?, ensures })`, from `tsverify`, takes the function's type as `F`.

- **`ensures`** holds the laws, each named for what it says: the report gives each its own line. A law of a pure function
  is `(...args, result) => boolean`, typed from `F`, so its parameters need no annotation.
- **`requires`** is what a caller promises, `(...args) => boolean`. The laws are checked only on the inputs that meet it.
- **Its type**, `export type StatusSpec = typeof statusSpec`, goes beside it, and is all the code imports: it is typed
  `Implementation<StatusSpec>`. `Implementation<typeof statusSpec>` is the same without the line, the spec exported.

A parcel's status, from a record with two dates that may be missing:

<!-- file: src/parcel.contract.ts -->
```ts
import { spec } from "tsverify"
import type { Parcel, Status } from "./parcel.ts"

const statusSpec = spec<(parcel: Parcel) => Status>({
  requires: (parcel) => parcel.deliveredAt === null || (parcel.shippedAt !== null && parcel.deliveredAt >= parcel.shippedAt),
  ensures: {
    deliveredWins: (parcel, status) => parcel.deliveredAt === null || status === "delivered",
    lostOnlyIfNotDelivered: (parcel, status) => status !== "lost" || (parcel.lost && parcel.deliveredAt === null),
    waitingUntilShipped: (parcel, status) => (status === "waiting") === (parcel.shippedAt === null && !parcel.lost),
  },
})
export type StatusSpec = typeof statusSpec
```

The code declares itself an implementation of the spec, `Implementation<StatusSpec>`, and `tsc` gives it the spec's
type. Both files import only the other's types, so nothing of the spec is in what runs:

<!-- file: src/parcel.ts -->
```ts
import type { Implementation } from "tsverify"
import type { StatusSpec } from "./parcel.contract.ts"

export interface Parcel {
  readonly shippedAt: bigint | null
  readonly deliveredAt: bigint | null
  readonly lost: boolean
}
export type Status = "waiting" | "in-transit" | "delivered" | "lost"

export const statusOf: Implementation<StatusSpec> = (parcel) => {
  if (parcel.deliveredAt !== null) return "delivered"
  if (parcel.lost) return "lost"
  return parcel.shippedAt === null ? "waiting" : "in-transit"
}
```

<!-- run -->
```text
$ npx tsverify src/parcel.ts
src/parcel.ts
  statusOf
    proved          deliveredWins  (122 ms)
    proved          lostOnlyIfNotDelivered  (14 ms)
    proved          waitingUntilShipped  (19 ms)

1 contract in 1 file: laws 3 proved
```

Given files, the command verifies every contract they export: each `const` typed `Implementation<S>`, and each
`contract`, `computation` or lemma. Given a folder, or nothing (the current folder), it reads every file under it that
imports `tsverify`, whatever its name, outside `node_modules` and dot folders. The names are the project's: these pages
write a spec in `*.contract.ts`, which no test runner claims, where Jest and Vitest run every `*.spec.ts` as a test.

**A law says what holds, not how.** `waitingUntilShipped` does not restate the code's `if`s; it says when the parcel waits,
in the record's words. A law that copies the code proves only that the code is the code.

## Async code: laws over what it did

A function that returns a promise is a *computation*: it calls operations on what it is given, and ends in a success or a
failure. Its laws take, after its arguments, how it ended and the calls it made:

- **the outcome**, `{ _tag: "Success", value }` or `{ _tag: "Failure", error }`. A `throw` is a failure, and so is an
  operation's failure the code does not catch.
- **the calls**, in the order made: `{ target, op, args, outcome }` for each call of a method of an argument that returns
  a promise. They are typed from the arguments' types, so checking `op` narrows `args` and `outcome`.

`Rejects<A, E>`, from `tsverify`, is a `Promise<A>` that also says what it rejects with, `E`. A plain `Promise<A>` may
reject with anything: its failure is `unknown`, carried and never read, so a law can say that it failed, not with what.

A store of users, each of its methods an operation:

<!-- file: src/users.ts -->
```ts
import type { Rejects } from "tsverify"

export interface User {
  readonly id: string
  readonly name: string
}

export class NotFound extends Error {
  readonly _tag = "NotFound" as const
}

export class StoreDown extends Error {
  readonly _tag = "StoreDown" as const
}

/** Where users are kept: each method an operation the verifier records. */
export interface Users {
  readonly get: (id: string) => Rejects<User | undefined, StoreDown>
  readonly put: (user: User) => Rejects<void, StoreDown>
}
```

Renaming a user reads it, fails if it is missing, and writes it back renamed. A first spec:

<!-- file: src/rename.contract.ts -->
```ts
import { type Rejects, spec } from "tsverify"
import type { NotFound, StoreDown, Users } from "./users.ts"

const renameSpec = spec<(users: Users, id: string, name: string) => Rejects<void, NotFound | StoreDown>>({
  ensures: {
    readsTheUserFirst: (_users, id, _name, _out, calls) => {
      const first = calls.at(0)
      return first !== undefined && first.op === "get" && first.args[0] === id
    },
    writesNothingWhenMissing: (_users, _id, _name, out, calls) => {
      const first = calls.at(0)
      if (first === undefined || first.op !== "get" || first.outcome._tag !== "Success" || first.outcome.value !== undefined) return true
      return out._tag === "Failure" && out.error._tag === "NotFound" && !calls.some((c) => c.op === "put")
    },
    writesTheNewName: (_users, id, name, out, calls) => {
      if (out._tag !== "Success") return true
      const write = calls.at(1)
      return calls.length === 2 && write !== undefined && write.op === "put" && write.args[0].id === id && write.args[0].name === name
    },
  },
})
export type RenameSpec = typeof renameSpec
```

<!-- file: src/rename.ts -->
```ts
import type { Implementation } from "tsverify"
import type { RenameSpec } from "./rename.contract.ts"
import { NotFound } from "./users.ts"

export const rename: Implementation<RenameSpec> = async (users, id, name) => {
  const user = await users.get(id)
  if (user === undefined) throw new NotFound(id)
  await users.put({ ...user, name })
}
```

<!-- run, exits 1 -->
```text
$ npx tsverify src/rename.ts
src/rename.ts
  rename
    proved          readsTheUserFirst  (99 ms)
    proved          writesNothingWhenMissing  (68 ms)
    counterexample  writesTheNewName  (31 ms)
                    e.g. ({}, "A", "")
                    where users.get gave { id: "", name: "" }, users.put succeeded

1 contract in 1 file: laws 2 proved, 1 counterexample
```

The code is what was meant; the law is not. Asked for `"A"`, the store gave back a user whose id is `""`, and the code
wrote that user renamed. Nothing says a store returns the user asked for, and the law took it for granted. Here the law
should say what the code means, that it writes the user it read:

<!-- file: src/rename.contract.ts -->
```ts
import { type Rejects, spec } from "tsverify"
import type { NotFound, StoreDown, Users } from "./users.ts"

const renameSpec = spec<(users: Users, id: string, name: string) => Rejects<void, NotFound | StoreDown>>({
  ensures: {
    readsTheUserFirst: (_users, id, _name, _out, calls) => {
      const first = calls.at(0)
      return first !== undefined && first.op === "get" && first.args[0] === id
    },
    writesNothingWhenMissing: (_users, _id, _name, out, calls) => {
      const first = calls.at(0)
      if (first === undefined || first.op !== "get" || first.outcome._tag !== "Success" || first.outcome.value !== undefined) return true
      return out._tag === "Failure" && out.error._tag === "NotFound" && !calls.some((c) => c.op === "put")
    },
    writesTheUserItReadRenamed: (_users, _id, name, out, calls) => {
      if (out._tag !== "Success") return true
      const read = calls.at(0)
      const write = calls.at(1)
      if (read === undefined || read.op !== "get" || read.outcome._tag !== "Success" || read.outcome.value === undefined) return false
      return calls.length === 2 && write !== undefined && write.op === "put" && write.args[0].id === read.outcome.value.id && write.args[0].name === name
    },
  },
})
export type RenameSpec = typeof renameSpec
```

<!-- run -->
```text
$ npx tsverify src/rename.ts
src/rename.ts
  rename
    proved          readsTheUserFirst  (87 ms)
    proved          writesNothingWhenMissing  (66 ms)
    proved          writesTheUserItReadRenamed  (12 ms)

1 contract in 1 file: laws 3 proved
```

The other choice was to change the code, `{ ...user, id, name }`, and keep the first law. Either way a person decides
which behaviour is meant; the verifier's part is to show that the two differ, and on what.

**A check of `op` narrows a call wherever it stands.** "The last call", `calls.at(-1)`, is a `get` on a run that fails
and a `put` on one that succeeds; once a law has checked `last.op === "put"`, `last.args[0]` is the user written. Over
every call it is the same: `calls.every((c) => c.op !== "put" || c.args[0].name === name)` reads each `put`'s argument,
and no run reads a `get`'s there.

The Effect adapter reads an Effect program the same way, its operations the methods of the services it requires:
[Effect programs](effect.md).

## Code that already exists

A `function` declaration takes no type annotation, and some code is not yours to change. For those, the spec names the
function instead: `contract(fn, { requires?, ensures })`. The type checker resolves `fn` to its declaration, and each law
is typed from the function's own signature.

<!-- file: src/overdue.ts -->
```ts
/** Whether something due at `due` is overdue at `now`; nothing is overdue that has no due date. */
export function isOverdue(due: bigint | null, now: bigint): boolean {
  return due !== null && due < now
}
```

<!-- file: src/overdue.contract.ts -->
```ts
import { contract } from "tsverify"
import { isOverdue } from "./overdue.ts"

export const overdue = contract(isOverdue, {
  ensures: {
    neverWithoutADate: (due, _now, late) => due !== null || !late,
    lateOnlyAfter: (due, now, late) => !late || (due !== null && now > due),
  },
})
```

<!-- run -->
```text
$ npx tsverify src/overdue.contract.ts
src/overdue.contract.ts
  overdue
    proved          neverWithoutADate  (117 ms)
    proved          lateOnlyAfter  (21 ms)

1 contract in 1 file: laws 2 proved
```

The code imports nothing of `tsverify`, and the spec imports the code. For an async function that exists,
`computation<Ops, E>()(fn, { ensures })` does the same, its calls those of `Ops`, an object of the interfaces it is given;
for an Effect program, `computation<Ops>()` from `tsverify/effect`.

## What a law may do

A law and a `requires` are *spec code*: pure and deterministic. The verifier reads them as it reads the code, and refuses
spec code that runs a computation, calls an operation, reads the clock, or calls a function declared `pure: false`. Spec
code may:

- use what the code may use ([what it reads](reads.md)): comparisons, `&&`, `?:`, optional chains, `.at`, `.some`,
  `.every`, `.includes`, `.filter(p).length`, `.slice`, and `/` and `%` on bigints, where a division by `0n` makes the law
  throw, so not hold (guard it, `b === 0n || …`);
- call the program's own pure functions, read from source, as the code would;
- call a function the spec declares with `assume`, whose laws are then assumed of it.

## A spec at run time

A spec is a plain object, so its laws run: `ChargeSpec.ensures.neverNegative!(5n, 3n, charge(5n, 3n))` is a test. The
same laws can drive property tests, check examples, or guard a value at the edge of a program. Only the code under
verification keeps to `import type`; a test may import the spec.

## Laws that say something

A law is only as good as what it rules out.

- **Vacuous.** A law no result could break, whatever the function returned, says nothing of the function. The verifier
  asks it of every law it proves, and reports `vacuous` rather than `proved`: a law over the inputs alone, or `!A || B`
  whose `A` no allowed input meets.
- **Too strong a `requires`.** A promise no input keeps makes every law vacuous; one that keeps out the inputs that matter
  hides the bugs there.
- **Gaps.** A law can be true and still let a wrong program through. `tsverify/mutants` plants one-line bugs in a function
  and asks which the laws catch; for each one they miss, the solver says whether the planted function equals the original
  for every input, or gives the input where they differ and no law notices ([what the examples show](measurements.md)).

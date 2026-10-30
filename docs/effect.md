# Effect programs

An Effect program is a computation, as an async function is: it runs steps, calls operations, and ends in a success or a
failure. The Effect adapter reads Effect 4's forms into the same model, so a spec of an Effect program reads like a spec of
async code ([Writing a spec](specs.md), *Async code*). What changes is where the operations come from: the services the
program requires.

## A program and its spec

A store of users, as an Effect service, and the errors a rename can fail with:

<!-- file: src/users.ts -->
```ts
import { Context, Data, type Effect } from "effect"

export interface User {
  readonly id: string
  readonly name: string
}

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: string }> {}
export class StoreDown extends Data.TaggedError("StoreDown")<{}> {}

/** Where users are kept: a service, each method returning an Effect an operation the verifier records. */
export class Users extends Context.Service<
  Users,
  {
    readonly get: (id: string) => Effect.Effect<User | undefined, StoreDown>
    readonly put: (user: User) => Effect.Effect<void, StoreDown>
  }
>()("Users") {}
```

The spec is `spec` from `tsverify/effect`, over the program's type, `(...args) => Effect.Effect<A, E, R>`. Each law takes
the arguments, the outcome (`Success` with a value of `A`, `Failure` with an error of `E`) and the calls the program made
to the services of `R`, typed from each service's methods:

<!-- file: src/rename.contract.ts -->
```ts
import type { Effect } from "effect"
import { spec } from "tsverify/effect"
import type { NotFound, StoreDown, Users } from "./users.ts"

const renameSpec = spec<(id: string, name: string) => Effect.Effect<void, NotFound | StoreDown, Users>>({
  ensures: {
    readsTheUserFirst: (id, _name, _out, calls) => {
      const first = calls.at(0)
      return first !== undefined && first.op === "get" && first.args[0] === id
    },
    failsAsNotFoundWhenMissing: (id, _name, out, calls) => {
      const first = calls.at(0)
      if (first === undefined || first.op !== "get" || first.outcome._tag !== "Success" || first.outcome.value !== undefined) return true
      return out._tag === "Failure" && out.error._tag === "NotFound" && out.error.id === id && calls.length === 1
    },
    writesTheUserItReadRenamed: (_id, name, out, calls) => {
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

The program takes the spec as its type, as any implementation does. Its generator's parameters are typed from the spec,
and `tsc` refuses a failure or a service the spec does not declare:

<!-- file: src/rename.ts -->
```ts
import { Effect } from "effect"
import type { Implementation } from "tsverify"
import type { RenameSpec } from "./rename.contract.ts"
import { NotFound, Users } from "./users.ts"

export const rename: Implementation<RenameSpec> = Effect.fn("rename")(function* (id, name) {
  const users = yield* Users
  const user = yield* users.get(id)
  if (user === undefined) return yield* Effect.fail(new NotFound({ id }))
  yield* users.put({ ...user, name })
})
```

<!-- run -->
```text
$ npx tsverify src/rename.ts rename
✓ rename  3 laws  (270 ms)
  ✓ readsTheUserFirst  (93 ms)
  ✓ failsAsNotFoundWhenMissing  (71 ms)
  ✓ writesTheUserItReadRenamed  (7 ms)
  reaches: Success, Failure NotFound, Failure StoreDown
  assumed:
    - The code throws only where it says so (a `throw`, a failure): an exception from anywhere else, a call or a binding never read, is not seen.
    - Each argument has its TypeScript type; the code's own casts, `any` and `!` are refused.
    - A spread copies each property its value's type requires: the value is taken to be plain data, its properties its own, none a getter.
```

- **Each operation can end however its type allows.** `users.get` may give any user, `undefined`, or fail with
  `StoreDown`; the laws are proved for every one of those, in every order the program allows.
- **`reaches:`** lists the ends the program can come to, each found with a witness: a success, `NotFound` and
  `StoreDown`, which passes through from either call.
- **A call records** `{ target, op, args, outcome }`: the service (`users`), the method, its arguments and how it ended.

## Errors a law can read

A failure is the error the program fails with: an object with a `_tag`, which `Data.TaggedError` and `Schema.TaggedError`
build, and its fields. `out.error._tag === "NotFound" && out.error.id === id` reads both.

`Effect.try` and `Effect.tryPromise` run code the verifier does not read, such as `JSON.parse` or `BigInt`. Each succeeds
with any value of its type, or fails with what its `catch` makes of what was thrown. What was thrown is `unknown`, so a
`catch` that passes it on gives the program an error no law can read:

<!-- file: src/amount.contract.ts -->
```ts
import type { Effect } from "effect"
import { spec } from "tsverify/effect"
import type { BadAmount } from "./amount.ts"

const amountSpec = spec<(text: string) => Effect.Effect<bigint, BadAmount>>({
  ensures: {
    namesTheText: (text, out) => (out._tag === "Failure" ? out.error.text === text : true),
  },
})
export type AmountSpec = typeof amountSpec

const looseAmountSpec = spec<(text: string) => Effect.Effect<bigint, unknown>>({
  ensures: {
    failsWithSomething: (_text, out) => (out._tag === "Failure" ? out.error !== undefined : true),
  },
})
export type LooseAmountSpec = typeof looseAmountSpec
```

<!-- file: src/amount.ts -->
```ts
import { Data, Effect } from "effect"
import type { Implementation } from "tsverify"
import type { AmountSpec, LooseAmountSpec } from "./amount.contract.ts"

export class BadAmount extends Data.TaggedError("BadAmount")<{ readonly text: string }> {}

/** The amount a person typed: its error says what they typed. */
export const amountOf: Implementation<AmountSpec> = (text) => Effect.try({ try: () => BigInt(text), catch: () => new BadAmount({ text }) })

/** The same, passing on whatever `BigInt` threw. */
export const looseAmountOf: Implementation<LooseAmountSpec> = (text) => Effect.try({ try: () => BigInt(text), catch: (err) => err })
```

<!-- run, exits 1 -->
```text
$ npx tsverify src/amount.ts
src/amount.ts
  ✓ amountOf       1 law  (183 ms)
    ✓ namesTheText  (139 ms)
  ! looseAmountOf  1 unsupported  (12 ms)
    ! failsWithSomething  (0 ms)
      src/amount.contract.ts:14:67: `===` of a value of type `unknown` is not modeled: such a value is carried and never read; give it a type where it is made (for an error, a `catch` that builds a typed one)

! 1 unsupported
✓ 1 law proved
  2 contracts in 1 file · 1.3 s
```

Build a typed error in `catch`, as `amountOf` does. A program whose errors are typed can be specified; one that carries
`unknown` and sorts it out later with `instanceof` cannot, and is harder to read for a person too.

## What it reads

| Form | How it is read |
| --- | --- |
| `Effect.fn(name)(function* ...)`, `Effect.fn(function* ...)`, `fnUntraced` | the generator's body, step by step |
| `Effect.gen(function* ...)`, a function that returns an Effect | the same |
| `yield* Service` | the service, its methods the operations |
| `yield* service.method(...)` | an operation call: any outcome its type allows, recorded |
| `Effect.succeed`, `fail`, `void`, `sync` | a success or a failure; `sync`'s function is read |
| `Effect.try`, `tryPromise` | any value of the type, or what `catch` makes of a thrown `unknown`; the code it runs is not read |
| `Effect.map`, `flatMap`, `catch`, `catchTag` | as written, the effect first or last |
| `x.pipe(f, g)`, `pipe(x, f, g)` | each function applied in turn |
| `Data.TaggedError`, `Schema.TaggedError` | an error with its `_tag` and fields |

Inside a generator, the core reads `const`, `if`, `return`, `throw` (in async code), blocks, `for (const x of xs)` over an
array, and steps anywhere inside an expression, in the order JavaScript runs them and only on the paths that reach them:
a step after `&&` runs only when the left side is true. A step after `?.` is refused, since it runs only when what is
before it is present: write an `if`.

## What it does not read

An Effect function the adapter does not read is refused where the program calls it, with what to write instead:

<!-- file: src/renameAll.contract.ts -->
```ts
import type { Effect } from "effect"
import { spec } from "tsverify/effect"
import type { StoreDown, Users } from "./users.ts"

const renameAllSpec = spec<(ids: ReadonlyArray<string>, name: string) => Effect.Effect<void, StoreDown, Users>>({
  ensures: {
    readsBeforeWriting: (_ids, _name, _out, calls) => calls.at(0)?.op !== "put",
  },
})
export type RenameAllSpec = typeof renameAllSpec
```

<!-- file: src/renameAll.ts -->
```ts
import { Effect } from "effect"
import type { Implementation } from "tsverify"
import type { RenameAllSpec } from "./renameAll.contract.ts"
import { Users } from "./users.ts"

export const renameAll: Implementation<RenameAllSpec> = Effect.fn("renameAll")(function* (ids, name) {
  const users = yield* Users
  yield* Effect.forEach(ids, (id) => users.get(id))
})
```

<!-- run, exits 1 -->
```text
$ npx tsverify src/renameAll.ts
src/renameAll.ts
  ! renameAll  not verified
    src/renameAll.ts:8:10: `Effect.forEach` is not read: write a `for (const x of xs)` loop of `yield*` steps in the generator

! 1 not verified
  1 contract in 1 file · 1.1 s
```

Beside `forEach`, it suggests what to write for `all`, `mapError`, `as`, `asVoid`, `andThen`, `tap` and `orElseSucceed`.
Defects (`die`, `orDie`), causes (`exit`, `catchCause`), resources (`acquireRelease`, scopes), concurrency (`fork`,
fibers, `race`) and schedules are not read at all.

### Loops of steps

The loop `forEach` names, written as steps:

<!-- file: src/renameAll.ts -->
```ts
import { Effect } from "effect"
import type { Implementation } from "tsverify"
import type { RenameAllSpec } from "./renameAll.contract.ts"
import { Users } from "./users.ts"

export const renameAll: Implementation<RenameAllSpec> = Effect.fn("renameAll")(function* (ids, name) {
  const users = yield* Users
  for (const id of ids) {
    const user = yield* users.get(id)
    if (user !== undefined) yield* users.put({ ...user, name })
  }
})
```

<!-- run, exits 1 -->
```text
$ npx tsverify src/renameAll.ts
src/renameAll.ts
  ~ renameAll  1 bounded  (220 ms)
    ~ readsBeforeWriting  (108 ms)
      proved only of the inputs that run no loop longer: the proof side runs a loop in a computation at most 4 times (src/renameAll.ts:8:3); no counterexample with arrays of at most 4 elements

~ 1 bounded
  1 contract in 1 file · 1.3 s
```

It is read, and the law holds of every run with up to 4 ids, which is all the verifier can say today. A loop of steps over
an array of unknown length is run at most 4 times on the proof side, so no law of its contract is proved, even one the
loop has no part in. A loop over an array of known length, one the program built, is run in full on both sides and can be
proved. Reading a loop of steps through invariants over its calls, as a fold's loop is read, is the next step for this.

## The same laws, async

`examples/hono` is a users API in Hono built both ways, its handlers async functions over a store in `basic/` and Effect
programs requiring it as a service in `with-effect/`; each build's specs hold the same laws, written once in `laws.ts`
([What the examples show](measurements.md), *An HTTP API*). `examples/account/withdraw.ts` is a larger Effect program, a
withdrawal against a ledger service, and `examples/account/withdraw.async.ts` the same program as async TypeScript. Their two specs hold the same five laws, written
once over the outcome and the calls (`examples/account/laws.ts`), and both programs are proved against them: the laws say
what the program does to the world, and neither how it is written nor in which library.

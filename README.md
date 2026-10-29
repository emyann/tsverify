# tsverify

A prototype verifier for ordinary TypeScript. A spec author writes laws as plain predicates. The verifier reads them,
and the code they're about, from source through the TypeScript compiler API. Z3 then proves each law for every input,
or returns an input that breaks it.

It reads pure functions; loops, through the invariants the code carries (proof mode, after Verus); and *computations*:
code that calls operations behind an interface and ends in a success or a failure. Effect is not part of the core. It is
one adapter, beside async/await and plain TypeScript, as `docs/design-2026-10-28-core-and-adapters.md` lays out.

Pinned: Node ≥ 24.16, `z3-solver` 5.3.2, `typescript` 6.0.3. Optional peers: `effect` 4 (the Effect adapter reads its
types; tested on 4.0.6) and `lodash-es` 4 (the lodash pack; tested on 4.18.1).

## Install

It is not on a registry yet, and its version is 0.0.0: `npm pack` here builds it and writes `tsverify-0.0.0.tgz`, which a
project installs as it would any tarball.

```sh
npm install --save-dev ./tsverify-0.0.0.tgz   # in the project; `effect` too for an Effect program
npx tsverify                                  # every spec and implementation under the current folder
npx tsverify src/charge.ts charge             # one contract, with everything it knows
npx tsverify --json                           # the same verdicts as one JSON document, for CI or an agent
```

The command exits 0 when every law and every obligation is proved, 1 when one is not (a counterexample, or a law bounded,
vacuous, unsupported), 2 on a usage error (a path that is not there, nothing to verify, no `tsconfig.json`), and 3 when the
verifier itself fails, which says nothing of the code. `--json` prints one document and nothing else: `passed` (what the exit code
says), `contracts` (each verdict in full: its `file`, its `laws`, `obligations`, `trusted`, `cover` and `notes`, and
whether it `passed`) and `totals`. A counterexample's values are JSON, a value JSON cannot hold written as a string of its
JavaScript text (`"5n"`, `"undefined"`, `"NaN"`); its `world` is what the world gave the code on that run: each operation
call's outcome, each declared function's result.

## In this repository

```sh
npm run verify      # every contract below here, a line per law, then a total
npm run verify -- examples/account                                   # one folder, or one file
npm test            # 196 tests, ~45 s
npm run verify -- examples/charge/charge.ts charge                   # code written against its spec
npm run verify -- examples/order/order.spec.ts status                # a state machine, its doc comment as laws
npm run verify -- examples/account/account.spec.ts folded            # a loop, its invariants written or found
npm run verify -- examples/account/withdraw.ts withdraw              # an Effect program, against its spec
npm run verify -- examples/account/withdraw.async.ts withdraw        # the same program, async
npm run bench       # planted bugs: the solver beside property testing (~15 s)
npm run coverage -- <tsconfig.json> [--modular]                      # how much of a code base it reads
npm run verify -- <file.ts> <export>                                 # one contract, with all it knows
npm run typecheck
```

The command (`tsverify` where the package is installed) exits 0 only when every law is proved and every obligation of the
proof code is. It verifies every implementation of a spec it finds (a file naming `Implementation<`), and every contract
of a `*.spec.ts`. Each file is verified as a program of its own, read through the nearest `tsconfig.json` (or
`--project`), so the declarations it imports are in force for it alone. On this repository it exits 1, on purpose: two examples keep a law the solver refutes, and
`fixtures/vacuous` holds three vacuous laws.

**A law that says nothing is not proved.** A law no result could break, whatever the function returned, is reported
`vacuous`: a law over the inputs alone, or `!A || B` whose `A` no allowed input meets. The verifier asks it of every law
it proves, by giving the law any value of its result's type in place of the function's.

What a program imports, the first two being what a spec and its code import (and the code only its types):
- `tsverify`: what a spec author writes. `spec` and `Implementation`; `contract` and `computation` for code that already
  exists; `assume`; and the proof code `invariant`, `assert`, `lemma`. It has no dependencies, and runs as a test oracle
  too.
- `tsverify/effect`: `spec` and `computation` for an Effect program, typed from the Effect.
- `tsverify/api`: the verifier as a program calls it (`loadProject`, `verify`, `openZ3`, `purityOf`). It changes with the
  verifier.
- `tsverify/mutants`: laws against planted bugs, the solver beside property testing. It changes with the verifier too.
- `tsverify/packs/lodash`: what the verifier may assume of the lodash functions it covers.

## A spec, then the code

The spec comes first. It is the function's type and its laws:

```ts
// charge.spec.ts
import { spec } from "tsverify"

export const ChargeSpec = spec<(balance: bigint, amount: bigint) => bigint>({
  requires: (balance, amount) => balance >= 0n && amount >= 0n,
  ensures: {
    neverNegative: (_balance, _amount, left) => left >= 0n,
    takesWhatItCan: (balance, amount, left) => (amount > balance ? left === 0n : left === balance - amount),
  },
})
```

The code takes it as its type, through a type-only import, so nothing of the spec runs, and is verified against it:

```ts
// charge.ts
import type { Implementation } from "tsverify"
import type { ChargeSpec } from "./charge.spec.ts"

export const charge: Implementation<typeof ChargeSpec> = (balance, amount) => (amount > balance ? 0n : balance - amount)
```

```sh
$ npx tsverify charge.ts
charge.ts
  charge
    proved          neverNegative
    proved          takesWhatItCan
```

- **The spec's type is the code's.** `tsc` refuses a body of another type, and for an Effect program, a failure or a
  service its spec does not declare (`test/withdraw.test.ts`). The verifier finds the spec from that type.
- **A wrong body that type-checks is refuted**, with an input the real code breaks on (`test/charge.test.ts`).
- **Each law is `(args..., result) => boolean`,** typed from the spec's function type. For an async function it is
  `(args..., outcome, calls) => boolean`, the calls those of the operations of its arguments; for an Effect program
  (`spec` from `tsverify/effect`), those of the services the Effect requires, typed from them.
- **At run time a spec is a plain object,** so the same laws work as a test oracle.

### Code that already exists

A `function` declaration takes no type of its own, and some code is not yours to change. For those, the spec names
the function instead, as Verus's `assume_specification` names code it does not own:

```ts
import { contract } from "tsverify"
import { statusOf } from "./order.ts"

export const status = contract(statusOf, {
  ensures: {
    cancelOutranks: (order, s) => order.resolution !== null || !order.cancelRequested || s === "canceling",
    awaitingNeedsASubscription: (order, s) => s !== "awaiting-reorder" || (order.subscription === true && !order.paused),
    placedHasNoShipmentThisRound: (order, s) =>
      s !== "placed" || !order.shipments.some((x) => (x.round ?? 0) === order.reorders.length),
    // ...
  },
})
```

- `contract(fn, { requires?, ensures })` names the function; the type checker resolves the name to its declaration.
  `computation<Ops>()(fn, { ... })` does the same for an async function or an Effect program.
- Each law is type-checked against the function's real signature.
- The code under verification imports nothing from this package, but for proof code (see *Proof mode*).

## The examples

### A state machine: an order's status

`examples/order/order.ts` maps an order's record to one of 10 statuses. It calls `awaitsReorder` and `roundOf`, and its
doc comment states six ordered rules, which `order.spec.ts` turns into 10 laws. `test/order.test.ts` shows:
- **9 laws proved** for every order, with arrays of any length.
- **1 law refuted:** `onItsWay`. The doc comment says "in transit once picked up", but the code tests `pickedUpAt` by
  truthiness, so a shipment picked up at `""` reads `awaiting-pickup`. The type (`string | null`) allows `""`. The
  counterexample is run through the real function, which agrees.
- **All 10 statuses are reachable**, each with a witness order the real function maps to it.
- **The lowering computes what the code computes** on 300 random orders, on both sides.

**Planted bugs.** `npm run bench` plants 17 one-line bugs in the three functions, and one harmless control, and hunts each
two ways: the solver, every counterexample run on the planted code, and property testing over the same laws on seeded,
edge-biased random orders (`examples/order/generate.ts`: every literal, `""`, NaN, -0, Infinity, fractions).

| | solver | property testing, 100 to 10,000 runs |
|---|---|---|
| bugs caught (of 17) | **10**, ~0.5 s each | 10 |
| missed bugs explained | **7 of 7** | none |

- **Both catch the same 10.** On a pure function with a small state space, a well-tuned property tester finds bugs as
  well as the solver does.
- **The solver explains every miss.** For each, it proves whether the planted `statusOf` equals the original for every
  order. Two are harmless in context, proved equivalent (W1, W5), as is the control. Five change a result no law forbids,
  each with the order that shows it: the laws have a gap there, and a person decides which behaviour is intended.

The value over property testing on this kind of code is not catching more bugs. It is proofs instead of samples,
equivalence (is this change behaviour-preserving?), reachability with witnesses, and gap witnesses where the spec is weak.

### A loop: an account folded from its ledger

`examples/account/account.ts` folds a ledger into an account: a `for…of` loop over seven kinds of entry, a `switch`, a
`push`, changes through what `.find` found, bigint arithmetic, and `??=`. Its loop carries five invariants, and
`account.spec.ts` five laws. `test/account.test.ts` shows:
- **The five laws and the ten invariant obligations are proved** for ledgers of every length, in about a second.
- **`requires` matters.** The balance law holds because deposits are positive; without that requirement, the solver
  finds a deposit-only ledger that ends in debt, and running the fold on it agrees.
- **Five planted bugs, five counterexamples**, each confirmed by running the planted fold: a second close that reopens, an
  opening lost after a freeze, a dispute that freezes, a deposit recorded twice, a deposit taken out.
- **A harmless change stays proved.**
- **Without its invariants, nothing is proved.** Every law is `bounded`: unbroken on ledgers of up to four entries, and no
  more than that.
- **The laws hold on 2,000 random ledgers**, run for real; and the purity check reads the fold as pure.

### A computation, twice: a withdrawal in Effect and in async/await

`examples/account/withdraw.ts` is an `Effect.fn` program: it reads the ledger through the `Ledger` service, asks a guard,
fails with `WithdrawalRefused`, or appends one withdrawal. `withdraw.async.ts` is the same program in plain TypeScript:
async, its ledger an interface, its refusal thrown. Each is typed by its spec in `withdraw.spec.ts`, written before it,
and the two specs hold the same five laws, stated once in `laws.ts` over the outcome and the calls made:
- **readsFirst.** The ledger is read first, this account's.
- **readFailurePassesThrough.** A failed read ends the withdrawal with that failure, and nothing else is called.
- **refusedWritesNothing.** A refused withdrawal writes nothing.
- **paidWritesOneWithdrawal.** A paid withdrawal writes exactly one entry, last, to this account: a withdrawal of the
  amount asked, under its id.
- **refusedExactlyWhenTheGuardSays.** The withdrawal is refused exactly when the guard gives words for the ledger read.

`test/withdraw.test.ts` shows:
- **All five are proved on both programs**, and every end each can come to is reachable: success, `WithdrawalRefused` and
  `LedgerError` for the Effect program; success and failure for the async one.
- **Both programs keep all five laws** on 90 runs against a stand-in ledger: 5 ledgers, 3 amounts, 2 account ids, and a
  read or an append that fails.
- **8 bugs planted in each program are all caught**, and each planted program, run, breaks a law the solver refuted:
  writing before the guard, inverting the guard, writing a deposit, writing to another account, writing twice, refusing
  only an empty id, reading another account, writing a fixed amount.

The spec declares the fold pure, `assume(accountOf, { pure: true })`, and the verifier checks that from its source. The
proof is modular: the program's orchestration is proved whatever the fold computes, and the fold's own laws are a
separate proof. Read here, the fold's loop would be one unknown in the program and another in the law, and the law could
not be proved.

## Modes and trust, after Verus

Verus sorts code into three modes. The same three are here, in TypeScript:

| Verus | Here | Rule |
|---|---|---|
| `spec`: pure, deterministic, ghost | the laws and `requires` in `*.spec.ts`, and whatever they call | runs no computation, calls no operation, reads no clock, calls nothing declared `pure: false` |
| `proof`: lemmas, invariants, asserts | typed no-op calls in the program: `invariant(i => ...)`, `assert(() => ...)`, a lemma's call | each proved where it is written, then known; spec code inside |
| `exec`: the compiled code | the program | |
| `assume_specification`, `external_body` | `assume(fn, { pure, ensures? })` | trusted without proof, listed in every report |
| `vstd` | a pack (`tsverify/packs/lodash`) a spec imports | tested against the real library |

**A function the verifier does not read is refused unless declared**, never silently taken as an unknown pure function.
The refusal says what to write:

```
`total` is not read (only `const` bindings are modeled): declare what the verifier may assume of it,
`assume(total, { pure: true, ensures: { ... } })` in the spec, or write its body in the subset the verifier reads
```

**`assume(fn, { pure, ensures })`** (`src/contract.ts`) declares a function of the program or of a package:
- `pure: true`: the same arguments give the same result, and a call changes nothing anyone sees. Where the program has
  the source, **the verifier checks it** (`src/purity.ts`). For a package's function it is trusted.
- `pure: false`: a fresh result per call (the clock, a random number). Spec code may not call it.
- `ensures`: laws over the arguments and the result, assumed at every call, inside quantifiers per element.
- The type arguments are the **view** the laws are written for. `assume<[xs: ReadonlyArray<string>], string[]>(uniq, ...)`
  says what `uniq` does on strings, and `tsc` checks `uniq` can be called so. A call on numbers is refused: no declaration
  covers it.

A declaration is in force when its module is in the program: the spec declares it, or imports a pack that does. It replaces
the function's body, read or not.

**The purity check** refuses:
- an effect: `await`, `yield`, `this`, the clock, `Math.random`, the console, a module's `let`, a function it was given, a
  method or a package function it does not know;
- a change to an object it did not allocate: its arguments, a module's constants;
- a cast or a type predicate, either of which would hide a value's type.

It accepts a function that changes only what it allocated, as a fold builds its state. The hard part is aliasing: a fresh
object can hold the caller's value, and a change made through it reaches the caller. The check records the type of every
value of the caller's it stores into a fresh one, and refuses a change to an object of a type that value could reach
(type-based alias analysis). `test/purity.test.ts` holds 12 impure functions, each refused for its reason, and 5 pure
ones accepted; `test/account.test.ts` accepts the account fold.

**Every report lists what it trusted.** The CLI prints it:

```
  trusted (declared, not proved):
    - accountOf: pure, checked from source (read accountOf, openInto) — examples/account/withdraw.spec.ts:16:32
```

A counterexample that leans on a declared function is marked as such: it holds of the function as declared, and may not
hold of the real one.

### The other ways Effect is written

`examples/account/effects.ts` holds four more programs over the same ledger, each written another way: `balanceOf`, a
function returning `Effect.gen`; `balanceOrZero`, `.pipe` with `Effect.catch`; `doubledBalance`, `pipe(...)` with
`Effect.map`; and `deposit`, an `Effect.fn` whose read is a pipeline of `map` and `catchTag` and whose write is a `flatMap`
of `Effect.sync`. `effects.spec.ts` gives them 13 laws. `test/effects.test.ts` shows:
- **All 13 are proved**, and each program's ends are what its types and handlers allow: `balanceOrZero` can never fail,
  which the verifier proves rather than assumes.
- **The laws hold on 32 runs of each** against a stand-in ledger.
- **A bug planted in each form is caught**, and each planted program, run, breaks a law the solver refuted: a generator
  that reads twice, a `catch` that answers 1, a `map` that triples, a `map` asking the guard of the wrong amount, a
  `catchTag` that lets an unreadable ledger through and one left out, a `flatMap` that writes twice the amount, and a
  `catch` that swallows a failed write.

### Code that may throw, steps inside expressions, loops of steps

`examples/account/imports.ts` takes text written elsewhere. `amountOf` parses what a person typed under `Effect.try`, its
`catch` building a typed error; `depositTyped` runs it as a step inside the arguments of another, `deposit(accountId,
id, yield* amountOf(text))`; `importDeposits` parses an export under `Effect.try` with `catch: (err) => err`, so its error
is `unknown`, then appends each deposit in a loop of steps; `openWith` appends two entries in a loop over an array it
built. `imports.async.ts` writes the same things as plain async TypeScript: an `await` inside an expression, a loop of
`await`s. The core reads both the same way: only `Effect.try` is the Effect adapter's. `test/imports.test.ts` shows:
- **Proved:** `depositTyped`'s 5 laws (an unreadable amount is refused before the ledger is read, and names the text),
  `openWith`'s 3 (a loop over an array of known length is run in full on both sides) and the async `balanceOf`'s 3.
- **Bounded, saying why:** the 8 laws of the two loops over an array of unknown length. On the proof side such a loop runs
  at most 4 times, the inputs kept to those that run it no longer, so what it finds is a real run and what it proves is
  not a proof; the report names the loop.
- **One failure, undistinguished,** where the error is `unknown`: a law can say where `importDeposits` failed, not with
  what. A value of type `unknown` is carried and never read: a law that compares it is refused.
- **The laws hold on 192 runs of each** against a stand-in ledger, and **a bug planted in each form is caught**: a
  `catch` that names no text and one that refuses instead; a ledger read moved inside the step's operand; a loop that
  writes to another account, writes every entry, or passes over a failed write; an opening dropped from the known array;
  and, async, a second read inside the expression, a copy into the source and a copy of every entry.

`fixtures/steps.ts` holds the edge cases: a step inside `&&`, `??` and `?:` runs only on the paths that evaluate its side;
two steps in one call run left to right; a step after `?.` is refused. It keeps `readsWhatItDrops`, which an earlier
version proved calls nothing: a step whose value nothing read was never run. `fixtures/state.ts` keeps `shorthand`, which
it proved returns `0n` when it returns `1n`: a closure kept for later read `{ n }` as `n` was where it was written.

### A package: lodash

`examples/lodash/labels.ts` calls lodash's `uniq` and `clamp`. `packs/lodash.ts` declares what they do on strings and on
numbers. `test/lodash.test.ts` shows:
- **`progress` is proved within its total, from `clamp`'s declared laws.**
- **`labelCount` is proved "none" exactly when it has no labels.**
- **"Several only with two different labels" is true of lodash and not provable from the pack.** The pack says nothing of
  duplicates, so to the verifier `uniq(["a", "a"])` may be `["a", "a"]`. The counterexample says it leans on `uniq`, and
  running the real function on it gives "one". The fix is a stronger pack, not a weaker law.
- **The pack is tested against lodash.** `brokenOn(assumption, inputs)` runs the real function and asks each law. A naive
  `clamp` law ("within its bounds") is caught on `NaN` and on reversed bounds.

No plugin per library: a library needs a pack only for the functions a verified program calls, and nothing at all when its
calls are inside code the verifier does not read.

## Proof mode

Proof code is written in the program, as calls that do nothing when it runs (`src/contract.ts`):

```ts
for (const e of entries) {
  invariant((i) => a.closed === entries.slice(0, i).some((x) => x.kind === "closed"))
  invariant((i) => a.transactions.length <= i)
  // ... the loop's body
}
assert(() => total >= 0n)
productNonNegative(a, b)   // a lemma: lemma((a, b) => a * b >= 0n, { requires: (a, b) => a >= 0n && b >= 0n })
```

- **`invariant(i => ...)`**, first in a loop's body: true before the first iteration, kept by each, and so true at the
  end. `i` counts the elements already gone through. In a `for` or `while` loop, `invariant(() => ...)` speaks of the
  loop's own variables.
- **`assert(() => ...)`**: true here.
- **A lemma**: a statement proved once for every argument its `requires` admits (`npm run verify -- <file> <lemma>`). A
  call proves `requires` there, then knows the statement. A lemma may not lean on itself.

Each is an **obligation**, proved on both sides like a law, or broken with an input. The CLI lists them under `proof code:`
and exits 1 unless every law and every obligation is proved. What one states is then known (a **hint**), but only on the
proof side: the search side checks each hint and never assumes it. Each obligation is checked with the hints written
before it, so no hint proves itself.

**How a loop is read.**
- The **search side** unrolls it: as many iterations as its arrays have elements (4), or up to 10 passes of a `for` or
  `while`, with an assumption that cuts longer runs.
- The **proof side** reads it through its invariants. It forgets what the body changes, assumes the invariants, checks
  that one pass keeps them, and knows them after the loop, on the paths that reach its end. A loop left early (a
  `return`, a `break`) is left by an iteration of the solver's choosing that keeps the invariants, and what holds at the
  end is not known there. (`fixtures/loops.ts` keeps two laws that were wrongly proved before this was so.)

**A loop with no invariant written gets guesses.** For a `for…of` loop of the contract's function over one of its
parameters, the function returning a variable after it, the verifier restates each law for the elements gone through
(`entries` read as `entries.slice(0, i)`, the result as that variable). It keeps the guesses proved on entry and kept by
an iteration, all of them assumed at its start, and drops the rest, round after round until those left hold together
(Houdini, the annotation assistant of ESC/Java, works so). A fold's laws are often its invariants: the account fold's
five are found this way, with none written, and each bug planted in it is still caught, its law's guess dropped
(`test/account.test.ts`). A guess is an obligation like any written invariant, so a wrong one is dropped, never trusted.

A loop with no invariant written and no guess that holds is still read: the search side looks for a counterexample, and
a law that needs what the loop changed is `bounded`, never `proved` (`fixtures/loops.ts`, `sumPlusOne`). A law the proof side proves while an obligation it leaned on is broken or unproved
is searched on the search side too, then reported as a counterexample or as `bounded`, with the reason.

**State.** A loop is only useful if the program changes something, so the lowering reads:
- `let`, assignment, compound operators, `??=`, `||=`, `&&=`, `++` and `--` on bigints;
- `delete`, `push`, `switch` with fallthrough, `for…of`, `for` and `while`;
- writes through fields and elements, and through what `.find` or `.at` found.

It reads them as Rust's borrow checker would, which keeps aliasing out of the solver:
- a variable owns what it allocated, and only what is owned changes;
- an argument, and anything reached from one, is borrowed: a change to it is refused;
- a part of an object has one name at a time, so a second is refused;
- a value stored into another object is moved: its old name is dead;
- a value cannot be replaced while something borrows it.

`fixtures/state.ts` holds four functions proved and six refused, one per rule.

`examples/account/account.ts` is the worked example: an account folded from its ledger, its loop carrying five
invariants. See *The examples*.

## Effect as an adapter

The core knows computations, not libraries:
- **Values:** primitives, records, tagged unions, arrays.
- **Computations:** a body that runs steps (`yield*` or `await`) and ends in `{ _tag: "Success", value }` or
  `{ _tag: "Failure", error }`.
- **Operations:** methods of something the code is given. Each call is recorded in a trace `{ target, op, args, outcome }`
  and ends in any outcome its types allow.

An adapter (`src/adapter.ts`) tells the core which forms are which:

| Adapter | What it reads |
|---|---|
| `src/adapters/ts.ts` | `new Date()`, `Date.now()` (a fresh time per call); `Error` subclasses with field initializers |
| `src/adapters/async.ts` | async functions as computations; `await` steps; methods returning a promise as operations; `Rejects<A, E>` for what a promise rejects with |
| `src/adapters/effect/` | `Effect.fn(...)(function* ...)` and `fnUntraced`; `Effect.gen`, and a function that returns an Effect; `yield*`; `Context.Service` keys as services; methods returning an Effect as operations; `Effect.succeed`, `fail`, `void`, `sync`; `Effect.try` and `tryPromise`, the code they run not read (any value of its type, or what `catch` makes of a thrown `unknown`); `map`, `flatMap`, `catch`, `catchTag`, effect first or last; `x.pipe(f, g)` and `pipe(x, f, g)`; `Schema.TaggedError` and `Data.TaggedError` construction; a `computation` helper typed from the Effect |

A computation's body, in the core, whatever marks its steps: `const`, a step as a statement, `return`, `throw` (async),
`if`, blocks, `for (const x of xs)` over an array, and steps anywhere inside an expression, run in the order JavaScript
evaluates them and only on the paths that reach them.

The core never names a library. What no adapter reads is refused where the code uses it, naming the function: for Effect
today, `forEach`, `exit`, `mapError`, `catchCause`, `die`, concurrency, resources and defects; for promises, `.then` and
`.catch`; and, in a computation's body, `let`, `try`, `switch`, `for`, `while` and `break`.

## How it works

| File | Role |
|---|---|
| `src/contract.ts` | what a spec author writes (`tsverify`): `contract`, `computation`, `assume`, `invariant`, `assert`, `lemma` |
| `src/api.ts` | the verifier as a program calls it (`tsverify/api`): `loadProject`, `verify`, `openZ3`, `purityOf` |
| `src/mutants.ts` | laws against planted bugs, the solver beside property testing (`tsverify/mutants`) |
| `src/trust.ts` | the declarations in force, read from source, and the report's trusted base |
| `src/purity.ts` | the purity check of a declared function's source |
| `packs/` | declarations of a library's functions, tested against the library (`tsverify/packs/lodash`) |
| `examples/` | the worked examples: an order's status, an account's ledger and a withdrawal, a program calling lodash |
| `src/project.ts` | the program (a file's text can be replaced or added in memory), diagnostics, a contract read from source |
| `src/symbolic.ts` | any value of a TypeScript type, built lazily: a field becomes an unknown only when read |
| `src/lower.ts` | pure TypeScript to symbolic values, with JavaScript's semantics |
| `src/exec.ts` | statements: state, places and ownership, loops through their invariants, and the proof code's obligations |
| `src/ops.ts` | truthiness, `===`, `<`, `??` and conditional values, exactly as JavaScript defines them |
| `src/universe.ts` | the Z3 context, its unknowns (one function per path through arrays), assumptions and quantifier scopes |
| `src/concrete.ts` | model to JS values (replay), and JS values to constraints (the translator check) |
| `src/verify.ts` | the queries: laws, reachability, the translator check |
| `src/computation.ts` | outcomes, traces, operations, and the lowering of a computation's body step by step |
| `src/adapter.ts`, `src/adapters/` | the adapter interface and the three adapters |
| `src/cli.ts` | `tsverify`: every contract found, or one by name |
| `bench/mutants.ts` | the planted-bug benchmark on the order example (`npm run bench`) |
| `bench/coverage.ts` | how much of a code base the verifier reads (`npm run coverage -- <tsconfig>`) |

**Two sides.** Each contract is lowered twice:
- The **proof side** keeps arrays of any length and real quantifiers. It may over-approximate: a filtered array is modelled
  by its length as "none or some", and numbers as reals. Its `unsat` is a proof. Its models aren't trusted once an
  approximation was used.
- The **search side** holds arrays to 4 elements, writes quantifiers out element by element, counts filtered elements
  exactly, and keeps numbers to values a double holds exactly. Every model it finds is a real input.

A law the proof side can't settle in time, and the search side can't break, is reported as `bounded`, never as `proved`. A
law proved that no result could break is reported as `vacuous`.

**Every proof is checked against the search side.** The proof side's encoding (havoc, loops read through invariants) is
where a verifier's own bugs hide, and one did: a loop left early was once read as having run to its end. So each proof
is checked against the search side, whose every model is a real input: one query for all the proved laws, one for all the
proved obligations, each obligation asked as the first of the proof code to fail on a run. A proof the search side breaks
is reported `inconsistent`, with the input, as a bug of tsverify rather than a verdict on the code. It costs about a
second on the account fold.

**Numbers.** A `number` is a class (finite, NaN, +∞ or −∞) plus a real value. `===`, `<` and truthiness follow IEEE-754
exactly. Every double is such a value, so proofs cover all doubles. Arithmetic on `number` is refused, since its rounding
isn't modelled. Exact IEEE floats in Z3 were tried first: comparing one with an array length needs `fp.to_real`, which Z3
handled so poorly that queries timed out at 30 s. With the real-valued model, the same queries take milliseconds.

**Supported:**
- primitives, `null` and `undefined`, optional fields, string-literal unions;
- a value of type `unknown`, carried and returned but never read (its truth, `===`, `??` and its fields are refused);
- `const`, `if` with early returns, `?:`, `&&`, `||`, `!`, `??`, `===`, `!==`, comparisons;
- `let`, assignment, `switch`, `for…of`, `for` and `while`, and changes to what the function allocated (see *Proof mode*);
- `+ - *` on bigints, `+` on strings, template strings (an unknown string of their parts);
- property access and optional chains;
- object and array literals;
- calls (inlined), closures, and calls to declared functions;
- `.length`, `.at(k)`, `.filter(p).length`, `.some`, `.every`, `.includes`, `.find` and `.slice` on arrays, and spreads.

**Refused, with a file:line:**
- casts, `!` and `any`, which are claims the verifier would have to trust;
- a member read on a value the type checker hasn't narrowed to non-null at that spot;
- `number` arithmetic, and bigint `/` and `%`;
- `==`;
- a change to an argument or to anything it reaches, a second name for part of an object, a moved value's old name, and
  a change to a value while something borrows it;
- `break` and `continue` to a label, `do…while`, `for…in`, `var`, `a[i] = …` with an index that is not a literal, and
  every array method that changes its array but `push`;
- recursion;
- globals, and functions it cannot read (a package's, or the program's) unless declared;
- in spec code, computations, operations, the clock and functions declared `pure: false`;
- element access `a[i]` with a computed index, string length.

**Checked against the code.** The translator is the part everything else trusts, so the tests check it against the real
function on 300 random inputs, on both sides (`test/order.test.ts`). Every counterexample the benchmark and the tests find
is run on the planted code: a refutation the code does not confirm stops the run as the verifier's bug. Two bugs in the
verifier were caught that way while building it.

## Caveats

- **The code is assumed to throw nothing.** A binding is evaluated only when read, so an exception in an unread binding is
  not seen.
- **Arguments are assumed to have their TypeScript types.** That is sound only for typed callers. Runtime validation is
  where Effect Schema would come in.
- **The examples are the author's own.** The same hand wrote each example, its laws, its planted bugs and the
  property-testing generator, so they show what the verifier reads and catches, not how it fares on code written by
  someone else.
- **No certificate yet.** A result is not bound to hashes of the code, the spec and the tool's version.
- **A declaration is trusted.** A law of `assume` is never proved, and a package's purity never checked. A pack is only
  as good as its tests against the library.
- **The purity check trusts three things,** and every report that leans on it says so: a property read runs no getter, a
  module constant is never changed by other code, and the function terminates. Its alias analysis relies on types, which
  is why it refuses casts and type predicates.
- **A declaration is in force across the whole program**, wherever it is written. Two specs in one program share them.
- **A loop of steps over an array of unknown length bounds its whole contract.** The proof side runs it at most 4 times,
  so no law of that contract is proved, not even one the loop has no part in; each is bounded at best.
- **What `Effect.try` runs is not read, nor recorded.** Its success is any value of its type; the trace holds operations
  only, so a law sees the try through the outcome alone.
- **A loop is assumed to end.** An invariant proves what holds *if* the loop ends (partial correctness); `for…of` over an
  array always does, but a `while` loop's termination is not proved.
- **Proof calls run.** `invariant`, `assert` and a lemma's call are no-ops, but they are calls, and their arguments are
  closures allocated each time. A loop pays for them at run time.
- **The terms a verification keys by are kept alive** until the process ends, because Z3 reuses the id of a term it has
  freed. A long-lived process verifying many contracts grows.
- **A pack ships as TypeScript.** Its laws are functions the verifier reads, so `tsverify/packs/lodash` points its types
  at its source: a project's `tsc` checks that file under the project's own options.

## How much of a code base it reads

`npm run coverage -- <tsconfig.json>` lowers every exported function and every exported computation (`Effect.fn`) of a
project, every callee inlined, runs each computation a function returns, and prints how many it reads and the first
refusal of each of the others, grouped by reason, most frequent first. `--effect` counts the Effect computations alone,
and `--names` keeps the names in the reasons, so a refusal of a library function groups by the function. With `--modular`, each
function is read on its own, every callee the purity check accepts taken as declared `pure`: what a spec gets by writing
one declaration per helper. The refusals are the verifier's to-do list for that code base.

## Building and packing

The repository runs its TypeScript source and no build. Each entry of `exports` names its source under a condition of
its own, `tsverify-source`: `tsconfig.json` sets it in `customConditions`, and every script passes
`--conditions=tsverify-source`, so a test that imports `tsverify` gets `src/contract.ts`. A project that installs the
package sets no such condition and gets `dist/`: `npm run build` emits it (JavaScript and declarations, through
`tsconfig.build.json`), and `npm pack` runs the build first. The verifier knows its own modules by package, the nearest
`package.json` named `tsverify`, and by their path in it, source or built (`ownModule` in `src/project.ts`), so a spec
reads the same whether it imports this checkout, a linked copy or an installed one.

`test/install.test.ts` packs the package, installs the tarball into a new project with some of the examples copied in,
and asks the installed command what the source answers on the same files: the same verdicts. It also checks that the
tarball holds nothing but the build and the packs, and that a planted bug's counterexample breaks the installed code when
it runs. It needs `npm` and, when the npm cache lacks a dependency, the network.

## Next

- Integer division (`/` on bigints, which truncates toward zero) and a string's `length` (its UTF-16 code units): the
  first two refusals a new project's first spec met.
- The next forms, by how often they stop real code: `instanceof` on a value of type `unknown` and `Effect.die`, which a
  `catch` after `Effect.try` uses to keep the errors it knows and die of the rest; `Effect.exit`, `forEach`, `mapError`,
  `catchCause`, `suspend`; destructuring with rest or defaults; `let` in a computation's body.
- A loop of steps read through invariants over the trace, as a fold's loop is read through its own, so a law of such a
  contract can be proved and not only bounded.
- Contracts on operations, assumed by every caller and proved by each implementation (a layer, a class).
- More guesses, so fewer invariants are written: for `while` and `for` loops, for loops in a callee, and from a
  computation's laws over its trace.
- Termination: a `decreases` measure for `while` loops and recursion, as Verus has.
- Packs for the most-called libraries, each tested against its library; a check of a package's purity from its JavaScript.
- Equivalence as a first-class check: "this refactor preserves behaviour", run on a diff.
- A versioned report bound to source hashes.
- A first release: a license, a version past 0.0.0, and the registry.

# effect-verify

A prototype verifier for ordinary TypeScript. A spec author writes laws as plain predicates. The verifier reads them,
and the code they're about, from source through the TypeScript compiler API. Z3 then proves each law for every input,
or returns an input that breaks it.

It reads pure functions, loops through the invariants the code carries (proof mode, after Verus), and *computations*: code that calls operations behind an interface and ends in a success or a
failure. Effect is not part of the core. It is one adapter, beside async/await and plain TypeScript, as
`docs/design-2026-10-28-core-and-adapters.md` lays out. (The repository's name predates that decision.)

The starting point was a design handoff, `docs/handoff-2026-10-28.md`. That document is a hypothesis, and parts of it were
changed on evidence: see *What changed from the handoff*.

Pinned: Node ≥ 24.16, `z3-solver` 5.3.2, `typescript` 6.0.3, `effect` 4.0.6 (used only by the Phase 0 spike).

```sh
npm test            # 120 tests, ~30 s
npm run pilot       # verify Nemia's lifecycleOf against its laws
npm run verify -- pilots/fold/fold.spec.ts folded       # Nemia's fold, through its loop's invariants (~2 s)
npm run verify -- pilots/stop/stop.spec.ts effectStop   # Nemia's requestStop (Effect) against five laws
npm run verify -- pilots/stop/stop.spec.ts asyncStop    # its async twin, against the same five
npm run bench       # planted bugs: the solver vs property testing (~20 s)
npm run verify -- <spec.ts> <export>
npm run typecheck
```

The pilot and the benchmark read `../hkb-v2` in place. They change nothing there.

## A spec

```ts
import { contract } from "../../src/contract.ts"
import { lifecycleOf } from "../../../hkb-v2/packages/agent-runtime/src/core/domain.ts"

export const lifecycle = contract(lifecycleOf, {
  ensures: {
    stopOutranks: (state, s) => state.settled !== null || !state.stopRequested || s === "stopping",
    inputRequiredNeedsHoldOpen: (state, s) => s !== "input-required" || (state.holdOpen === true && !state.closed),
    submittedHasNoAttemptThisTurn: (state, s) =>
      s !== "submitted" || !state.attempts.some((a) => (a.turn ?? 0) === state.inputs.length),
    // ...
  },
})
```

- `contract(fn, { requires?, ensures })` names the function. The type checker resolves that name to its declaration, which
  is the link from spec to code.
- Each law is `(args..., result) => boolean`, and is type-checked against the function's real signature.
- At run time the contract is a plain object, so the same laws work as a test oracle.
- The code under verification imports nothing from this package.

## The pilot: Nemia's `lifecycleOf`

`lifecycleOf` (agent-runtime, `src/core/domain.ts`) maps a task's journal state to one of 9 lifecycle states. It calls
`waitsForInput` and `turnOf`. The spec turns the six ordered rules of its doc comment into 10 laws. `npm run pilot` gives:

- **9 laws proved** for every state, with arrays of any length, each in 4–130 ms.
- **1 law refuted:** `inFlight`. The doc comment says "working once spawned", but the code tests `last.spawnedAt` by
  truthiness. An attempt whose `spawnedAt` is `""` therefore reads `starting`. The type (`string | null`) allows `""`; the
  runtime never writes it. Either the domain says `spawnedAt` is never empty, or the code says `!== null`. That choice is
  the code owner's.
- **All 9 lifecycle states are reachable.** Each comes with a concrete witness state, and the tests run that state through
  the real function.

### Benchmark: 17 planted bugs and one harmless control

`npm run bench` plants one-line bugs in the three functions and hunts each one two ways:
- the solver, with each counterexample replayed on the planted code;
- property testing over the same laws, on seeded random states from `pilots/lifecycle/generate.ts`. That generator is
  edge-biased: every literal, `""`, NaN, -0, Infinity, fractions, arrays of 0–4 elements.

A bug counts as caught when a law that holds on the original fails on the planted copy.

| | solver | property testing, 100 runs | property testing, 1,000–100,000 runs |
|---|---|---|---|
| bugs caught (of 17) | **10**, ~0.75 s each | 9 | 10 |
| missed bugs explained | **8 of 8** | — | — |

- **Both methods catch the same 10 bugs.** The solver's only lead is T2, which sampling first catches at run 110. On a pure
  function with a small state space, a well-tuned property tester is as good at *finding* bugs. That generator was tuned by
  someone who knew the edges: it reaches `input-required` in only 4 of 2,000 states.
- **The solver explains every miss; sampling explains none.** For each missed bug, it proves whether the planted
  `lifecycleOf` equals the original for every state:
  - **Harmless in context, proved:** W1 and W5 (a `waitsForInput` change that `lifecycleOf` returns before reaching) and
    the control E1.
  - **A gap in the laws, with a witness:** L6, W2, W3, W4 and T1. Each comes with a state whose result the bug changes
    while no law forbids it. For example, L6 turns `submitted` into `ending` for a held-open task with nothing attempted.
    This is the weak-spec signal the handoff thought formal methods could not give. Mutants plus equivalence give it
    concretely. A person still decides which behaviour is intended.

The value over property testing on this kind of code is therefore not catching more bugs. It is:
- proofs instead of samples;
- equivalence (is this change behaviour-preserving?);
- reachability with witnesses;
- gap witnesses that show where the spec is weak.

## Computations: `requestStop` and its async twin

`requestStop` (hkb-v2, `agent-runtime/src/core/engine/filing.ts`) is an `Effect.fn` verb. It reads the journal through the
`Journal` service, asks a guard, fails with `StopRefused`, or appends a `stop-requested` entry.
`pilots/stop/stop.async.ts` is the same verb in plain TypeScript: async, its journal given as an interface, its refusal
thrown. `pilots/stop/laws.ts` states five laws once, over the outcome and the calls made:
- **readsFirst.** The journal is read first, for this task.
- **readFailurePassesThrough.** A failed read ends the request with that failure, and nothing else is called.
- **refusedWritesNothing.** A refused stop writes nothing.
- **acceptedWritesOneStop.** An accepted stop writes exactly one entry, last, to this task, of kind `stop-requested`.
- **refusedExactlyWhenTheGuardSays.** The request is refused exactly when the guard gives words for the journal read.

`pilots/stop/stop.spec.ts` holds both programs to these laws. `test/stop.test.ts` shows:

- **All five are proved on both programs**, each in 5–100 ms.
- **Every end each program can come to is reachable:** success, `StopRefused` and `JournalError` for the verb; success and
  failure for the twin.
- **The real programs keep all five laws** when run on 24 runs: 4 journals, 2 task ids, and a read or an append that fails.
- **7 bugs planted in each program are all caught.** They are: writing before the guard, inverting the guard, writing the
  wrong kind, writing to another task, writing twice, refusing only an empty id, and reading another task. Each one planted
  in the twin also breaks a law when the planted code is run.

The verifier does not read `fold` (a loop) or `verbTakes` (`.find` on a table). The spec declares both pure,
`assume(fold, { pure: true })`, and the verifier checks that from their source (see *Modes and trust*). The proofs are
modular: the verb's orchestration is proved whatever the helpers compute, and the helpers' own laws are a separate proof,
as `lifecycleOf`'s are. The report lists both under what it trusted.

## Modes and trust, after Verus

Verus sorts code into three modes. The same three are here, in TypeScript:

| Verus | Here | Rule |
|---|---|---|
| `spec`: pure, deterministic, ghost | the laws and `requires` in `*.spec.ts`, and whatever they call | runs no computation, calls no operation, reads no clock, calls nothing declared `pure: false` |
| `proof`: lemmas, invariants, asserts | typed no-op calls in the program: `invariant(i => ...)`, `assert(() => ...)`, a lemma's call | each proved where it is written, then known; spec code inside |
| `exec`: the compiled code | the program | |
| `assume_specification`, `external_body` | `assume(fn, { pure, ensures? })` | trusted without proof, listed in every report |
| `vstd` | a pack (`packs/lodash.ts`) a spec imports | tested against the real library |

**A function the verifier does not read is refused unless declared.** Before, it became an unknown pure function, with a
note. Its purity was assumed, never checked. Now the refusal says what to write:

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

It accepts a function that changes only what it allocated, as `fold` builds its state. The hard part is aliasing: a fresh
object can hold the caller's value, and a change made through it reaches the caller. The check records the type of every
value of the caller's it stores into a fresh one, and refuses a change to an object of a type that value could reach
(type-based alias analysis). `test/purity.test.ts` holds 12 impure functions, each refused for its reason, and 6 pure ones
accepted, `fold` among them.

**Every report lists what it trusted.** The CLI prints it:

```
  trusted (declared, not proved):
    - fold: pure, checked from source (read fold, fileInto, foldInto, endAttempt) — pilots/stop/stop.spec.ts:14
    - verbTakes: pure, checked from source (read verbTakes, stoppable, awaitsWord, waitsForInput) — pilots/stop/stop.spec.ts:17
```

A counterexample that leans on a declared function is marked as such: it holds of the function as declared, and may not
hold of the real one.

### A package: lodash

`pilots/lodash/labels.ts` calls lodash's `uniq` and `clamp`. `packs/lodash.ts` declares what they do on strings and on
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

## Proof mode: Nemia's `fold`, read through its invariants

Proof code is written in the program, as calls that do nothing when it runs (`src/contract.ts`):

```ts
for (const e of events) {
  invariant(() => s.taskId === taskId);
  invariant((i) => s.stopRequested === events.slice(0, i).some((x) => x.kind === 'stop-requested'));
  // ... the loop's body, unchanged
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
  that one pass keeps them, and knows them after the loop.

A loop with no invariant is still read: the search side looks for a counterexample, and a law that needs what the loop
changed is `bounded`, never `proved`. A law the proof side proves while an obligation it leaned on is broken or unproved
is searched on the search side too, then reported as a counterexample or as `bounded`, with the reason.

**State.** A loop is only useful if the program changes something, so the lowering now reads:
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

**The pilot is hkb-v2's own `fold`**, the function that turns a task's journal into its state. `pilots/fold/fold.ts` is a
copy of `fold` and its three helpers, with five `invariant(...)` lines added. `test/fold.test.ts` shows:
- **The copy is hkb-v2's code but for those lines.** Both are parsed and printed with the invariants dropped, and compared.
- **Five laws are proved for journals of every length, and the ten invariant obligations with them, in about 2 s:**
  - the task keeps its id;
  - a stop is requested exactly when the journal holds a stop request;
  - closed exactly when it holds a close;
  - no more attempts than events;
  - settled only when it holds a settlement.
- **Five planted bugs, five counterexamples.** Each breaks the law it targets, and running the planted code on the
  counterexample's journal confirms it: a second stop request taking the first back, a close lost after an answer, an
  admission that settles, an admission that starts two attempts, a filing that renames the task.
- **A harmless change stays proved.**
- **Without the invariants, nothing is proved.** All five laws are `bounded`: unbroken on journals of up to four events,
  and no more than that.
- **2,000 random journals:** the copy and hkb-v2's `fold` give the same state, and every law holds.

Before this round, `fold` could only be *declared* pure (`assume`): its body, a loop that changes its state, was not read.

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
| `src/adapters/effect/` | `Effect.fn(...)(function* ...)`; `yield*`; `Context.Service` keys as services; methods returning an Effect as operations; `Effect.succeed`, `fail`, `void`; `Schema.TaggedError` and `Data.TaggedError` construction; a `computation` helper typed from the Effect |

The core never names a library. What no adapter reads is refused where the code uses it: for Effect today, `pipe`, `map`,
`catch`, concurrency and resources.

## How it works

| File | Role |
|---|---|
| `src/contract.ts` | `contract(fn, laws)`, `computation`, `assume(fn, { pure, ensures })`, what a spec author writes |
| `src/trust.ts` | the declarations in force, read from source, and the report's trusted base |
| `src/purity.ts` | the purity check of a declared function's source |
| `packs/` | declarations of a library's functions, tested against the library |
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
| `src/cli.ts` | `npm run verify` |
| `bench/coverage.ts` | how much of a code base the verifier reads (`npm run coverage -- <tsconfig>`) |

**Two sides.** Each contract is lowered twice:
- The **proof side** keeps arrays of any length and real quantifiers. It may over-approximate: a filtered array is modelled
  by its length as "none or some", and numbers as reals. Its `unsat` is a proof. Its models aren't trusted once an
  approximation was used.
- The **search side** holds arrays to 4 elements, writes quantifiers out element by element, counts filtered elements
  exactly, and keeps numbers to values a double holds exactly. Every model it finds is a real input.

A law the proof side can't settle in time, and the search side can't break, is reported as `bounded`, never as `proved`.

**Numbers.** A `number` is a class (finite, NaN, +∞ or −∞) plus a real value. `===`, `<` and truthiness follow IEEE-754
exactly. Every double is such a value, so proofs cover all doubles. Arithmetic on `number` is refused, since its rounding
isn't modelled. Exact IEEE floats in Z3 were tried first: comparing one with an array length needs `fp.to_real`, which Z3
handled so poorly that queries timed out at 30 s. With the real-valued model, the same queries take milliseconds.

**Supported:**
- primitives, `null` and `undefined`, optional fields, string-literal unions;
- `const`, `if` with early returns, `?:`, `&&`, `||`, `!`, `??`, `===`, `!==`, comparisons;
- `let`, assignment, `switch`, `for…of`, `for` and `while`, and changes to what the function allocated (see *Proof mode*);
- `+ - *` on bigints, `+` on strings;
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
- element access `a[i]`, string length, template strings.

**Checked against the code.** The translator is the part everything else trusts, so the tests check it against the real
function on 300 random states, on both sides. A deliberate bug planted in the translator (empty strings truthy) fails five
tests. It would also have produced a false proof of `inFlight`. In the benchmark, every counterexample is replayed on the
planted code, and two bugs in the verifier were caught that way while building it.

## What changed from the handoff

- **Contracts are read from source only.** Phase 0 imported the spec module to read its Effect Schema representation. A
  spec module's top-level code could then change what the verifier read (`x >= -100` for a source saying `>= 0n`), and a
  custom filter could claim any built-in's id. The verifier now never runs what it judges: `fixtures/never-imported.ts`
  throws on import and verifies.
- **Laws are plain predicates.** `Schema.makeFilter` is opaque at run time, so its meaning came from source anyway. The
  `Struct({ input, output }).check(...)` wrapper added ceremony and nothing more. Reading Effect Schema domains from source
  is not built yet.
- **The target is real code, not `charge`.** The handoff's examples restate the code: the `charge` proof reduced to
  `x = x`. `lifecycleOf` has string unions, optionals, numbers, arrays and calls, the shape of Nemia's pure core. `charge`
  remains as the bigint fixture.
- **Effect pipelines are not modelled.** Scenario B (`Effect.flatMap` composition) is deferred.
- **Not built:** Gate 1's "an output exists for every input" check. Satisfiability and reachability cover most of its value.

Phase 0's findings about Effect 4.0.6 still hold (`spike/dump-representations.ts`):
- built-in checks carry `{ id, payload }`;
- `makeFilter` is opaque at run time;
- `Schema.brand` leaves the representation unchanged;
- `representation` is a public annotation, so it can be forged.

## Caveats

- **The code is assumed to throw nothing.** A binding is evaluated only when read, so an exception in an unread binding is
  not seen.
- **Arguments are assumed to have their TypeScript types.** That is sound only for typed callers. Runtime validation is
  where Effect Schema would come in.
- **One code base.** The pilot is one function family. The benchmark's bugs were planted by the same person who wrote the
  laws, and the property-testing generator was tuned by that person too.
- **No certificate yet.** A result is not bound to hashes of the code, spec and tool versions, as the handoff asked.
- **A declaration is trusted.** A law of `assume` is never proved, and a package's purity never checked. A pack is only
  as good as its tests against the library.
- **The purity check trusts three things,** and every report that leans on it says so: a property read runs no getter, a
  module constant is never changed by other code, and the function terminates. Its alias analysis relies on types, which
  is why it refuses casts and type predicates.
- **A declaration is in force across the whole program**, wherever it is written. Two specs in one program share them.
- **A loop is assumed to end.** An invariant proves what holds *if* the loop ends (partial correctness); `for…of` over an
  array always does, but a `while` loop's termination is not proved.
- **Proof calls run.** `invariant`, `assert` and a lemma's call are no-ops, but they are calls, and their arguments are
  closures allocated each time. A loop pays for them at run time.
- **The terms a verification keys by are kept alive** until the process ends, because Z3 reuses the id of a term it has
  freed. A long-lived process verifying many contracts grows.
- **The tool itself is plain TypeScript, not Effect.**

## How much of a real code base it reads

`npm run coverage -- <tsconfig>` lowers every exported function of a project. On hkb-v2's runtime, orchestrator and api
(2,261 functions):
- **Every callee inlined, nothing declared:** 466 (21%). Runtime 102 of 414, orchestrator 343 of 1,720, api 21 of 127.
- **Each function on its own (`--modular`), every callee the purity check accepts taken as declared `pure`:** 519 (23%).
  That is what a spec gets by writing one declaration per helper.
- **Before proof mode:** 387 inlined and 420 modular. The gain is loops, `let`, `switch`, changes to what a function
  allocated, `.find`, `.slice` and spreads.
- **Earlier:** 507 (22%) counting helpers whose purity was assumed and never checked, and 212 (10%) before that.

Of the exported and module-level functions, the purity check accepts 307 of 953 in the runtime and 1,316 of 3,338 in the
orchestrator. Most of the rest call something impure (an Effect, a package, a method it cannot see into).

The first refusals left, most frequent first (inlined, over the three):
- package functions no pack declares (271);
- a function passed or returned as data (170);
- array methods it does not read (122);
- globals and other bindings it cannot see (109);
- `try` (105);
- generic type parameters (99);
- string methods (67);
- class methods, `async` functions read as plain ones, element access with a computed index, regular expressions.

Exported functions that *return* an Effect are still barely read. They are written `(x) => Effect.gen(...)` or with `pipe`,
which the Effect adapter does not read yet. The probe does not count `Effect.fn` constants at all.

## Next

- The Effect adapter's next forms: `Effect.gen`, `pipe`, `map`, `flatMap`, `catchTag`, `catch`.
- Contracts on operations, assumed by every caller and proved by each implementation (a layer, a class).
- Read hkb-v2's `fold` in place: an invariant that lives in the spec, not the code, attached to a loop by its position.
  Today the invariants are in a copy, held equal to the original by a test.
- Termination: a `decreases` measure for `while` loops and recursion, as Verus has.
- Packs for what hkb-v2 calls most, each tested against its library; a check of a package's purity from its JavaScript.
- Pin `inFlight`'s finding with the code owner: the domain says `spawnedAt` is never empty, or the code says `!== null`.
- Add the five laws the gap witnesses point to, then rerun the benchmark.
- A second real target with different shapes: `decide`'s `observe` (durations, numbers) or a verb guard.
- Turn equivalence into a first-class check: "this refactor preserves behaviour", run on a diff.
- A versioned report bound to source hashes, for a factory gate.

# tsverify: a TypeScript verifier with Effect as an adapter

**Date:** 28 October 2026, revised 29 October. **Status:** the core and both adapters are built for the subset the
withdrawal example needs, and the proof below holds (`test/withdraw.test.ts`). Spec, proof and exec modes and
declarations of unread functions are built, after Verus (*Modes and trust*, *Proof mode*), and the Effect forms
`Effect.gen`, `pipe`, `map`, `flatMap`, `catch`, `catchTag`, `sync`, `try` and `tryPromise`. In the core, a computation's
body runs loops of steps and steps inside expressions, whether a generator or an async function marks them. A spec is
written before the code and is its type (*Spec first*). Operation contracts, a loop of steps read through invariants,
and concurrency are not.

## The answer in one paragraph

The library verifies TypeScript. Effect is not part of its core: it is one **adapter**, a plugin that tells the core what
Effect's constructs mean in the core's own generic terms. Those terms are values, functions, computations that succeed or
fail, and calls to operations behind an interface. A second adapter does the same for `async`/`await`, and plain synchronous
TypeScript (`throw`, `try`) is built in. This is not more ambitious than an Effect-only tool:
- the pure core already exists and never mentions Effect;
- the effects model is the same for Effect and for async code (see *The core's model*);
- the hard parts (loops, library functions, mutation) are hard either way, and are measured on a code base by
  `bench/coverage.ts`.

The adapter boundary is kept honest by building two adapters from the start, and by holding the same laws against an Effect
program and its async twin.

## What Effect gives, and what plain TypeScript needs instead

| Effect makes it easy | Why it matters to a verifier | Plain TypeScript's way, at a cost |
|---|---|---|
| Dependencies are in the type (`R`): `Context.Service` | The boundary of what the code calls is known, so callers assume a service's contract and its layer proves it. One contract spans every program that uses the service | Dependencies passed as interface-typed parameters (dependency injection), or declared with an `extern` hint, LemmaScript-style |
| Failures are typed (`E`), tagged classes | Failure laws are typed and checked: "fails with `StopRefused` only when…" | `throw` is untyped: laws over `unknown`, or a declared `throws` type the verifier checks |
| Every effect point is a `yield*` | Sequencing and the trace of calls are explicit | `await` marks it the same way; in sync code any call may be effectful, so purity must be declared (`pure`/`impure` hints) |
| Schema declares domains and refinements | Preconditions come for free from the types | Written as `requires` |
| Layers compose implementations | Each implementation of a service is one proof obligation, made once | An interface with several classes implementing it, each proved against the interface contract |

So Effect is the best case, not a requirement. The verifier gets more for free from an Effect project and needs more hints
from a plain one. In both, the engine and the laws are the same.

## Packages

```
@x/contract        zero dependencies: contract(), Outcome, Call types; runs as a test oracle and a runtime guard
@x/verify          the core: TypeScript to core terms to Z3; the two sides (proof, search); reports; CLI
  adapters/ts      built in: pure TS, throw/try as failure, calls inlined or opaque
  adapters/async   built in: async/await, interface-typed parameters as operations, rejection as failure
@x/verify-effect   the Effect 4 adapter: Effect.gen/fn, yield*, succeed/fail, map/flatMap/catchTag/catch,
                   Context.Service as operations, tagged errors, Option/Result/Match, Schema as domains
```

`@x/contract` never imports Effect or TypeScript. `@x/verify-effect` is the only package that knows Effect's names. A
project with no Effect never installs it. Today the three are one package, `tsverify`, whose entries split the same
way: `tsverify` (zero dependencies), `tsverify/api`, `tsverify/effect`.

## The core's model

**Values** are what exists today, extended with the measured gaps:
- primitives, `null`, `undefined`;
- records, discriminated unions, arrays, maps and sets;
- `number` as a class plus a real, which is sound for comparisons. Arithmetic needs an integer model with overflow
  obligations, or IEEE floats where rounding matters.

**Computations.** A function the core reads either returns a value, or is a *computation* that ends in an outcome:

```ts
type Outcome<A, E> = { readonly _tag: "Success"; readonly value: A } | { readonly _tag: "Failure"; readonly error: E }
```

On the way it may call **operations**. Each call is recorded in a **trace**:

```ts
type Call = { readonly target: string; readonly op: string; readonly args: ReadonlyArray<unknown>; readonly outcome: Outcome<unknown, unknown> }
```

An Effect program, an async function and a function that throws are all computations. They differ only in how an adapter
recognises the steps:
- Effect: `yield*` of a service method;
- async: `await` of an interface method;
- sync: a call to an `impure` extern.

**Laws over computations** take the arguments, the outcome and the trace: `(…args, outcome, calls) => boolean`. A law
like "refused means nothing written" is then `outcome is StopRefused ⇒ no call with op "append"`, the same sentence for
every adapter.

**Calls**, by what the verifier knows of the callee (borrowed from LemmaScript's extern, impure and havoc):

| Callee | Treatment | Sound because |
|---|---|---|
| A function it can read | Inlined (today) | It is the code |
| A function it cannot or should not read (a fold, in a law about its caller) | Refused unless declared: `assume(accountOf, { pure: true, ensures })`. Then deterministic, the same arguments giving the same unknown result, of which the laws are assumed | Any implementation that keeps the declaration satisfies what is proved; purity is checked where the source is, the laws are trusted |
| An operation (service method, interface method, `impure` extern) | A fresh outcome per call, constrained by the operation's contract when it has one, and recorded in the trace | Any behaviour the contract allows is covered |
| A library function (`uniq`, `Math.max`) | A declaration in a pack the spec imports, tested against the real library; an adapter's model where the library's meaning is the point (`Effect.fail`) | The pack and the model are tested like the translator is |

Opaque calls make proofs modular. A computation's laws (orchestration: what is called, in what order, what fails) are proved
with its pure helpers left opaque. The helpers' laws are proved separately, as the account fold's are. A model that leans on
an opaque call's arbitrary result is an *abstract* counterexample. It is reported as such, never as a concrete input, and it
tells the agent that its code relies on something about the helper that no contract states.

**Contracts for operations** are written once and serve both sides of the boundary:

```ts
export const journal = operations<JournalShape>("engine/Journal", {
  append: { ensures: { … } },
  read: { ensures: { readsWhatWasAppended: … } },
})
```

Every caller assumes them. Every implementation (an Effect layer, a class implementing the interface) is proved against them.

## The adapter interface

An adapter gives the core two things:
1. **Recognisers.** A recogniser takes a node with its type and returns a core term, or nothing. The Effect adapter
   recognises `Effect.fn(name)(function* …)` as a computation, `yield* X` where `X` is a `Context.Service` as the service's
   operations, `yield* svc.m(args)` as a call, `Effect.fail(e)` as a failure, and so on.
2. **Models of its library's functions**, keyed by resolved symbol, versioned with the library (`effect@4.0.6`) and tested
   against the library itself.

Anything an adapter does not recognise is refused with a location, as today. The core never learns a library's names. A
missing construct is added to its adapter, never to the core.

## What we take from LemmaScript, and where we differ

| | LemmaScript 0.6 | This design |
|---|---|---|
| Specs | `//@ requires/ensures` comments inside the function | Laws as TypeScript predicates in a separate spec file, type-checked, runnable as an oracle; the implementing agent cannot edit them |
| Proof hints | `//@ invariant`, `decreases`, `assert`, `ghost` in the code; proofs written in Dafny or Lean | The same hints in the code, in TypeScript; no second language |
| Backend | Dafny (primary) or Lean, through three IRs | Z3 directly; one small core term language once adapters need it |
| Calls across files | Opaque deterministic externs carrying the callee's contract | The same, plus impure operations with a trace |
| Effects, async | Refused (`await` unsupported) | The core's computation model, through adapters |
| `number` | Mapped to `int`, IEEE assumed away | Class plus real: sound for comparisons; arithmetic to come |
| Trust | The generator, by inspection; the prover | The translator tested against the real code; counterexamples replayed; the solver |
| Proofs and regeneration | Generated stubs, additions-only merge of hand proofs | Hints live in the TypeScript, so there is nothing to merge |
| Tools for agents | `lsc info --typed` JSON, a run log | A JSON report per law, gap witnesses, contract lock |

Taken as is:
- the extern, pure, impure and havoc vocabulary;
- "calls into other files are opaque, carrying the callee's contract";
- "the LLM is not trusted, only the prover";
- the additions-only rule, as policy: an agent may add hints, never change a contract;
- the run log.

## Out of scope, reported as such

- concurrency (`Effect.all` with concurrency, `Promise.all` ordering);
- interruption and defects (`Effect.die`, a `throw` inside `Effect.sync`);
- resources and finalizers;
- schedules, retries and timeouts;
- streams;
- time, except as an operation (`Clock`, `Date.now`), which yields a fresh value per call.

A construct here is refused, never read as true.

## Spec first

A spec is written before the code, and the code takes it as its type:

```ts
// charge.spec.ts
export const ChargeSpec = spec<(balance: bigint, amount: bigint) => bigint>({ requires, ensures: { ... } })

// charge.ts: a type-only import, erased, so nothing of the spec runs
import type { ChargeSpec } from "./charge.spec.ts"
export const charge: Implementation<typeof ChargeSpec> = (balance, amount) => ...
```

- **The link is the type.** The verifier reads `Implementation<typeof S>` on a declaration, resolves `S` to its
  `spec<F>({ ... })` and reads the laws written there. `tsc` checks that the code has type `F`: for an Effect program,
  that it fails with no error and requires no service the spec does not declare.
- **The laws are typed from `F`.** `(args..., result)` for a pure function; `(args..., outcome, calls)` for an async
  one, the calls those of its arguments' methods that return a promise; for an Effect program (`spec` from
  `tsverify/effect`), those of the services in the Effect's requirements, read from each service's `Service` shape.
- **Code that exists keeps the other link.** A `function` declaration takes no type, and some code is not yours: for
  those, `contract(fn, …)` and `computation<Ops>()(fn, …)` name the function from the spec, as Verus's
  `assume_specification` names code it does not own.

## The proof of the design: a withdrawal and its async twin

`examples/account/withdraw.ts`, an Effect program, typed by `WithdrawSpec` (`withdraw.spec.ts`):

```ts
export const withdraw: Implementation<typeof WithdrawSpec> = Effect.fn("withdraw")(function* (accountId: string, id: string, amount: bigint) {
  const ledger = yield* Ledger
  const entries = yield* ledger.read(accountId)
  const refused = withdrawalRefusalOf(accountOf(entries), amount)
  if (refused) return yield* Effect.fail(new WithdrawalRefused({ message: refused }))
  yield* ledger.append(accountId, { kind: "withdrawn", at: new Date().toISOString(), id, amount })
})
```

Its twin in plain TypeScript, `examples/account/withdraw.async.ts`, typed by `AsyncWithdrawSpec`:

```ts
export const withdraw: Implementation<typeof AsyncWithdrawSpec> = async (ledger, accountId, id, amount) => {
  const entries = await ledger.read(accountId)
  const refused = withdrawalRefusalOf(accountOf(entries), amount)
  if (refused) throw new WithdrawalRefused(refused)
  await ledger.append(accountId, { kind: "withdrawn", at: new Date().toISOString(), id, amount })
}
```

One set of laws, held against both (`examples/account/laws.ts`):
- **readsFirst.** The first call is `read(accountId)`.
- **readFailurePassesThrough.** When the read fails, the outcome is that failure and nothing else is called.
- **refusedWritesNothing.** A `WithdrawalRefused` outcome means no `append` was called.
- **paidWritesOneWithdrawal.** A success means exactly one `append`, last, to `accountId`, of a withdrawal of the amount
  asked, under its id.
- **refusedExactlyWhenTheGuardSays.** The outcome is `WithdrawalRefused` exactly when the guard gave words for the account
  the ledger folds to (the fold opaque, declared pure).

It holds (`test/withdraw.test.ts`): all five laws proved on both; every end each can come to reachable; each law kept when
the real programs run against a stand-in ledger; and eight bugs planted in each caught, each planted program breaking a
law the solver refuted when it runs.

## Modes and trust, after Verus

Verus classifies code as `spec` (pure, deterministic, ghost), `proof` (lemmas, ghost state) or `exec` (compiled), and calls
into code it does not verify through specifications it trusts without proof: `assume_specification` for a function it did
not write, `external_body` for one whose body it skips, and `vstd`'s specifications of Rust's standard library. Its guide
lists every such mechanism as part of the trusted base.

The design takes the same shape:
- **spec** is the laws and `requires`, and whatever they call. The lowering carries a mode; a binding keeps the mode of the
  code that wrote it. Spec code runs no computation, calls no operation, reads no clock and calls nothing declared
  `pure: false`.
- **exec** is the program.
- **proof** is typed no-op calls the program carries: `invariant(i => ...)` first in a loop's body, `assert(() => ...)`, and
  a lemma's call (`lemma(statement, { requires })`, declared in a spec), the owner's choice over `//@` comments. Each is
  an obligation proved where it is written, then known. See *Proof mode* below.
- **`assume(fn, { pure, ensures })`** is `assume_specification`. Its type arguments are the view its laws are written for,
  which `tsc` checks against the function's own signature. A call no view covers is refused.
- **A pack** is `vstd`: a module of declarations a spec imports. `packs/lodash.ts` is the first.
- **Every report lists its trusted base:** each declaration a verification leaned on, its laws, and whether its purity was
  checked.

Where TypeScript differs:
- **No mode checker in the language.** The verifier enforces the modes as it lowers, and the hints will cost a call at
  run time instead of being erased.
- **Aliasing.** Rust's ownership gives Verus `old(x)` and `final(x)` for `&mut`. TypeScript objects alias freely. The
  purity check (`src/purity.ts`) handles it by types: it records the type of every value of the caller's stored into a
  fresh object, and refuses a change to an object of a type such a value could reach. It refuses casts and type
  predicates, which would defeat that.
- **Undeclared calls.** Verus refuses them, and so does this design. Taking an unread function as an unknown pure
  function, silently, would make code look read whose helpers' purity nobody checked.

## Proof mode: loops, asserts, lemmas

A loop is read twice, once per side:
- **The search side unrolls it**, as far as the side's arrays go (4 elements, or 10 passes of a `for` or `while`), with an
  assumption that cuts longer runs. Every model it finds is still a real input; it proves nothing about a longer one.
- **The proof side reads it through its invariants.** Every variable the body changes becomes an unknown, the invariants
  are assumed of it, and one pass of the body must keep them. After the loop, the invariants hold at `i` = the array's
  length, on the paths that reach its end: how the loop is left is the solver's choice, its end or an iteration that
  returns or breaks, and the invariants at the end are known only on the first. A loop with none is havocked: the proof side knows nothing of what it changed, and a law that needs it is
  `bounded`, never `proved`.

**A loop of steps** (`for (const x of xs) yield* ...`, or `await`) is a computation's, and carries no invariants yet. The
search side runs it as far as its arrays go; so does the proof side when the array's length is bounded (a literal). Over
an array of unknown length the proof side runs it at most 4 times and keeps the inputs to those that run it no longer:
its models are real runs, and its `unsat` is no proof, so every law and obligation of the contract is `bounded` at best,
with the loop named. Each iteration is continued once, from the merged trace of every path that reached its end, so the
code after a body with an `if` is read once per iteration, not once per path.

Each proof call is an **obligation** with a key (`invariant@account.ts:44#kept`), checked on both sides like a law: proved,
or broken with a counterexample run for real. What it states is then a **hint**: the proof side assumes it from there
on, the search side checks it and never assumes it. An obligation is checked with only the hints written before it, so
no hint proves itself. A law the proof side proves while an obligation it leaned on is unproved is not reported proved:
the search side looks for a counterexample, and the law is `bounded` with the reason when none is found.

**A lemma** is a statement proved once, for every argument its `requires` admits, as its own contract (`npm run verify --
<file> <lemma>`); a call proves `requires` there and then knows the statement. A lemma's proof may not lean on itself.

**State.** Proof mode needs a program that changes things, so the lowering reads `let`, assignment, compound
operators, `??=`, `delete`, `push`, `switch` and the three loops. It reads them as Rust would: a variable owns what it
allocated; an argument, or anything reached from one, is borrowed and never changed; a part of an object has one name
at a time (a second is refused, so a change through one is always seen through the other); a value moved into another
object is dead under its old name. `.find` gives a borrow of the element, and a change through it writes the array.
That is what lets a fold, which builds its state by changing it, be read without an alias analysis inside the
solver. Verus has `&mut` from the language; here the lowering refuses what Rust's borrow checker would.

## Open questions for the owner

1. **Proof hints in the code.** Settled: typed no-op calls, checked by `tsc`.
2. **Laws over the trace.** As shown, laws filter `calls` by `op` name. Typed from the spec, a misspelt op is already a
   type error (`c.op === "reed"` compares a union of the real names with a string none of them is).
3. **The name.** Settled: `tsverify`.
4. **Where a loop's invariants live.** Mostly nowhere: a `for…of` loop with none written gets each law, restated for
   the elements gone through, as a guess, and keeps those proved on entry and kept (Houdini's way). The account fold and
   Nemia's `fold` need none written. Where a guess is not enough, the open choice: in the code (a call per iteration and
   an import of `tsverify`), a `//@` comment at the loop (no cost, checked by the verifier, not by `tsc`), or a proof
   file naming the function (no trace in the code; a pointer an edit can break, refused then, never a false proof).

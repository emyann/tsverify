# A TypeScript verifier with Effect as an adapter

**Date:** 28 October 2026. **Status:** the core and both adapters are built for the subset `requestStop` needs, and the proof below holds (`test/stop.test.ts`). Spec and exec modes and declarations of unread functions are built, after Verus (*Modes and trust*). Operation contracts, proof mode (loops, invariants, lemmas) and the wider Effect forms are not built. It supersedes the handoff's framing of an "Effect verifier".

## The answer in one paragraph

The library verifies TypeScript. Effect is not part of its core: it is one **adapter**, a plugin that tells the core what
Effect's constructs mean in the core's own generic terms. Those terms are values, functions, computations that succeed or
fail, and calls to operations behind an interface. A second adapter does the same for `async`/`await`, and plain synchronous
TypeScript (`throw`, `try`) is built in. This is not more ambitious than an Effect-only tool:
- the pure core already exists and never mentions Effect;
- the effects model is the same for Effect and for async code (see *The core's model*);
- the hard parts (loops, library functions, mutation) are hard either way, and are measured: the verifier reads 10% of
  hkb-v2's exported functions today (`bench/coverage.ts`).

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
project with no Effect never installs it. (The repository's name, `effect-verify`, is then wrong; that is the owner's to
choose.)

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
| A function it cannot or should not read (`fold` with its loop) | Refused unless declared: `assume(fold, { pure: true, ensures })`. Then deterministic, the same arguments giving the same unknown result, of which the laws are assumed | Any implementation that keeps the declaration satisfies what is proved; purity is checked where the source is, the laws are trusted |
| An operation (service method, interface method, `impure` extern) | A fresh outcome per call, constrained by the operation's contract when it has one, and recorded in the trace | Any behaviour the contract allows is covered |
| A library function (`uniq`, `Math.max`) | A declaration in a pack the spec imports, tested against the real library; an adapter's model where the library's meaning is the point (`Effect.fail`) | The pack and the model are tested like the translator is |

Opaque calls make proofs modular. A computation's laws (orchestration: what is called, in what order, what fails) are proved
with its pure helpers left opaque. The helpers' laws are proved separately, as `lifecycleOf`'s were. A model that leans on
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

## The proof of the design: `requestStop` and its async twin

`requestStop` (hkb-v2, `agent-runtime/src/core/engine/filing.ts`):

```ts
export const requestStop = Effect.fn('requestStop')(function* (taskId: string) {
  const journal = yield* Journal
  const events = yield* journal.read(taskId)
  const refused = stopRefusalOf(taskId, events.length ? fold(taskId, events) : undefined)
  if (refused) return yield* Effect.fail(new StopRefused({ message: refused }))
  yield* journal.append(taskId, { kind: 'stop-requested', at: new Date().toISOString() })
})
```

Its twin, written in plain TypeScript (in this repository, not in hkb-v2):

```ts
export const requestStop = async (journal: JournalPort, taskId: string): Promise<void> => {
  const events = await journal.read(taskId)
  const refused = stopRefusalOf(taskId, events.length ? fold(taskId, events) : undefined)
  if (refused) throw new StopRefused({ message: refused })
  await journal.append(taskId, { kind: 'stop-requested', at: new Date().toISOString() })
}
```

One set of laws, held against both:
- **readsFirst.** The first call is `read(taskId)`.
- **readFailurePassesThrough.** When the read fails, the outcome is that failure and nothing else is called.
- **refusedWritesNothing.** A `StopRefused` outcome means no `append` was called.
- **acceptedWritesOneStop.** A success means exactly one `append`, to `taskId`, of an event of kind `stop-requested`.
- **refusedExactlyWhenTheGuardSays.** The outcome is `StopRefused` exactly when `stopRefusalOf` (opaque) returned words for
  the folded journal.

The proof of the design:
- all five laws proved on both;
- a planted bug in either caught. For example, appending before the guard, or catching the read's failure.
- each law checked against running the real code with stand-in implementations of the journal.

What it needs that does not exist yet:
- tagged unions;
- the computation model and its trace;
- opaque calls;
- recognisers for the two adapters' forms;
- `new` of a tagged error class;
- `Date` as an operation.

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
- **proof** is not built: typed no-op hints (`invariant(() => ...)`, `assert`, lemmas), the owner's choice over `//@`
  comments.
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
- **Undeclared calls.** Verus refuses them. So does this design now. Before, an unread function was silently an unknown
  pure function. That made 120 of hkb-v2's functions look read whose helpers' purity nobody had checked.

## Open questions for the owner

1. **Proof hints in the code.** Settled: typed no-op calls, checked by `tsc`.
2. **Laws over the trace.** As shown, laws filter `calls` by `op` name. A typed helper per operation set (`calls.of(journal)`)
   would make a misspelt op a type error.
3. **The repository's name**, now that it is not Effect's.

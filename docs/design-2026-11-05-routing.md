# tsverify: each question to the engine suited to it

**Date:** 5 November 2026. **Status:** proposed, nothing built. A plan in six phases: time each question, cap the
slowest one, move to effect 4.1.2, find examples by running the code, ask the spec's own questions of the spec alone,
and check actors over time with TLA+ beside tsverify. Every number below is measured unless it is marked as a
prediction.

## The answer in one paragraph

tsverify asks Z3 two kinds of question. "Is there no input where this fails?" is a proof: Z3 answers it fast, since it
can stop at the first contradiction. "Is there an example?" is a search: to say yes, Z3 must build the whole example, a
record with every field, its arrays and strings, under every fact the code's lowering states for all elements, and
that is where it is slowest. On Nemia's two slowest contracts, the proofs take under ten seconds and the searches take
the rest of five minutes. So the plan sends each question to the engine suited to it: an example is looked for first by
running the code and the laws on generated inputs (fast-check, or Effect's `Arbitrary` where a Schema gives the type),
and Z3 is asked only when none is found; a proof stays Z3's. What happens across steps and actors over time, the
lifetime of a daemon or a session, is a third kind of question, a model checker's: TLA+ beside tsverify, fed by the
contracts tsverify proves.

## What was measured

Nemia's contracts (`emyann/nemia`, on tsverify 0.5.1), run with every Z3 check timed:

| Contract | CI | Here | The proofs | "Can any result break this law?" |
|---|---|---|---|---|
| `rewired`, 8 laws | 398–530 s | 313 s | 0.4 s | 312 s, of which 292 s in 4 queries that ran out of work |
| `approvalRefusal`, 13 laws | 264–514 s | 270 s | 7.3 s, and 1.5 s of obligations | 257 s, of which 95 s in 4 queries that ran out of work |

- **The slow question is the check that a law says something** (`vacuous`): `lawOnAnyResult` in `judge`, asked of
  the search side and then of the proof side. It is a question about the spec, yet every query carries every fact of
  the code's lowering (`u.assumptions`), the quantified facts of `filter`, `find` and the trusted callees' laws among
  them.
- **When it runs out of work, it changes nothing.** The law reads `proved` as before. On `rewired`, 93% of the run
  buys no verdict.
- **At `--work 3000000`** both contracts keep every law proved: `rewired` takes 40 s and `approvalRefusal` 97 s. But on
  `approvalRefusal` all 13 of its says-anything queries then end without an answer on both sides, and so does the
  cross-check of the search side, and the report says nothing of it.
- **Uncached, Nemia's contracts job took 9 to 31 minutes** on every push since 2 November.
- **Reading the TypeScript is about 1% of a run.** On `inheritedLabels` (main, bound 1, work 5M), 0.5 s of 48 s is the
  TypeScript compiler; the rest is Z3.

`inheritedLabels` is a different problem: there the proofs themselves run out of work, on how a loop read key by key is
phrased for Z3 (`design-2026-11-03-maps.md`, and the roadmap's first item). This plan does not replace that work.

## The questions, and who answers each

| Question | It asks for | Today | Proposed |
|---|---|---|---|
| Is the law kept on every input? | none to exist | Z3, proof side | Z3 |
| Where is it broken? | an example | Z3, search side, after a failed proof | running first, before the proof; Z3's search side after |
| Does the law say anything? | an example: a result that breaks it | Z3, search side then proof side, with the code | running, on the spec alone; Z3 only when none is found |
| Which ends are reached? (`cover`) | an example per end | Z3 | running; Z3 for the ends not reached |
| Does the spec decide? (`undecided`) | an example: two results | Z3 | running; Z3 when none is found |
| Can the laws hold together here? (`unmeetable`) | none to exist | Z3, a tenth of the work | Z3 |
| Do the two sides agree? (`inconsistent`) | an example, expected never | Z3, one query | running, on every input generated; Z3 as today |
| Obligations | none to exist | Z3 | Z3 |

## Phase 0: time by question, built in

The measurements above came from a script that wrapped `Solver.check`. Built in, `--json` gives each law's time by
question (proof, says-anything on each side, counterexample search, cover, undecided, unmeetable, cross-check,
obligations) and by end (answered, out of work, out of time).

- **Baseline:** Nemia's 45 contracts, the examples and `fixtures/corpus/`, timed before any later phase.
- **Done when** each later phase states its gain against that baseline.

## Phase 1: the says-anything check, capped and said

- **Cap it at a tenth of a query's work**, as `unmeetable` already is: an answer it cannot give in that already counts
  as "says something".
- **Say when it ended without an answer**, on the law's line, instead of a silent `proved`. Then a lower `--work` in CI
  loses nothing a reader cannot see, and the skill's "in CI, keep the default" can become "lower it, and read the notes".
- **Fold in the roadmap's `canceled` item**: a stop at the work limit named as one, never as "out of time: 5 minutes".
- **Prediction:** `rewired` and `approvalRefusal` each under a minute at the default work, every law still proved.
- **Done when** the baseline's verdicts are unchanged and its time is measured again.

## Phase 2: effect 4.1.2

tsverify is built and tested against effect 4.0.6 (`devDependencies`), and its adapter says it is pinned to that
version (`src/adapters/effect/index.ts`). Its peer range, `^4.0.6`, already admits 4.1.2, effect's latest since
2 November. Moving first means Phase 3's Effect engine is written against the version a project installs today.

- **What changed that bears on tsverify**, from the release notes of 4.0.7 to 4.1.2:
  - `effect/Arbitrary` has the same exports, and is still marked `@stability unstable`; 4.0.7 adds a `concurrency`
    option to `Arbitrary.checkEffect`.
  - 4.1.0's breaking change is to crypto (`effect/Crypto` split into `effect/crypto/*`, `effect/testing/TestCrypto`
    removed): tsverify uses neither.
  - No note names a form the adapter reads (`Effect.fn`, `gen`, `map`, `flatMap`, `catch`, `catchTag`, `try`,
    `Context.Service`, `Schema.TaggedError`). The adapter knows each form by the module of effect that exports it
    (`packageExport`), so an export moved to another module would be refused where code uses it: the tests below show
    whether one was.
- **What changes:** `effect` 4.1.2 in `devDependencies` and the lockfile, the adapter's "Pinned to" line, and the peer
  range.
- **The peer range becomes `^4.1.2`**, the version tsverify is then tested against, as `^4.0.6` follows 4.0.6 today. A
  range that still admitted 4.0.x would promise what no test checks.
- **The order of release.** npm refuses an install where an optional peer is present outside its range: with npm
  11.19, a project holding effect 4.0.6 and a package asking `^4.1.2` fails `npm install` with `ERESOLVE`. So a project
  on effect 4.0.x cannot take the tsverify release that carries `^4.1.2` until it moves effect too. Nemia, on 4.0.6 in
  its three packages and moving to 4.1, takes that release in the same change as its own move, or after it. For any
  other project it is a breaking change of the release (a minor version, before 1.0), said in its notes.
- **Checked by** `npm run typecheck`, `npm run lint`, and the seven test files that import effect, one at a time:
  `effects`, `withdraw`, `imports`, `hono`, `steps`, `defects` and `destructuring`. CI's `ci` runs the rest,
  `docs/effect.md`'s examples among them.
- **Done when** those seven keep every verdict on 4.1.2.

## Phase 3: finding examples by running

### Running the code

The command never runs the code it verifies today: only `mutants.ts` imports a module. Running it means:
- **A child process per contract**, as `--workers` has: a module's top-level code runs there, not in the verifier.
- **Node's type stripping.** A module it cannot load (syntax that does not strip, a path alias, a top-level effect that
  throws) is verified by Z3 alone, and the report says why.
- **Only what may run**: a function the purity check reads as pure, or an async function or Effect program whose world
  is generated (below). Nothing else is run.
- **A contract's laws are plain functions** (`spec(...)` returns them), so they run on `{ input, output }`, and on
  `calls` for a computation, as written.

### Inputs from the types

The checker's types give each parameter a generator description: records, unions told apart by a tag, literals,
arrays and tuples, `Record<string, V>`, `Map`, `Set`, optional fields, `bigint`, `number`, strings, and functions. The
hard part is that most inputs do not meet `requires`: `steps.every((s) => Object.hasOwn(run.steps, s.name))` or
`accepted(factory, change)` almost never hold of values drawn at random. So the description draws from a small world:
- **strings from a pool**: every string literal of the code and the spec, `""`, and a few names, so keys collide and
  `includes`, `hasOwn` and `===` hold as often as not;
- **values reused across fields**: a key of `factory.hires` drawn again for `change.step`;
- **numbers at their edges**: 0, -0, NaN, ±Infinity, fractions, the largest safe integers;
- **arrays no longer than `--bound`**, so a run here and the search side look at the same sizes;
- **`requires` as a filter**, with a budget of discards that the report gives.

### Two engines behind one description

- **fast-check**, by default: a stable, widely used property-testing library, with seeds and shrinking.
- **Effect's `Arbitrary`** (`effect/Arbitrary`, written against effect 4.1.2, Phase 2), where a parameter's type comes
  from a Schema: its refinements and brands (a non-empty string, an integer, a pattern) then shape the inputs, which a
  TypeScript type cannot say. Where no Schema gives the type, building one to feed `Arbitrary.schema` gains nothing over
  fast-check from the same type. Two caveats: the module is still marked `@stability unstable` in 4.1.2, and `effect`
  is an optional peer dependency of tsverify, so a project without Effect never loads it.

### The world a run is given

- **A function given as a parameter** (`phaseOf`, `closeoutOf` in `approvalRefusal`) is a generated function that
  gives the same result for the same arguments.
- **An Effect program's services** are a Layer generated from the spec's operations (`EffectCallsOf<Ops>`): each method
  returns a generated success or a failure of its error type, and records `{ target, op, args, outcome }`, the shape a
  law reads as `calls` (`Call` in `contract.ts`).
- **An async function's interfaces** are generated the same way, a rejection standing for a failure (`Rejects<A, E>`).

### What is routed

In the order a contract is verified:
1. **Every law, on every generated input, before any proof.** A law broken there is a `counterexample`, real by
   construction: no step confirms it on the code, and Z3 is not asked to prove it. While a law is new, and should come
   back broken (the skill's loop, step 2), this is most of what is asked.
2. **The proofs**, Z3's, of the laws not broken.
3. **Says-anything, on the spec alone**: an input that meets `requires` and any result of the output's type; one that
   breaks the law settles it. Only where none is found is Z3 asked, and then of the proof side, where a vacuous law's
   answer, none, is the fast direction.
4. **Ends and `undecided`**: the runs of step 1 show which ends are reached, each with its input; at each input, a
   generated result of another kind that keeps every law shows the spec undecided there. Z3 is asked of what is left.
5. **The cross-check, free**: a law Z3 proved and a run breaks is either a wrong `assume` (a declared law the real
   function does not keep: the run executes the real callee, the proof took its declaration) or a bug of tsverify. The
   report names which, by rerunning with the callee's declared laws checked (`brokenOn`).

### The same verdict on every run

The roadmap's first rule holds here too. Each contract's generator is seeded from its cache key (`contractKey`: the
text of every file its program reads, the settings, the verifier's version), and runs a fixed number of inputs, not a
time. The same code gets the same inputs, and so the same verdicts, on every machine.

### What a verdict means, unchanged

- No new verdict. "No counterexample found in N runs" is not reported as one: it only sends the question on to Z3.
- `bounded` keeps its meaning, Z3's exhaustive search up to `--bound`.
- Each question's line, and `--json`, say which engine answered it: `by: "run"` or `by: "z3"`.

### Done when, and risks

- **Done when** Nemia's baseline keeps its verdicts, but where running finds a counterexample Z3 did not (each such
  one examined by hand); and the share of generated inputs meeting `requires` on Nemia is measured.
- **Prediction:** the says-anything check of a law like `keepsRepos` is answered in milliseconds; every Nemia contract
  verifies in under 10 seconds, and the uncached job in under 2 minutes.
- **Risk: `requires` rarely met.** Then step 1 finds little and Z3 does the work as today: slower, never wrong. The
  discard budget in the report shows it.
- **Risk: running user code.** A module with effects at load time runs them, in a child process. The report names
  every module it loaded.

## Phase 4: the spec's questions of the spec alone

Where Phase 3 leaves a spec question to Z3 (says-anything, `undecided`, `unmeetable`), it is asked of the types,
`requires` and the laws on a free result, with none of the code's facts: so it depends on the spec's text alone, and is
cached by it, asked again only when the spec changes. This is the roadmap's "Checks on a spec alone, before any code"
(`design-2026-11-01-spec-checks.md`), and the two are one item.

- **A change of meaning:** says-anything today counts only inputs where the code returns
  (`searchRuns`); asked of the spec alone, it counts every input `requires` allows. A law broken only where the code
  throws would read as saying something.
- **A report in three parts:** what is proved of the code, what is checked of it up to a bound, and what is checked of
  the spec. The two axes of verification, proving and checking, and the spec's own.

## Phase 5: actors over a lifetime, TLA+ beside tsverify

What happens across steps, actors and crashes ("every parked session is eventually resumed", "one writer at a time")
is a model checker's question, not a contract's. The pilot, its properties and how to choose between TLA+ and Quint are
in `experiment-2026-11-02-tla-and-quint.md`. Liveness needs fairness, which TLC checks and Apalache supports only in
part, so the pilot starts in TLA+. What this plan adds:
- **A trace replayed against the code.** Phase 3's generated world can be scripted instead: a model checker's trace says
  which actor steps and what each service returns, and the runner plays the real code through it, comparing its state
  with the model's at each step. This is how the model is kept from drifting from the code (Quint's
  `@firfi/quint-connect` does the same for Quint, with an Effect API).
- **A proved contract as the model's step.** The model's `decide` takes any result `decide`'s laws allow, not a copy of
  its rules. That needs the laws written in TLA+, and tsverify lowers straight to Z3 terms today (`Val`, `value.ts`):
  this is the first place a second lowering, or a form between the two, is needed. Done by hand for the pilot's two or
  three functions first.
- **Steps cut at service calls.** An Effect program's calls to its services are where another actor can step in: each
  could be one atomic step of the model. Tried by hand in the pilot before anything is generated.
- **What stays by hand:** the world around the actors, who runs when, crashes, leases and timers, is in no function.
- **Bounded:** TLC checks a set size (two daemons, three sessions, two crashes). With each step proved by tsverify for
  every input, that is checking within bounds plus proving of each step, not a proof of the whole.

## Decisions for the owner

1. **A new dependency**: fast-check beside `ink`, `react`, `typescript` and `z3-solver`; or Effect's `Arbitrary` for
   every type (still unstable in 4.1.2, and `effect` made a dependency); or both behind one description, fast-check by
   default. The plan assumes the last.
2. **Running the code verified**, in a child process per contract, and falling back to Z3 alone where a module cannot
   load.
3. **Says-anything asked of the spec alone**, and the change of meaning it brings (Phase 4).
4. **A mode for the inner loop**: only the questions that look for an example, while an agent writes; no proof, and no
   verdict for what it does not find. Its name, and whether it is a mode or `--work` and `--bound` lowered.
5. **Where the phases go in the roadmap's order.** Phases 1 and 2 stand alone and are small; Phase 3 is the large one.
6. **When the raised peer range ships**: `^4.1.2` in tsverify's next minor version, taken by Nemia in the same change as
   its move to effect 4.1, since npm refuses the install on effect 4.0.x.

## Not in this plan

- **The encoding of loops read key by key** (`inheritedLabels`): the roadmap's first item, a separate lever.
- **The laws of one contract in parallel**: each law's queries could run in a process of its own, now that each
  contract has a Z3 context of its own. Not measured.
- **Native Z3**, or another solver beside it (cvc5 for strings): not measured, and no npm package of cvc5 was found.
- **A prover of its own behind Z3** (Dafny, Boogie, Why3), as LemmaScript does through Dafny and Lean: those prove,
  and the time measured here went to finding examples.

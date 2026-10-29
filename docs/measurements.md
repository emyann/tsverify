# What the examples show

Each example in `examples/` was written to measure one thing the verifier claims, and a test holds each measurement below
(`npm test`), but for the planted-bug benchmark on the order example, which `npm run bench` runs and records in
`bench/results.json`. The same hand wrote each example, its laws, its planted bugs and the property-testing generator: they show
what the verifier reads and catches, not how it fares on code someone else wrote.

A planted bug counts as caught only when its counterexample, run on the planted code, breaks the law: a refutation the
code does not confirm stops the run as the verifier's own bug. Two bugs of the verifier were caught that way while it was
built, and the translator is checked against the real function on 300 random inputs, on both sides (`test/order.test.ts`).

## A state machine: an order's status

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
| bugs caught (of 17) | **10**, under a second each | 10 |
| missed bugs explained | **7 of 7** | none |

- **Both catch the same 10.** On a pure function with a small state space, a well-tuned property tester finds bugs as
  well as the solver does.
- **The solver explains every miss.** For each, it proves whether the planted `statusOf` equals the original for every
  order. Two are harmless in context, proved equivalent (W1, W5), as is the control. Five change a result no law forbids,
  each with the order that shows it: the laws have a gap there, and a person decides which behaviour is intended.

The value over property testing on this kind of code is not catching more bugs. It is proofs instead of samples,
equivalence (is this change behaviour-preserving?), reachability with witnesses, and gap witnesses where the spec is weak.

## A loop: an account folded from its ledger

`examples/account/account.ts` folds a ledger into an account: a `for…of` loop over seven kinds of entry, a `switch`, a
`push`, changes through what `.find` found, bigint arithmetic, and `??=`. Its loop carries five invariants, and
`account.spec.ts` five laws. `test/account.test.ts` shows:
- **The five laws and the ten invariant obligations are proved** for ledgers of every length, in about a second.
- **`requires` matters.** The balance law holds because deposits are positive; without that requirement, the solver
  finds a deposit-only ledger that ends in debt, and running the fold on it agrees.
- **Five planted bugs, five counterexamples**, each confirmed by running the planted fold: a second close that reopens, an
  opening lost after a freeze, a dispute that freezes, a deposit recorded twice, a deposit taken out.
- **A harmless change stays proved.**
- **Without its invariants, the five laws are still proved.** The verifier guesses each law, restated for the entries
  gone through, keeps those proved on entry and kept, and proves the laws through them; each bug planted in the fold
  without invariants is still refuted, its law's guess dropped.
- **The laws hold on 2,000 random ledgers**, run for real; and the purity check reads the fold as pure.

## A computation, twice: a withdrawal in Effect and in async/await

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

## An HTTP API: Hono, with async and Effect handlers

`examples/hono` is a users API in Hono: `GET /users/:id` and `PATCH /users/:id` with `{ "name": ... }`. A route only reads
the request and writes the reply. What to answer is its handler's, a function of the store and the request's values that
returns a status and a body, and the handlers are verified. The routes are not: they are Hono's API, `c.req` and
`c.json`, which the verifier does not read, so they are kept to reading and writing and checked by running them.

The handlers are written twice. `handlers.ts` holds async functions given the store as an interface; `handlers.effect.ts`
holds Effect programs that require it as a service, and `app.effect.ts` runs them, turning the store's failure into a 503.
Each takes its type from a spec in `handlers.spec.ts`, and the four specs hold the same laws, written once over the reply
and the store's calls in `laws.ts`: an empty name is a 400 that touches nothing; the user asked for is read first; a user
not found is a 404 and nothing is written; a 200 is the user read, renamed, written once and sent back as written; a store
that fails ends the handler with that failure. `test/hono.test.ts` shows:
- **All 16 laws are proved on both**, and a reply and the store's failure are both reachable.
- **Three bugs planted in each are caught**: a name check against the wrong value, a rename that keeps the old name, a 404
  for a user found.
- **The two apps answer eight requests alike**, run through Hono against a store that keeps every call: a user found and
  missing, a rename, an empty name, a body that is no name, and a store down on the read or on the write. The laws hold of
  every run a handler made, read from the store's calls and the response.

## The other ways Effect is written

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

## Code that may throw, steps inside expressions, loops of steps

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

## A package: lodash

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

## How much of a code base it reads

`npm run coverage -- <tsconfig.json>` lowers every exported function and every exported computation (`Effect.fn`) of a
project, every callee inlined, runs each computation a function returns, and prints how many it reads and the first
refusal of each of the others, grouped by reason, most frequent first. `--effect` counts the Effect computations alone,
and `--names` keeps the names in the reasons, so a refusal of a library function groups by the function. With `--modular`, each
function is read on its own, every callee the purity check accepts taken as declared `pure`: what a spec gets by writing
one declaration per helper. The refusals are the verifier's to-do list for that code base.

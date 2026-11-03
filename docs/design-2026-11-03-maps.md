# tsverify: maps the code builds

**Date:** 3 November 2026. **Status:** released in 0.6.0; since then, unreleased, each contract is verified in a
context of its own, so its verdicts are the same on every run (*Verdicts*). Five of `inheritedLabels`' eight laws are
proved at bound 1; the other three, the search side's speed at two elements and the planted bugs it misses there are
the limit (*The limit*), and the next step is on the roadmap.

## The answer in one paragraph

tsverify reads a map the code builds at keys it computes: a `Record<string, T>` it writes with `out[k] = v` and
`delete out[k]`, a `Map` or a `Set` it fills with `set`, `add` and `delete`, read through `has`, `get` and `size`, and
listed (`Object.keys`, `Object.entries`, a spread, a `for…of`), made distinct with `new Set` and sorted with `.sort()`.
Each is a table: what it held when made, with each write on top. A loop whose passes only write maps or push onto
arrays is read whole on the proof side, with no invariant, and one over a list of distinct keys that writes a map at
its element alone is read key by key. Where a loop is read key by key, each law is asked first with what that loop
writes left unknown. On Nemia's `inheritedLabels`, copied as written, that first round proves `typedWins`,
`droppedAtStart`, `cardOverRuns`, `leftOutOnlyDisagreed` and `leftOutNamesEachRun`: the last two need only what the
first loop pushes onto `leftOut`, which that round still reads. The three laws about which keys the runs agree on, and
what the result holds of them, need what the first loop writes to the map, and reading it runs the solver out of work:
they stay bounded or unknown.

## Why

Nemia's `inheritedLabels` (agent-orchestrator, `src/labels/labels.ts`, at `d77e7c7`) is covered by 19 test rows. Their
sentences are laws over every key: a typed `key=value` wins; `key-` is absent; the card's value beats the runs'; keys
the runs agree on are copied; keys they disagree on go to `leftOut`, unless the card or an edit names them. The function
builds its result in three loops over keys it computes. 0.5.1 refused it at its first line, the spread of a `Set` ("a
spread of a record into an array is not modeled").

The owner's rule: the code is built to satisfy the spec, and is not reshaped for the verifier. `fixtures/maps.ts` is the
function as written, character for character but for quotes and semicolons, checked against `d77e7c7`. The roadmap had
this as "Collections the code changes".

## The model

**A table** (`src/maps.ts`) is a chain of values, none of which changes:
- what the map held when made: nothing; a dictionary it copied (`{ ...given }`); an array's elements (`new Set(xs)`,
  `new Map(pairs)`);
- a write on top (`out[k] = v`, `delete out[k]`, `m.set(k, v)`, `s.add(k)`), under the branch it runs on;
- two paths' tables merged, keeping their common writes once;
- a loop's writes, read whole.

A key's entry is the last write's that names it, else what the table below holds. Both sides read this alike.

**Its keys, listed:**
- **Search side:** exactly JavaScript's order. An object lists array positions first, by number, then the rest as first
  written. A `Map` and a `Set` list as first written. A key deleted and written again goes last.
- **Proof side:** a list of the keys the table holds, each once, in an order not known. The report says so.
- **A table no write changed** (`input.card ?? {}`): listed exactly on both sides, as the dictionary's own entries.

**A loop that only builds** (its passes write maps or push onto arrays the code built before it) is read whole on the
proof side.
- Each write of a pass is a function of the pass's index: whether the pass makes it, at which key, with which value.
- For a key, whether some pass writes it, and the last one that does.
- A pushed array is every pass's pushes in order, read through `.flatMap`'s exact model.

**A loop over a list of keys, each once, that writes a map at its element alone** is read key by key instead.
- The list is a `Set`'s elements, a map's keys listed, or either sorted.
- A key's entry is what the pass at that key writes, where the list holds the key.
- No function of the pass's index is made for it.

Read so, a key's entry is a function of the key alone, which is what lets the first round leave it unknown (below). Read
by the pass's index, the definitions of those functions, with the first loop's lookups and searches inside them, swamped
every query, even for a law that never reads the first loop.

**The first round, with the loop's writes unknown.** Where a loop is read key by key, `verify` asks each law first on a
proof side of its own:
- There, what the loop writes at each key is unknown: whether it writes the key, sets it or deletes it, and each part
  of the value, each a function of the key.
- Any write the pass could make is one of these, so a law proved there holds whatever the loop writes.
- That side reads that law alone, so the other laws' reads do not weigh on it.
- A law proved there is reported `proved` with the reason "proved with what a loop read key by key writes at each key
  unknown…".
- A law it cannot settle is asked on the full proof side, as before.
- The obligations, the search side and the cross-check of each proof against it are unchanged.

## Decisions, and why

1. **`requires: noProto` on the contract.**
   - Writing a string at `__proto__` sets no key: JavaScript's `__proto__` setter ignores a primitive (an object there
     becomes the prototype).
   - Without the `requires`, `typedWins` is false at `__proto__`, and tsverify finds that counterexample.
   - Nemia never meets it: `labelKeyRefusal` refuses `__proto__`, since `LABEL_NAME`
     (`/^[A-Za-z0-9]([-A-Za-z0-9_.]*[A-Za-z0-9])?$/`) needs an alphanumeric at both ends. So the `requires` is the code's
     own invariant, stated where the law can see it.
   - The model writes no key there; of an object written there, that the key is another is an obligation.
2. **Dictionaries inside arrays (`parents[].labels`) are read through two functions per path:** whether the dictionary
   holds a key, and where its entry is.
   - Searching the entries at each read (0.5.1's way), inside the first loop's quantifier, took over five minutes on a
     probe that this reads in 112 ms.
   - What every dictionary of the path keeps is said once, of all of them, and that a held key is an entry's is said
     once of every key.
   - Said at each read instead, a key read inside a quantifier (`key(i − n)`) made a matching loop.
   - A dictionary the code is given outright keeps 0.5.1's reading. With this one on top-level dictionaries,
     `records.test.ts` ran Z3 out of memory on a planted bug, and `zeroFirst` came back bounded.
3. **A `{}` whose type is a dictionary is a table** (`const out: Record<string, string> = {}`), so a write to it at a
   computed key is read. `input.card ?? {}` is then a choice of two tables, listed exactly.
4. **A closure is not changed by a library call that only reads.**
   - `named` reads `card` and `edits`. 0.5.1 counted `Object.hasOwn(card, key)` as a call that may change `card`, and
     `edits.some(...)` as one that may change `edits`, and refused the closure ("a closure kept for later over card").
   - Now a library method changes what the library's table says (`effects.ts`): `xs.push(x)` its receiver,
     `Object.hasOwn` and `.some` nothing. Any other call is read as before.
5. **An empty array merged with another takes the other's element; an array literal with no contextual type takes its
   own.** `value === undefined ? [] : [{ run: p.run, value }]` merged two arrays whose element types differed, and read
   the element as "a maybe of a maybe".
6. **`.flatMap` is exact on the proof side.**
   - Each element's part goes in order, at a place counted from the parts before it, and each place is known to come
     from one part.
   - Order is said of any two places, never of neighbours (`k − 1` inside a function's argument made a matching loop).
   - 0.5.1 knew it only as empty when its array is.
   - What it knows of each place it also states beside its claim (below), and that costs precision:
     the count of a list of three or four elements, doubled into six or eight, may now be left undecided within a
     query's work. That is why `test/maps-constructs.test.ts` asks the proof side for no wrong count, not for every
     count decided.
7. **This fixture runs at bound 1, with a third of a query's work** (`test/maps.test.ts`).
   - At bound 2 the search side runs out of work on every law but the four the first round proves there, and refutes
     none of the planted bugs (*Verdicts*).
   - With the usual work, the queries that do not end hold enough of Z3's memory, one after another, to exhaust it
     within one process.
   - A third of the work is enough for the four proofs, whose queries end in under 2 s at bound 1.
8. **The loop read key by key** (*The model*), and with it the first round with its writes unknown.

Three smaller changes the work showed were needed:
- `solve` and the other queries now release each solver once read, where they waited for the garbage collector; queries
  that run to their limit had piled up past Z3's 2 GB.
- Each quantifier the proof side gains here (a map's keys listed, `.flatMap`, `.sort()`, `new Set`) states what is known
  of each element on its own, as `elementwise` does, as well as under its claim. Under the claim alone, a model could
  break what is known and void the claim. On `fixtures/lists.ts` that let `flat([])` be non-empty, and since `.flatMap`
  is read exactly, the proof side reported it as a counterexample: a wrong verdict, which the suite caught.
- `disagreements`, the translator check, compares a `number` result; it could not before.

## Verdicts

`fixtures/maps.ts`, `inheritedLabelsLaws`, with a third of a query's work (5 million), measured 3 November:

| law | bound 1 | bound 2 |
| --- | --- | --- |
| `typedWins` | proved, first round | proved, first round |
| `droppedAtStart` | proved, first round | proved, first round |
| `cardOverRuns` | proved, first round | proved, first round |
| `agreedInherited` | bounded | unknown |
| `disagreedLeftOut` | bounded | unknown |
| `leftOutOnlyDisagreed` | proved, first round | proved, first round |
| `leftOutNamesEachRun` | proved, first round | unknown |
| `nothingElse` | unknown | unknown |
| time, peak memory | 44 s, 1.2 GB | 61 s, 1.2 GB |

The one obligation, a key read (`p.labels[key]`), is proved. No law is refuted on the code as written.

**The same verdicts on every run.** As released in 0.6.0, `leftOutNamesEachRun` sat at the work limit, and its verdict
at bound 1 changed from run to run: run alone four times on one machine with the same flags, the first round proved it
twice and ran out of work twice, and queries stopped as `canceled` on some runs and not on others. Neither the query
timeout (turned off, the runs still differed) nor V8's collection schedule (pinned by `--predictable-gc-schedule`, and
by flags that stop it marking in the background, which made it worse) was the cause. z3-solver frees each term from a
finalizer, when JavaScript collects the object that holds it, and runs it as soon as the main thread waits, which it
does while Z3 solves on a thread of its own; a term freed hands its number to the next one made, and the numbers order
the solver's search. With no finalizer at all, four runs agreed; with the finalizers held until the next query, five of
eight did. Each contract is now verified in a Z3 context of its own, whose objects no finalizer frees: the context is
deleted with all it holds once the contract's verdicts are read (`ownContext`, `src/verify.ts`). Eight runs alone, two
beside another test file and four without the flag all gave every law the same verdict and reason, and
`test/maps-steady.test.ts` asks it of five runs, each in a process of its own, the last after another contract. z3-solver
has a registry that waits for a running query before it frees, but uses it for a context alone: a term goes to the one
that frees at once. What reads a side `lowerSide` made, on the context `openZ3` returns, still frees as z3-solver does:
`test/maps-constructs.test.ts`'s pinned queries do, and the flatMap counts it leaves undecided sit near the limit. A
query that runs 5 minutes without counting its work is still stopped by a clock, so where it stops hangs on the
machine; none of `inheritedLabels`' does.

**Two laws that do not hold** (`inheritedLabelsWrong`) are refuted at bound 1: that a typed key is never held, and that
a key the runs agree on is never held. The first round proves neither. Each counterexample breaks its law when the
function runs on it.

**Planted bugs,** one against each law proved, each refuted at bound 1 and its counterexample replayed on the planted
code (and kept by the code as written); at bound 2, with the same work, none is refuted, and with the usual work M1's
search ran five minutes without counting its work. M5 leaves out a key the runs agree on, named with none of its runs:
with one run, no key has two values, so a key left out can name its runs wrong only where it should not have been left
out at all.

| plant | law | bound 1 | bound 2 |
| --- | --- | --- | --- |
| M1, a typed edit sets the key's name | `typedWins` | caught, 9 s | not caught: search out of work, 7 s |
| M2, `key-` sets the key empty | `droppedAtStart` | caught, 11 s | not caught: search out of work, 8 s |
| M3, the card's key is given its name | `cardOverRuns` | caught, 13 s | not caught: search out of work, 9 s |
| M4, a key the runs agree on left out too | `leftOutOnlyDisagreed` | caught, 20 s | not caught: search out of work, 9 s |
| M5, a key the runs agree on left out, named with none of its runs | `leftOutNamesEachRun` | caught, 10 s | not caught: search out of work, 14 s |

Each construct is checked against JavaScript (`test/maps-constructs.test.ts`). The search side checks every
construct; the proof side checks those it reads exactly. Each input pins the result, and a wrong one is told apart on
every input.

| construct | search side | proof side |
| --- | --- | --- |
| writes at computed keys in a loop, a write and a delete after | agrees | agrees |
| keys listed: positions first, a key deleted and set again last | agrees | not asked: an order not known |
| a key count after writes and a delete | agrees | not asked: a list of the keys |
| `new Set` spread and sorted; a `Set`'s count | agrees | not asked: `.join`, a count |
| `.flatMap`, joined; its count | agrees | the count: no wrong count; lists of three or four may be undecided |
| a `Map` filled in a loop, `delete`, `has` and `get`; its `size` | agrees | `has` and `get` agree |
| a `Set` filled in a loop, `delete`, iterated; `has`; `size` | agrees | `has` agrees |
| a loop over a `Set` that writes a map at each key, read key by key; its count | agrees | the entry agrees, on lists of none or one |

The proof side's pinned queries through the `Set` → `.sort()` chain run Z3 out of memory, so the key-by-key loop is
checked there over a `Set` directly, on lists of none or one element. Through a `Set` of two or three, each pinned query
agrees alone, in 18 to 47 s, but run one after another in one context, some orders of them run Z3 out of memory. `inheritedLabels` itself is checked through its laws, its plants and the two laws
that do not hold.

## Soundness

- `fixtures/corpus/`: no wrong verdict. `soundness.test.ts` and every corpus file pass.
- Every proof is cross-checked against the search side, the first round's among them.
- The first round's writes are an over-approximation by construction: every write a pass can make is one of them.
- The laws that do not hold, and the planted bugs, are refuted, never proved.
- `leftOutOnlyDisagreed` became provable once the new quantifiers stated what they know beside their claims. Two false
  laws about what the first loop pushes (no key is ever left out; every key left out names fewer than two runs) stay
  unproved by both rounds, `bounded` at bound 1 and `unknown` at bound 2: the facts said beside add precision, not more
  than holds.
- A counterexample is replayed on the code.

## The limit

1. **Three laws stay bounded or unknown:** `agreedInherited`, `disagreedLeftOut`, `nothingElse`.
   - They need what the first loop writes to the map. Read key by key, the pass's body is read at each key the law
     reads, inside the law's own quantifier: `named(key)` (a search of the card's entries and of the edits), the `flatMap` over the runs at
     that key, and `values.every`.
   - Its facts sit in every branch of the lookup, including where a later loop decides the key, and the solver runs out
     of work.
   - With those writes unknown, the first round proves `typedWins` in about a second; read as they are, the same query
     runs to its limit.
2. **The search side at two elements runs out of work** on this function. Two runs, two labels each, are 4 keys through
   a `Set`, a sort, and a pass per key over the runs again. At four elements, the default, it runs longer still.
3. **The planted bugs are caught at bound 1 only.** A law about two runs disagreeing needs two runs, so its plants
   would need bound 2.

**Next** (roadmap): the facts the pass at a key brings, said under the branch that reads that key's entry, so a later
loop that decides the key leaves them aside. That needs the universe to collect a lowering's facts under a condition.
It is not tried here.

## What it cost the solver, learned on the way

- A fact stated at each read inside a quantifier, about a key that is `key(i − n)`, makes a matching loop. Said once of
  every key, the same query is sat in 1.2 s instead of running to its limit.
- A function of a pass's index defined as `cond(i) = φ(i)`, with searches inside `φ`, alternates quantifiers in both
  directions, and blocks laws that never read it.
- On the search side, an order of array positions written in string lengths and `str.<` alone, in place of
  `str.to_int`, was tried beside the sort's own `str.<`: it did not help, and was dropped.
- Z3's memory in one process only grows. A query that runs to its limit leaves hundreds of megabytes behind until its
  solver is released.
- What one context has seen before shapes a query: the same pinned queries, each ending alone, can run Z3 out of memory
  in another order. A test of the proof side keeps to inputs whose queries end in a fraction of a second.
- Z3 reports some queries stopped by their work limit as "canceled", which tsverify reads as "out of time: ran 5 minutes".
  The verdicts above that say so stopped within seconds.

# tsverify: each question to the engine suited to it

**Date:** 5 November 2026. **Status:** Phases 0 and 1 built and measured; Phase 3(a) built and measured (below); the rest proposed. A plan in six phases: time each question, cap the
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

**Built.** Each law's `asked` in `--json` sums its queries by question, side and end, and each contract's `asked` its
own questions; each contract has its whole `ms` (`docs/verdicts.md`, *`--json`*).

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

**Built.** The check is asked at a tenth of `--work` on both sides. One it cannot settle leaves the law `proved`, with
a note, and so does a cross-check, `unmeetable` or `undecided` that ends without an answer. A stop Z3 calls `canceled`
before the 5 minutes is named "out of work".

### Measured: the baseline, then the cap

**How.** Each target was run with this checkout's CLI, `--json`, without `--cache`, one command at a time, on a machine
other work shares (WSL2, 12 cores, 15 GB). The targets were each of Nemia's four roots as one folder
(`tools/contracts/legs.ts`, `ROOTS`), each folder of `examples/` and each file of `fixtures/corpus/`. The baseline is
tsverify at cfdf956 (Phase 0 alone). After is 7455ec1 (Phase 1), whose code is that of this change's head. Nemia's
`main` moved three times while the baseline ran, so both trees read one frozen copy of Nemia at ab395d4, taken with
`git archive`, its `node_modules` linked to the checkout's. Nothing was written into the checkout. `--json` asks
`cover`, which CI's text run does not: *less cover* is a contract's time without its cover queries, which is what CI
pays. A difference under about 20% is noise here: the same query, stopped at the same work, took 12.6 s in one run and
23.7 s in the other.

**Verdicts.** 137 contracts and 506 laws were measured. Every law's status and counterexample are the same before and
after. Five reasons changed, each from "out of time: the query ran 5 minutes" to "out of work": the queries had stopped
at the work limit after 5 to 93 seconds, and Z3 had reported each stop as `canceled`. They are
`assoc`, `iffEqual` (`fixtures/corpus/floats.ts`), `differ` (`arrays.ts`), `countsWhatItWrote`
(`examples/account/imports.contract.ts`) and Nemia's `standing.overBudgetWhereATryIsTheWayOn`.

**Notes.** After the cap, 64 laws carry a note, every one a says-anything check out of work, all in five of Nemia's
contracts: `observe` 24 of its 31 laws, `standing` 13 of 14, `approvalRefusal` 12 of 13, `wiringRefusal` 11 of 11,
`rewired` 4 of 8. The examples and the corpus carry none. In the baseline, most of these checks answered at the whole
work, many in under a second. The cap trades those answers for notes, and it cut the run's longest checks.

**By contract** (seconds):

| Contract | Laws | Before | Before, less cover | After | After, less cover | Gain, less cover |
|---|---|---|---|---|---|---|
| `observe` (`agent-runtime/src/core/domain.ts`) | 31 | 931.3 | 482.7 | 541.6 | 52.3 | 89% |
| `wiringRefusal` (`agent-orchestrator/src/wiring/wiring.ts`) | 11 | 382.2 | 382.2 | 30.7 | 30.7 | 92% |
| `rewired` (same file) | 8 | 176.4 | 176.4 | 19.7 | 19.7 | 89% |
| `approvalRefusal` (`agent-orchestrator/src/gate/gate.ts`) | 13 | 60.4 | 60.4 | 32.9 | 32.9 | 46% |
| `standing` (`agent-orchestrator/src/status/status.ts`) | 14 | 22.4 | 22.4 | 43.6 | 43.6 | −95% |
| `decide` (`domain.ts`) | 5 | 42.8 | 8.5 | 43.1 | 8.5 | 0% |
| `adopted` (`agent-orchestrator/src/adopt/adopt.ts`) | 10 | 5.8 | 5.8 | 5.2 | 5.2 | 10% |
| `reciprocalsOfEquals` (`fixtures/corpus/floats.ts`) | 1 | 300.4 | 300.4 | 300.4 | 300.4 | 0%: its search runs to the 5 minutes |

Every other contract took under 25 s before and after, with no gain beyond noise. Each folder's wall-clock went from
988 s to 596 s for Nemia's runtime (cover is most of what is left) and from 699 s to 185 s for its orchestrator. The
examples and the corpus did not change beyond noise.

**The prediction holds.** `rewired` takes 20 s and `approvalRefusal` 33 s at the default work, every law still
proved. On this tree they took 176 s and 60 s before the cap: tsverify 0.7.0 already halved the plan's 0.5.1 figures.
`observe`, without cover, went from 483 s to 52 s.

**`standing`** is slower for two reasons. Its bounded law's proof query stops out of work in both runs, and took 12.6 s
then 23.7 s: the machine's load, not the change. Its says-anything checks used to answer in 0.4 s at the whole work,
and now run out at a tenth, so the proof side is asked too, for about 1 s each.

**`adopted`** ends `undecided` (`output.generation === undefined`) on this tree, before and after. Its undecided query
answers in about 4.5 s, and the time of each question is:

| Question | Side | End | Queries | Seconds, before | Seconds, after |
|---|---|---|---|---|---|
| undecided | search | answered | 1 | 4.7 | 4.2 |
| says-anything | search | answered | 10 | 0.8 | 0.7 |
| proof | proof | answered | 10 | 0.1 | 0.1 |
| cross-check | search | answered | 1 | 0.0 | 0.0 |

That answer needs between 6,000,000 and 7,000,000 of the default 15,000,000 steps. Asked alone at a lower `--work`,
the undecided query runs out at 6,000,000 or less, and answers from 7,000,000 up. Before this change, a query that ran out was silent and the contract passed as
decided: on Nemia's CI (tsverify 0.5.1) it ended `undecided` after 27.9 s at aa3ca26 and `proved` in 23.2 s at
2198f9c. Now a run that stops short says so under the contract ("whether the laws decide every input was not
settled (out of work)") instead of passing in silence.

**By law**, for the contracts named above (seconds; the slowest question by side, end and time):

**`observe`** (`packages/agent-runtime/src/core/domain.ts`)

| Law | before (s) | after (s) | gain | slowest question before | after | note after |
|---|---|---|---|---|---|---|
| settledExactly | 6.4 | 0.9 | 86% | says-anything (search), answered, 6.1 | says-anything (proof), out of work, 0.5 | says-anything, out of work |
| theStopOutranksTheDeadline | 0.2 | 3.9 | -1717% | says-anything (search), answered, 0.2 | says-anything (search), out of work, 3.1 | says-anything, out of work |
| anEndOfItsOwnOutranksTheDeadline | 3.8 | 5.5 | -42% | proof (proof), answered, 3.3 | says-anything (search), out of work, 4.0 | says-anything, out of work |
| noDeadlinePassesWhileDrained | 82.4 | 0.7 | 99% | says-anything (search), out of work, 78.0 | says-anything (proof), out of work, 0.5 | says-anything, out of work |
| aHeldAttemptsDeadlineDoesNotPass | 0.7 | 0.5 | 21% | says-anything (search), answered, 0.6 | says-anything (search), answered, 0.5 |  |
| aDeadlineCountsFromTheLastResume | 24.9 | 0.8 | 97% | says-anything (search), answered, 24.9 | says-anything (proof), out of work, 0.7 | says-anything, out of work |
| aDeadlineIsOneSet | 13.2 | 0.8 | 94% | says-anything (search), answered, 13.1 | says-anything (proof), out of work, 0.6 | says-anything, out of work |
| aSightingIsAdopted | 1.2 | 1.0 | 16% | says-anything (search), answered, 0.9 | says-anything (search), answered, 0.8 |  |
| anUnreadHarnessIsNeitherRestartedNorLost | 52.3 | 1.1 | 98% | says-anything (search), out of work, 48.6 | says-anything (search), answered, 0.9 |  |
| anUnreadHarnessLosesNothing | 0.9 | 1.6 | -84% | says-anything (search), answered, 0.6 | says-anything (search), answered, 1.4 |  |
| lostOnlyOnceSpawned | 1.3 | 1.2 | 13% | says-anything (search), answered, 0.8 | proof (proof), answered, 0.5 | says-anything, out of work |
| inFlightEventsOnlyInFlight | 4.2 | 2.1 | 49% | says-anything (search), answered, 3.2 | proof (proof), answered, 1.4 | says-anything, out of work |
| inFlightSeesOnlyItsSession | 3.3 | 1.1 | 65% | says-anything (search), answered, 3.1 | says-anything (search), answered, 0.9 |  |
| aStopWithNothingInFlight | 0.3 | 4.2 | -1110% | says-anything (search), answered, 0.3 | says-anything (search), out of work, 3.3 | says-anything, out of work |
| nothingOpenOnlyOnAStop | 2.0 | 0.7 | 64% | says-anything (search), answered, 2.0 | says-anything (proof), out of work, 0.6 | says-anything, out of work |
| closedOnlyWhenClosed | 8.5 | 0.9 | 90% | says-anything (search), answered, 8.4 | says-anything (proof), out of work, 0.6 | says-anything, out of work |
| aPersonOutranksTheDeadline | 1.1 | 0.9 | 22% | says-anything (search), answered, 1.0 | says-anything (search), answered, 0.8 |  |
| aPersonIsWaitedOnOnlyWhenHeldOpen | 40.2 | 0.7 | 98% | says-anything (search), answered, 40.1 | says-anything (proof), out of work, 0.5 | says-anything, out of work |
| onlyALongLivedTaskIdles | 45.7 | 0.9 | 98% | says-anything (search), out of work, 44.2 | says-anything (proof), out of work, 0.6 | says-anything, out of work |
| onlyALongLivedTaskOrAParkedJobRestarts | 14.8 | 1.1 | 92% | says-anything (search), answered, 14.3 | says-anything (proof), out of work, 0.5 | says-anything, out of work |
| aParkedJobIsContinued | 32.0 | 2.0 | 94% | says-anything (search), answered, 30.6 | proof (proof), answered, 1.1 | says-anything, out of work |
| aParkedJobIsHeldWhileDrained | 6.4 | 1.2 | 81% | says-anything (search), answered, 6.0 | says-anything (proof), out of work, 0.6 | says-anything, out of work |
| heldOnlyWhenParkedAndDrained | 4.7 | 1.2 | 74% | says-anything (search), answered, 4.2 | says-anything (proof), out of work, 0.6 | says-anything, out of work |
| queuedOnlyWhenQueued | 3.5 | 1.4 | 60% | says-anything (search), answered, 2.9 | says-anything (proof), out of work, 0.6 | says-anything, out of work |
| aStartIsTheNextAttempt | 42.2 | 3.3 | 92% | says-anything (search), out of work, 36.8 | proof (proof), answered, 2.6 | says-anything, out of work |
| aQueuedTaskIsNeverStarted | 14.6 | 0.9 | 94% | says-anything (search), answered, 14.3 | says-anything (proof), out of work, 0.4 | says-anything, out of work |
| aWaitingTurnIsQueued | 8.7 | 0.9 | 89% | says-anything (search), answered, 8.4 | says-anything (proof), out of work, 0.4 | says-anything, out of work |
| queuedOnlyWhileWaiting | 16.6 | 2.1 | 87% | says-anything (search), answered, 16.1 | proof (proof), answered, 1.5 | says-anything, out of work |
| aClosedTaskIsSeenClosed | 0.3 | 0.3 | 8% | says-anything (search), answered, 0.3 | says-anything (search), answered, 0.2 |  |
| previousLiveOnlyWhenSeen | 39.0 | 1.4 | 96% | says-anything (search), out of work, 35.7 | proof (proof), answered, 0.8 | says-anything, out of work |
| noSessionToContinueOnlyInALaterTurn | 2.0 | 0.9 | 57% | says-anything (search), answered, 1.9 | says-anything (proof), out of work, 0.6 | says-anything, out of work |

**`rewired`** (`packages/agent-orchestrator/src/wiring/wiring.ts`)

| Law | before (s) | after (s) | gain | slowest question before | after | note after |
|---|---|---|---|---|---|---|
| detachWithdraws | 0.7 | 0.8 | -9% | says-anything (search), answered, 0.7 | says-anything (search), answered, 0.8 |  |
| fireLeaves | 1.0 | 1.0 | -3% | says-anything (search), answered, 0.9 | says-anything (search), answered, 1.0 |  |
| scheduleHolds | 0.9 | 1.0 | -11% | says-anything (search), answered, 0.8 | says-anything (search), answered, 0.9 |  |
| unscheduleLeaves | 1.5 | 2.4 | -65% | says-anything (search), answered, 1.4 | says-anything (search), out of work, 1.3 | says-anything, out of work |
| keepsRepos | 59.4 | 4.3 | 93% | says-anything (search), out of work, 43.9 | says-anything (search), out of work, 3.0 | says-anything, out of work |
| hireNames | 19.3 | 4.0 | 79% | says-anything (search), answered, 19.2 | says-anything (search), out of work, 2.6 | says-anything, out of work |
| keepsItsName | 91.7 | 4.8 | 95% | says-anything (proof), out of work, 49.2 | says-anything (search), out of work, 2.9 | says-anything, out of work |
| attachOffers | 1.7 | 1.2 | 29% | says-anything (search), answered, 1.6 | says-anything (search), answered, 1.1 |  |

**`approvalRefusal`** (`packages/agent-orchestrator/src/gate/gate.ts`)

| Law | before (s) | after (s) | gain | slowest question before | after | note after |
|---|---|---|---|---|---|---|
| emptyWords | 5.6 | 2.1 | 63% | says-anything (search), answered, 4.9 | says-anything (proof), out of work, 1.2 | says-anything, out of work |
| aStepOfTheWorkflow | 4.4 | 6.3 | -43% | says-anything (search), answered, 4.3 | says-anything (search), out of work, 4.9 | says-anything, out of work |
| aCancelledRunFilesNothing | 1.9 | 2.3 | -20% | says-anything (search), answered, 1.9 | says-anything (proof), out of work, 1.2 | says-anything, out of work |
| aPrunedRunFilesNothing | 6.2 | 1.6 | 75% | says-anything (search), answered, 6.1 | says-anything (proof), out of work, 1.3 | says-anything, out of work |
| aHeldRunFilesNothing | 0.7 | 0.5 | 20% | says-anything (search), answered, 0.6 | says-anything (search), answered, 0.5 |  |
| onlyAGate | 2.7 | 1.6 | 39% | says-anything (search), answered, 2.5 | says-anything (proof), out of work, 1.3 | says-anything, out of work |
| onceATry | 2.5 | 1.8 | 27% | says-anything (search), answered, 1.9 | says-anything (proof), out of work, 1.1 | says-anything, out of work |
| notWhileASendBackIsAsked | 6.6 | 2.3 | 65% | says-anything (search), answered, 6.0 | says-anything (proof), out of work, 1.8 | says-anything, out of work |
| onlyWhereItWaits | 5.5 | 1.6 | 71% | says-anything (search), answered, 5.3 | says-anything (proof), out of work, 1.3 | says-anything, out of work |
| takenAtItsGate | 8.2 | 3.3 | 59% | says-anything (search), answered, 6.9 | proof (proof), answered, 1.6 | says-anything, out of work |
| heldOpenForIt | 5.0 | 1.8 | 63% | says-anything (search), answered, 4.9 | says-anything (proof), out of work, 1.5 | says-anything, out of work |
| anEndingAlreadyLanded | 5.5 | 2.2 | 60% | says-anything (search), answered, 5.0 | says-anything (proof), out of work, 1.4 | says-anything, out of work |
| anEndingWhileItsWorkIsSentBack | 2.6 | 2.2 | 15% | says-anything (search), answered, 2.3 | says-anything (proof), out of work, 1.5 | says-anything, out of work |

**`adopted`** (`packages/agent-orchestrator/src/adopt/adopt.ts`)

| Law | before (s) | after (s) | gain | slowest question before | after | note after |
|---|---|---|---|---|---|---|
| keepsItsName | 0.0 | 0.0 | 4% | says-anything (search), answered, 0.0 | says-anything (search), answered, 0.0 |  |
| keepsItsRepos | 0.0 | 0.0 | 37% | says-anything (search), answered, 0.0 | says-anything (search), answered, 0.0 |  |
| keepsItsSchedules | 0.1 | 0.1 | 8% | says-anything (search), answered, 0.1 | says-anything (search), answered, 0.1 |  |
| keepsItsInstruction | 0.0 | 0.0 | 6% | says-anything (search), answered, 0.0 | says-anything (search), answered, 0.0 |  |
| keepsItsVolumes | 0.0 | 0.0 | 8% | says-anything (search), answered, 0.0 | says-anything (search), answered, 0.0 |  |
| keepsItsHarnessSettings | 0.2 | 0.2 | 6% | says-anything (search), answered, 0.2 | says-anything (search), answered, 0.1 |  |
| offersTheTemplates | 0.0 | 0.0 | 39% | says-anything (search), answered, 0.0 | says-anything (search), answered, 0.0 |  |
| hiresTheTemplates | 0.2 | 0.2 | 10% | says-anything (search), answered, 0.2 | says-anything (search), answered, 0.2 |  |
| followsTheTemplates | 0.0 | 0.0 | 7% | says-anything (search), answered, 0.0 | says-anything (search), answered, 0.0 |  |
| recordsItsTemplate | 0.2 | 0.2 | 8% | says-anything (search), answered, 0.2 | says-anything (search), answered, 0.2 |  |

**`wiringRefusal`** (`packages/agent-orchestrator/src/wiring/wiring.ts`)

| Law | before (s) | after (s) | gain | slowest question before | after | note after |
|---|---|---|---|---|---|---|
| hireOnlyIntoOffered | 59.8 | 2.5 | 96% | says-anything (proof), out of work, 48.9 | says-anything (proof), out of work, 1.4 | says-anything, out of work |
| fireOnlyHired | 28.4 | 2.5 | 91% | says-anything (proof), out of work, 16.2 | says-anything (proof), out of work, 1.4 | says-anything, out of work |
| detachOnlyOffered | 27.4 | 2.7 | 90% | says-anything (proof), answered, 16.2 | says-anything (proof), out of work, 1.6 | says-anything, out of work |
| detachLeavesNoHire | 36.7 | 2.9 | 92% | says-anything (proof), out of work, 22.8 | says-anything (proof), out of work, 1.8 | says-anything, out of work |
| detachLeavesNoSchedule | 39.8 | 2.7 | 93% | says-anything (proof), out of work, 25.1 | says-anything (proof), out of work, 1.5 | says-anything, out of work |
| scheduleOnlyOffered | 33.6 | 2.7 | 92% | says-anything (proof), out of work, 18.6 | says-anything (search), out of work, 1.3 | says-anything, out of work |
| unscheduleOnlyScheduled | 30.2 | 2.9 | 90% | says-anything (proof), out of work, 18.0 | says-anything (proof), out of work, 1.6 | says-anything, out of work |
| attachAccepted | 29.6 | 3.2 | 89% | says-anything (proof), out of work, 18.0 | says-anything (proof), out of work, 1.9 | says-anything, out of work |
| takesWhatItCan | 25.7 | 2.5 | 90% | says-anything (proof), out of work, 14.8 | says-anything (proof), out of work, 1.3 | says-anything, out of work |
| aBadNameIsInvalid | 44.2 | 2.6 | 94% | says-anything (proof), out of work, 17.4 | says-anything (proof), out of work, 1.4 | says-anything, out of work |
| missingOnlyOfWhatIsNotThere | 25.9 | 2.5 | 90% | says-anything (proof), out of work, 15.6 | says-anything (proof), out of work, 1.3 | says-anything, out of work |


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

### Card (a), built: a pure function's examples are found by running

What was built: every law of a pure function's contract is run first, on 1,000 inputs meeting `requires`, generated from
the parameters' types (`src/run/`, fast-check 4.10.2), in a child process per contract. A law a run breaks is its
counterexample (`by: "run"`), not asked of Z3 but for one pinned proof-side query at a tenth of `--work`. Where that query
says the law holds, the reason names the `assume` Z3 leaned on, or the law is `inconsistent` where it leaned on none.
Says-anything is a question of the spec alone: a run answers it, else one proof-side query of the spec alone
(`lowerSpecSide`) at a tenth; the search-side query is gone. The command runs by default, `--no-run` turns it off, and
`verify()` as a library runs only with `run: true`. Left to cards (b) and (c): computations and Effect programs, Schema's
`Arbitrary`, and `cover` and `undecided` by running.

Three choices differ from the plan above. The seed is not `contractKey`, which hashes `process.cwd()` and absolute
paths: it hashes the program's file texts, the contract's name and `--bound` (`runSeed`), so a laptop and CI draw the
same inputs. A spec no module exports (Nemia's `const approvalRefusalSpec = spec<…>`) is reached by a load hook that
appends an export to its source in memory. The child gets an environment of its own: PATH, a throwaway HOME and TMPDIR,
USERPROFILE, and NODE_OPTIONS when set; never the parent's whole one, which on this machine names the live stores.

### Measured: Nemia's 64 notes, and the five contracts' times

**How.** This checkout's CLI, `--json`, no `--cache`, one file at a time, from Nemia's own checkout at e0ec8e67f. Phase 1
read a frozen ab395d4, and Nemia has moved since: `standing` has 18 laws now, not 14, and `holdsOpen` is new. Same
machine, shared, as Phase 1. The child loaded Nemia's modules, `effect` and `xstate` among them (58 to 77 modules for an
orchestrator contract, 12 for the runtime's), each named in the report.

**Notes.** Of the 64 says-anything notes, 62 are answered, each by a run or by Z3's query of the spec alone:

| Contract | Notes in Phase 1 | Left | Answered by run / by Z3 (of its laws) | Inputs meeting `requires` |
|---|---|---|---|---|
| `observe` | 24 | 0 | 19 / 12 | 289 of 10,000 draws |
| `standing` | 13 | 0 | 11 / 7 | 1,000 of 1,795 |
| `approvalRefusal` | 12 | 2 | 8 / 3 | 1,000 of 1,865 |
| `wiringRefusal` | 11 | 0 | 0 / 11: not run, it calls `hireRefusal`, declared `pure: false` | — |
| `rewired` | 4 | 0 | 6 / 2 | 1,000 of 2,184 |

The two left, `approvalRefusal.takenAtItsGate` and `anEndingAlreadyLanded`, are laws no generated free result broke at
the first 100 inputs `requires` met, and whose spec-alone query runs out at a tenth: they keep the note, worded "of the
spec alone". The spec-alone query alone, before any run was possible, answered 53 of the 64 (a first pass, where every
contract was still refused a run, on its types or its purity): the code's facts were most of what the old query paid for.

**Verdicts.** Every law of the five contracts is `proved`, as in Phase 1. No run broke a law, so no counterexample by run
needed examining. A run of `observe` first stopped at the 60 s clock: drawing a free result for every law at every draw
cost 27 ms a draw. The free results are now drawn at the first 100 inputs `requires` met, and its run takes 5 s.

**By contract** (seconds, less cover, which is what CI pays):

| Contract | Phase 1, after | This card | Its run |
|---|---|---|---|
| `observe` | 52.3 | 29.4 | 5.0 |
| `wiringRefusal` | 30.7 | 2.5 | not run |
| `rewired` | 19.7 | 4.0 | 0.2 |
| `approvalRefusal` | 32.9 | 32.7 | 1.4 |
| `standing` | 43.6 | 26.5 (18 laws) | 1.7 |
| `decide` | 8.5 | 5.8 | 3.9 |

A run adds the child's start and its modules' loading, under 2 s for each orchestrator contract. `decide` meets `requires`
at 170 of 10,000 draws, and `observe` at 289: the risk named above, measured. Their runs still answer most of their
says-anything questions.

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

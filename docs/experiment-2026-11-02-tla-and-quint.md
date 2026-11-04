# Experiment: TLA+ or Quint beside tsverify

**Date:** 2 November 2026. **Status:** an experiment to run, nothing built. It is not a tsverify feature: it tries a
neighbour tool on Nemia, to find where tsverify's job ends. TLA+ and Quint are both still to be evaluated.

## The question

tsverify proves one function's laws, one call at a time, read from the TypeScript. Z3 answers one question per call: is
there an input where this law fails? Some of what goes wrong in Nemia is not in any one call. It is in the order of steps
across several actors, with a crash possible between any two of them. TLA+ is made for that: a model of the system as
states and steps, and a checker that tries every order the steps can happen in, crashes included. It checks two kinds of
property:
- **safety:** something bad never happens;
- **liveness:** something good eventually happens.

The experiment asks three things: what a model finds in Nemia that tsverify cannot, what it costs to keep, and which
language to write it in.

## Where the line falls

| Question | Tool |
|---|---|
| `decide` never starts a second attempt while one is live, in any state | tsverify (proved) |
| `lifecycleOf` names a task's phase for every state | tsverify (`undecided` cases being answered) |
| A task eventually settles, across many ticks and restarts | a model checker |
| Two daemons in a handover never both write the store | a model checker |
| A parked session is always picked back up, even when the daemon is killed mid-handover | a model checker |

Signs in Nemia that the second half exists:
- **`decide` is `undecided` on 0.5.0.** For a fresh task, `{ do: "start" }` and `{ do: "nothing" }` both keep every law,
  because its laws only say what it must never do. "It eventually makes progress" is not a property of one call. It is a
  property of the loop over many ticks, and today tests hold it.
- **Bugs found by hand, one at a time, after the fact** (Nemia's `packages/agent-runtime/docs/open-issues.md`):
  - #15, words delivered and not journalled if the process dies between the two writes;
  - #33, an append that reaches the record and not the feed;
  - #34, a remote Task answered in the instant before the registry holds it, owned by nobody.
- **The daemon killed during its let-go,** on 2 November at 1:43 AM: no `stoppedAt` written, and a session's subagent
  lost.

Which of these a model would have caught depends on what the model includes. That is part of what the pilot measures.

## Do linked specs patch what TLA+ would do?

Mostly no. The linked specs proposed in `design-2026-11-01-spec-checks.md` (`agrees`, `needs`) relate two functions at
one call:
- **`agrees`** asks whether two specs answer the same at one moment. Nemia's definition and workflow version refusals
  answer Missing and Conflict for the same write.
- **`needs`** asks whether what a caller counts on is given by its callee's spec.

Neither has time or a second actor in it. That is modular proof over the code's call graph, Dafny's and Verus's
tradition, and Z3's home. A TLA+ model does not read the TypeScript. To ask `agrees` there, both functions' rules would be
written out a third time, for a question with no "after" in it. A model of the store's writes would most likely abstract
the refusal to "refused" and never see Missing against Conflict.

**Where the two overlap:** the motive. Both check a design before the code. TLA+ checks one model of the whole design,
written apart from the code. Links check the seams between specs that tsverify already holds, which are the code's own.

**The line to keep:** a link never says "after" or "eventually". A link that chains specs across ticks to get progress
("`decide` starts, then `observe` sees READY, then …, eventually settled") would be rebuilding a model checker inside
tsverify, badly. That question goes to the model.

## How the two would meet

A proved spec can stand in for its function in the model. The model's `decide` step picks any answer `decide`'s laws
allow, not the code's own answer. Checked that way:
- **Liveness holds:** it holds for the code too, since the code's answer is one of those the laws allow.
- **Liveness fails:** the trace shows the progress law `decide`'s spec is missing, or a gap in the design.

In both cases tsverify proves each step and the model checks the machine around them. The `undecided` verdict is the
place where they hand over: what the laws leave open is what the model must not assume.

## TLA+ or Quint: to evaluate

The owner sees far more traction for TLA+ than for Quint. What is known so far:
- **Quint** is another syntax for the same logic (TLA), with a type checker and a simulator (`quint run`). It is checked
  by two backends ([Quint's model checkers](https://quint.sh/docs/model-checkers)):
  - **Apalache:** built in, symbolic over Z3, and always bounded (`--max-steps`, 10 by default). The page says temporal
    properties have "partial support".
  - **TLC:** through `quint verify --backend=tlc`.

  That page says nothing of fairness.
- **TLA+** is Lamport's language. TLC is its exhaustive checker, and PlusCal is a pseudocode form that compiles to it.
  Fairness is part of the language itself (weak and strong fairness), and TLC checks liveness under it. It has a long
  record in industry, Amazon's included ("How Amazon Web Services Uses Formal Methods", CACM, 2015), and a foundation
  under the Linux Foundation.
- **tla-ts** ([aidenybai/tla-ts](https://github.com/aidenybai/tla-ts)), read on 2 November 2026 and not yet run: TLC,
  its parser, PlusCal and TLAPM rewritten in TypeScript, so a model is checked in Node or a browser with no JVM. It reads
  `.tla` files, never TypeScript: TypeScript is only what it is written in. Two things in it bear on the pilot:
  - **Traces:** `check()` returns a failing trace as JavaScript values, in the same process as a Node test, which suits
    replaying it against the engine.
  - **Liveness:** TLC's liveness checker is ported, and its tests check specs with fairness. Whether it holds on the
    pilot's model is not yet known.

  Its SMT backend for proofs is a TypeScript port of Z3's core (about 45,000 lines), cut to the one setting TLAPM uses:
  arithmetic and uninterpreted functions, no strings. That is no reason to change how tsverify calls Z3. It is a week
  old (0.0.5, one author), and its correctness rests on matching TLC's recorded results on 542 models, so the pilot runs
  the model through both TLC and tla-ts.

To decide by, measured on the pilot below:
- **Liveness under fairness.** "Every parked session is eventually resumed" needs "the next daemon eventually takes a
  step". Can each one say and check that, and at what model size?
- **An agent writing it.** The same model is written by an agent in each language. Count the tries to a model that
  parses, checks and finds a planted bug. TLA+ has far more public examples, and Quint reads like TypeScript; which one
  that favours is unknown until measured.
- **Traces a test can replay.** Can a counterexample, or a random trace, be replayed against the real engine as a test?
  This is how a model is kept from drifting from the code.
- **Traction and longevity:** users, tooling, upkeep of the checkers, books and courses.
- **Cost to keep:** lines, and time to a first check.

## The pilot

Nemia's daemon handover, read from the code first:
- the store's lease and `stoppedAt` are in `packages/agent-orchestrator/src/daemon/daemon.store.ts`;
- the sessions' let-go and parking are in `packages/agent-runtime/src/harness/claude/attached.ts`.

What the model has:
- **The holder:** holds the lease, then lets go: it holds new calls, waits at most 60 s (`LET_GO_MS`) for the calls in
  flight, parks its sessions and writes `stoppedAt`.
- **The next holder:** takes the lease and adopts what was parked.
- **A crash:** allowed between any two steps.

The properties to check:
- **Safety:** one writer of the store at a time.
- **Liveness:** every parked session is eventually resumed or settled.

The same model is written once in TLA+ (or PlusCal) and once in Quint. Each is checked against a planted bug, the way
tsverify's bench plants them. For example, a let-go cut before `stoppedAt`, read by a next holder that then skips
adoption.

**It succeeds** if it gives a trace the code also has (confirmed by a test of the engine), or a reason to trust the
handover, plus the measures above for choosing the language. A second model, the task lifecycle across restarts, waits
on that result.

## Open questions

- **Where the model lives:** beside the Nemia code it models, or in a repository of its own. Nothing of it ships in
  tsverify.
- **The bridge:** whether a spec's laws could be written out as the model's step, so the model's `decide` is generated
  from `decide`'s spec and the two never drift.
- **Who writes it:** by hand first, as an experiment, before it ever becomes a factory card.

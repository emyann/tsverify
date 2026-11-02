# tsverify 0.5.0: checks on a spec alone

**Date:** 1 November 2026, revised 2 November. **Status:** item 1, accept-or-refuse, is built (the `undecided` verdict and
`open`), uncommitted. The rest is proposed: `agrees`, `needs`, `uses` and `Pure` do not exist in tsverify. Decided on
2 November: meeting a callee's `requires` becomes the caller's own obligation (*Open questions*).

## The answer in one paragraph

0.4.0 checks code against its spec. Its one check of a spec's own laws, `unmeetable`, runs only at the input of a
counterexample, so it needs code that fails first. 0.5.0 would check specs before any code exists:
- whether the laws decide every input (*accept-or-refuse*);
- whether some input has no answer at all (*unmeetable anywhere*);
- whether two specs that restate or rely on each other agree (*linked specs*).

It would also close one reading gap: a callback parameter declared pure. Each item comes from something Nemia's contracts
ran into this week, and four of the five questions are a single "there is" search, the kind Z3 is best at.

## Why: what Nemia's contracts ran into

- **Five laws that said when to refuse but not when to accept** (Nemia's spec-holes run, `9085023`). A function that
  refuses too much kept every law, and tsverify proved exactly what the laws said. The journal's `attemptsInOrder` is the
  subtle one: it ties a start refused *as `attempt-out-of-order`* to a wrong number, so a correct start refused for another
  reason still keeps it. The skill's "Say both sides" rule was loaded and the hole still slipped through; a review caught it.
- **A callback read twice.** `standing`'s `phaseOf` and `verdictOf` are parameters, so the verifier lets each call answer
  differently, and a law that reads one twice gets a false counterexample. Two "over budget" cases stay covered by tests
  rather than laws. `assume(fn, { pure: true })` exists for an imported function, not for a parameter.
- **Two specs that claim to be the same rules,** linked by a comment. Nemia's `definition-version.contract.ts` says it is
  "the Workflow door's laws … in a definition's words". Nothing checks that, and there is one case where the two differ
  (*Linked specs* below).
- **A spec change that breaks a caller** surfaces today only as a counterexample on the caller, after the caller's code
  exists. It does not say that two specs conflict.

## 1. Accept-or-refuse

**The question:** is there an input `requires` allows where two answers of different kinds both keep every law? If so,
the laws do not decide that input: code could go either way, and "proved" says nothing about which.

**The kind of an answer:**
- for `T | undefined` or `T | null`, whether it is the empty case;
- for a union told apart by a tag (`kind`, `_tag`, `status`, `reason`), the tag;
- never a free string such as a message, which is meant to be free.

**Today's journal hole, as it would have read:**

```
appendRefusal: undecided
  at:    (undefined, starting #1, { journal: true, started: 0 })
  both:  undefined                   keeps every law
         { reason: 'not-filed' }     keeps every law
  write the law that picks one, or say the choice is left open
```

**How:** one query. A free input that meets `requires`, two free answers, every law asserted on each, and their kinds
required to differ. The report is on the contract, not on one law. A spec meant to leave a choice open says so: `open:
["output.reason"]` leaves that part and what is under it to the code, `open: true` the whole result.

**As built:** asked of a pure function's spec only. A computation's laws read its calls, and two runs that share calls no
code of it could make (none at all, say) are undecided wherever the laws pin no trace: most specs of what code did. How
to ask it of a computation, with a trace the code could make, is a follow-up. Two results differ in kind where a closed
part differs: a value of a few literal cases, whether it is
`undefined` or `null`, or such a field of a record, two levels down. The verdict is `undecided` (◐), fails the command,
and names the part (`output === undefined`, `output`, `output.status`).

**Measured, 2 November:**
- **Nemia's contracts before the spec-holes run** (`c62672974`): 9 of 17 undecided, the five the run fixed among them
  (the journal's `appendRefusal`, the gate's `approvalRefusal`, `standing`, `ownStatus` and `lifecycleOf`). On the proof
  side, with a tenth of a query's work, the gate's and standing's came back unknown: their records are large, which is
  why the check is asked on the search side.
- **Nemia's contracts on main:** 6 of 17 undecided.
  - `decide`'s laws are all of what it must never do, so a fresh task may start or wait: a spec of safety alone, for
    `open: true`.
  - `lifecycleOf` leaves a task held open with no attempt between `submitted` and `input-required`.
  - `observe` leaves a fresh task between `QUEUED` and `READY`.
  - `standing`, `ownStatus` and `holdsOpen` take `phaseOf` and `verdictOf`, which the verifier rereads as answering anew
    on each call: the two cases the spec-holes run left to tests are among them. Item 4 bears on these.
- **tsverify's own examples:** `account` (twice), `lodash/labels`, `order/status`, and two specs in `docs/specs.md`, each
  a law said one way only. Each now says both sides, every new law proved on the code as it is.
- **The planted-bug benchmark on `order`:** its laws had five gaps, five planted bugs that changed a result no law
  forbade. The laws added to decide every order catch all five: the solver catches 15 of 17, up from 10, and the two it
  misses are proved harmless.

All five holes of the spec-holes run had this shape. It turns "Say both sides" from prose into a verdict.

## 2. Unmeetable anywhere

**The question:** is there an input where no answer keeps every law? It is 0.4.0's `unmeetable`, with no counterexample to
hand it the input.

**Why it is harder than the others:** it is a "for every answer" inside a "there is an input". With the input pinned,
as 0.4.0 does, the inner part is a plain search for one answer, and finding none settles it. Without the input, the solver
has to find the input and prove that every answer fails there. Z3's support for that is partial: with numbers it often
manages, and with strings and arrays it often answers `unknown`.

**Where it stays cheap:** when the answer has a few possible values, "every answer fails" is "each of these fails", one
condition per value, and the search is plain again. Nemia's deciders mostly answer a closed union. `appendRefusal`
answers `undefined` or a refusal with one of four reasons: five cases. Its message can be any string, but no law reads it.

**Elsewhere:** a guess-and-check loop. Guess an input, ask 0.4.0's question there, learn from the answer that worked, and
guess again. When a bad input exists the loop finds it. When none exists it cannot always prove so, and stops at a bound,
reported like `bounded`.

## 3. Linked specs

### What exists today

- A call to a function typed `Implementation<S>` takes S's laws, not its body, in code and in a law alike. Nemia's
  `standing` spec has a law, `ownIsItsOwn`, that calls `ownStatus`, and the solver uses `ownStatus`'s laws there.
- So the raw material is there. What is missing:
  - a way for a spec to name what it relies on with no implementation present;
  - a check run on the specs alone;
  - a report that names the two specs that conflict.

Linking does not mean one big solver. Each question still gets a fresh solver (`src/verify.ts`); a linked check puts
the other spec's laws into that one question, as a call does today.

### 3a. Two specs that say the same rules: `agrees`

Nemia's two version refusals, for an agent or a skill and for a workflow folder, as they would be linked:

```ts
// definition-version.contract.ts (proposed syntax)
import { agrees } from "@emyann/tsverify"

/** A definition's place, read as a workflow folder's. */
const asFolder = (there: DefinitionThere): WorkflowThere =>
  there.kind === "held" ? { kind: "folder", version: there.version }
  : there.kind === "other" ? { kind: "file" }
  : { kind: "none" }

export const sameRulesAsWorkflows = agrees(definitionVersionRefusalSpec, workflowVersionRefusalSpec, {
  // a definition's call, read as a workflow's call
  input: ([, name, does, there, given]) => [name, does, asFolder(there), given],
  // both must answer the same kind of refusal
  output: (definition, workflow) => definition?.kind === workflow?.kind,
})
```

**The question:** is there a call where an answer the first spec allows and an answer the second allows break `output`?
One "there is" search. It finds both:
- a contradiction, where each spec forces a different kind;
- a hole, where one spec leaves the kind open.

**What it would report today**, checked by hand against both files:

```
sameRulesAsWorkflows: counterexample
  call:        write 'a' over { kind: 'other' } given version 'v1'
               as a workflow: write over { kind: 'file' } given 'v1'
  definition:  Missing   (goneIsMissing)
  workflow:    Conflict  (fileIsTaken)
```

For a definition, `goneIsMissing` covers anything not held when a version is given, so `other` gives Missing. For a
workflow, `fileIsTaken` gives Conflict for any write over a file, version or not. Every other case agrees. Whether that
one case is intended is Nemia's call; today nothing would have raised it.

### 3b. A spec that relies on another: `needs`

Nemia's api answers a write of an agent by calling `definitionVersionRefusal` and mapping its kind to a status (`Missing`
404, `Conflict` 409, `Invalid` 422). Its spec names what it counts on, in its own words:

```ts
// write-answer.contract.ts (proposed syntax)
import { needs, spec, type Implementation } from "@emyann/tsverify"

const writeAnswerSpec = spec<(there: DefinitionThere, given: string | undefined) => 200 | 404 | 409 | 422>({
  // the link: what this function counts on from the one it calls
  uses: {
    refusal: needs(definitionVersionRefusalSpec, {
      staleIsRefusedAsConflict: ({ input: [, , , there, given], output }) =>
        !(there.kind === "held" && given !== undefined && given !== there.version) || output?.kind === "Conflict",
    }),
  },
  ensures: {
    staleIs409: ({ input: [there, given], output }) =>
      !(there.kind === "held" && given !== undefined && given !== there.version) || output === 409,
  },
})
export type WriteAnswer = Implementation<typeof writeAnswerSpec>
```

**Two checks:**
- **Before any code:** is there a call and an answer that keep every law of the refusal's spec but break
  `staleIsRefusedAsConflict`? None today: `staleIsConflict` gives it. If someone later loosens `staleIsConflict`, the link
  fails at once, naming both specs, before the api's code changes.
- **Once the api's code exists:** its proof takes only the law it named, not the refusal's body or its other seven laws.
  The api then depends on exactly what it wrote down. That is today's mechanism, narrowed to what the caller says it needs.

### Which questions stay cheap

| Question | Shape | Cost |
|---|---|---|
| Does the callee's spec give what the caller needs? (`needs`) | there is an input and an answer that keep the callee's laws and break the need | one search |
| Do two specs answer the same? (`agrees`) | there is an input and two allowed answers that break `output` | one search |
| Do the linked laws contradict each other everywhere? | there is no input and answer that keeps them all | one search |
| Is there an input where no answer keeps the linked laws? | for every answer, inside there is an input | cheap for a closed answer, best-effort otherwise (item 2) |

## 4. A callback parameter declared pure

The roadmap already has it: "A function the code is given, declared pure where a spec says so". The case that needs it
is `standing`'s `phaseOf` and `verdictOf`. A sketch, as a type the spec's signature carries:

```ts
import { type Pure, spec } from "@emyann/tsverify"

const standingSpec = spec<(step: Step, run: Run, phaseOf: Pure<(task: string) => Phase>) => Standing>({ ... })
```

`Pure<F>` would be a type alias of `F`, with no cost at run time. The verifier reads it as `assume(…, { pure: true })`
reads an import: the same arguments give the same result, and a call changes nothing anyone sees. A caller's proof then
owes that its argument is pure, as a call of an `Implementation<S>` owes its `requires`.

## 5. One command for specs alone

`npx tsverify specs [files…]` would run items 1 to 3 on every exported spec, with no implementation needed, and
report one line per contract and per link. It would be cheap enough for a design step to run it before anyone writes
code, which is where Nemia wants it: today a spec problem is found at implement, or at review.

## Order

1. **Accept-or-refuse:** the cheapest, and five real holes to test it on. It reuses `unmeetable`'s machinery: input
   pinned, answer free.
2. **A callback parameter declared pure:** unblocks two laws Nemia already wants.
3. **Linked specs:** `agrees` first, since the `other`/`file` case is a ready fixture; then `needs`.
4. **Unmeetable anywhere,** for closed answers first. The guess-and-check loop only if a real spec needs it.
5. **The command,** gathering what is built.

## Open questions

- **A link's verdict name.** Accept-or-refuse's is `undecided`.
- **A call outside the callee's `requires`.** Decided 2 November: it becomes the caller's own obligation, as in Dafny,
  checked against Nemia's contracts before a release. Today
  it is not. A probe on 0.4.0, `caller = (n) => half(n - 10n)` with `half` requiring `n >= 0n`, reported nothing about the
  call: a call outside `requires` just gets none of the callee's laws. A lemma's call does prove its `requires`
  (`src/exec.ts`). `needs` leans on this, so it should be decided first. Making it an obligation could turn a proved
  contract red where its code calls outside a callee's `requires`.
- **Across packages:** whether tsverify follows an `Implementation<S>` import across two packages of a monorepo, untried.
  Most of Nemia's cross-package calls go through Effect services, which no spec types today.
- **Where a link lives:** beside the spec that relies on it, or in a file of links.

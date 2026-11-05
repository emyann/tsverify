// What a verification asked the solver, and how each question ended: the time of each, by question and by end, for
// `--json`, and the questions that ended without an answer, said on the law or contract they belong to. Pure: no Z3.

/** A question a verification asks of the solver. */
export type Question =
  /** Whether any allowed input breaks the law, on the proof side (`unsat` proves it). */
  | "proof"
  /** Whether any result of the law's type breaks it: whether it says anything of the function (`vacuous`). */
  | "says-anything"
  /** A counterexample to a law the proof side did not prove, on the search side. */
  | "search"
  /** Whether some result keeps every law at a counterexample's input (`unmeetable`). */
  | "unmeetable"
  /** Whether the search side breaks what the proof side proved: the laws', and the obligations'. */
  | "cross-check"
  /** Which ends the result reaches. */
  | "cover"
  /** Whether the laws leave a result open between two kinds at some input. */
  | "undecided"
  /** An obligation of the proof code, a lemma among them, and the rounds that guess a loop's invariants. */
  | "obligation"

export type Side = "proof" | "search"

/** What answered a question: a run of the code on generated inputs, or Z3. */
export type Engine = "run" | "z3"

/**
 * How a query ended: with an answer; at the work limit (`--work`), which stops a query at the same step on every run;
 * at `STUCK_MS`, a clock, the one stop that may not be the same on every run; or with the solver giving up for a reason
 * of its own, such as quantifiers it cannot decide.
 */
export type End = "answered" | "out of work" | "out of time" | "gave up"

/** The queries asked for one question on one side that ended one way, and their time. */
export interface Asked {
  readonly question: Question
  readonly side?: Side
  /** What answered it. For a run, `queries` counts the inputs run. */
  readonly by: Engine
  readonly end: End
  readonly queries: number
  readonly ms: number
}

/** A question that ended without an answer, and what the verdict took of it instead. */
export interface Unanswered {
  readonly question: Question
  /** The side whose query ended without an answer; unset where both did. */
  readonly side?: Side
  readonly end: End
  /** In a report's words: what was not settled, how it ended, and what the verdict reads it as. */
  readonly reason: string
}

/**
 * A guard against a query that never counts its work: far past what the default work takes, and named "out of time"
 * when it is reached. A clock, so where it stops a query hangs on the machine.
 */
export const STUCK_MS = 300_000

/**
 * How a query ended, from its status, the solver's reason when it has no answer, and how long it ran. A stop at the work
 * limit is said "resource limit" or, at times, "canceled": the clock is the only other thing that stops a query, and it
 * fires only at `STUCK_MS`, so a stop said "canceled" or "timeout" before that is one at the work limit.
 */
export const endOf = (status: "sat" | "unsat" | "unknown", reason: string, ms: number): End =>
  status !== "unknown"
    ? "answered"
    : /resource limit/i.test(reason)
      ? "out of work"
      : /timeout|canceled/i.test(reason)
        ? ms < STUCK_MS
          ? "out of work"
          : "out of time"
        : "gave up"

/** How a query ended, in a report's words: out of work or out of time, or the solver's own reason. */
export const endWords = (end: End, reason: string): string =>
  end === "out of work"
    ? "out of work (the solver's limit per query, `--work`)"
    : end === "out of time"
      ? `out of time: the query ran ${STUCK_MS / 60_000} minutes without counting its work`
      : end === "answered"
        ? "answered"
        : reason

/** How one side's says-anything query ended: with a result that breaks the law (`sat`), none (`unsat`), or no answer. */
export type SidesEnd = { readonly status: "sat" } | { readonly status: "unsat" } | { readonly status: "unknown"; readonly end: End }

/**
 * What the check that a law says something decides of a proved law. It is a question of the spec alone: its types,
 * `requires`, the law, and a free result of the law's type, never what the code does. A run that found such a result
 * breaking it (`byRun`) says it says something; else the proof side's one query of the spec alone (unset where it was
 * not asked: the law cannot be read on any result) decides: a result that breaks it says something, none that it says
 * nothing. A query that ends without an answer reads as saying something, and says so.
 */
export const saysAnything = (
  byRun: boolean,
  proof: SidesEnd | undefined,
): { readonly vacuous: boolean; readonly unanswered?: Unanswered } => {
  if (byRun || proof?.status === "sat") return { vacuous: false }
  if (proof?.status === "unsat") return { vacuous: true }
  if (proof?.status !== "unknown") return { vacuous: false }
  return {
    vacuous: false,
    unanswered: {
      question: "says-anything",
      side: "proof",
      end: proof.end,
      reason: `whether it says anything of the function was not settled (${proof.end} on the proof side, of the spec alone, at a tenth of \`--work\`): read as saying something`,
    },
  }
}

/** The time of every query asked for one law, or for one contract's own questions, summed by question, side and end. */
export class Ledger {
  readonly #entries: Array<{ question: Question; side: Side | undefined; by: Engine; end: End; queries: number; ms: number }> = []

  /** `queries` asked for `question` on `side` that ended `end`, in `ms`, answered by `by` (Z3 unless said). */
  add(question: Question, side: Side | undefined, end: End, ms: number, queries = 1, by: Engine = "z3"): void {
    const e = this.#entries.find((x) => x.question === question && x.side === side && x.by === by && x.end === end)
    if (e === undefined) this.#entries.push({ question, side, by, end, queries, ms })
    else {
      e.queries += queries
      e.ms += ms
    }
  }

  /** Each entry of `asked` added under its own question, or under `as`. */
  addAll(asked: ReadonlyArray<Asked>, as?: Question): void {
    for (const a of asked) this.add(as ?? a.question, a.side, a.end, a.ms, a.queries, a.by)
  }

  /** Each question, side, engine and end asked, in the order first asked. */
  get asked(): ReadonlyArray<Asked> {
    return this.#entries.map(({ question, side, by, end, queries, ms }) => ({
      question,
      ...(side === undefined ? {} : { side }),
      by,
      end,
      queries,
      ms,
    }))
  }
}

/** What each question's verdict takes of it when it ends without an answer, in a report's words. */
const TAKEN: Readonly<Record<Exclude<Question, "says-anything" | "proof" | "search" | "cover" | "obligation">, string>> = {
  unmeetable:
    "whether some result keeps every law at this input was not settled (END, at a tenth of `--work`): read as the code's counterexample",
  "cross-check": "not checked against the search side (END): proved on the proof side alone",
  undecided: "whether the laws decide every input was not settled (END): read as deciding it",
}

/** A question that ended `end` without an answer, as a note on its law or contract; `what` names what it was asked of. */
export const unansweredOf = (question: keyof typeof TAKEN, end: End, side?: Side, what?: string): Unanswered => ({
  question,
  ...(side === undefined ? {} : { side }),
  end,
  reason: `${what === undefined ? "" : `${what}: `}${TAKEN[question].replace("END", end)}`,
})

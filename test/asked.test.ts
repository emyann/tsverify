// How a query ended, what the check that a law says something decides from its two sides, and the sums of a ledger:
// the pure rules of src/asked.ts, without Z3.
import assert from "node:assert/strict"
import { it } from "node:test"
import { Ledger, STUCK_MS, endOf, endWords, saysAnything } from "../src/asked.ts"

it("a query ends answered, out of work, out of time or given up, and a stop said canceled before the clock is one at the work limit", () => {
  const rows: ReadonlyArray<readonly [Parameters<typeof endOf>, ReturnType<typeof endOf>]> = [
    [["sat", "", 10], "answered"],
    [["unsat", "", 10], "answered"],
    [["unknown", "max. resource limit exceeded", 2_000], "out of work"],
    // Z3 says a stop at the work limit "canceled" at times: before the clock fires, it is one.
    [["unknown", "canceled", 2_000], "out of work"],
    [["unknown", "canceled", STUCK_MS], "out of time"],
    [["unknown", "timeout", STUCK_MS + 1], "out of time"],
    [["unknown", "(incomplete quantifiers)", 2_000], "gave up"],
  ]
  for (const [args, end] of rows) assert.equal(endOf(...args), end, args.join(", "))
})

it("a stop at the work limit is said out of work, never out of time", () => {
  const said = endWords(endOf("unknown", "canceled", 2_000), "canceled")
  assert.match(said, /out of work/)
  assert.doesNotMatch(said, /out of time/)
})

it("a ledger sums the queries of one question, side and end, in the order first asked", () => {
  const l = new Ledger()
  l.add("proof", "proof", "answered", 3)
  l.add("says-anything", "search", "out of work", 5)
  l.add("proof", "proof", "answered", 4)
  l.add("proof", "proof", "out of work", 1)
  l.add("cross-check", undefined, "answered", 2)
  // A run's inputs are its queries, apart from Z3's.
  l.add("says-anything", undefined, "answered", 6, 1000, "run")
  assert.deepEqual(l.asked, [
    { question: "proof", side: "proof", by: "z3", end: "answered", queries: 2, ms: 7 },
    { question: "says-anything", side: "search", by: "z3", end: "out of work", queries: 1, ms: 5 },
    { question: "proof", side: "proof", by: "z3", end: "out of work", queries: 1, ms: 1 },
    { question: "cross-check", by: "z3", end: "answered", queries: 1, ms: 2 },
    { question: "says-anything", by: "run", end: "answered", queries: 1000, ms: 6 },
  ])
  const folded = new Ledger()
  folded.addAll(l.asked, "obligation")
  assert.deepEqual(folded.asked, [
    { question: "obligation", side: "proof", by: "z3", end: "answered", queries: 2, ms: 7 },
    { question: "obligation", side: "search", by: "z3", end: "out of work", queries: 1, ms: 5 },
    { question: "obligation", side: "proof", by: "z3", end: "out of work", queries: 1, ms: 1 },
    { question: "obligation", by: "z3", end: "answered", queries: 1, ms: 2 },
    { question: "obligation", by: "run", end: "answered", queries: 1000, ms: 6 },
  ])
})

it("the check that a law says something: a result that breaks it says so, none on the proof side says not, and no answer reads as saying something, said", () => {
  const sat = { status: "sat" } as const
  const unsat = { status: "unsat" } as const
  const out = { status: "unknown", end: "out of work" } as const
  const late = { status: "unknown", end: "out of time" } as const
  const rows: ReadonlyArray<readonly [string, Parameters<typeof saysAnything>, boolean, ReadonlyArray<string | undefined> | undefined]> = [
    // [name, (shown by a run, the proof side's query of the spec alone), vacuous, the unanswered entry's question, side and end]
    ["a run shows a result that breaks it", [true, undefined], false, undefined],
    ["none run, a result on the proof side", [false, sat], false, undefined],
    ["none on the proof side", [false, unsat], true, undefined],
    ["the proof side without an answer", [false, out], false, ["says-anything", "proof", "out of work"]],
    ["the proof side out of time", [false, late], false, ["says-anything", "proof", "out of time"]],
    ["the law not read on any result", [false, undefined], false, undefined],
  ]
  for (const [name, [byRun, proof], vacuous, unanswered] of rows) {
    const got = saysAnything(byRun, proof)
    assert.equal(got.vacuous, vacuous, name)
    assert.deepEqual(
      got.unanswered === undefined ? undefined : [got.unanswered.question, got.unanswered.side, got.unanswered.end],
      unanswered,
      name,
    )
  }
})

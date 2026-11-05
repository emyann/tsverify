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
  assert.deepEqual(l.asked, [
    { question: "proof", side: "proof", end: "answered", queries: 2, ms: 7 },
    { question: "says-anything", side: "search", end: "out of work", queries: 1, ms: 5 },
    { question: "proof", side: "proof", end: "out of work", queries: 1, ms: 1 },
    { question: "cross-check", end: "answered", queries: 1, ms: 2 },
  ])
  const folded = new Ledger()
  folded.addAll(l.asked, "obligation")
  assert.deepEqual(folded.asked, [
    { question: "obligation", side: "proof", end: "answered", queries: 2, ms: 7 },
    { question: "obligation", side: "search", end: "out of work", queries: 1, ms: 5 },
    { question: "obligation", side: "proof", end: "out of work", queries: 1, ms: 1 },
    { question: "obligation", end: "answered", queries: 1, ms: 2 },
  ])
})

it("the check that a law says something: a result that breaks it says so, none on the proof side says not, and no answer reads as saying something, said", () => {
  const sat = { status: "sat" } as const
  const unsat = { status: "unsat" } as const
  const out = { status: "unknown", end: "out of work" } as const
  const late = { status: "unknown", end: "out of time" } as const
  const rows: ReadonlyArray<readonly [string, Parameters<typeof saysAnything>, boolean, ReadonlyArray<string | undefined> | undefined]> = [
    // [name, (search, proof), vacuous, the unanswered entry's question, side and end]
    ["a result breaks it on the search side", [sat, undefined], false, undefined],
    ["none there, one on the proof side", [unsat, sat], false, undefined],
    ["the search side without an answer, one on the proof side", [out, sat], false, undefined],
    ["none on the proof side", [unsat, unsat], true, undefined],
    ["none on the proof side, the search side without an answer", [out, unsat], true, undefined],
    ["the proof side without an answer", [unsat, out], false, ["says-anything", "proof", "out of work"]],
    ["both sides without an answer", [out, late], false, ["says-anything", undefined, "out of time"]],
    ["the law not read on any result", [undefined, undefined], false, undefined],
  ]
  for (const [name, [search, proof], vacuous, unanswered] of rows) {
    const got = saysAnything(search, proof)
    assert.equal(got.vacuous, vacuous, name)
    assert.deepEqual(
      got.unanswered === undefined ? undefined : [got.unanswered.question, got.unanswered.side, got.unanswered.end],
      unanswered,
      name,
    )
  }
})

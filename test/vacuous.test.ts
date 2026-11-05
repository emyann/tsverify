// A law no result could break is reported `vacuous`, not `proved`: it would hold
// of any function with the same signature (fixtures/vacuous/sign.contract.ts).
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, it } from "node:test"
import { loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "fixtures/vacuous/sign.contract.ts")
const throws = path.join(root, "fixtures/runs/throws.contract.ts")
const project = loadProject([spec, throws], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const statuses = async (name: string) => Object.fromEntries((await verify(z3, project, spec, name)).laws.map((l) => [l.name, l.status]))

it("a law over the input alone, or whose condition is never met, is vacuous; one a wrong result would break is proved", async () => {
  assert.deepEqual(await statuses("signed"), { zeroOnlyAtZero: "proved", squareNotNegative: "vacuous", neverAsked: "vacuous" })
})

it("a law whose condition `requires` rules out is vacuous", async () => {
  assert.deepEqual(await statuses("positive"), { pos: "proved", negativeIsNeg: "vacuous" })
})

it("whether a law says something is asked of the spec alone: one broken only where the code throws says something", async () => {
  // `10n / x` throws at 0n, so no run of the code meets `x === 0n`; a result of the spec's type there breaks the law.
  for (const run of [false, true])
    assert.deepEqual(
      (await verify(z3, project, throws, "divided", { run })).laws.map((l) => l.status),
      ["proved"],
      `run: ${run}`,
    )
})

it("a run shows a law says something, and Z3 is not asked", async () => {
  const v = await verify(z3, project, spec, "signed", { run: true })
  const law = v.laws.find((l) => l.name === "zeroOnlyAtZero")!
  assert.ok(
    law.asked?.some((a) => a.question === "says-anything" && a.by === "run"),
    JSON.stringify(law.asked),
  )
  assert.ok(!law.asked?.some((a) => a.question === "says-anything" && a.by === "z3"), JSON.stringify(law.asked))
  assert.deepEqual(
    v.laws.map((l) => l.status),
    ["proved", "vacuous", "vacuous"],
  )
})

it("each law says the time of each question asked of it, by side and by how it ended", async () => {
  const v = await verify(z3, project, spec, "signed")
  for (const l of v.laws) {
    assert.ok(
      l.asked?.some((a) => a.question === "proof" && a.side === "proof" && a.queries >= 1),
      `${l.name}: ${JSON.stringify(l.asked)}`,
    )
    // Every proved law is asked whether it says something, of the spec alone: by Z3 on the proof side, where nothing ran.
    assert.ok(
      l.asked?.some((a) => a.question === "says-anything" && a.side === "proof" && a.by === "z3"),
      `${l.name}: ${JSON.stringify(l.asked)}`,
    )
    assert.ok(!l.asked?.some((a) => a.question === "says-anything" && a.side === "search"), `${l.name}: ${JSON.stringify(l.asked)}`)
    for (const a of l.asked ?? []) assert.ok(a.ms >= 0 && a.queries >= 1)
  }
  // The contract's own questions: every proved law checked against the search side.
  assert.ok(
    v.asked?.some((a) => a.question === "cross-check"),
    JSON.stringify(v.asked),
  )
  // And its whole time, which is no less than its laws' and its own questions' together.
  const parts = [...v.laws.flatMap((l) => l.asked ?? []), ...(v.asked ?? [])].reduce((n, a) => n + a.ms, 0)
  assert.ok(v.ms !== undefined && v.ms >= parts, `${v.ms} < ${parts}`)
})

/**
 * A work at which `zeroOnlyAtZero` is proved and its check of saying something, asked of the spec alone on the proof side
 * at a tenth of it, runs out. Found by sweeping `--work` with z3-solver 5.3.2: the check runs out at 150 and answers at
 * 160, the proof answers at 20, and the laws that say nothing are settled from 30. So at 800 the check, at 80, runs out;
 * asked at the whole 800, it would answer. A z3-solver upgrade may move these, and this is picked again the same way.
 */
const PINNED_WORK = 800

it("the check that a law says something is asked at a tenth of the work: one it cannot settle leaves the law proved, and says so", async () => {
  const v = await verify(z3, project, spec, "signed", { work: PINNED_WORK })
  const law = v.laws.find((l) => l.name === "zeroOnlyAtZero")!
  assert.equal(law.status, "proved")
  assert.deepEqual(
    law.unanswered?.map(({ question, side, end }) => ({ question, side, end })),
    [{ question: "says-anything", side: "proof", end: "out of work" }],
  )
  // The laws that say nothing are settled at that tenth too, and stay vacuous.
  assert.deepEqual(
    v.laws.map((l) => l.status),
    ["proved", "vacuous", "vacuous"],
  )
  // A work whose tenth is not a whole number is taken all the same: Z3 takes only whole numbers as a limit.
  assert.deepEqual(
    (await verify(z3, project, spec, "signed", { work: PINNED_WORK + 5 })).laws.map((l) => l.status),
    ["proved", "vacuous", "vacuous"],
  )
  // At the default work every check answers: no note.
  assert.equal((await verify(z3, project, spec, "signed")).laws.find((l) => l.name === "zeroOnlyAtZero")!.unanswered, undefined)
})

// Laws that leave a result open between two kinds at an input `requires` allows make the contract `undecided`, naming
// the part left open and an input where two results of different kinds both keep every law
// (fixtures/undecided/start.contract.ts). Laws that decide every input, a part named `open`, a spec wholly `open`, a hole
// outside `requires` and a free string leave it unset.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, it } from "node:test"
import { loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "fixtures/undecided/start.contract.ts")
const project = loadProject([spec], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const of = (name: string) => verify(z3, project, spec, name)

it("laws that only say when to refuse leave a start undecided between taken and refused", async () => {
  const v = await of("refusesOnly")
  assert.ok(
    v.laws.every((l) => l.status === "proved"),
    "every law proved: the code is not the question",
  )
  const u = v.undecided
  assert.ok(u !== undefined, "undecided")
  assert.equal(u.differ, "output === undefined")
  const [filed, attempt, started] = (u.args ?? []) as [boolean, bigint, bigint]
  assert.ok(filed && attempt === started + 1n, "a correctly numbered start of a filed task")
  assert.deepEqual(new Set((u.results ?? []).map((r) => (r === undefined ? "taken" : "refused"))), new Set(["refused", "taken"]))
})

it("laws that say both sides decide every input", async () => {
  assert.equal((await of("bothSides")).undecided, undefined)
})

it("a closed field the laws leave open is undecided, named by its path", async () => {
  assert.equal((await of("reasonUnsaid")).undecided?.differ, "output.reason")
})

it("a part named open, and a spec wholly open, are not asked", async () => {
  assert.equal((await of("reasonLeftOpen")).undecided, undefined)
  assert.equal((await of("safetyOnly")).undecided, undefined)
})

it("a union of strings left open is undecided, and a hole outside requires is none", async () => {
  const u = (await of("phaseLeftOpen")).undecided
  assert.ok(u !== undefined, "undecided")
  assert.equal(u.differ, "output")
  assert.deepEqual(new Set(u.results ?? []), new Set(["done", "failed"]))
  assert.equal((await of("holeOutsideRequires")).undecided, undefined)
})

it("two results that differ only in a free string are of one kind", async () => {
  assert.equal((await of("freeLabel")).undecided, undefined)
})

/**
 * Works at which `refusesOnly`'s laws are proved and a question around them runs out, found by sweeping `work` with
 * z3-solver 5.3.2: whether the laws decide every input runs out up to 2000 and answers from 2500, and the laws are
 * proved from 100 up; the cross-check of the laws against the search side runs out from 100 to 135 and answers from 140
 * (swept again once whether a law says anything was asked of the spec alone, which left fewer queries before it).
 * Picked again the same way after a z3-solver upgrade.
 */
const UNDECIDED_RUNS_OUT = 800
const CROSS_CHECK_RUNS_OUT = 120

it("whether the laws decide every input, unsettled, leaves the contract unflagged and says so", async () => {
  const v = await verify(z3, project, spec, "refusesOnly", { work: UNDECIDED_RUNS_OUT, cover: false })
  assert.deepEqual(
    v.laws.map((l) => l.status),
    ["proved", "proved"],
  )
  assert.equal(v.undecided, undefined)
  assert.deepEqual(
    v.unanswered?.map(({ question, side, end }) => ({ question, side, end })),
    [{ question: "undecided", side: "search", end: "out of work" }],
  )
})

it("the cross-check of a proved law, unsettled, leaves it proved and says so", async () => {
  const v = await verify(z3, project, spec, "refusesOnly", { work: CROSS_CHECK_RUNS_OUT, cover: false })
  for (const l of v.laws) {
    assert.equal(l.status, "proved", l.name)
    assert.ok(
      l.unanswered?.some((u) => u.question === "cross-check" && u.side === "search" && u.end === "out of work"),
      `${l.name}: ${JSON.stringify(l.unanswered)}`,
    )
  }
})

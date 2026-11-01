// A law broken where no result keeps every law at once is reported `unmeetable`, naming the laws that leave none: the
// spec has to change, since no code could keep it (fixtures/unmeetable/cap.contract.ts). A law the code merely breaks,
// where some result would keep it, stays a counterexample.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, it } from "node:test"
import { loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const spec = path.join(root, "fixtures/unmeetable/cap.contract.ts")
const project = loadProject([spec], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const lawsOf = async (name: string) =>
  Object.fromEntries((await verify(z3, project, spec, name)).laws.map((l) => [l.name, { status: l.status, conflicts: l.conflicts }]))

it("two laws no result keeps together at an input: the one broken there is unmeetable, naming both", async () => {
  const laws = await lawsOf("capped")
  assert.equal(laws.atMostTen?.status, "proved")
  assert.deepEqual(laws.atLeastTheInput, { status: "unmeetable", conflicts: ["atMostTen", "atLeastTheInput"] })
})

it("a law the code breaks where some result would keep it is a counterexample, not unmeetable", async () => {
  assert.deepEqual(await lawsOf("leftUncapped"), { atMostTen: { status: "counterexample", conflicts: undefined } })
})

it("one law that refuses every result where its condition holds is unmeetable alone", async () => {
  assert.deepEqual(await lawsOf("impossible"), { aboveAndBelow: { status: "unmeetable", conflicts: ["aboveAndBelow"] } })
})

it("the unmeetable law keeps its input, and its reason names the laws and the fix", async () => {
  const law = (await verify(z3, project, spec, "capped")).laws.find((l) => l.name === "atLeastTheInput")!
  assert.ok(law.args !== undefined && (law.args[0] as bigint) > 10n, "an input above 10")
  assert.match(law.reason ?? "", /atMostTen and atLeastTheInput together/)
  assert.match(law.reason ?? "", /change the spec/)
})

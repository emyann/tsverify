// Two wrong verdicts the verifier once gave (fixtures/soundness.ts): a proof
// that a plain promise never rejects, and a counterexample no double makes.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/soundness.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("verdicts the verifier once got wrong", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  it("an operation returning a plain promise may reject: 'it always succeeds' is refuted, and failure is reachable", async () => {
    const v = await verify(z3, project, file, "alwaysSucceeds")
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(
      v.laws.map((l) => l.status),
      ["counterexample"],
    )
    assert.equal(v.cover.find((c) => c.value === "Failure")?.status, "reachable")
  })

  it("a real no double holds is no counterexample: a law true of every double is not refuted", async () => {
    const v = await verify(z3, project, file, "noneBetween")
    const [law] = v.laws
    assert.notEqual(law?.status, "counterexample", JSON.stringify(law))
    assert.ok(law?.status === "proved" || law?.status === "bounded", JSON.stringify(law))
  })
})

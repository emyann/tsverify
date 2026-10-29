// The small cases: the bigint `charge`, every refusal, and a spec module that
// throws when imported (the verifier never runs what it judges).
import assert from "node:assert/strict"
import { after, before, describe, it } from "node:test"
import { init, killThreads } from "z3-solver"
import * as charge from "../fixtures/charge.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { verify } from "../src/verify.ts"

const fixture = (name: string) => new URL(`../fixtures/${name}.ts`, import.meta.url).pathname
const files = ["charge", "refused", "never-imported", "ill-typed"].map(fixture)
const project = loadProject(files, new URL("../tsconfig.json", import.meta.url).pathname)

let api: Awaited<ReturnType<typeof init>>
let z3: Ctx
before(async () => {
  api = await init()
  z3 = api.Context("main")
})
after(() => killThreads(api.em))

const statuses = async (file: string, name: string) =>
  Object.fromEntries((await verify(z3, project, fixture(file), name)).laws.map((l) => [l.name, l.status]))

it("the fixtures type-check", () => {
  for (const f of files) assert.deepEqual(diagnostics(project, f), [])
})

describe("charge", () => {
  it("proves the right code and the code written differently", async () => {
    const all = { nonNegative: "proved", leavesTheRest: "proved", zeroWhenShort: "proved" }
    assert.deepEqual(await statuses("charge", "right"), all)
    assert.deepEqual(await statuses("charge", "rewritten"), all)
  })

  it("refutes `return 0n` with an input the real code fails", async () => {
    const v = await verify(z3, project, fixture("charge"), "zero")
    const law = v.laws.find((l) => l.name === "leavesTheRest")!
    assert.equal(law.status, "counterexample")
    const input = law.args![0] as charge.ChargeInput
    assert.equal(charge.zero.requires!(input), true)
    assert.equal(charge.zero.ensures["leavesTheRest"]!(input, charge.chargeZero(input)), false)
  })

  it("refutes the code that can go negative", async () => {
    const v = await verify(z3, project, fixture("charge"), "negative")
    const law = v.laws.find((l) => l.name === "nonNegative")!
    assert.equal(law.status, "counterexample")
    const input = law.args![0] as charge.ChargeInput
    assert.ok(charge.chargeNegative(input) < 0n)
  })
})

describe("a refused construct leaves its contract unverified", () => {
  const cases: ReadonlyArray<readonly [string, RegExp]> = [
    ["cast", /a cast is a claim/],
    ["nonNull", /`!` is a claim/],
    ["numberArithmetic", /arithmetic on `number` rounds/],
    ["looseEquality", /operator == is not modeled/],
    ["letCapture", /`limit` is a binding the verifier cannot see/],
    ["bigintDivision", /bigint `\/` truncates/],
    ["loop", /only `const` bindings are modeled/],
    ["elementAccess", /element access on a array: `\.at\(0\)` reads an array/],
    ["global", /`Math` is a binding the verifier cannot see/],
    ["stringLength", /UTF-16 code units/],
  ]
  it("recursion: the recursive call is an unknown function of its arguments, said in the notes", async () => {
    const v = await verify(z3, project, fixture("refused"), "recursion")
    assert.equal(v.unsupported, undefined)
    assert.ok(v.notes.some((n) => /`countdown` was not read \(recursion is not modeled\)/.test(n)), v.notes.join("\n"))
  })
  it("unnarrowed: a member of a value the checker has not shown present", async () => {
    const v = await verify(z3, project, fixture("ill-typed"), "unnarrowed")
    assert.match(v.unsupported ?? "(verified)", /fixtures\/ill-typed\.ts:\d+:\d+: a member of a value the type checker has not shown/)
  })
  for (const [name, reason] of cases)
    it(`${name}`, async () => {
      const v = await verify(z3, project, fixture("refused"), name)
      assert.match(v.unsupported ?? "(verified)", reason)
      assert.match(v.unsupported!, /fixtures\/refused\.ts:\d+:\d+: /)
      assert.deepEqual(v.laws, [])
    })
})

describe("a spec module that throws when imported", () => {
  it("is verified from source", async () => {
    assert.deepEqual(await statuses("never-imported", "signContract"), { oneOfThree: "proved", followsTheValue: "proved" })
  })

  it("does throw when imported", async () => {
    await assert.rejects(import(fixture("never-imported")), /the verifier ran the module it judges/)
  })
})

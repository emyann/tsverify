// The small cases: the bigint `charge`, every refusal, a project whose types
// leave out `null`, and a spec module that throws when imported (the verifier
// never runs what it judges).
import assert from "node:assert/strict"
import { mkdtempSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as charge from "../fixtures/charge.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { verify, openZ3 } from "../src/verify.ts"

const fixture = (name: string) => new URL(`../fixtures/${name}.ts`, import.meta.url).pathname
const files = ["charge", "refused", "never-imported", "ill-typed", "reached"].map(fixture)
const project = loadProject(files, new URL("../tsconfig.json", import.meta.url).pathname)

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

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

describe("a counterexample shows what its run read of the world, and nothing else", () => {
  const worldOf = async (name: string) => {
    const law = (await verify(z3, project, fixture("reached"), name)).laws[0]
    assert.equal(law?.status, "counterexample")
    return { args: law.args, read: Object.keys(law.world ?? {}).map((k) => k.replace(/!\d+$/, "")) }
  }
  it("a clock read on the branch the run did not take is not shown", async () => {
    assert.deepEqual(await worldOf("neverOnTime"), { args: [false], read: [] })
  })
  it("one on the branch it took is", async () => {
    assert.deepEqual(await worldOf("alwaysOnTime"), { args: [true], read: ["date.iso"] })
  })
})

describe("a refused construct leaves its contract unverified", () => {
  const cases: ReadonlyArray<readonly [string, RegExp]> = [
    ["cast", /a cast is a claim the verifier would have to trust: check the value instead/],
    ["nonNull", /`!` is a claim the verifier would have to trust: check the value/],
    ["numberArithmetic", /arithmetic on `number` rounds.*: use `bigint` where the values are whole/],
    ["looseEquality", /operator == is not modeled: write `===`/],
    ["letCapture", /`limit` is a binding the verifier cannot see .*: read it from a `const` or an argument/],
    ["elementAccess", /`xs\[0\]` on an array is not read: write `xs\.at\(0\)`/],
    ["global", /`Math` is a binding the verifier cannot see/],
  ]
  it("recursion: the recursive call is refused, saying what to declare instead", async () => {
    const v = await verify(z3, project, fixture("refused"), "recursion")
    assert.match(
      v.unsupported ?? "(verified)",
      /`countdown` is not read \(recursion is not modeled\): declare what the verifier may assume of it, `assume\(countdown, /,
    )
  })
  it("unnarrowed: a member of a value the checker has not shown present", async () => {
    const v = await verify(z3, project, fixture("ill-typed"), "unnarrowed")
    assert.match(v.unsupported ?? "(verified)", /fixtures\/ill-typed\.ts:\d+:\d+: a member of a value the type checker has not shown/)
  })
  for (const [name, reason] of cases)
    it(name, async () => {
      const v = await verify(z3, project, fixture("refused"), name)
      assert.match(v.unsupported ?? "(verified)", reason)
      assert.match(v.unsupported!, /fixtures\/refused\.ts:\d+:\d+: /)
      assert.deepEqual(v.laws, [])
    })
})

it("a project whose types leave out `null` is refused, saying which option to set", async () => {
  const dir = mkdtempSync(path.join(tmpdir(), "tsverify-loose-"))
  try {
    const tsconfig = path.join(dir, "tsconfig.json")
    writeFileSync(
      tsconfig,
      JSON.stringify({ extends: new URL("../tsconfig.json", import.meta.url).pathname, compilerOptions: { strict: false } }),
    )
    const v = await verify(z3, loadProject([fixture("charge")], tsconfig), fixture("charge"), "right")
    assert.match(v.unsupported ?? "(verified)", /`strictNullChecks` is off .*: set `"strict": true`/)
    assert.deepEqual(v.laws, [])
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})

describe("a spec module that throws when imported", () => {
  it("is verified from source", async () => {
    assert.deepEqual(await statuses("never-imported", "signContract"), { oneOfThree: "proved", followsTheValue: "proved" })
  })

  it("does throw when imported", async () => {
    await assert.rejects(import(fixture("never-imported")), /the verifier ran the module it judges/)
  })
})

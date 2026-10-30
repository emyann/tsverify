// What the verifier takes on trust, rule by rule: a declared function's laws
// assumed at each call, a function nobody declared refused with what to write,
// a declaration of purity checked where the source is, `pure: false` fresh per
// call and kept out of laws, spec code kept from computations and the clock,
// and the report's trusted base.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { verify, openZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/trusted.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

const run = (name: string) => verify(z3, project, file, name)

it("the fixture type-checks", () => {
  assert.deepEqual(diagnostics(project, file), [])
})

describe("a declared function", () => {
  it("its law holds of every element of a quantifier, and the report names it as trusted, its purity checked", async () => {
    const v = await run("everyScoreNonNegative")
    assert.deepEqual(
      v.laws.map((l) => [l.name, l.status]),
      [["always", "proved"]],
    )
    assert.deepEqual(v.trusted, [
      { name: "score", declared: [v.trusted[0]!.declared[0]], purity: "checked", laws: ["nonNegative"], read: ["score"] },
    ])
    assert.match(v.trusted[0]!.declared[0]!, /fixtures\/trusted\.ts:\d+/)
  })

  it("what its laws do not say is not proved, and the counterexample says it leans on it", async () => {
    const v = await run("everyScorePositive")
    const law = v.laws[0]!
    assert.equal(law.status, "counterexample")
    assert.deepEqual(law.abstract, ["score"])
  })

  it("`pure: false`: each call its own result", async () => {
    const v = await run("twoReadsAgree")
    assert.equal(v.laws[0]!.status, "counterexample")
    assert.equal(v.trusted[0]!.purity, "impure")
  })
})

describe("refused, with what to write instead", () => {
  const cases: ReadonlyArray<readonly [string, RegExp]> = [
    [
      "undeclared",
      /`total` is not read \(`Math` is a binding the verifier cannot see.*\): declare what the verifier may assume of it, `assume\(total, \{ pure: true/,
    ],
    ["stamped", /`stamp` is declared pure and is not: .*changes its argument `log`\. Declare it `pure: false`/],
    [
      "uncovered",
      /`uniq \(lodash-es\)` is called with \(readonly number\[\]\), which no declaration covers: \(readonly string\[\]\) at packs\/lodash\.ts/,
    ],
    ["otherForm", /`clamp \(lodash-es\)` is called with \(number, 10\), which no declaration covers: \(number, number, number\)/],
    ["undeclaredPackage", /`compact` is a package's, which the verifier does not read: declare .*`assume\(compact/],
  ]
  for (const [name, why] of cases)
    it(name, async () => {
      const v = await run(name)
      assert.match(v.unsupported ?? "(verified)", why)
    })
})

describe("spec code", () => {
  const laws: ReadonlyArray<readonly [string, RegExp]> = [
    ["lawReadsTheClockThroughADeclaration", /spec code is deterministic, and `nowMs` is declared `pure: false`/],
    ["lawReadsTheClock", /spec code is deterministic and does not read the clock/],
    ["lawRunsAComputation", /spec code runs no computation: `fetchOne` is one/],
  ]
  for (const [name, why] of laws)
    it(name, async () => {
      const v = await run(name)
      assert.equal(v.laws[0]!.status, "unsupported")
      assert.match(v.laws[0]!.reason ?? "", why)
    })

  it("reads what the program computed with the clock: a binding keeps the mode of the code that wrote it", async () => {
    const v = await run("stampedNow")
    assert.deepEqual(
      v.laws.map((l) => [l.name, l.status]),
      [["keeps", "proved"]],
    )
  })
})

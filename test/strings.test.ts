// Strings as JavaScript has them (fixtures/strings.ts): `.length` counts UTF-16
// code units, and a counterexample's string comes back as the JavaScript string
// the model meant. Each law here fails on strings handed to Z3 as their UTF-8
// bytes, an emoji then being four characters.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { units } from "../fixtures/strings.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/strings.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("strings, as JavaScript counts them", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  it("`.length` counts UTF-16 code units: an emoji is two, an accented letter one", async () => {
    const v = await verify(z3, project, file, "unitsAsJavaScriptCounts")
    assert.deepEqual(statuses(v), { emojiIsTwo: "proved", accentIsOne: "proved", neverNegative: "proved" })
  })

  it("a law that counts an emoji as one is broken by the emoji, which comes back as JavaScript's string", async () => {
    const v = await verify(z3, project, file, "unitsMiscounted")
    const law = v.laws.find((l) => l.name === "emojiIsOne")
    assert.equal(law?.status, "counterexample")
    assert.deepEqual(law.args, ["😀"])
    assert.equal(units("😀"), 2)
  })
})

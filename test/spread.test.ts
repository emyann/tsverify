// Object spreads (fixtures/spread.ts): a key the spread value's type requires
// is read from it, through a union too, a later key overriding it; the report
// says what reading it assumed; a key the value may lack is refused.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/spread.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("object spreads", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  it("a key the type requires is read from the spread, and the key written after it wins", async () => {
    assert.deepEqual(statuses(await verify(z3, project, file, "renamed")), { keepsItsId: "proved", takesTheName: "proved" })
  })

  it("a key every member of a union requires is read too", async () => {
    assert.deepEqual(statuses(await verify(z3, project, file, "eitherId")), { sameId: "proved" })
  })

  it("the report says what reading it assumed of the value", async () => {
    const v = await verify(z3, project, file, "renamed")
    assert.ok(v.notes.some((n) => n.startsWith('A spread copies each property its value\'s type requires')), JSON.stringify(v.notes))
  })

  it("a key the value may lack is refused", async () => {
    const v = await verify(z3, project, file, "optionalKey")
    assert.match(v.unsupported ?? "(verified)", /`retries` is read from an object built with a spread of a value whose keys the verifier does not know/)
  })
})

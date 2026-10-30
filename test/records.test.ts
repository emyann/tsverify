// Records read by key and values of more than one kind (fixtures/records.ts): every law proved; the laws hold when the
// functions run; a bug planted in each is caught; a key `Object.prototype` holds is an obligation broken where nothing
// rules it out; and a counterexample reads a dictionary back as a plain object, a value of two kinds as the kind it is.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as fixture from "../fixtures/records.ts"
import { loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"
import { checkFixture } from "./fixture-plants.ts"

checkFixture(
  "records.ts",
  fixture,
  {
    filedAsItsRecordSays: [
      [{ a: { taskId: "t" } }, "a"],
      [{}, "sx"],
      [{ a: { taskId: null } }, "a"],
    ],
    saidOfEachPhase: [["waiting"], ["running"], ["done"]],
    modeOfASetting: [[true], [false], ["strict"], ["loose"]],
    kindOfAField: [["a"], [1], [undefined], [null]],
    blankWords: [[""], [" \t\n"], ["a"], [undefined], [" a "]],
    listsAWhenGiven: [[undefined], [["a"]], [["b"]], [[]]],
    prunedAtItsTime: [[{ id: "r" }], [{ id: "r", pruned: { at: "t", files: 1 } }]],
  },
  [
    {
      id: "R1",
      what: "a step with no record read as filed",
      change: ["return record === undefined ? null : record.taskId", 'return record === undefined ? "" : record.taskId'],
      contract: "filedAsItsRecordSays",
    },
    {
      id: "R2",
      what: "the words of another phase",
      change: ['running: "still running"', 'done: "still running"'],
      contract: "saidOfEachPhase",
    },
    {
      id: "R3",
      what: "a switch read as the other mode",
      change: ['setting ? "strict" : "off"', 'setting ? "loose" : "off"'],
      contract: "modeOfASetting",
    },
    { id: "R4", what: "null named apart", change: ["return typeof v", 'return v === null ? "null" : typeof v'], contract: "kindOfAField" },
    { id: "R5", what: "words not trimmed", change: ["!message.trim()", "!message"], contract: "blankWords" },
    {
      id: "R6",
      what: "another name asked",
      change: ['Boolean(xs?.includes("a"))', 'Boolean(xs?.includes("b"))'],
      contract: "listsAWhenGiven",
    },
    { id: "R7", what: "the run's id for its time", change: ["  return at\n", "  return run.id\n"], contract: "prunedAtItsTime" },
  ],
)

describe("records: keys of Object's, and what a counterexample reads back", () => {
  const file = path.resolve(import.meta.dirname, "../fixtures/records.ts")
  const project = loadProject([file], path.resolve(import.meta.dirname, "../tsconfig.json"))
  let z3: Ctx
  let close: () => Promise<void>
  before(async () => {
    ;({ z3, close } = await openZ3())
  })
  after(() => close())

  it("a key nothing rules out may be a name `Object.prototype` holds: `steps[name]` then finds Object's", async () => {
    const v = await verify(z3, project, file, "anyNameRead")
    const key = v.obligations.find((o) => o.kind === "key")
    assert.equal(key?.status, "counterexample")
    const [steps, name] = key.args as [fixture.Steps, string]
    assert.ok(name in Object.prototype && !Object.hasOwn(steps, name), name)
    // Run, the function gives what its type says it never does.
    assert.equal(fixture.filedAs(steps, name), undefined)
  })
  it("a dictionary is read back as a plain object, its entries its own keys", async () => {
    const v = await verify(z3, project, file, "neverFiled")
    const [law] = v.laws
    assert.equal(law?.status, "counterexample")
    const [steps, name] = law.args as [fixture.Steps, string]
    assert.equal(Object.getPrototypeOf(steps), Object.prototype)
    assert.ok(Object.hasOwn(steps, name))
    assert.notEqual(fixture.filedAs(steps, name), null)
  })
  it("a value of two kinds is read back as the kind it is", async () => {
    const v = await verify(z3, project, file, "neverStrict")
    const [law] = v.laws
    assert.equal(law?.status, "counterexample")
    const [setting] = law.args as [boolean | "strict"]
    assert.ok(setting === true || setting === "strict", String(setting))
    assert.equal(fixture.modeOf(setting), "strict")
  })
})

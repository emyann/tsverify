// Collections and keys (fixtures/collections.ts): every law proved; the laws hold when the functions run, on empty,
// one and several entries; a bug planted in each is caught; what is refused is refused with its reason; and the ends
// of a union told apart by `kind` are each found or shown never made.
import assert from "node:assert/strict"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import * as fixture from "../fixtures/collections.ts"
import { loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"
import { checkFixture } from "./fixture-plants.ts"

const job = (id: string, done: boolean, turn?: number): fixture.Job => (turn === undefined ? { id, done } : { id, done, turn })
checkFixture(
  "collections.ts",
  fixture,
  {
    pendingOnes: [[[]], [[job("a", true)]], [[job("a", false), job("b", true), job("c", false)]]],
    ownedOrNobody: [
      [new Map([["a", "ada"]]), job("a", false)],
      [new Map(), job("a", false)],
      [new Map([["b", "bo"]]), job("a", true)],
    ],
    finishedStates: [
      ["done", new Set()],
      ["failed", new Set()],
      ["x", new Set(["x"])],
      ["y", new Set(["x"])],
    ],
    lastWithATurn: [
      [[]],
      [[job("a", false, 1), job("b", false)]],
      [[job("a", false), job("b", false, 2)]],
      [[job("a", false, 1), job("b", false, 2)]],
    ],
    lastIdsKept: [
      [["a", "b", "c", "d"], 2],
      [["a"], 3],
      [[], 1],
      [["a", "b"], 1],
    ],
    saidOfAMove: [[{ to: "x", note: "n" }], [{ refused: "r" }]],
    taggedWhenAsked: [[true], [false]],
    labelNeverEmpty: [
      ["a", () => ""],
      ["a", (id: string) => `${id}!`],
      ["", () => ""],
    ],
    stepsOfACount: [[0n], [3n], [-4n]],
  },
  [
    {
      id: "K1",
      what: "the done jobs kept",
      change: ["jobs.filter((j) => !j.done)", "jobs.filter((j) => j.done)"],
      contract: "pendingOnes",
    },
    {
      id: "K2",
      what: "another default",
      change: ['owners.get(job.id) ?? "nobody"', 'owners.get(job.id) ?? "anybody"'],
      contract: "ownedOrNobody",
    },
    {
      id: "K3",
      what: "a state left out of a set",
      change: ['new Set(["done", "failed"])', 'new Set(["done"])'],
      contract: "finishedStates",
    },
    { id: "K4", what: "read from the start", change: ["[...jobs].reverse().find(", "[...jobs].find("], contract: "lastWithATurn" },
    { id: "K5", what: "the first n, not the last", change: ["ids.slice(-n)", "ids.slice(0, n)"], contract: "lastIdsKept" },
    { id: "K6", what: "the note for the destination", change: [": moved.to\n", ": moved.note\n"], contract: "saidOfAMove" },
    {
      id: "K7",
      what: "a note written either way",
      change: ['withNote ? { id: "a", note: "n" } : { id: "a" }', 'withNote ? { id: "a", note: "n" } : { id: "a", note: "" }'],
      contract: "taggedWhenAsked",
    },
    {
      id: "K8",
      what: "what the naming function gives, empty or not",
      change: ['return given === "" ? id : given', "return given"],
      contract: "labelNeverEmpty",
    },
  ],
)

describe("collections: refused, and the ends of a union", () => {
  const file = path.resolve(import.meta.dirname, "../fixtures/collections.ts")
  const project = loadProject([file], path.resolve(import.meta.dirname, "../tsconfig.json"))
  let z3: Ctx
  let close: () => Promise<void>
  before(async () => {
    ;({ z3, close } = await openZ3())
  })
  after(() => close())
  for (const [name, reason] of [
    ["reversedRefused", /`\.reverse\(\)` changes the array it is called on/],
    ["optionalKeyRefused", /makes `note` optional is not modeled/],
    ["sizeRefused", /read through `has` and `get`: `\.size` is not modeled/],
  ] as const)
    it(`${name}: refused, saying why`, async () => {
      const v = await verify(z3, project, file, name)
      assert.match(v.unsupported ?? v.laws.map((l) => l.reason ?? "").join(" "), reason)
    })
  it("the ends of a union told apart by `kind`: two made, one never", async () => {
    const v = await verify(z3, project, file, "stepsOfACount")
    assert.deepEqual(Object.fromEntries(v.cover.map((c) => [c.value, c.status])), {
      'kind: "even"': "reachable",
      'kind: "odd"': "reachable",
      'kind: "never"': "unreachable",
    })
  })
  it("`only` decides the laws it names, and asks no cover", async () => {
    const v = await verify(z3, project, file, "pendingOnes", { only: ["lastNotDone"] })
    assert.deepEqual(
      v.laws.map((l) => [l.name, l.status]),
      [["lastNotDone", "proved"]],
    )
    assert.deepEqual(v.cover, [])
  })
})

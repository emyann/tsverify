// A map the code builds at keys it computes (fixtures/maps.ts): Nemia's `inheritedLabels`, copied as it is written. Four
// of its laws are proved, by the round that reads what its first loop writes at each key as unknown; the other four are
// left bounded or unknown, never refuted on the code as written. Two laws that do not hold are refuted, and a bug planted
// against each law proved is caught, each counterexample breaking the law when the code runs on it. Each construct it
// takes is checked against JavaScript on its own, in a process of its own (`maps-constructs.test.ts`).
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import * as fixture from "../fixtures/maps.ts"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { type LawResult, type Verification, openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/maps.ts")
const tsconfig = path.join(root, "tsconfig.json")
const project = loadProject([file], tsconfig)
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
const lawOf = (v: Verification, name: string): LawResult => {
  const l = v.laws.find((x) => x.name === name)
  assert.ok(l !== undefined, `no law ${name}`)
  return l
}

/**
 * What the contract is verified with: the search side's arrays of one element, and a third of a query's usual work.
 * At two elements the search side runs out of work on this function, and refutes none of the planted bugs; with the
 * usual work, the queries that do not end hold enough of Z3's memory, one after another, to run it out.
 */
const SETTINGS = { bound: 1, work: 5_000_000, cover: false } as const
const PROVED = ["typedWins", "droppedAtStart", "cardOverRuns", "leftOutOnlyDisagreed"] as const
const OPEN = ["agreedInherited", "disagreedLeftOut", "leftOutNamesEachRun", "nothingElse"] as const

type Start = Parameters<typeof fixture.inheritedLabels>[0]
type Contract = typeof fixture.inheritedLabelsLaws | typeof fixture.inheritedLabelsWrong
type Law = (run: { readonly input: ReadonlyArray<unknown>; readonly output: unknown }) => boolean

/** Whether running `inherited` on `args` breaks `law` of `contract`, `requires` holding there. */
const breaks = (contract: Contract, inherited: (s: Start) => fixture.Inherited, law: string, args: ReadonlyArray<unknown>): boolean => {
  const [start] = args as [Start]
  assert.ok(contract.requires?.({ input: [start] }) ?? true, "the counterexample meets `requires`")
  const l = (contract.ensures as Record<string, Parameters<typeof holds>[0]>)[law]!
  return !(holds(l) as Law)({ input: [start], output: inherited(start) })
}

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("inheritedLabels, as Nemia writes it", () => {
  it("the fixture type-checks", () => {
    assert.deepEqual(diagnostics(project, file), [])
  })

  let v: Verification | undefined
  it("typedWins, droppedAtStart, cardOverRuns and leftOutOnlyDisagreed are proved, by the round that reads the first loop's writes as unknown", async () => {
    v = await verify(z3, project, file, "inheritedLabelsLaws", SETTINGS)
    assert.equal(v.unsupported, undefined)
    for (const name of PROVED) {
      const l = lawOf(v, name)
      assert.equal(l.status, "proved", `${name}: ${JSON.stringify(statuses(v))}`)
      assert.match(l.reason ?? "", /writes at each key unknown/)
    }
    assert.ok(
      v.obligations.every((o) => o.status === "proved"),
      JSON.stringify(v.obligations),
    )
  })

  it("the other four are never refuted on the code as written: each is bounded or unknown", () => {
    assert.ok(v !== undefined, "verified above")
    for (const name of OPEN) assert.ok(["bounded", "unknown"].includes(lawOf(v, name).status), `${name}: ${lawOf(v, name).status}`)
  })

  it("two laws that do not hold are refuted, the round that reads the loop's writes as unknown proving neither", async () => {
    const w = await verify(z3, project, file, "inheritedLabelsWrong", SETTINGS)
    assert.deepEqual(statuses(w), { typedNeverHeld: "counterexample", agreedNeverHeld: "counterexample" })
    for (const l of w.laws) assert.ok(breaks(fixture.inheritedLabelsWrong, fixture.inheritedLabels, l.name, l.args ?? []), l.name)
  })
})

describe("inheritedLabels: a bug planted against each law the first round proves", () => {
  const plants = [
    {
      id: "M1",
      law: "typedWins",
      what: "a typed edit sets the key's name",
      change: ["out[edit.key] = edit.value", "out[edit.key] = edit.key"],
    },
    { id: "M2", law: "droppedAtStart", what: "key- sets the key empty", change: ["else delete out[edit.key]", 'else out[edit.key] = ""'] },
    {
      id: "M3",
      law: "cardOverRuns",
      what: "the card's key is given its name",
      change: ["of Object.entries(card)) out[key] = value", "of Object.entries(card)) out[key] = key"],
    },
    {
      id: "M4",
      law: "leftOutOnlyDisagreed",
      what: "a key the runs agree on left out too",
      change: ["else leftOut.push({ key, values })", "leftOut.push({ key, values })"],
    },
  ] as const
  for (const p of plants)
    it(`${p.id}, ${p.what}: ${p.law} refuted, and the planted code breaks it on the counterexample`, async () => {
      const original = readFileSync(file, "utf8")
      assert.equal(original.split(p.change[0]).length - 1, 1, `${p.id}: the text to change must occur once`)
      const text = original.replace(p.change[0], p.change[1])
      const v = await verify(z3, loadProject([file], tsconfig, new Map([[file, text]])), file, "inheritedLabelsLaws", {
        ...SETTINGS,
        only: [p.law],
      })
      const l = lawOf(v, p.law)
      assert.equal(l.status, "counterexample", JSON.stringify(statuses(v)))
      const planted = path.join(root, `fixtures/maps.planted-${p.id}.ts`)
      writeFileSync(planted, text)
      try {
        const m = (await import(pathToFileURL(planted).href)) as typeof fixture
        assert.ok(breaks(m.inheritedLabelsLaws, m.inheritedLabels, p.law, l.args ?? []), JSON.stringify(l.args))
        // The code as written keeps it there.
        assert.ok(!breaks(fixture.inheritedLabelsLaws, fixture.inheritedLabels, p.law, l.args ?? []))
      } finally {
        rmSync(planted)
      }
    })
})

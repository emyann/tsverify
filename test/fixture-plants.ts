// What `test/methods.test.ts` and `test/signs.test.ts` share: a fixture whose every law is proved, whose laws hold when
// its functions run on given inputs, and a bug planted in each, caught, the planted code breaking a law it refutes
// when run on those inputs.
import assert from "node:assert/strict"
import { readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")

export interface Plant {
  readonly id: string
  readonly what: string
  readonly change: readonly [find: string, replace: string]
  readonly contract: string
}

type Law = (run: { readonly input: ReadonlyArray<unknown>; readonly output: unknown }) => boolean
interface Contract {
  readonly fn: (...a: Array<unknown>) => unknown
  readonly requires?: (given: { readonly input: ReadonlyArray<unknown> }) => boolean
  readonly ensures: Record<string, Parameters<typeof holds>[0]>
}

/** Registers the tests of the fixture `name` (`methods.ts`): its contracts, each with the inputs it is run on, and its plants. */
export const checkFixture = (
  name: string,
  module: Record<string, unknown>,
  inputs: Readonly<Record<string, ReadonlyArray<ReadonlyArray<unknown>>>>,
  plants: ReadonlyArray<Plant>,
): void => {
  const file = path.join(root, "fixtures", name)
  const tsconfig = path.join(root, "tsconfig.json")
  const project = loadProject([file], tsconfig)
  let z3: Ctx
  let close: () => Promise<void>
  before(async () => {
    ;({ z3, close } = await openZ3())
  })
  after(() => close())
  const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
  /** The laws of `contract` that `m`'s function breaks on its inputs, where its `requires` allows them. */
  const brokenBy = (m: Record<string, unknown>, contract: string): Set<string> => {
    const c = m[contract] as Contract
    const broken = new Set<string>()
    for (const args of inputs[contract] ?? []) {
      if (c.requires !== undefined && !c.requires({ input: args })) continue
      const out = c.fn(...args)
      for (const [law, l] of Object.entries(c.ensures)) if (!(holds(l) as Law)({ input: args, output: out })) broken.add(law)
    }
    return broken
  }

  describe(`${name}, verified`, () => {
    it("the fixture type-checks", () => {
      assert.deepEqual(diagnostics(project, file), [])
    })
    for (const contract of Object.keys(inputs))
      it(`${contract}: every law proved, and every obligation`, async () => {
        const v = await verify(z3, project, file, contract)
        assert.equal(v.unsupported, undefined)
        assert.ok(
          v.laws.every((l) => l.status === "proved"),
          JSON.stringify(statuses(v)),
        )
        assert.ok(v.obligations.every((o) => o.status === "proved"))
      })
  })

  describe(`${name}: the laws hold when the functions run`, () => {
    for (const contract of Object.keys(inputs))
      it(contract, () => {
        assert.deepEqual([...brokenBy(module, contract)], [])
      })
  })

  describe(`${name}: a bug planted in each`, () => {
    for (const p of plants)
      it(`${p.id}, ${p.what}: caught, and the planted code breaks a law it refutes when run`, async () => {
        const original = readFileSync(file, "utf8")
        assert.equal(original.split(p.change[0]).length - 1, 1, `${p.id}: the text to change must occur once`)
        const text = original.replace(p.change[0], p.change[1])
        const v = await verify(z3, loadProject([file], tsconfig, new Map([[file, text]])), file, p.contract)
        assert.equal(v.unsupported, undefined)
        const refuted = v.laws.filter((l) => l.status === "counterexample").map((l) => l.name)
        assert.ok(refuted.length > 0, JSON.stringify(statuses(v)))
        const planted = path.join(root, `fixtures/${name.replace(/\.ts$/, "")}.planted-${p.id}.ts`)
        writeFileSync(planted, text)
        try {
          const seen = brokenBy((await import(pathToFileURL(planted).href)) as Record<string, unknown>, p.contract)
          assert.ok(
            refuted.some((l) => seen.has(l)),
            `refuted ${refuted.join(", ")}; runs broke ${[...seen].join(", ") || "nothing"}`,
          )
        } finally {
          rmSync(planted)
        }
      })
  })
}

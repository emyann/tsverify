// A spec written before the code (examples/charge): the implementation takes the
// spec as its type, `Implementation<ChargeSpec>` (`ChargeSpec` the spec's type,
// or `typeof chargeSpec` in place), through a type-only import, so nothing of the
// spec runs. The verifier finds the spec from that type and proves its laws; a
// wrong body is refuted with an input the real code breaks on; a wrong signature
// does not type-check; and a type that names no spec is refused.
import assert from "node:assert/strict"
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import ts from "typescript"
import { chargeSpec } from "../examples/charge/charge.contract.ts"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, type Verification, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const source = path.join(root, "examples/charge/charge.ts")
const tsconfig = path.join(root, "tsconfig.json")
const statuses = (v: Verification) => Object.fromEntries(v.laws.map((l) => [l.name, l.status]))
const withBody = (body: string) => readFileSync(source, "utf8").replace("(amount > balance ? 0n : balance - amount)", body)

let z3: Ctx
let close: () => Promise<void>
before(async () => {
  ;({ z3, close } = await openZ3())
})
after(() => close())

describe("charge, written against its spec", () => {
  it("type-checks, and nothing of the spec is left in what runs", () => {
    assert.deepEqual(diagnostics(loadProject([source], tsconfig), source), [])
    const js = ts.transpileModule(readFileSync(source, "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext },
    }).outputText
    assert.doesNotMatch(js, /import|charge\.contract|tsverify/)
  })

  it("is proved: the verifier finds the spec from the implementation's type", async () => {
    const v = await verify(z3, loadProject([source], tsconfig), source, "charge")
    assert.equal(v.unsupported, undefined)
    assert.deepEqual(statuses(v), { neverNegative: "proved", takesWhatItCan: "proved" })
  })

  it("a body that type-checks and is wrong is refuted, on an input the real code breaks on", async () => {
    const text = withBody("0n")
    const project = loadProject([source], tsconfig, new Map([[source, text]]))
    assert.deepEqual(diagnostics(project, source), [])
    const v = await verify(z3, project, source, "charge")
    const law = v.laws.find((l) => l.name === "takesWhatItCan")!
    assert.equal(law.status, "counterexample", JSON.stringify(statuses(v)))
    // Run from a folder of its own: `test/cli.test.ts` counts the files of examples/charge. It imports only types.
    const dir = mkdtempSync(path.join(tmpdir(), "tsverify-charge-"))
    const planted = path.join(dir, "charge.planted.ts")
    writeFileSync(planted, text)
    try {
      const { charge } = (await import(pathToFileURL(planted).href)) as { charge: (b: bigint, a: bigint) => bigint }
      const [balance, amount] = law.args as [bigint, bigint]
      assert.equal(holds(chargeSpec.ensures.takesWhatItCan!)(balance, amount, charge(balance, amount)), false)
    } finally {
      rmSync(dir, { recursive: true, force: true })
    }
  })

  it("a body of the wrong type does not type-check: the spec's type is the implementation's", () => {
    const project = loadProject([source], tsconfig, new Map([[source, withBody('"none"')]]))
    assert.ok(diagnostics(project, source).length > 0)
  })

  it("a spec of a function whose result is a union types each law over the whole union", () => {
    const spec = path.join(root, "examples/charge/light.contract.ts")
    const text = `import { spec } from "tsverify"\nexport const NextSpec = spec<(light: "red" | "green") => "red" | "green">({ ensures: { changes: (light, next) => next !== light } })\n`
    assert.deepEqual(diagnostics(loadProject([spec], tsconfig, new Map([[spec, text]])), spec), [])
  })

  it("finds the spec through `typeof` in place, and through a type of the spec's own name", async () => {
    const inPlace = readFileSync(source, "utf8")
      .replace("import type { ChargeSpec }", "import type { chargeSpec }")
      .replace("Implementation<ChargeSpec>", "Implementation<typeof chargeSpec>")
    const spec = path.join(root, "examples/charge/charge.contract.ts")
    const oneName = readFileSync(spec, "utf8")
      .replace("export const chargeSpec = spec", "export const ChargeSpec = spec")
      .replace("export type ChargeSpec = typeof chargeSpec", "export type ChargeSpec = typeof ChargeSpec")
    for (const files of [new Map([[source, inPlace]]), new Map([[spec, oneName]])]) {
      const project = loadProject([source], tsconfig, files)
      assert.deepEqual(diagnostics(project, source), [])
      assert.deepEqual(statuses(await verify(z3, project, source, "charge")), { neverNegative: "proved", takesWhatItCan: "proved" })
    }
  })

  it("a type that names no spec is refused, saying what it takes", async () => {
    const text = `import type { Implementation } from "tsverify"\nconst notASpec = { "~fn": (x: bigint) => x }\nexport const f: Implementation<typeof notASpec> = (x) => x\n`
    const v = await verify(z3, loadProject([source], tsconfig, new Map([[source, text]])), source, "f")
    assert.match(v.unsupported ?? "", /`notASpec` is no spec: write `const notASpec = spec<F>\(\{ \.\.\. \}\)`/)
    const typed = `import type { Implementation } from "tsverify"\nexport const f: Implementation<{ "~fn"?: (x: bigint) => bigint }> = (x) => x\n`
    const w = await verify(z3, loadProject([source], tsconfig, new Map([[source, typed]])), source, "f")
    assert.match(
      w.unsupported ?? "",
      /an implementation names its spec: `Implementation<ChargeSpec>`, where `export type ChargeSpec = typeof chargeSpec`/,
    )
  })
})

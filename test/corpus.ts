// The corpus (fixtures/corpus): problems published with Z3, each ported to a function and its laws, beside what
// JavaScript makes of each law. Every verdict is held to it:
// - a law proved holds on every sample, and JavaScript says it is valid: else the proof is unsound;
// - a counterexample breaks the law when the function runs on it, and JavaScript says the law is invalid: else it is a
//   false alarm;
// - a law tsverify cannot judge yet has the gap its case names, and no other: a gap closed is a case to update.
// The truth itself is checked too: a valid law holds on every sample, and an invalid one fails on its witness.
import assert from "node:assert/strict"
import { readdirSync } from "node:fs"
import path from "node:path"
import { after, before, describe, it } from "node:test"
import { pathToFileURL } from "node:url"
import type { Case, Gap, Truth } from "../fixtures/corpus/cases.ts"
import { holds } from "../src/contract.ts"
import { diagnostics, loadProject } from "../src/project.ts"
import type { Ctx } from "../src/value.ts"
import { openZ3, verify } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const dir = path.join(root, "fixtures/corpus")

/** Registers the corpus file `name` (`integers.ts`), each of its cases a test: one test file per corpus file, run apart. */
export const checkCorpus = (name: string): void => {
  const file = path.join(dir, name)
  const project = loadProject([file], path.join(root, "tsconfig.json"))
  let z3: Ctx
  let close: () => Promise<void>
  before(async () => {
    ;({ z3, close } = await openZ3())
  })
  after(() => close())
  describe(`corpus: ${name}`, async () => {
    const module = (await import(pathToFileURL(file).href)) as Record<string, unknown> & { cases: Readonly<Record<string, Case>> }
    it("type-checks", () => {
      assert.deepEqual(diagnostics(project, file), [])
    })
    for (const [contractName, c] of Object.entries(module.cases))
      it(`${contractName} (${c.source})`, () => judged(z3, project, file, module, contractName, c))
  })
}

/** Every file of the corpus, which `corpus-files.test.ts` holds each to have its test file. */
export const CORPUS = readdirSync(dir).filter((f) => f.endsWith(".ts") && f !== "cases.ts")

type Fn = (...args: Array<unknown>) => unknown
type Pred = (...args: Array<unknown>) => boolean
interface Contract {
  readonly fn: Fn
  readonly requires?: Pred
  readonly ensures: Readonly<Record<string, Parameters<typeof holds>[0]>>
}

/** What the function gives on `args`, where its `requires` allows them and it returns; `undefined` where not. */
const ran = (c: Contract, args: ReadonlyArray<unknown>): { out: unknown } | undefined => {
  if (c.requires !== undefined && !c.requires(...args)) return undefined
  try {
    return { out: c.fn(...args) }
  } catch {
    return undefined
  }
}
const lawHolds = (c: Contract, law: string, args: ReadonlyArray<unknown>, out: unknown): boolean =>
  (holds(c.ensures[law]!) as Pred)(...args, out)

const truthOf = (t: Truth | readonly [Truth, Gap]): Truth => (typeof t === "string" ? t : t[0])
const gapOf = (t: Truth | readonly [Truth, Gap]): Gap | undefined => (typeof t === "string" ? undefined : t[1])
const GAP: Readonly<Record<string, Gap>> = { unsupported: "refused", bounded: "bounded", unknown: "unknown" }

/** Holds one case's verdicts, and its truth, to what JavaScript does. */
const judged = async (
  z3: Ctx,
  project: ReturnType<typeof loadProject>,
  file: string,
  module: Record<string, unknown>,
  contractName: string,
  c: Case,
): Promise<void> => {
  const contract = module[contractName] as Contract
  const wrong: Array<string> = []
  // The truth, by running the function.
  for (const [law, t] of Object.entries(c.laws)) {
    assert.ok(contract.ensures[law] !== undefined, `${law}: no such law`)
    if (truthOf(t) === "valid")
      for (const args of c.samples) {
        const r = ran(contract, args)
        if (r !== undefined && !lawHolds(contract, law, args, r.out))
          wrong.push(`${law} is said valid, but fails when run on ${show(args)}`)
      }
    else {
      const w = c.witnesses?.[law]
      const r = w === undefined ? undefined : ran(contract, w)
      if (w === undefined) wrong.push(`${law} is said invalid, with no witness`)
      else if (r === undefined || lawHolds(contract, law, w, r.out))
        wrong.push(`${law} is said invalid, but its witness ${show(w)} does not break it`)
    }
  }
  // The verdicts, held to it.
  // The default work a query: a case it does not decide within it is a gap the case names.
  const v = await verify(z3, project, file, contractName)
  for (const [law, t] of Object.entries(c.laws)) {
    const result = v.laws.find((l) => l.name === law)
    const status = result?.status ?? (v.unsupported !== undefined ? "unsupported" : "missing")
    const gap = gapOf(t)
    if (status === "proved") {
      if (truthOf(t) === "invalid") wrong.push(`UNSOUND: ${law} proved, but its witness breaks it`)
      for (const args of c.samples) {
        const r = ran(contract, args)
        if (r !== undefined && !lawHolds(contract, law, args, r.out))
          wrong.push(`UNSOUND: ${law} proved, but fails when run on ${show(args)}`)
      }
    } else if (status === "counterexample") {
      const args = result!.args!
      const r = ran(contract, args)
      if (truthOf(t) === "valid") wrong.push(`false alarm: ${law} refuted at ${show(args)}, but it is valid`)
      else if (r === undefined || lawHolds(contract, law, args, r.out))
        wrong.push(`false alarm: ${law} refuted at ${show(args)}, where running it does not break it`)
    } else if (GAP[status] === undefined) wrong.push(`${law}: ${status}${result?.reason === undefined ? "" : `, ${result.reason}`}`)
    // Read and not judged is one gap, whether the solver ran out of work (`unknown`) or not (`bounded`).
    const unjudged = (g: Gap | undefined) => (g === "bounded" || g === "unknown" ? "unjudged" : g)
    if (gap !== undefined && unjudged(GAP[status]) !== unjudged(gap))
      wrong.push(`${law}: the case says ${gap}, tsverify says ${status}: update the case`)
    if (gap === undefined && GAP[status] !== undefined)
      wrong.push(`${law}: ${status}${result?.reason === undefined ? `, ${v.unsupported ?? ""}` : `, ${result.reason}`}`)
  }
  assert.deepEqual(wrong, [])
}

const show = (args: ReadonlyArray<unknown>): string =>
  `(${args.map((a) => (typeof a === "bigint" ? `${a}n` : typeof a === "string" ? JSON.stringify(a) : Array.isArray(a) ? `[${a.join(", ")}]` : String(a))).join(", ")})`

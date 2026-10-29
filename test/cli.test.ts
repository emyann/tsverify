// The command: every contract of a folder, a total and the exit code; one
// contract by name, with everything known of it; the same as one JSON
// document; a path that is not there.
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import path from "node:path"
import { it } from "node:test"

const root = path.resolve(import.meta.dirname, "..")
const cli = (...args: Array<string>) => {
  const r = spawnSync(process.execPath, [path.join(root, "src/cli.ts"), ...args], { cwd: root, encoding: "utf8", timeout: 300_000 })
  return { code: r.status, out: r.stdout, err: r.stderr }
}

it("verifies every contract under a folder, and exits 1 on a vacuous law", () => {
  const r = cli("fixtures/vacuous")
  assert.equal(r.code, 1, r.err)
  assert.match(r.out, /^fixtures\/vacuous\/sign\.spec\.ts\n  signed\n/)
  assert.match(r.out, /\n {4}vacuous +squareNotNegative /)
  assert.match(r.out, /\n2 contracts in 1 file: laws 2 proved, 3 vacuous\n$/)
})

it("exits 0 when every law and every obligation is proved", () => {
  const r = cli(...["account.spec", "withdraw", "withdraw.async", "effects.spec"].map((f) => `examples/account/${f}.ts`))
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /\n7 contracts in 4 files: laws 28 proved; obligations 10 proved\n$/)
})

it("finds a spec's implementation in a folder, the spec file holding none", () => {
  const r = cli("examples/charge")
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /^examples\/charge\/charge\.ts\n {2}charge\n/)
  assert.match(r.out, /\n1 contract in 1 file: laws 2 proved\n$/)
})

it("exits 1 when a law is only bounded: a loop of steps over an array of unknown length", () => {
  const r = cli("examples/account/imports.spec.ts")
  assert.equal(r.code, 1, r.out + r.err)
  assert.match(r.out, /\n5 contracts in 1 file: laws 11 proved, 8 bounded\n$/)
})

it("verifies one contract by name, with what it reaches, trusted and assumed", () => {
  const r = cli("examples/account/withdraw.ts", "withdraw")
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /^withdraw\n/)
  assert.match(r.out, /\n {2}reaches: /)
  assert.match(r.out, /\n {2}trusted \(declared, not proved\):\n {4}- accountOf: pure, checked from source/)
  assert.match(r.out, /\n {2}assumed:\n/)
})

it("refuses a path that is not there, with code 2", () => {
  const r = cli("no/such/folder")
  assert.equal(r.code, 2)
  assert.match(r.err, /no such file or folder/)
})

it("refuses a --project that is not there, with code 2", () => {
  const r = cli("examples/charge", "--project", "no/tsconfig.json")
  assert.equal(r.code, 2)
  assert.match(r.err, /--project no\/tsconfig\.json: no such file/)
})

interface Report {
  readonly passed: boolean
  readonly contracts: ReadonlyArray<{
    readonly file: string
    readonly contract: string
    readonly passed: boolean
    readonly laws: ReadonlyArray<{ readonly name: string; readonly status: string; readonly args?: unknown; readonly world?: unknown }>
  }>
  readonly totals: { readonly contracts: number; readonly files: number; readonly laws: Readonly<Record<string, number>> }
}

it("--json: one document and nothing else, its passed what the exit code says", () => {
  const r = cli("examples/charge", "--json")
  assert.equal(r.code, 0, r.err)
  const report = JSON.parse(r.out) as Report
  assert.equal(report.passed, true)
  assert.deepEqual(
    report.contracts.map((c) => [c.file, c.contract, c.passed, c.laws.map((l) => l.status)]),
    [["examples/charge/charge.ts", "charge", true, ["proved", "proved"]]],
  )
  assert.deepEqual(report.totals, { contracts: 1, files: 1, laws: { proved: 2 }, obligations: {}, unsupported: 0 })
})

it("--json: a counterexample's world is what the world gave the code, none of the verifier's own names", () => {
  const r = cli("examples/lodash/labels.spec.ts", "--json")
  assert.equal(r.code, 1, r.err)
  const report = JSON.parse(r.out) as Report
  assert.equal(report.passed, false)
  const law = report.contracts.find((c) => c.contract === "labels")?.laws.find((l) => l.name === "severalOnlyWithTwoDifferent")
  assert.equal(law?.status, "counterexample")
  // The labels, and what `uniq` was taken to return for them: the two the same, which lodash would never return.
  const [labels] = law.args as [ReadonlyArray<string>]
  assert.deepEqual(Object.values(law.world as Record<string, unknown>), [labels])
  assert.deepEqual(Object.keys(law.world as Record<string, unknown>).map((k) => k.replace(/!\d+$/, "")), ["uniq"])
})

// The package as a project installs it: packed (`npm pack`, which builds `dist/`)
// and installed from the tarball into a project of its own, the library's
// examples copied in. The installed command reaches the verdicts the source
// reaches on the same files, though it reads what the build made: the
// declarations of `@emyann/tsverify` and `@emyann/tsverify/effect`, a loop's `invariant`
// declared in a `.d.ts` (read by the statements and by the purity check), and
// the lodash pack from under `node_modules`. A planted bug exits 1, with a
// counterexample the installed code breaks on when it runs.
import assert from "node:assert/strict"
import { spawn, spawnSync } from "node:child_process"
import { cpSync, mkdtempSync, readFileSync, realpathSync, rmSync, statSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import path from "node:path"
import { after, before, describe, it } from "node:test"

const root = path.resolve(import.meta.dirname, "..")
const manifest = JSON.parse(readFileSync(path.join(root, "package.json"), "utf8")) as {
  name: string
  version: string
  devDependencies: Readonly<Record<string, string>>
}
/** The tarball `npm pack` writes: a scoped name's `@scope/name` as `scope-name`. */
const TARBALL = `${manifest.name.replace(/^@/, "").replace("/", "-")}-${manifest.version}.tgz`
const dev = (name: string) => `${name}@${manifest.devDependencies[name]}`

// The examples that reach what only an installed copy reads differently, the
// bench's planted copies left out. Named one by one: a test planting bugs
// beside them writes files the folders would hold for a while.
const FILES = [
  "account/account.contract.ts",
  "account/account.ts",
  "account/withdraw.contract.ts",
  "account/withdraw.ts",
  "account/withdraw.async.ts",
  "account/laws.ts",
  "charge/charge.contract.ts",
  "charge/charge.ts",
  "lodash/labels.contract.ts",
  "lodash/labels.ts",
].map((f) => `examples/${f}`)
const VERIFIED = FILES.filter((f) => /\.contract\.ts$|withdraw(\.async)?\.ts$|charge\.ts$/.test(f))

const PLANTED = `import type { Implementation } from "@emyann/tsverify"
import type { chargeSpec } from "./charge.contract.ts"

/** A bug planted: takes the amount whatever the balance. Its spec named by \`typeof\`, as the examples' are not. */
export const overdraw: Implementation<typeof chargeSpec> = (balance, amount) => balance - amount
`
// Runs the law on the counterexample, through what the project installed: no condition, the built JavaScript.
const REPLAY = `import { holds } from "@emyann/tsverify"
import { chargeSpec } from "./examples/charge/charge.contract.ts"
import { overdraw } from "./examples/charge/overdraw.ts"

const [balance, amount] = (JSON.parse(process.argv[2]!) as Array<string>).map((x) => BigInt(x.slice(0, -1))) as [bigint, bigint]
console.log(JSON.stringify(holds(chargeSpec.ensures.neverNegative!)(balance, amount, overdraw(balance, amount))))
`

/**
 * The environment without a `NODE_OPTIONS` of this run's, so what runs in the project runs as it would there, and
 * without `FORCE_COLOR`, so the reports compared are plain text.
 */
const { NODE_OPTIONS: _, FORCE_COLOR: __, ...env } = process.env
const ran = (cmd: string, args: ReadonlyArray<string>, cwd: string): Promise<{ code: number | null; out: string; err: string }> =>
  new Promise((resolve, reject) => {
    const child = spawn(cmd, args, { cwd, env })
    let out = ""
    let err = ""
    child.stdout.on("data", (d) => (out += d))
    child.stderr.on("data", (d) => (err += d))
    child.on("error", reject)
    child.on("close", (code) => resolve({ code, out, err }))
  })
const sync = (cmd: string, args: ReadonlyArray<string>, cwd: string) => {
  const r = spawnSync(cmd, args, { cwd, env, encoding: "utf8", timeout: 300_000 })
  assert.equal(r.status, 0, `${cmd} ${args.join(" ")}\n${r.stdout}\n${r.stderr}`)
  return r.stdout
}

interface Report {
  readonly passed: boolean
  readonly contracts: ReadonlyArray<{
    readonly file: string
    readonly contract: string
    readonly unsupported?: string
    readonly laws: ReadonlyArray<{ readonly name: string; readonly status: string; readonly args?: ReadonlyArray<unknown> }>
    readonly obligations: ReadonlyArray<{ readonly kind: string; readonly phase: string; readonly status: string }>
    readonly trusted: ReadonlyArray<{ readonly name: string; readonly purity: string; readonly laws: ReadonlyArray<string> }>
  }>
}
/** What a report decides, without its timings and its witnesses. */
const verdicts = (r: Report) =>
  r.contracts.map((c) => ({
    at: `${c.file} ${c.contract}`,
    unsupported: c.unsupported,
    laws: c.laws.map((l) => `${l.name}: ${l.status}`),
    obligations: c.obligations.map((o) => `${o.kind} ${o.phase}: ${o.status}`),
    trusted: c.trusted.map((t) => `${t.name}: ${t.purity}, ${t.laws.length} laws`),
  }))
const contract = (r: Report, at: string) => {
  const c = r.contracts.find((x) => `${x.file} ${x.contract}` === at)
  assert.ok(c !== undefined, `no ${at} in ${r.contracts.map((x) => `${x.file} ${x.contract}`).join(", ")}`)
  return c
}

let dir: string
let project: string
let bin: string
before(() => {
  dir = mkdtempSync(path.join(tmpdir(), "tsverify-install-"))
  sync("npm", ["pack", "--pack-destination", dir], root)
  project = path.join(dir, "project")
  for (const f of FILES) cpSync(path.join(root, f), path.join(project, f))
  writeFileSync(path.join(project, "examples/charge/overdraw.ts"), PLANTED)
  writeFileSync(path.join(project, "replay.ts"), REPLAY)
  writeFileSync(path.join(project, "package.json"), JSON.stringify({ name: "project", private: true, type: "module" }))
  writeFileSync(
    path.join(project, "tsconfig.json"),
    JSON.stringify({
      compilerOptions: {
        target: "es2023",
        module: "nodenext",
        moduleResolution: "nodenext",
        strict: true,
        allowImportingTsExtensions: true,
        noEmit: true,
        skipLibCheck: true,
        types: [],
      },
      include: ["examples"],
    }),
  )
  const tarball = path.join(dir, TARBALL)
  sync(
    "npm",
    ["install", "--prefer-offline", "--no-audit", "--no-fund", tarball, dev("effect"), dev("lodash-es"), dev("@types/lodash-es")],
    project,
  )
  bin = path.join(project, "node_modules/.bin/tsverify")
})
after(() => rmSync(dir, { recursive: true, force: true }))

describe("tsverify, installed from its tarball", () => {
  it("ships what it builds, the packs' source, its pages, its skill and its license, and none of its own source or tests", () => {
    const files = sync("tar", ["-tzf", path.join(dir, TARBALL)], dir)
      .trim()
      .split("\n")
    const outside = files.filter(
      (f) =>
        !/^package\/(dist\/.*\.(js|d\.ts)|packs\/[^/]+\.ts|docs\/[^/]+\.md|skills\/tsverify\/SKILL\.md|package\.json|README\.md|LICENSE)$/.test(
          f,
        ),
    )
    assert.deepEqual(outside, [])
    for (const f of ["dist/src/cli.js", "packs/lodash.ts", "docs/specs.md", "skills/tsverify/SKILL.md"])
      assert.ok(files.includes(`package/${f}`), f)
  })

  it("puts the command on the project's path, the built one", () => {
    assert.equal(realpathSync(bin), realpathSync(path.join(project, "node_modules/@emyann/tsverify/dist/src/cli.js")))
    assert.ok(statSync(bin).mode & 0o111)
  })

  it("type-checks the project's code against the declarations it installed", () => {
    sync(process.execPath, [path.join(project, "node_modules/typescript/bin/tsc"), "-p", "."], project)
  })

  it("reaches the verdicts the source reaches on the same files", async () => {
    const [source, installed] = await Promise.all([
      ran(process.execPath, [path.join(root, "src/cli.ts"), ...VERIFIED, "--json"], root),
      ran(process.execPath, [bin, ...VERIFIED, "--json"], project),
    ])
    // Exit 1 on both: the lodash example holds a counterexample on purpose.
    assert.equal(source.code, 1, source.err)
    assert.equal(installed.code, 1, installed.err)
    const s = JSON.parse(source.out) as Report
    const i = JSON.parse(installed.out) as Report
    assert.deepEqual(verdicts(i), verdicts(s))
    // And what each reads differently once installed, decided as it should be.
    const folded = contract(i, "examples/account/account.contract.ts folded")
    assert.ok(folded.obligations.length > 0 && folded.obligations.every((o) => o.status === "proved"), JSON.stringify(folded.obligations))
    for (const at of [
      "examples/account/withdraw.ts withdraw",
      "examples/account/withdraw.async.ts withdraw",
      "examples/charge/charge.ts charge",
    ]) {
      const c = contract(i, at)
      assert.ok(c.laws.length > 0 && c.laws.every((l) => l.status === "proved"), `${at}: ${JSON.stringify(c.laws)}`)
    }
    assert.deepEqual(
      contract(i, "examples/account/withdraw.ts withdraw").trusted.map((t) => `${t.name}: ${t.purity}`),
      ["accountOf: checked"],
    )
    const labels = contract(i, "examples/lodash/labels.contract.ts labels")
    assert.deepEqual(
      labels.trusted.map((t) => [t.purity, t.laws.length]),
      [["unchecked", 4]],
    )
  })

  it("exits 1 on a planted bug, with a counterexample the installed code breaks on", async () => {
    const r = await ran(process.execPath, [bin, "examples/charge/overdraw.ts", "overdraw", "--json"], project)
    assert.equal(r.code, 1, r.err)
    const law = contract(JSON.parse(r.out) as Report, "examples/charge/overdraw.ts overdraw").laws.find((l) => l.name === "neverNegative")
    assert.equal(law?.status, "counterexample")
    assert.ok(
      law.args?.every((a) => typeof a === "string" && /^-?\d+n$/.test(a)),
      JSON.stringify(law.args),
    )
    assert.equal(sync(process.execPath, ["replay.ts", JSON.stringify(law.args)], project).trim(), "false")
  })
})

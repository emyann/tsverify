// The command: every contract of a folder, found by its file's import of
// tsverify, a total and the exit code; one
// contract by name, with everything known of it; the same as one JSON
// document; a path that is not there; colour in a terminal and plain text
// otherwise; and --watch, a run again on each change, until stopped.
import assert from "node:assert/strict"
import { spawn, spawnSync } from "node:child_process"
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { it } from "node:test"

const root = path.resolve(import.meta.dirname, "..")
// A run's own `FORCE_COLOR` (a test runner's, in a terminal) left out: piped, the report is plain text.
const { FORCE_COLOR: _, ...plain } = process.env
const cli = (...args: Array<string>) => {
  const r = spawnSync(process.execPath, [path.join(root, "src/cli.ts"), ...args], {
    cwd: root,
    env: plain,
    encoding: "utf8",
    timeout: 300_000,
  })
  return { code: r.status, out: r.stdout, err: r.stderr }
}

/** A project of its own under `.docs/`, a dot folder no command scans, importing `tsverify` through this package's condition. */
const project = (files: Readonly<Record<string, string>>): string => {
  mkdirSync(path.join(root, ".docs"), { recursive: true })
  const dir = mkdtempSync(path.join(root, ".docs", "cli-"))
  const compilerOptions = {
    module: "nodenext",
    strict: true,
    noEmit: true,
    allowImportingTsExtensions: true,
    customConditions: ["tsverify-source"],
  }
  writeFileSync(path.join(dir, "tsconfig.json"), JSON.stringify({ compilerOptions }))
  mkdirSync(path.join(dir, "src"))
  for (const [name, text] of Object.entries(files)) writeFileSync(path.join(dir, name), text)
  return dir
}
const clamp = (body: string) =>
  `import { contract } from "tsverify"\n\nexport const clamp = (n: bigint): bigint => ${body}\n\n` +
  `export const clampNeverNegative = contract(clamp, { ensures: { notNegative: (_n, out) => out >= 0n } })\n`

it("verifies every contract under a folder, and exits 1 on a vacuous law", () => {
  const r = cli("fixtures/vacuous")
  assert.equal(r.code, 1, r.err)
  assert.match(r.out, /^fixtures\/vacuous\/sign\.contract\.ts\n  signed\n/)
  assert.match(r.out, /\n {4}vacuous +squareNotNegative /)
  assert.match(r.out, /\n2 contracts in 1 file: laws 2 proved, 3 vacuous\n$/)
})

it("exits 0 when every law and every obligation is proved", () => {
  const r = cli(...["account.contract", "withdraw", "withdraw.async", "effects.contract"].map((f) => `examples/account/${f}.ts`))
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /\n7 contracts in 4 files: laws 28 proved; obligations 10 proved\n$/)
})

it("finds a spec's implementation in a folder, the spec file holding none", () => {
  const r = cli("examples/charge")
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /^examples\/charge\/charge\.ts\n {2}charge\n/)
  assert.match(r.out, /\n1 contract in 1 file: laws 2 proved\n$/)
})

it("finds a contract by its file's import of tsverify, whatever the file's name", () => {
  const dir = project({ "src/clamp.ts": clamp("(n < 0n ? 0n : n)") })
  try {
    const r = spawnSync(process.execPath, [path.join(root, "src/cli.ts")], { cwd: dir, env: plain, encoding: "utf8", timeout: 300_000 })
    assert.equal(r.status, 0, r.stdout + r.stderr)
    assert.match(r.stdout, /^src\/clamp\.ts\n {2}clampNeverNegative\n/)
    assert.match(r.stdout, /\n1 contract in 1 file: laws 1 proved\n$/)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})

it("exits 1 when a law is only bounded: a loop of steps over an array of unknown length", () => {
  const r = cli("examples/account/imports.contract.ts")
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

it("refuses files that hold no contract, with code 2: a spec is verified through its implementation", () => {
  const r = cli("examples/charge/charge.contract.ts")
  assert.equal(r.code, 2)
  assert.match(r.err, /no contract in examples\/charge\/charge\.contract\.ts: a spec is verified through its implementation/)
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
  const r = cli("examples/lodash/labels.contract.ts", "--json")
  assert.equal(r.code, 1, r.err)
  const report = JSON.parse(r.out) as Report
  assert.equal(report.passed, false)
  const law = report.contracts.find((c) => c.contract === "labels")?.laws.find((l) => l.name === "severalOnlyWithTwoDifferent")
  assert.equal(law?.status, "counterexample")
  // The labels, and what `uniq` was taken to return for them: the two the same, which lodash would never return.
  const [labels] = law.args as [ReadonlyArray<string>]
  assert.deepEqual(Object.values(law.world as Record<string, unknown>), [labels])
  assert.deepEqual(
    Object.keys(law.world as Record<string, unknown>).map((k) => k.replace(/!\d+$/, "")),
    ["uniq"],
  )
})

it("colours the report in a terminal, and never --json", () => {
  const coloured = (...args: Array<string>) =>
    spawnSync(process.execPath, [path.join(root, "src/cli.ts"), ...args], {
      cwd: root,
      env: { ...plain, FORCE_COLOR: "1" },
      encoding: "utf8",
      timeout: 300_000,
    }).stdout
  // ESC [ 32 m: green, around the verdict.
  const ESC = "\u001b["
  assert.ok(coloured("examples/charge").includes(`${ESC}32mproved`))
  assert.ok(!coloured("examples/charge", "--json").includes(ESC))
  assert.ok(!cli("examples/charge").out.includes(ESC))
})

/** Waits until `ok` holds, polling; fails after a minute. */
const until = async (ok: () => boolean, what: string): Promise<void> => {
  for (const started = Date.now(); !ok(); await new Promise((r) => setTimeout(r, 100)))
    if (Date.now() - started > 60_000) assert.fail(`waited a minute for ${what}`)
}

it("--watch runs again on each change until stopped: piped, each run's report after the last one", async () => {
  const dir = project({ "src/clamp.ts": clamp("n") })
  const watcher = spawn(process.execPath, [path.join(root, "src/cli.ts"), "--watch"], { cwd: dir, env: plain })
  let out = ""
  watcher.stdout.on("data", (d) => (out += d))
  // Stopped, it exits 143 itself, its run under way stopped with it: a signal it did not handle would leave the code null.
  const ended = new Promise<number | null>((r) => watcher.on("exit", (code) => r(code)))
  try {
    await until(() => out.includes("waiting for a change"), "the first run")
    assert.match(out, /tsverify --watch · .* · started\n/)
    assert.match(out, /counterexample +notNegative/)
    assert.match(out, /\nnot all proved in \d+\.\d s · waiting for a change/)
    writeFileSync(path.join(dir, "src/clamp.ts"), clamp("(n < 0n ? 0n : n)"))
    await until(() => out.split("waiting for a change").length > 2, "the run after the change")
    assert.match(out, /tsverify --watch · .* · src[\\/]clamp\.ts changed\n/)
    assert.match(out, /\nall proved in \d+\.\d s · waiting for a change/)
  } finally {
    watcher.kill("SIGTERM")
    assert.equal(await ended, 143)
    rmSync(dir, { recursive: true, force: true })
  }
})

it("--watch --json: a line of JSON per run, the same report as --json", async () => {
  const dir = project({ "src/clamp.ts": clamp("n") })
  const watcher = spawn(process.execPath, [path.join(root, "src/cli.ts"), "--watch", "--json"], { cwd: dir, env: plain })
  let out = ""
  watcher.stdout.on("data", (d) => (out += d))
  const runs = () => out.split("\n").filter((l) => l.trim() !== "")
  try {
    await until(() => runs().length === 1, "the first run")
    writeFileSync(path.join(dir, "src/clamp.ts"), clamp("(n < 0n ? 0n : n)"))
    await until(() => runs().length === 2, "the run after the change")
    assert.deepEqual(
      runs().map((l) => (JSON.parse(l) as { passed: boolean }).passed),
      [false, true],
    )
  } finally {
    watcher.kill("SIGTERM")
    rmSync(dir, { recursive: true, force: true })
  }
})

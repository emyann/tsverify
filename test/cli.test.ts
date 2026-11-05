// The command: every contract of a folder, found by its file's import of
// tsverify, a line each, the totals and the exit code; every law of a run of
// one file, and of several only those that need a look, unless --verbose; one
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

/** A project of its own under `.docs/`, a dot folder no command scans, importing `@emyann/tsverify` through this package's condition. */
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
  `import { contract } from "@emyann/tsverify"\n\nexport const clamp = (n: bigint): bigint => ${body}\n\n` +
  `export const clampNeverNegative = contract(clamp, { ensures: { notNegative: ({ output }) => output >= 0n } })\n`

it("verifies every contract under a folder, and exits 1 on a vacuous law", () => {
  const r = cli("fixtures/vacuous")
  assert.equal(r.code, 1, r.err)
  assert.match(r.out, /^fixtures\/vacuous\/sign\.contract\.ts\n {2}○ signed +2 vacuous, 1 proved {2}\(\d+ ms\)\n/)
  assert.match(r.out, /\n {4}○ squareNotNegative {2}\(\d+ ms\)\n {6}no result breaks it/)
  assert.match(r.out, /\n○ 3 vacuous\n✓ 2 laws proved\n {2}2 contracts in 1 file · \d+\.\d s\n$/)
})

it("exits 0 when every law and every obligation is proved", () => {
  const r = cli(...["account.contract", "withdraw", "withdraw.async", "effects.contract"].map((f) => `examples/account/${f}.ts`))
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /\n✓ 31 laws, 10 obligations proved\n {2}7 contracts in 4 files · \d+\.\d s\n$/)
  // Over several files, a contract whose laws all hold is its one line: no law under it.
  assert.doesNotMatch(r.out, /^ {4}/m)
})

it("over several files lists only the laws that need a look, and every law with --verbose", () => {
  const r = cli("examples/charge", "examples/lodash")
  assert.equal(r.code, 1, r.out + r.err)
  assert.match(r.out, /^examples\/charge\/charge\.ts\n {2}✓ charge {2}2 laws {2}\(\d+ ms\)\nexamples\/lodash\/labels\.contract\.ts\n/)
  assert.match(
    r.out,
    /\n {2}✗ labels +1 counterexample, 2 proved · trusts uniq \(lodash-es\) {2}\(\d+ ms\)\n {4}✗ severalOnlyWithTwoDifferent {2}\(/,
  )
  assert.ok(!r.out.includes("noneExactlyWhenEmpty"), r.out)
  assert.match(r.out, /\n✗ 1 counterexample\n✓ 7 laws proved\n {2}3 contracts in 2 files · /)
  const verbose = cli("examples/charge", "examples/lodash", "--verbose")
  assert.match(verbose.out, /\n {4}✓ noneExactlyWhenEmpty {2}\(/)
  assert.match(verbose.out, /\n {4}assumed:\n/)
})

it("over several files lists a proved law whose check of saying something ended without an answer, with why, and counts it", () => {
  // At this work the check, at a tenth of it, runs out for `zeroOnlyAtZero` (test/vacuous.test.ts, `PINNED_WORK`). The
  // sign the code answers is left open, so whether the laws decide it is not asked: that would run out here too.
  const sign =
    `import { contract } from "@emyann/tsverify"\n\nexport function sign(n: bigint): "neg" | "zero" | "pos" {\n  return n < 0n ? "neg" : n === 0n ? "zero" : "pos"\n}\n\n` +
    `export const signed = contract(sign, { ensures: { zeroOnlyAtZero: ({ input: [n], output }) => output !== "zero" || n === 0n }, open: true })\n`
  const dir = project({ "src/clamp.ts": clamp("(n < 0n ? 0n : n)"), "src/sign.ts": sign })
  try {
    const run = (...args: Array<string>) =>
      spawnSync(process.execPath, [path.join(root, "src/cli.ts"), "src", "--work", "800", ...args], {
        cwd: dir,
        env: plain,
        encoding: "utf8",
        timeout: 300_000,
      })
    const r = run()
    assert.equal(r.status, 0, r.stdout + r.stderr)
    assert.match(
      r.stdout,
      /\n {2}✓ signed +1 law · 1 unanswered {2}\(\d+ ms\)\n {4}✓ zeroOnlyAtZero {2}\(\d+ ms\)\n {6}whether it says anything/,
    )
    assert.match(r.stdout, /\n✓ 2 laws proved · 1 question unanswered\n/)
    const j = run("--json")
    assert.equal(j.status, 0, j.stderr)
    const report = JSON.parse(j.stdout) as {
      readonly passed: boolean
      readonly totals: { readonly unanswered: number }
      readonly contracts: ReadonlyArray<{
        readonly contract: string
        readonly laws: ReadonlyArray<{ readonly asked?: unknown; readonly unanswered?: ReadonlyArray<{ readonly question: string }> }>
      }>
    }
    assert.equal(report.passed, true)
    assert.equal(report.totals.unanswered, 1)
    const law = report.contracts.find((c) => c.contract === "signed")!.laws[0]!
    assert.ok(Array.isArray(law.asked))
    assert.deepEqual(
      law.unanswered?.map((u) => u.question),
      ["says-anything"],
    )
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
  // A contract's own question unsettled is said under the contract, after its laws: at this work, whether `refusesOnly`'s
  // laws decide every input runs out (test/undecided.test.ts, `UNDECIDED_RUNS_OUT`).
  const own = cli("fixtures/undecided/start.contract.ts", "--work", "800")
  assert.match(
    own.out,
    /\n {2}✓ refusesOnly +2 laws · 3 unanswered {2}\(\d+ ms\)\n(?: {6}.*\n| {4}✓.*\n)* {4}whether the laws decide every input was not settled/,
  )
})

it("finds a spec's implementation in a folder, the spec file holding none", () => {
  const r = cli("examples/charge")
  assert.equal(r.code, 0, r.out + r.err)
  // The folder holds two files, and one contract: a run of one file's contracts lists every law.
  assert.match(r.out, /^examples\/charge\/charge\.ts\n {2}✓ charge {2}2 laws {2}\(\d+ ms\)\n {4}✓ neverNegative {2}\(/)
  assert.match(r.out, /\n✓ 2 laws proved\n {2}1 contract in 1 file · \d+\.\d s\n$/)
})

it("finds a contract by its file's import of tsverify, whatever the file's name", () => {
  const dir = project({ "src/clamp.ts": clamp("(n < 0n ? 0n : n)") })
  try {
    const r = spawnSync(process.execPath, [path.join(root, "src/cli.ts")], { cwd: dir, env: plain, encoding: "utf8", timeout: 300_000 })
    assert.equal(r.status, 0, r.stdout + r.stderr)
    assert.match(r.stdout, /^src\/clamp\.ts\n {2}✓ clampNeverNegative {2}1 law {2}\(\d+ ms\)\n/)
    assert.match(r.stdout, /\n✓ 1 law proved\n {2}1 contract in 1 file · \d+\.\d s\n$/)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})

it("finds an implementation typed by its spec's module, which imports no tsverify, in a folder the spec is outside of", () => {
  const dir = project({
    "shipping.contract.ts":
      `import { type Implementation, spec } from "@emyann/tsverify"\n\n` +
      `const shippingSpec = spec<(total: number) => number>({\n  requires: ({ input: [total] }) => total >= 0,\n` +
      `  ensures: { freeFrom50: ({ input: [total], output }) => total < 50 || output === 0 },\n})\n` +
      `export type Shipping = Implementation<typeof shippingSpec>\n`,
    "src/shipping.ts": `import type { Shipping } from "../shipping.contract.ts"\n\nexport const shipping: Shipping = (total) => (total >= 50 ? 0 : 5)\n`,
    "src/checkout.ts": `import { shipping } from "./shipping.ts"\n\n/** Whether an order ships free. */\nexport const shipsFree = (total: number): boolean => shipping(total) === 0\n`,
  })
  try {
    const r = spawnSync(process.execPath, [path.join(root, "src/cli.ts"), "src", "--verbose"], {
      cwd: dir,
      env: plain,
      encoding: "utf8",
      timeout: 300_000,
    })
    assert.equal(r.status, 0, r.stdout + r.stderr)
    assert.match(r.stdout, /^src\/shipping\.ts\n {2}✓ shipping {2}1 law {2}\(\d+ ms\)\n/)
    assert.match(r.stdout, /\n✓ 1 law proved\n {2}1 contract in 1 file · \d+\.\d s\n$/)
    // A caller takes it by its spec, named as its type names it.
    const caller = path.join(dir, "src/checkout.contract.ts")
    writeFileSync(
      caller,
      `import { contract } from "@emyann/tsverify"\nimport { shipsFree } from "./checkout.ts"\n\n` +
        `export const freeFrom50 = contract(shipsFree, {\n  requires: ({ input: [total] }) => total >= 0,\n` +
        // It says only the free side: under 50, what the code answers is its own (`open`), as the callee's spec says nothing.
        `  ensures: { from50: ({ input: [total], output }) => total < 50 || output },\n  open: true,\n})\n`,
    )
    const c = spawnSync(process.execPath, [path.join(root, "src/cli.ts"), "src/checkout.contract.ts", "freeFrom50"], {
      cwd: dir,
      env: plain,
      encoding: "utf8",
      timeout: 300_000,
    })
    assert.equal(c.status, 0, c.stdout + c.stderr)
    assert.match(c.stdout, /\n {4}- shipping: shippingSpec, pure, checked from source/)
  } finally {
    rmSync(dir, { recursive: true, force: true })
  }
})

it("exits 1 when a law is only bounded: a loop of steps over an array of unknown length", () => {
  const r = cli("examples/account/imports.contract.ts")
  assert.equal(r.code, 1, r.out + r.err)
  assert.match(r.out, /\n~ 8 bounded\n✓ 11 laws proved\n {2}5 contracts in 1 file · \d+\.\d s\n$/)
})

it("verifies one contract by name, with what it reaches, trusted and assumed", () => {
  const r = cli("examples/account/withdraw.ts", "withdraw")
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /^✓ withdraw {2}5 laws {2}\(\d+ ms\)\n/)
  assert.match(r.out, /\n {2}reaches: /)
  assert.match(r.out, /\n {2}trusted \(declared, not proved\):\n {4}- accountOf: pure, checked from source/)
  assert.match(r.out, /\n {2}assumed:\n/)
})

it("refuses a path that is not there, with code 2", () => {
  const r = cli("no/such/folder")
  assert.equal(r.code, 2)
  assert.match(r.err, /no such file or folder/)
})

it("refuses files that hold no contract, with code 2, and says to name the file the function is written in", () => {
  const r = cli("examples/charge/charge.contract.ts")
  assert.equal(r.code, 2)
  assert.match(r.err, /no contract in examples\/charge\/charge\.contract\.ts: a spec is verified through the function that implements it/)
  assert.match(r.err, /name the file that function is written in/)
})

it("--help and -h print the usage and every option, read nothing, and exit 0", () => {
  const help = cli("--help")
  assert.equal(help.code, 0)
  assert.match(help.out, /^usage: tsverify /)
  for (const option of [
    "--project",
    "--bound",
    "--work",
    "--verbose",
    "--json",
    "--watch",
    "--cache",
    "--cache-location",
    "--workers",
    "--config",
    "--help",
  ])
    assert.ok(help.out.includes(option), `names ${option}`)
  // The same text with a folder named: the folder's contracts are never read.
  for (const asked of [["-h"], ["examples/charge", "--help"]]) {
    const r = cli(...asked)
    assert.equal(r.code, 0, asked.join(" "))
    assert.equal(r.out, help.out, asked.join(" "))
    assert.equal(r.err, "")
  }
})

it("refuses an option it does not take, with code 2, before reading anything", () => {
  for (const asked of [["--hlep"], ["examples/charge", "--bound=4"], ["-x"]]) {
    const r = cli(...asked)
    assert.equal(r.code, 2, asked.join(" "))
    assert.ok(r.err.startsWith(`${asked.at(-1)}: `), r.err)
    assert.match(r.err, /usage: tsverify /)
    assert.equal(r.out, "")
  }
  // A value that opens with a dash is the value of the option before it, not an option.
  assert.match(cli("examples/charge", "--project", "-nowhere/tsconfig.json").err, /^--project -nowhere\/tsconfig\.json: no such file/)
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
  assert.deepEqual(report.totals, {
    contracts: 1,
    files: 1,
    laws: { proved: 2 },
    obligations: {},
    unsupported: 0,
    undecided: 0,
    unanswered: 0,
  })
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
  // ESC [ 32 m: green, around a law's mark.
  const ESC = "\u001b["
  assert.ok(coloured("examples/charge").includes(`${ESC}32m✓`))
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
    assert.match(out, /\n {4}✗ notNegative {2}\(/)
    assert.match(out, /\nnot all proved · waiting for a change/)
    writeFileSync(path.join(dir, "src/clamp.ts"), clamp("(n < 0n ? 0n : n)"))
    await until(() => out.split("waiting for a change").length > 2, "the run after the change")
    assert.match(out, /tsverify --watch · .* · src[\\/]clamp\.ts changed\n/)
    assert.match(out, /\nall proved · waiting for a change/)
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

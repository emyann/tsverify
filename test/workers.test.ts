// Workers: `--workers N` verifies the files in N processes, and the run says
// what one process says: the same verdicts, the same report in the same order,
// the same JSON document and the same exit code, 3 among them when a worker
// fails. One cache folder serves them all.
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { mkdirSync, mkdtempSync, readdirSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { after, before, it } from "node:test"

const root = path.resolve(import.meta.dirname, "..")
const { FORCE_COLOR: _, ...plain } = process.env
const cli = (cwd: string, ...args: Array<string>) => {
  const r = spawnSync(process.execPath, [path.join(root, "src/cli.ts"), ...args], { cwd, env: plain, encoding: "utf8", timeout: 300_000 })
  return { code: r.status, out: r.stdout, err: r.stderr }
}

const compilerOptions = {
  module: "nodenext",
  strict: true,
  noEmit: true,
  allowImportingTsExtensions: true,
  customConditions: ["tsverify-source"],
}
const law = (name: string, body: string, holds: string) =>
  `import { contract } from "@emyann/tsverify"\n\nexport const ${name} = (n: bigint): bigint => ${body}\n\n` +
  `export const ${name}Law = contract(${name}, { ensures: { holds: ({ output }) => ${holds} } })\n`

/** Two roots, each a project of its own, five files, one with a counterexample: the first, and the slowest, so the others are done before it. */
const FILES: Readonly<Record<string, string>> = {
  "one/src/clamp.ts": law("clamp", "(n < 0n ? 0n : n)", "output >= 0n"),
  "one/src/square.ts": law("square", "n * n", "output >= 0n"),
  "one/src/broken.ts":
    law("broken", "n - 1n", "output >= 0n") +
    `export const brokenBelow = contract(broken, { ensures: { below: ({ output }) => output < 1000n } })\n` +
    `export const brokenSquare = contract(broken, { ensures: { square: ({ output }) => output * output >= 0n } })\n`,
  "two/src/double.ts": law("double", "n + n", "output === 2n * n"),
  "two/src/abs.ts": law("abs", "(n < 0n ? -n : n)", "output >= 0n"),
}
let dir = ""
before(() => {
  mkdirSync(path.join(root, ".docs"), { recursive: true })
  dir = mkdtempSync(path.join(root, ".docs", "workers-"))
  for (const p of ["one", "two"]) {
    mkdirSync(path.join(dir, p, "src"), { recursive: true })
    writeFileSync(path.join(dir, p, "tsconfig.json"), JSON.stringify({ compilerOptions }))
  }
  for (const [name, text] of Object.entries(FILES)) writeFileSync(path.join(dir, name), text)
})
after(() => rmSync(dir, { recursive: true, force: true }))

/** A document with every time left out: the one thing two runs may differ in. */
const timeless = (x: unknown): unknown =>
  Array.isArray(x)
    ? x.map(timeless)
    : x !== null && typeof x === "object"
      ? Object.fromEntries(Object.entries(x).flatMap(([k, v]) => (k === "ms" ? [] : [[k, timeless(v)]])))
      : x
/** The text report with its times normalised, as test/docs.test.ts does. */
const untimed = (s: string) => s.replace(/\(\d+ ms\)/g, "(N ms)").replace(/ · \d+\.\d s$/m, " · N s")

interface Law {
  readonly name: string
  readonly status: string
  readonly args?: ReadonlyArray<unknown>
}
interface Report {
  readonly contracts: ReadonlyArray<{ readonly file: string; readonly contract: string; readonly laws: ReadonlyArray<Law> }>
}

it("says with three workers what one says: the same document, the same report in the same order, the same exit code", () => {
  const one = cli(dir, "one/src", "two/src", "--json", "--workers", "1")
  const three = cli(dir, "one/src", "two/src", "--json", "--workers", "3")
  assert.equal(one.code, 1, one.err)
  assert.equal(three.code, 1, three.err)
  const doc = JSON.parse(three.out) as Report
  assert.deepEqual(timeless(doc), timeless(JSON.parse(one.out)))
  assert.deepEqual(
    doc.contracts.map((c) => c.file),
    [
      "one/src/broken.ts",
      "one/src/broken.ts",
      "one/src/broken.ts",
      "one/src/clamp.ts",
      "one/src/square.ts",
      "two/src/abs.ts",
      "two/src/double.ts",
    ],
  )
  // The counterexample, found the same.
  const broken = doc.contracts[0]?.laws.find((l) => l.name === "holds")
  assert.equal(broken?.status, "counterexample")
  assert.ok(broken.args !== undefined && broken.args.length === 1, JSON.stringify(broken))
  const text1 = cli(dir, "one/src", "two/src", "--workers", "1")
  const text3 = cli(dir, "one/src", "two/src", "--workers", "3")
  assert.equal(text3.code, 1, text3.err)
  assert.equal(untimed(text3.out), untimed(text1.out))
  assert.match(text3.out, /\n {2}7 contracts in 5 files · /)
})

it("exits 3 when a worker fails, as one process does", () => {
  const failing = path.join(dir, "failing")
  mkdirSync(path.join(failing, "src"), { recursive: true })
  // There, so each file finds it; not JSON, so the program read through it fails.
  writeFileSync(path.join(failing, "tsconfig.json"), `{ "compilerOptions": `)
  writeFileSync(path.join(failing, "src/clamp.ts"), FILES["one/src/clamp.ts"]!)
  try {
    for (const workers of ["1", "2"]) {
      const r = cli(dir, "one/src", "failing/src", "--workers", workers)
      assert.equal(r.code, 3, `--workers ${workers}: ${r.out}${r.err}`)
      assert.match(r.err, /tsverify failed, which says nothing of the code/)
    }
  } finally {
    rmSync(failing, { recursive: true, force: true })
  }
})

it("keeps one cache for every worker: each verdict once, none half-written, and read back by one process alike", () => {
  const cache = path.join(dir, ".cache")
  const run = (workers: string) => cli(dir, "one/src", "two/src", "--json", "--cache", "--cache-location", cache, "--workers", workers)
  const first = run("3")
  assert.equal(first.code, 1, first.err)
  const kept = readdirSync(cache, { recursive: true, encoding: "utf8" })
  assert.equal(kept.filter((f) => f.endsWith(".json")).length, 7, kept.join(", "))
  assert.deepEqual(
    kept.filter((f) => f.endsWith(".tmp")),
    [],
  )
  for (const again of [run("3"), run("1")]) {
    assert.equal(again.code, 1, again.err)
    assert.deepEqual(timeless(JSON.parse(again.out)), timeless(JSON.parse(first.out)))
  }
})

it("refuses --workers that is not a positive whole number, with code 2, reading nothing", () => {
  for (const asked of [["--workers", "0"], ["--workers", "x"], ["--workers"], ["--workers", "--json"]]) {
    const r = cli(dir, "one/src", ...asked)
    assert.equal(r.code, 2, `${asked.join(" ")}: ${r.out}${r.err}`)
    assert.equal(r.out, "", asked.join(" "))
    assert.ok(r.err.includes("usage: tsverify"), r.err)
  }
})

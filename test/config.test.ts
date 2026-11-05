// The config file: `tsverify.config.json` in the current folder, or the file
// `--config` names, lists the roots and the options of a run with no root
// named. A root named and a flag beat it; anything it holds that is not one of
// its keys, of its type, is a usage error before anything is read.
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs"
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

/** Three roots, each a project of its own: `a` and `b` proved, `c` a counterexample. The config names `a` and `b`. */
let dir = ""
before(() => {
  mkdirSync(path.join(root, ".docs"), { recursive: true })
  dir = mkdtempSync(path.join(root, ".docs", "config-"))
  const files: Record<string, string> = {
    "a/src/clamp.ts": law("clamp", "(n < 0n ? 0n : n)", "output >= 0n"),
    "b/src/square.ts": law("square", "n * n", "output >= 0n"),
    "c/src/broken.ts": law("broken", "n", "output >= 0n"),
    "tsverify.config.json": JSON.stringify({ roots: ["a/src", "b/src"] }),
  }
  for (const p of ["a", "b", "c"]) {
    mkdirSync(path.join(dir, p, "src"), { recursive: true })
    writeFileSync(path.join(dir, p, "tsconfig.json"), JSON.stringify({ compilerOptions }))
  }
  for (const [name, text] of Object.entries(files)) writeFileSync(path.join(dir, name), text)
})
after(() => rmSync(dir, { recursive: true, force: true }))

it("verifies every root the config file names, each through its own tsconfig.json, when no root is named", () => {
  const r = cli(dir)
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /^a\/src\/clamp\.ts\n/m)
  assert.match(r.out, /^b\/src\/square\.ts\n/m)
  assert.ok(!r.out.includes("c/src"), r.out)
  assert.match(r.out, /\n {2}2 contracts in 2 files · /)
})

it("takes a root named over the config's roots, and a flag over its key", () => {
  const named = cli(dir, "c/src")
  assert.equal(named.code, 1, named.out + named.err)
  assert.match(named.out, /^c\/src\/broken\.ts\n/)
  assert.ok(!named.out.includes("a/src"), named.out)
  const sub = path.join(dir, "work")
  mkdirSync(sub, { recursive: true })
  writeFileSync(path.join(sub, "starved.json"), JSON.stringify({ roots: ["../a/src"], work: 1 }))
  const starved = cli(dir, "--config", "work/starved.json", "--json")
  assert.equal(starved.code, 1, starved.out + starved.err)
  const laws = (JSON.parse(starved.out) as { contracts: Array<{ laws: Array<{ status: string }> }> }).contracts.flatMap((c) => c.laws)
  assert.deepEqual(
    laws.map((l) => l.status),
    ["unknown"],
  )
  const given = cli(dir, "--config", "work/starved.json", "--work", "15000000")
  assert.equal(given.code, 0, given.out + given.err)
})

it("reads the file --config names, its roots from its own folder, and refuses one that is not there", () => {
  const sub = path.join(dir, "sub")
  mkdirSync(sub, { recursive: true })
  writeFileSync(path.join(sub, "other.json"), JSON.stringify({ roots: ["../b/src"] }))
  // Run from `c`: the roots are the file's, not the current folder's, and `c`'s own files are not read.
  const r = cli(path.join(dir, "c"), "--config", "../sub/other.json")
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /^\.\.\/b\/src\/square\.ts\n/)
  const missing = cli(dir, "--config", "no/such.json")
  assert.equal(missing.code, 2, missing.out + missing.err)
  assert.equal(missing.out, "")
  assert.ok(missing.err.includes("no/such.json"), missing.err)
})

it("refuses a config file that is not JSON, holds a key it does not take, or a value of the wrong type, with code 2, reading nothing", () => {
  // A folder with a contract proved of its own: without the rule, the run would go on and exit 0.
  const bad = path.join(dir, "bad")
  mkdirSync(path.join(bad, "src"), { recursive: true })
  writeFileSync(path.join(bad, "tsconfig.json"), JSON.stringify({ compilerOptions }))
  writeFileSync(path.join(bad, "src/clamp.ts"), law("clamp", "(n < 0n ? 0n : n)", "output >= 0n"))
  for (const text of [
    `{ "roots": `,
    `{ "bonud": 4 }`,
    `{ "roots": "../a/src" }`,
    `{ "roots": [] }`,
    `{ "workers": 0 }`,
    `{ "cache": "yes" }`,
  ]) {
    writeFileSync(path.join(bad, "tsverify.config.json"), text)
    const r = cli(bad)
    assert.equal(r.code, 2, `${text}: ${r.out}${r.err}`)
    assert.equal(r.out, "", text)
    assert.ok(r.err.startsWith("tsverify.config.json: "), `${text}: ${r.err}`)
    assert.ok(r.err.includes("usage: tsverify"), `${text}: ${r.err}`)
  }
})

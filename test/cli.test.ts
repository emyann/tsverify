// The command: every contract of a folder, a total and the exit code; one
// contract by name, with everything known of it; a path that is not there.
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
  const r = cli("examples/account")
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /\n7 contracts in 3 files: laws 28 proved; obligations 10 proved\n$/)
})

it("verifies one contract by name, with what it reaches, trusted and assumed", () => {
  const r = cli("examples/account/withdraw.spec.ts", "effectWithdraw")
  assert.equal(r.code, 0, r.out + r.err)
  assert.match(r.out, /^effectWithdraw\n/)
  assert.match(r.out, /\n {2}reaches: /)
  assert.match(r.out, /\n {2}trusted \(declared, not proved\):\n {4}- accountOf: pure, checked from source/)
  assert.match(r.out, /\n {2}assumed:\n/)
})

it("refuses a path that is not there, with code 2", () => {
  const r = cli("no/such/folder")
  assert.equal(r.code, 2)
  assert.match(r.err, /no such file or folder/)
})

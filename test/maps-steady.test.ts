// The same verdicts on every run. `inheritedLabelsLaws` (fixtures/maps.ts) has laws the solver decides only near its
// work limit, where a verdict once changed from run to run: a term z3-solver frees hands its number to the next one
// made, and it frees a term when JavaScript collects it, which is not at the same moment on every run. Each contract is
// now verified in a Z3 context of its own, which frees nothing until the contract's verdicts are read (`ownContext` in
// src/verify.ts). Verified five times here, each in a process of its own with the flags the command gives Node, each
// law gets the same verdict and the same reason every time, the last time after another contract in the same process.
import assert from "node:assert/strict"
import { execFile } from "node:child_process"
import path from "node:path"
import { describe, it } from "node:test"
import { promisify } from "node:util"

const root = path.resolve(import.meta.dirname, "..")
const exec = promisify(execFile)
/** As `test/maps.test.ts` verifies it. */
const SETTINGS = { bound: 1, work: 5_000_000, cover: false }
const RUNS = 5

/** One run, in a process of its own with the flags `npm test` gives Node: each law's name, verdict and reason. */
const once = async (after: boolean): Promise<ReadonlyArray<string>> => {
  const run = path.join(root, "test/maps-run.ts")
  const { stdout } = await exec(
    process.execPath,
    ["--predictable-gc-schedule", "--conditions=tsverify-source", run, JSON.stringify(SETTINGS), ...(after ? ["after"] : [])],
    { cwd: root },
  )
  return JSON.parse(stdout) as ReadonlyArray<string>
}

describe("the same verdicts on every run", () => {
  // One run after another, not side by side: each holds about a gigabyte of Z3's memory.
  it(`inheritedLabelsLaws, verified ${RUNS} times, each in a process of its own: every law the same verdict and reason each time`, async () => {
    const first = await once(false)
    assert.equal(first.length, 8, JSON.stringify(first))
    for (let i = 2; i <= RUNS; i++) assert.deepEqual(await once(i === RUNS), first, `run ${i} against run 1`)
  })
})

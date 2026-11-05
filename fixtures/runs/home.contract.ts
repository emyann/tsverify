// A module whose top level writes a file under the home folder: a run gives it a throwaway one.
import { writeFileSync } from "node:fs"
import os from "node:os"
import path from "node:path"
import { contract } from "@emyann/tsverify"

writeFileSync(path.join(os.homedir(), ".tsverify-runs-home-fixture"), "written by fixtures/runs/home.contract.ts\n")

export function twice(x: bigint): bigint {
  return x * 2n
}

export const doubled = contract(twice, { ensures: { even: ({ output }) => output % 2n === 0n } })

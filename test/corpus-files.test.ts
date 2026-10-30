// Every file of the corpus has a test file of its own, `corpus-<name>.test.ts`, which the suite runs beside the others.
import assert from "node:assert/strict"
import { existsSync } from "node:fs"
import path from "node:path"
import { it } from "node:test"
import { CORPUS } from "./corpus.ts"

it("every corpus file is checked", () => {
  const missing = CORPUS.filter((f) => !existsSync(path.join(import.meta.dirname, `corpus-${path.basename(f, ".ts")}.test.ts`)))
  assert.deepEqual(missing, [])
})

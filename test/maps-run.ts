// One run of what `maps-steady.test.ts` compares, in a process of its own: `inheritedLabelsLaws` of fixtures/maps.ts,
// verified with the options given as JSON, and each law's name, verdict and reason printed as one JSON array. With
// `after` as well, `inheritedLabelsWrong` is verified first, in the same process.
import path from "node:path"
import { loadProject } from "../src/project.ts"
import { type Options, verify, withZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/maps.ts")
const opts = JSON.parse(process.argv[2] ?? "{}") as Options
const project = loadProject([file], path.join(root, "tsconfig.json"))
const v = await withZ3(async (z3) => {
  if (process.argv[3] === "after") await verify(z3, project, file, "inheritedLabelsWrong", opts)
  return verify(z3, project, file, "inheritedLabelsLaws", opts)
})
process.stdout.write(`${JSON.stringify(v.laws.map((l) => `${l.name}: ${l.status}: ${l.reason ?? ""}`))}\n`)

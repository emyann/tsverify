// `node src/cli.ts <spec.ts> <export> [--bound 4] [--timeout 10000]`: verifies
// one contract and prints each law's verdict, the states the result reaches,
// and what the model assumed. Exits 1 when a law is not proved.
import path from "node:path"
import { loadProject } from "./project.ts"
import { verify, withZ3 } from "./verify.ts"

const [file, name] = process.argv.slice(2).filter((a, i, all) => !a.startsWith("--") && !all[i - 1]?.startsWith("--"))
if (file === undefined || name === undefined) {
  console.error("usage: node src/cli.ts <spec.ts> <export> [--bound N] [--timeout MS]")
  process.exit(2)
}
const flag = (f: string) => {
  const i = process.argv.indexOf(f)
  return i < 0 ? undefined : Number(process.argv[i + 1])
}
const tsconfig = path.resolve(import.meta.dirname, "../tsconfig.json")
const project = loadProject([file], tsconfig)
const bound = flag("--bound")
const timeoutMs = flag("--timeout")
const v = await withZ3((z3) => verify(z3, project, file, name, { ...(bound ? { bound } : {}), ...(timeoutMs ? { timeoutMs } : {}) }))

if (v.unsupported !== undefined) {
  console.log(`${name}: not verified — ${v.unsupported}`)
  process.exit(1)
}
console.log(`${name}`)
for (const l of v.laws) {
  console.log(`  ${l.status.padEnd(15)} ${l.name}  (${Math.round(l.ms)} ms)`)
  if (l.args !== undefined) console.log(`  ${"".padEnd(15)} e.g. ${JSON.stringify(l.args, (_, x) => (typeof x === "bigint" ? `${x}n` : typeof x === "number" && !Number.isFinite(x) ? String(x) : x))}`)
  if (l.reason !== undefined) console.log(`  ${"".padEnd(15)} ${l.reason}`)
}
if (v.cover.length > 0) console.log(`  reaches: ${v.cover.map((c) => (c.status === "reachable" ? c.value : `${c.value} (${c.status})`)).join(", ")}`)
console.log("  assumed:")
for (const n of v.notes) console.log(`    - ${n}`)
process.exit(v.laws.every((l) => l.status === "proved") ? 0 : 1)

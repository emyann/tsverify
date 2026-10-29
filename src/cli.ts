#!/usr/bin/env node
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
  if (l.abstract !== undefined) console.log(`  ${"".padEnd(15)} leans on what is declared of ${l.abstract.join(", ")}: true of them as declared, maybe not as they are`)
  if (l.reason !== undefined) console.log(`  ${"".padEnd(15)} ${l.reason}`)
}
if (v.cover.length > 0) console.log(`  reaches: ${v.cover.map((c) => (c.status === "reachable" ? c.value : `${c.value} (${c.status})`)).join(", ")}`)
if (v.obligations.length > 0) {
  console.log("  proof code:")
  for (const o of v.obligations) {
    const what = o.kind === "invariant" ? `invariant ${o.phase === "entry" ? "on entry" : "kept by each iteration"}` : o.kind === "requires" ? "lemma's requires" : o.kind
    console.log(`    ${o.status.padEnd(15)} ${what}: ${o.text}  (${o.at.replace(process.cwd() + "/", "")})`)
    if (o.args !== undefined) console.log(`    ${"".padEnd(15)} e.g. ${JSON.stringify(o.args, (_, x) => (typeof x === "bigint" ? `${x}n` : x))}`)
    if (o.reason !== undefined) console.log(`    ${"".padEnd(15)} ${o.reason}`)
  }
}
if (v.trusted.length > 0) {
  console.log("  trusted (declared, not proved):")
  for (const t of v.trusted) {
    const purity = t.purity === "checked" ? `pure, checked from source (read ${t.read?.join(", ")})` : t.purity === "unchecked" ? "pure, unchecked: no source" : "not pure: a fresh result per call"
    console.log(`    - ${t.name}: ${purity}${t.laws.length > 0 ? `; laws ${t.laws.join(", ")}` : ""} — ${t.declared.join(", ")}`)
  }
}
console.log("  assumed:")
for (const n of v.notes) console.log(`    - ${n}`)
process.exit(v.laws.every((l) => l.status === "proved") && v.obligations.every((o) => o.status === "proved") ? 0 : 1)

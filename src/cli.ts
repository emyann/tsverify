#!/usr/bin/env node
// tsverify [<file or folder>...] [--project tsconfig.json] [--bound 4] [--timeout 10000] [--verbose]
//   Verifies every contract each file exports: every implementation of a spec (`const f: Implementation<typeof S>`),
//   and every `contract`, computation and lemma of a `*.spec.ts`, in each folder (the current one by default), a line
//   per law, then a total. Exits 1 unless every law is proved and says something of its function, and every
//   obligation of the proof code is proved.
// tsverify <spec.ts> <export>
//   Verifies one contract, with everything the verification knows: the states its result reaches, what it trusted
//   and what it assumed.
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs"
import path from "node:path"
import ts from "typescript"
import { contractsIn, loadProject } from "./project.ts"
import type { Ctx } from "./value.ts"
import { type Options, type Verification, verify, withZ3 } from "./verify.ts"

const USAGE = "usage: tsverify [<file or folder>...] [--project tsconfig.json] [--bound N] [--timeout MS] [--verbose]\n       tsverify <spec.ts> <export>"
const argv = process.argv.slice(2)
const VALUED = new Set(["--project", "--bound", "--timeout"])
const positional = argv.filter((a, i) => !a.startsWith("--") && !VALUED.has(argv[i - 1] ?? ""))
const flag = (f: string): string | undefined => {
  const i = argv.indexOf(f)
  return i < 0 ? undefined : argv[i + 1]
}
const verbose = argv.includes("--verbose")
const bound = flag("--bound") === undefined ? undefined : Number(flag("--bound"))
const timeoutMs = flag("--timeout") === undefined ? undefined : Number(flag("--timeout"))
const opts: Options = { ...(bound ? { bound } : {}), ...(timeoutMs ? { timeoutMs } : {}) }

/** The `tsconfig.json` a file is checked by: `--project`, or the nearest one above it. */
const tsconfigOf = (file: string): string => {
  const given = flag("--project")
  if (given !== undefined) return path.resolve(given)
  const found = ts.findConfigFile(path.dirname(file), ts.sys.fileExists)
  if (found === undefined) {
    console.error(`no tsconfig.json above ${file}: pass one with --project <tsconfig.json>`)
    process.exit(2)
  }
  return found
}

/**
 * Every file under `dir` that may hold a contract, outside `node_modules` and dot folders: a `*.spec.ts`, and a
 * TypeScript file that names `Implementation<`, whose program is then read to know.
 */
const contractFilesUnder = (dir: string): Array<string> =>
  readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
    const p = path.join(dir, e.name)
    if (e.isDirectory()) return e.name === "node_modules" || e.name.startsWith(".") ? [] : contractFilesUnder(p)
    if (!e.isFile() || !/\.tsx?$/.test(e.name) || e.name.endsWith(".d.ts")) return []
    return e.name.endsWith(".spec.ts") || readFileSync(p, "utf8").includes("Implementation<") ? [p] : []
  })

const show = (x: unknown) => JSON.stringify(x, (_, v) => (typeof v === "bigint" ? `${v}n` : typeof v === "number" && !Number.isFinite(v) ? String(v) : v))
const rel = (p: string) => path.relative(process.cwd(), p) || p

/** The report of one verification, each line indented by `pad`. */
const report = (v: Verification, pad: string, full: boolean): Array<string> => {
  const out: Array<string> = []
  const under = `${pad}${"".padEnd(15)} `
  for (const l of v.laws) {
    out.push(`${pad}${l.status.padEnd(15)} ${l.name}  (${Math.round(l.ms)} ms)`)
    if (l.args !== undefined) out.push(`${under}e.g. ${show(l.args)}`)
    if (l.abstract !== undefined) out.push(`${under}leans on what is declared of ${l.abstract.join(", ")}: true of them as declared, maybe not as they are`)
    if (l.reason !== undefined) out.push(`${under}${l.reason}`)
  }
  if (v.obligations.length > 0) {
    out.push(`${pad}proof code:`)
    for (const o of v.obligations) {
      const what = o.kind === "invariant" ? `invariant ${o.phase === "entry" ? "on entry" : "kept by each iteration"}` : o.kind === "requires" ? "lemma's requires" : o.kind
      out.push(`${pad}  ${o.status.padEnd(15)} ${what}: ${o.text}  (${rel(o.at)})`)
      if (o.args !== undefined) out.push(`${pad}  ${"".padEnd(15)} e.g. ${show(o.args)}`)
      if (o.reason !== undefined) out.push(`${pad}  ${"".padEnd(15)} ${o.reason}`)
    }
  }
  if (v.trusted.length > 0) {
    if (full) {
      out.push(`${pad}trusted (declared, not proved):`)
      for (const t of v.trusted) {
        const purity = t.purity === "checked" ? `pure, checked from source (read ${t.read?.join(", ")})` : t.purity === "unchecked" ? "pure, unchecked: no source" : "not pure: a fresh result per call"
        out.push(`${pad}  - ${t.name}: ${purity}${t.laws.length > 0 ? `; laws ${t.laws.join(", ")}` : ""} — ${t.declared.join(", ")}`)
      }
    } else out.push(`${pad}trusted: ${v.trusted.map((t) => `${t.name} (${t.purity}${t.laws.length > 0 ? `, ${t.laws.length} laws` : ""})`).join(", ")}`)
  }
  if (full) {
    if (v.cover.length > 0) out.push(`${pad}reaches: ${v.cover.map((c) => (c.status === "reachable" ? c.value : `${c.value} (${c.status})`)).join(", ")}`)
    out.push(`${pad}assumed:`)
    for (const n of v.notes) out.push(`${pad}  - ${n}`)
  }
  return out
}

const passed = (v: Verification) => v.unsupported === undefined && v.laws.every((l) => l.status === "proved") && v.obligations.every((o) => o.status === "proved")

const one = async (z3: Ctx, file: string, name: string, pad: string, full: boolean): Promise<Verification> => {
  const v = await verify(z3, loadProject([file], tsconfigOf(file)), file, name, opts)
  if (v.unsupported !== undefined) console.log(`${pad}${name}: not verified — ${v.unsupported}`)
  else console.log([`${pad}${name}`, ...report(v, `${pad}  `, full)].join("\n"))
  return v
}

// One contract, named: everything about it.
const [first, second] = positional
if (positional.length === 2 && first !== undefined && second !== undefined && !existsSync(second)) {
  const v = await withZ3((z3) => one(z3, path.resolve(first), second, "", true))
  process.exit(passed(v) ? 0 : 1)
}

// Every contract of every file found.
const files = (positional.length === 0 ? ["."] : positional).flatMap((p) => {
  if (!existsSync(p)) {
    console.error(`${p}: no such file or folder\n${USAGE}`)
    process.exit(2)
  }
  return statSync(p).isDirectory() ? contractFilesUnder(path.resolve(p)) : [path.resolve(p)]
})
if (files.length === 0) {
  console.error(`no spec or implementation found under ${positional.join(", ") || "."}: name a file, or a folder that holds one\n${USAGE}`)
  process.exit(2)
}

const verdicts: Array<Verification> = []
let filesRead = 0
await withZ3(async (z3) => {
  for (const file of files.sort()) {
    // Each file is its own program: the declarations it imports (an implementation, through its spec) are in force for it alone.
    const names = contractsIn(loadProject([file], tsconfigOf(file)), file)
    if (names.length === 0) continue
    filesRead++
    console.log(rel(file))
    for (const name of names) verdicts.push(await one(z3, file, name, "  ", verbose))
  }
})

const count = <A,>(xs: ReadonlyArray<A>, key: (x: A) => string) =>
  Object.entries(xs.reduce<Record<string, number>>((m, x) => ({ ...m, [key(x)]: (m[key(x)] ?? 0) + 1 }), {}))
    .map(([k, n]) => `${n} ${k}`)
    .join(", ")
const plural = (n: number, word: string) => `${n} ${word}${n === 1 ? "" : "s"}`
const laws = verdicts.flatMap((v) => v.laws)
const obligations = verdicts.flatMap((v) => v.obligations)
const unread = verdicts.filter((v) => v.unsupported !== undefined).length
console.log(
  `\n${plural(verdicts.length, "contract")} in ${plural(filesRead, "file")}: laws ${count(laws, (l) => l.status) || "none"}` +
    (obligations.length > 0 ? `; obligations ${count(obligations, (o) => o.status)}` : "") +
    (unread > 0 ? `; ${unread} not verified` : ""),
)
process.exit(verdicts.every(passed) ? 0 : 1)

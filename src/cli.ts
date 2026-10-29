#!/usr/bin/env node
// tsverify [<file or folder>...] [--project tsconfig.json] [--bound 4] [--timeout 10000] [--verbose] [--json]
//   Verifies every contract each file exports: every implementation of a spec (`const f: Implementation<S>`),
//   and every `contract`, computation and lemma, in each file that imports tsverify under each folder (the current one
//   by default), a line per law, then a total. Exits 1 unless every law is proved and says something of its function, and every
//   obligation of the proof code is proved.
// tsverify <file.ts> <export>
//   Verifies one contract, with everything the verification knows: the states its result reaches, what it trusted
//   and what it assumed.
// --json prints one JSON document instead, of every verdict in full (`Report`), and the same exit code.
// Exits 0 when everything is proved, 1 when something is not, 2 on a usage error, 3 when the verifier itself fails.
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs"
import path from "node:path"
import ts from "typescript"
import { contractsIn, loadProject } from "./project.ts"
import type { Ctx } from "./value.ts"
import { type Options, type Verification, verify, withZ3 } from "./verify.ts"

// A failure of the verifier is no verdict on the code: exit 3, so no caller reads it as a law not proved.
process.on("uncaughtException", (e) => {
  console.error(`tsverify failed, which says nothing of the code: ${e instanceof Error ? (e.stack ?? e.message) : String(e)}`)
  process.exit(3)
})

const USAGE =
  "usage: tsverify [<file or folder>...] [--project tsconfig.json] [--bound N] [--timeout MS] [--verbose] [--json]\n       tsverify <file.ts> <export> [--json]"
const argv = process.argv.slice(2)
const VALUED = new Set(["--project", "--bound", "--timeout"])
const positional = argv.filter((a, i) => !a.startsWith("--") && !VALUED.has(argv[i - 1] ?? ""))
const flag = (f: string): string | undefined => {
  const i = argv.indexOf(f)
  return i < 0 ? undefined : argv[i + 1]
}
const verbose = argv.includes("--verbose")
const json = argv.includes("--json")
const bound = flag("--bound") === undefined ? undefined : Number(flag("--bound"))
const timeoutMs = flag("--timeout") === undefined ? undefined : Number(flag("--timeout"))
const opts: Options = { ...(bound ? { bound } : {}), ...(timeoutMs ? { timeoutMs } : {}) }

/** The `tsconfig.json` a file is checked by: `--project`, or the nearest one above it. */
const tsconfigOf = (file: string): string => {
  const given = flag("--project")
  if (given !== undefined) {
    if (!existsSync(given)) {
      console.error(`--project ${given}: no such file; name a tsconfig.json, or leave --project out to use the nearest one above each file`)
      process.exit(2)
    }
    return path.resolve(given)
  }
  const found = ts.findConfigFile(path.dirname(file), (f) => ts.sys.fileExists(f))
  if (found === undefined) {
    console.error(`no tsconfig.json above ${file}: pass one with --project <tsconfig.json>`)
    process.exit(2)
  }
  return found
}

/** An import of this package or one of its entries, in any form: `from "tsverify"`, `"tsverify/effect"`, `import "tsverify/packs/lodash"`. */
const IMPORTS_TSVERIFY = /["']tsverify(?:\/[^"'\n]*)?["']/

/**
 * Every file under `dir` that may hold a contract, outside `node_modules` and dot folders: a TypeScript file that
 * imports tsverify, whatever its name, whose program is then read to know. A test named `*.spec.ts` that does not import
 * it is never read.
 */
const contractFilesUnder = (dir: string): Array<string> =>
  readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
    const p = path.join(dir, e.name)
    if (e.isDirectory()) return e.name === "node_modules" || e.name.startsWith(".") ? [] : contractFilesUnder(p)
    if (!e.isFile() || !/\.tsx?$/.test(e.name) || e.name.endsWith(".d.ts")) return []
    return IMPORTS_TSVERIFY.test(readFileSync(p, "utf8")) ? [p] : []
  })

/** A value as JavaScript writes it, so a counterexample can be pasted into a call: `0n`, `"a"`, `[1, NaN]`, `{ id: "a" }`. */
const literal = (x: unknown): string =>
  typeof x === "bigint"
    ? `${x}n`
    : typeof x === "number"
      ? Object.is(x, -0)
        ? "-0"
        : String(x)
      : typeof x === "string"
        ? JSON.stringify(x)
        : x === undefined
          ? "undefined"
          : Array.isArray(x)
            ? `[${x.map(literal).join(", ")}]`
            : x !== null && typeof x === "object"
              ? Object.keys(x).length === 0
                ? "{}"
                : `{ ${Object.entries(x)
                    .map(([k, v]) => `${/^[A-Za-z_$][\w$]*$/.test(k) ? k : JSON.stringify(k)}: ${literal(v)}`)
                    .join(", ")} }`
              : x === null || typeof x === "boolean"
                ? String(x)
                : `<${typeof x}>`
/** A counterexample's arguments, as the call that takes them would write them. */
const show = (args: ReadonlyArray<unknown>) => `(${args.map(literal).join(", ")})`

/** What the world gave the code on a counterexample's run: each operation's outcome, each declared function's result. */
const given = (world: Readonly<Record<string, unknown>>) =>
  Object.entries(world)
    .map(([key, x]) => {
      const what = key.replace(/!\d+$/, "")
      if (x !== null && typeof x === "object" && "_tag" in x) {
        const o = x as { readonly _tag: unknown; readonly value?: unknown; readonly error?: unknown }
        if (o._tag === "Failure") return `${what} failed with ${literal(o.error)}`
        if (o._tag === "Success") return "value" in o ? `${what} gave ${literal(o.value)}` : `${what} succeeded`
      }
      return `${what} gave ${literal(x)}`
    })
    .join(", ")

/** A counterexample's value as JSON holds it: a bigint, `undefined`, `NaN`, `±Infinity` or `-0` as a string of its JavaScript text (`"5n"`). */
const plain = (x: unknown): unknown =>
  typeof x === "bigint"
    ? `${x}n`
    : x === undefined
      ? "undefined"
      : typeof x === "number" && (!Number.isFinite(x) || Object.is(x, -0))
        ? Object.is(x, -0)
          ? "-0"
          : String(x)
        : Array.isArray(x)
          ? x.map(plain)
          : x !== null && typeof x === "object"
            ? Object.fromEntries(Object.entries(x).map(([k, v]) => [k, plain(v)]))
            : x
const plainArgs = <T extends { readonly args?: ReadonlyArray<unknown>; readonly world?: Readonly<Record<string, unknown>> }>(r: T): T => ({
  ...r,
  ...(r.args !== undefined ? { args: plain(r.args) } : {}),
  ...(r.world !== undefined ? { world: plain(r.world) } : {}),
})
const rel = (p: string) => path.relative(process.cwd(), p) || p

/** The same verdict, each place it names relative to the current folder, as the files it reports are. */
const here = (s: string) => s.replaceAll(`${process.cwd()}${path.sep}`, "")
const relative = (v: Verification): Verification => ({
  ...v,
  ...(v.unsupported !== undefined ? { unsupported: here(v.unsupported) } : {}),
  notes: v.notes.map(here),
  laws: v.laws.map((l) => (l.reason === undefined ? l : { ...l, reason: here(l.reason) })),
  obligations: v.obligations.map((o) => ({ ...o, at: here(o.at), ...(o.reason !== undefined ? { reason: here(o.reason) } : {}) })),
  trusted: v.trusted.map((t) => ({ ...t, declared: t.declared.map(here) })),
})

const plural = (n: number, word: string) => `${n} ${word}${n === 1 ? "" : "s"}`

/** The report of one verification, each line indented by `pad`. */
const report = (v: Verification, pad: string, full: boolean): Array<string> => {
  const out: Array<string> = []
  const under = `${pad}${"".padEnd(15)} `
  for (const l of v.laws) {
    // A law that says what it means leads with its sentence, and its name, as the code spells it, follows.
    const ms = `${Math.round(l.ms)} ms`
    out.push(`${pad}${l.status.padEnd(15)} ${l.says === undefined ? `${l.name}  (${ms})` : `${l.says}  (${l.name}, ${ms})`}`)
    if (l.args !== undefined) out.push(`${under}e.g. ${show(l.args)}`)
    if (l.world !== undefined && Object.keys(l.world).length > 0) out.push(`${under}where ${given(l.world)}`)
    if (l.abstract !== undefined)
      out.push(`${under}leans on what is declared of ${l.abstract.join(", ")}: true of them as declared, maybe not as they are`)
    if (l.reason !== undefined) out.push(`${under}${l.reason}`)
  }
  // What the proof code asked, then each division's divisor: proved where it runs, or the input that makes it 0n.
  for (const [heading, os] of [
    ["proof code", v.obligations.filter((o) => o.kind !== "division")],
    ["divisions", v.obligations.filter((o) => o.kind === "division")],
  ] as const) {
    if (os.length === 0) continue
    out.push(`${pad}${heading}:`)
    for (const o of os) {
      const what =
        o.kind === "invariant"
          ? `invariant ${o.phase === "entry" ? "on entry" : "kept by each iteration"}`
          : o.kind === "requires"
            ? "lemma's requires"
            : o.kind === "division"
              ? "divisor not 0n"
              : o.kind
      out.push(`${pad}  ${o.status.padEnd(15)} ${what}: ${o.text}  (${rel(o.at)})`)
      if (o.args !== undefined) out.push(`${pad}  ${"".padEnd(15)} e.g. ${show(o.args)}`)
      if (o.world !== undefined && Object.keys(o.world).length > 0) out.push(`${pad}  ${"".padEnd(15)} where ${given(o.world)}`)
      if (o.reason !== undefined) out.push(`${pad}  ${"".padEnd(15)} ${o.reason}`)
    }
  }
  if (v.trusted.length > 0) {
    if (full) {
      out.push(`${pad}trusted (declared, not proved):`)
      for (const t of v.trusted) {
        const purity =
          t.purity === "checked"
            ? `pure, checked from source (read ${t.read?.join(", ")})`
            : t.purity === "unchecked"
              ? "pure, unchecked: no source"
              : "not pure: a fresh result per call"
        out.push(`${pad}  - ${t.name}: ${purity}${t.laws.length > 0 ? `; laws ${t.laws.join(", ")}` : ""} — ${t.declared.join(", ")}`)
      }
    } else
      out.push(
        `${pad}trusted: ${v.trusted.map((t) => `${t.name} (${t.purity === "impure" ? "not pure" : `pure, ${t.purity}`}${t.laws.length > 0 ? `; ${plural(t.laws.length, "law")}` : ""})`).join(", ")}`,
      )
  }
  if (full) {
    if (v.cover.length > 0)
      out.push(`${pad}reaches: ${v.cover.map((c) => (c.status === "reachable" ? c.value : `${c.value} (${c.status})`)).join(", ")}`)
    out.push(`${pad}assumed:`)
    for (const n of v.notes) out.push(`${pad}  - ${n}`)
  }
  return out
}

const passed = (v: Verification) =>
  v.unsupported === undefined && v.laws.every((l) => l.status === "proved") && v.obligations.every((o) => o.status === "proved")

const one = async (z3: Ctx, file: string, name: string, pad: string, full: boolean): Promise<Verification> => {
  const v = relative(await verify(z3, loadProject([file], tsconfigOf(file)), file, name, opts))
  if (json) return v
  if (v.unsupported !== undefined) console.log(`${pad}${name}: not verified — ${v.unsupported}`)
  else console.log([`${pad}${name}`, ...report(v, `${pad}  `, full)].join("\n"))
  return v
}

const tally = <A>(xs: ReadonlyArray<A>, key: (x: A) => string): Record<string, number> =>
  xs.reduce<Record<string, number>>((m, x) => ({ ...m, [key(x)]: (m[key(x)] ?? 0) + 1 }), {})

/**
 * What `--json` prints: every contract verified, each with its file (relative to the current folder) and whether it
 * passed, and the totals. `passed` is what the exit code says: 0 when every contract passed.
 */
interface Report {
  readonly passed: boolean
  readonly contracts: ReadonlyArray<Verification & { readonly file: string; readonly passed: boolean }>
  readonly totals: {
    readonly contracts: number
    readonly files: number
    readonly laws: Readonly<Record<string, number>>
    readonly obligations: Readonly<Record<string, number>>
    readonly unsupported: number
  }
}
const printReport = (verdicts: ReadonlyArray<{ readonly file: string; readonly v: Verification }>) => {
  const contracts = verdicts.map(({ file, v }) => ({
    file: rel(file),
    ...v,
    laws: v.laws.map(plainArgs),
    obligations: v.obligations.map(plainArgs),
    cover: v.cover.map(plainArgs),
    passed: passed(v),
  }))
  const out: Report = {
    passed: contracts.every((c) => c.passed),
    contracts,
    totals: {
      contracts: contracts.length,
      files: new Set(contracts.map((c) => c.file)).size,
      laws: tally(
        contracts.flatMap((c) => c.laws),
        (l) => l.status,
      ),
      obligations: tally(
        contracts.flatMap((c) => c.obligations),
        (o) => o.status,
      ),
      unsupported: contracts.filter((c) => c.unsupported !== undefined).length,
    },
  }
  console.log(JSON.stringify(out, null, 2))
}

// One contract, named: everything about it.
const [first, second] = positional
if (positional.length === 2 && first !== undefined && second !== undefined && !existsSync(second)) {
  const file = path.resolve(first)
  const v = await withZ3((z3) => one(z3, file, second, "", true))
  if (json) printReport([{ file, v }])
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
  console.error(`no file that imports tsverify under ${positional.join(", ") || "."}: name a file, or a folder that holds one\n${USAGE}`)
  process.exit(2)
}

const found: Array<{ readonly file: string; readonly v: Verification }> = []
let filesRead = 0
await withZ3(async (z3) => {
  for (const file of files.sort()) {
    // Each file is its own program: the declarations it imports (an implementation, through its spec) are in force for it alone.
    const names = contractsIn(loadProject([file], tsconfigOf(file)), file)
    if (names.length === 0) continue
    filesRead++
    if (!json) console.log(rel(file))
    for (const name of names) found.push({ file, v: await one(z3, file, name, "  ", verbose) })
  }
})
const verdicts = found.map((f) => f.v)
if (verdicts.length === 0) {
  console.error(
    `no contract in ${files.map(rel).join(", ")}: a spec is verified through its implementation, \`const f: Implementation<S> = ...\`, or a \`contract\`, \`computation\` or lemma the file exports\n${USAGE}`,
  )
  process.exit(2)
}
if (json) {
  printReport(found)
  process.exit(verdicts.every(passed) ? 0 : 1)
}

const count = <A>(xs: ReadonlyArray<A>, key: (x: A) => string) =>
  Object.entries(tally(xs, key))
    .map(([k, n]) => `${n} ${k}`)
    .join(", ")
const laws = verdicts.flatMap((v) => v.laws)
const obligations = verdicts.flatMap((v) => v.obligations)
const unread = verdicts.filter((v) => v.unsupported !== undefined).length
console.log(
  `\n${plural(verdicts.length, "contract")} in ${plural(filesRead, "file")}: laws ${count(laws, (l) => l.status) || "none"}` +
    (obligations.length > 0 ? `; obligations ${count(obligations, (o) => o.status)}` : "") +
    (unread > 0 ? `; ${unread} not verified` : ""),
)
process.exit(verdicts.every(passed) ? 0 : 1)

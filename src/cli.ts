#!/usr/bin/env node
// tsverify [<file or folder>...] [--project tsconfig.json] [--bound 4] [--work 15000000] [--verbose] [--json] [--watch]
//   Verifies every contract each file exports: every implementation of a spec (`const f: Implementation<S>`),
//   and every `contract`, computation and lemma, in each file that imports tsverify under each folder (the current one
//   by default): a line per contract, under it a line per law that needs a look (per law, of a run of one file or with
//   --verbose), then the totals. Exits 1 unless every law is proved and says something of its function, and every
//   obligation of the proof code is proved.
// tsverify <file.ts> <export>
//   Verifies one contract, with everything the verification knows: the states its result reaches, what it trusted
//   and what it assumed.
// --json prints one JSON document instead, of every verdict in full (`Report`), and the same exit code.
// --watch runs it again on every change to the project's TypeScript, until stopped: each run in a process of its own,
//   the screen redrawn in a terminal, each run's report after the last one otherwise (with --json, a line per run).
// Exits 0 when everything is proved, 1 when something is not, 2 on a usage error, 3 when the verifier itself fails.
// In a terminal the report is drawn live and in colour (`./view.ts`); piped, or with NO_COLOR set, it is plain text.
import { type ChildProcess, spawn } from "node:child_process"
import { existsSync, readdirSync, readFileSync, statSync, watch as watchFiles } from "node:fs"
import path from "node:path"
import { fileURLToPath } from "node:url"
import { styleText } from "node:util"
import ts from "typescript"
import { contractsIn, loadProject, type Project } from "./project.ts"
import type { Ctx } from "./value.ts"
import { type Options, type Verification, verify, withZ3 } from "./verify.ts"
import type { Run } from "./view.ts"

// A failure of the verifier is no verdict on the code: exit 3, so no caller reads it as a law not proved.
process.on("uncaughtException", (e) => {
  console.error(`tsverify failed, which says nothing of the code: ${e instanceof Error ? (e.stack ?? e.message) : String(e)}`)
  process.exit(3)
})

// The same verdict on every run asks for the same collections of the solver's terms: when JavaScript collects them
// decides which of their numbers the solver hands out again, and so the order of its search. V8 collects on a schedule
// of its own only by a flag it takes on its command line alone (`NODE_OPTIONS` refuses it), so the command runs itself
// again with it, and leaves with what that run leaves with.
const STEADY = "--predictable-gc-schedule"
if (!process.execArgv.includes(STEADY)) {
  const run = spawn(process.execPath, [STEADY, ...process.execArgv, ...process.argv.slice(1)], { stdio: "inherit" })
  const signals = ["SIGINT", "SIGTERM", "SIGHUP"] as const
  for (const s of signals) process.on(s, () => run.kill(s))
  run.on("exit", (code, signal) => {
    if (signal === null) process.exit(code ?? 3)
    for (const s of signals) process.removeAllListeners(s)
    process.kill(process.pid, signal)
  })
  await new Promise<never>(() => {})
}

const USAGE =
  "usage: tsverify [<file or folder>...] [--project tsconfig.json] [--bound N] [--work N] [--verbose] [--json] [--watch]\n       tsverify <file.ts> <export> [--json] [--watch]"
const argv = process.argv.slice(2)
const VALUED = new Set(["--project", "--bound", "--work"])
const positional = argv.filter((a, i) => !a.startsWith("--") && !VALUED.has(argv[i - 1] ?? ""))
const flag = (f: string): string | undefined => {
  const i = argv.indexOf(f)
  return i < 0 ? undefined : argv[i + 1]
}
const verbose = argv.includes("--verbose")
const json = argv.includes("--json")
const bound = flag("--bound") === undefined ? undefined : Number(flag("--bound"))
const work = flag("--work") === undefined ? undefined : Number(flag("--work"))
const opts: Options = { ...(bound ? { bound } : {}), ...(work ? { work } : {}) }

/** The watch's own lines, styled for a terminal; `styleText` leaves them plain when stdout is not one, or `NO_COLOR` is set. */
const paint = (style: Parameters<typeof styleText>[0], text: string): string => (json ? text : styleText(style, text))

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

/** An import of this package or one of its entries, in any form: `from "@emyann/tsverify"`, `"@emyann/tsverify/effect"`, `import "@emyann/tsverify/packs/lodash"`. */
const IMPORTS_TSVERIFY = /["']@emyann\/tsverify(?:\/[^"'\n]*)?["']/

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

const passed = (v: Verification) =>
  v.unsupported === undefined && v.laws.every((l) => l.status === "proved") && v.obligations.every((o) => o.status === "proved")

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

/** A change the verdicts may follow: the project's TypeScript or its configuration, outside `node_modules` and dot folders. */
const relevant = (name: string): boolean => {
  const parts = name.split(/[\\/]/)
  if (parts.some((p) => p === "node_modules" || p.startsWith("."))) return false
  const base = parts.at(-1) ?? ""
  return (/\.[cm]?tsx?$/.test(base) && !base.endsWith(".d.ts")) || base === "tsconfig.json" || base === "package.json"
}

/**
 * `--watch`: the same command again on every change, until stopped. Each run is a process of its own, so a run starts
 * fresh, as a single run does, and one a newer change makes stale is stopped. In a terminal the screen is redrawn; piped,
 * each run's report follows the last one's under a line saying when and why it ran, and with `--json` each run is one
 * line of JSON.
 */
const watching = (): Promise<never> => {
  const args = argv.filter((a) => a !== "--watch")
  const tty = process.stdout.isTTY === true
  const start = path.resolve(positional[0] ?? ".")
  const config =
    flag("--project") ??
    ts.findConfigFile(statSync(start, { throwIfNoEntry: false })?.isDirectory() ? start : path.dirname(start), (f) => ts.sys.fileExists(f))
  const root = config === undefined ? process.cwd() : path.dirname(path.resolve(config))
  let child: ChildProcess | undefined
  let pending: string | undefined
  let timer: ReturnType<typeof setTimeout> | undefined
  const run = (why: string): void => {
    if (child !== undefined) {
      pending = why
      child.kill()
      return
    }
    const at = new Date().toLocaleTimeString()
    if (tty) process.stdout.write("\x1b[2J\x1b[3J\x1b[H")
    else if (!json) console.log("")
    if (!json) console.log(paint("dim", `tsverify --watch · ${at} · ${why}`))
    let out = ""
    const c = spawn(process.execPath, [...process.execArgv, fileURLToPath(import.meta.url), ...args], {
      stdio: ["ignore", json ? "pipe" : "inherit", "inherit"],
    })
    c.stdout?.on("data", (d: Buffer) => (out += d.toString()))
    child = c
    c.on("exit", (code, signal) => {
      child = undefined
      if (pending !== undefined) {
        const next = pending
        pending = undefined
        run(next)
        return
      }
      if (signal !== null) return
      if (json) {
        // One line per run, so a reader takes each run as it comes.
        try {
          console.log(JSON.stringify(JSON.parse(out)))
        } catch {
          process.stdout.write(out)
        }
        return
      }
      // The report ends with how long the run took: this line says only where it leaves you.
      const state =
        code === 0 ? paint("green", "all proved") : code === 1 ? paint("red", "not all proved") : paint("magenta", `exit ${code}`)
      console.log(`\n${state}${paint("dim", " · waiting for a change (Ctrl+C to stop)")}`)
    })
  }
  watchFiles(root, { recursive: true }, (_event, name) => {
    if (name === null || !relevant(name)) return
    clearTimeout(timer)
    // An editor saves in several writes: run once they are done.
    timer = setTimeout(() => run(`${name} changed`), 150)
  })
  const stop = (code: number) => () => {
    child?.kill()
    process.exit(code)
  }
  process.on("SIGINT", stop(130))
  process.on("SIGTERM", stop(143))
  process.on("SIGHUP", stop(129))
  run("started")
  return new Promise<never>(() => {})
}
if (argv.includes("--watch")) await watching()

/** Nothing as it goes: with `--json` the run prints one document, at its end. */
const QUIET: Run = {
  reading: () => Promise.resolve(),
  file: () => {},
  verifying: () => {},
  progress: () => {},
  verified: () => {},
  end: () => Promise.resolve(),
  quit: () => Promise.resolve(),
}
/** The report as text, drawn by `./view.ts`, which is loaded only then: `--json` never loads Ink, nor React. */
const reporting = async (files: number, single: boolean): Promise<Run> => {
  if (json) return QUIET
  // React's checks for a developer of React components, slower and noisier, are not this command's.
  process.env.NODE_ENV ??= "production"
  const view = await import("./view.ts")
  return view.run({ live: process.stdout.isTTY === true, files, verbose, single })
}

/** Verifies one contract of a program read, telling the report as it goes; and how long it took. */
const verified = async (z3: Ctx, r: Run, project: Project, file: string, name: string): Promise<Verification> => {
  r.verifying(name)
  const started = performance.now()
  const v = relative(await verify(z3, project, file, name, { ...opts, progress: r.progress }))
  r.verified(v, performance.now() - started)
  return v
}

// One contract, named: everything about it.
const [first, second] = positional
if (positional.length === 2 && first !== undefined && second !== undefined && !existsSync(second)) {
  const file = path.resolve(first)
  const config = tsconfigOf(file)
  const r = await reporting(1, true)
  await r.reading(rel(file))
  const project = loadProject([file], config)
  const v = await withZ3((z3) => verified(z3, r, project, file, second))
  await r.end(1)
  if (json) printReport([{ file, v }])
  process.exit(passed(v) ? 0 : 1)
}

// Every contract of every file found.
const files = (positional.length === 0 ? ["."] : positional)
  .flatMap((p) => {
    if (!existsSync(p)) {
      console.error(`${p}: no such file or folder\n${USAGE}`)
      process.exit(2)
    }
    return statSync(p).isDirectory() ? contractFilesUnder(path.resolve(p)) : [path.resolve(p)]
  })
  .sort()
if (files.length === 0) {
  console.error(`no file that imports tsverify under ${positional.join(", ") || "."}: name a file, or a folder that holds one\n${USAGE}`)
  process.exit(2)
}
// Each one's tsconfig.json found first, so a usage error is told before the report starts drawing.
const configs = new Map(files.map((f) => [f, tsconfigOf(f)]))

const r = await reporting(files.length, false)
const found: Array<{ readonly file: string; readonly v: Verification }> = []
let filesRead = 0
await withZ3(async (z3) => {
  for (const file of files) {
    await r.reading(rel(file))
    // Each file is its own program, read once for all its contracts: the declarations it imports (an implementation,
    // through its spec) are in force for it alone.
    const project = loadProject([file], configs.get(file) ?? tsconfigOf(file))
    const names = contractsIn(project, file)
    if (names.length === 0) continue
    filesRead++
    r.file(rel(file), names)
    for (const name of names) found.push({ file, v: await verified(z3, r, project, file, name) })
  }
})
if (found.length === 0) {
  await r.quit()
  console.error(
    `no contract in ${files.map(rel).join(", ")}: a spec is verified through its implementation, \`const f: Implementation<S> = ...\`, or a \`contract\`, \`computation\` or lemma the file exports\n${USAGE}`,
  )
  process.exit(2)
}
await r.end(filesRead)
if (json) printReport(found)
process.exit(found.every(({ v }) => passed(v)) ? 0 : 1)

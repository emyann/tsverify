#!/usr/bin/env node
// tsverify [<file or folder>...] [--project tsconfig.json] [--bound 4] [--work 15000000] [--verbose] [--json] [--watch]
//          [--cache] [--cache-location <folder>] [--workers 1] [--config tsverify.config.json]
//   Verifies every contract each file exports: every implementation of a spec (typed `Implementation<S>`, itself or
//   through the type its spec's module exports), and every `contract`, computation and lemma, in each file under each
//   folder (the current one by default) that imports tsverify, or imports a file of its own that does: a line per
//   contract, under it a line per law that needs a look (per law, of a run of one file or with --verbose), then the
//   totals. Exits 1 unless every law is proved and says something of its function, and every
//   obligation of the proof code is proved.
// tsverify <file.ts> <export>
//   Verifies one contract, with everything the verification knows: the states its result reaches, what it trusted
//   and what it assumed.
// --json prints one JSON document instead, of every verdict in full (`Report`), and the same exit code.
// --cache keeps each contract's verdict between runs, and answers a contract whose program reads the same text again
//   from it (`./cache.ts`), in node_modules/.cache/tsverify beside the nearest package.json above the current folder,
//   or in --cache-location <folder>. A verdict not used for 14 days is removed at the end of a run. A counterexample so
//   answered is one an earlier run found, which may not be the one a run without it would print.
// --workers N verifies the files in N processes of their own (`./pool.ts`), 1 by default: the same report, in the same
//   order, the same document and the same exit code as one process.
// --config <file>, else tsverify.config.json in the current folder, sets the roots of a run that names none and the
//   options above (`./config.ts`); a flag beats it, and anything in it the command does not take is a usage error.
// --watch runs it again on every change to the project's TypeScript, until stopped: each run in a process of its own,
//   the screen redrawn in a terminal, each run's report after the last one otherwise (with --json, a line per run).
// --help (or -h) prints the usage and each option, and reads nothing; an option it does not take is a usage error.
// Exits 0 when everything is proved, 1 when something is not, 2 on a usage error, 3 when the verifier itself fails.
// In a terminal the report is drawn live and in colour (`./view.ts`); piped, or with NO_COLOR set, it is plain text.
import { type ChildProcess, spawn } from "node:child_process"
import { existsSync, readdirSync, readFileSync, statSync, watch as watchFiles } from "node:fs"
import path from "node:path"
import { fileURLToPath } from "node:url"
import { styleText } from "node:util"
import ts from "typescript"
import { verdictsIn, prune } from "./cache.ts"
import { CONFIG_FILE, type Config, configIn, readConfig } from "./config.ts"
import { verifyInWorkers } from "./pool.ts"
import { loadProject } from "./project.ts"
import { type Tell, verifyContract, verifyFile } from "./verify-file.ts"
import { type Options, type Verification, withZ3 } from "./verify.ts"
import type { Run } from "./view.ts"

// A failure of the verifier is no verdict on the code: exit 3, so no caller reads it as a law not proved.
process.on("uncaughtException", (e) => {
  console.error(`tsverify failed, which says nothing of the code: ${e instanceof Error ? (e.stack ?? e.message) : String(e)}`)
  process.exit(3)
})

const USAGE =
  "usage: tsverify [<file or folder>...] [--project tsconfig.json] [--bound N] [--work N] [--verbose] [--json] [--watch] [--cache] [--cache-location <folder>] [--workers N] [--config <file>]\n       tsverify <file.ts> <export> [--json] [--watch] [--cache] [--cache-location <folder>]"
const HELP = `${USAGE}

  <file or folder>...    every contract each file exports, the current folder's by default
  <file.ts> <export>     one contract, with everything the verification knows of it
  --project <tsconfig>   the tsconfig.json every file is read through, instead of the nearest one above it
  --bound N              the longest array the search side tries, 4 by default
  --work N               the work each query may do, in Z3's own steps, 15000000 by default
  --verbose              every law of every contract, as the one-contract form prints them
  --json                 one JSON document instead of the text
  --watch                the same again on every change to the project's TypeScript, until stopped
  --cache                keep each contract's verdict, and answer a contract verified before from it
  --cache-location <dir> where --cache keeps them, node_modules/.cache/tsverify by default
  --workers N            verify the files in N processes, each its own Z3 and its own memory, 1 by default; the report
                         is the one a single process gives
  --config <file>        the config file to read, instead of tsverify.config.json in the current folder
  --help, -h             this

tsverify.config.json, in the current folder, is JSON of these keys alone: "roots" (the folders and files verified when
none is named), "bound", "work", "workers", "cache" (true or false) and "cacheLocation". Its paths are read from its own
folder. A root named, or a flag, beats it; a flag can only turn on the cache, not off. Anything else in it is a usage
error.

Exits 0 when everything is proved, 1 when something is not, 2 on a usage error, 3 when the verifier itself fails.`
const argv = process.argv.slice(2)
const VALUED = new Set(["--project", "--bound", "--work", "--cache-location", "--workers", "--config"])
const OPTIONS = new Set([...VALUED, "--verbose", "--json", "--watch", "--cache"])
// Asked before anything is read: an option the command does not take would otherwise be dropped, and a run with no file
// named verifies every contract under the current folder.
if (argv.includes("--help") || argv.includes("-h")) {
  console.log(HELP)
  process.exit(0)
}
const unknown = argv.find((a, i) => a.startsWith("-") && !OPTIONS.has(a) && !VALUED.has(argv[i - 1] ?? ""))
if (unknown !== undefined) {
  console.error(`${unknown}: tsverify takes no such option (tsverify --help lists them)\n${USAGE}`)
  process.exit(2)
}

// When JavaScript collects the solver's terms decided which of their numbers the solver hands out again, and so the
// order of its search, until each contract was verified in a Z3 context of its own that frees no term while it is
// verified (`ownContext` in ./verify.ts). The command still runs itself again with V8 collecting on a schedule of
// its own, a flag it takes on its command line alone (`NODE_OPTIONS` refuses it), and leaves with what that run
// leaves with.
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

const positional = argv.filter((a, i) => !a.startsWith("--") && !VALUED.has(argv[i - 1] ?? ""))
const flag = (f: string): string | undefined => {
  const i = argv.indexOf(f)
  return i < 0 ? undefined : argv[i + 1]
}
const verbose = argv.includes("--verbose")
const json = argv.includes("--json")
/** The value a valued flag is given, refused when it has none: the next word an option, or nothing. */
const valued = (f: string, what: string): string | undefined => {
  if (!argv.includes(f)) return undefined
  const given = flag(f)
  if (given === undefined || given.startsWith("--")) {
    console.error(`${f} takes ${what}\n${USAGE}`)
    process.exit(2)
  }
  return given
}
/** The config file of the run, `--config <file>` or the current folder's, and the path it is named by. */
const configFile = valued("--config", "the config file to read") ?? configIn(process.cwd())
const config = ((): Config => {
  if (configFile === undefined) return {}
  const read = readConfig(configFile)
  if ("error" in read) {
    console.error(`${path.relative(process.cwd(), path.resolve(configFile)) || configFile}: ${read.error}\n${USAGE}`)
    process.exit(2)
  }
  return read.config
})()
const bound = flag("--bound") === undefined ? config.bound : Number(flag("--bound"))
const work = flag("--work") === undefined ? config.work : Number(flag("--work"))
/** How many processes verify the files: `--workers N`, else the config's, else 1. */
const workers = ((): number => {
  const given = valued("--workers", "how many processes verify the files, a positive whole number")
  if (given === undefined) return config.workers ?? 1
  if (!/^[1-9]\d*$/.test(given)) {
    console.error(`--workers ${given}: how many processes verify the files is a positive whole number\n${USAGE}`)
    process.exit(2)
  }
  return Number(given)
})()
/** The roots a run with none named verifies: the config's, else the current folder. */
const roots = positional.length > 0 ? positional : (config.roots ?? ["."])
/** Where the verdicts are kept, with `--cache` or the config's: `--cache-location <folder>`, the config's, else the nearest package's. */
const cacheDir = ((): string | undefined => {
  if (!argv.includes("--cache") && config.cache !== true) return undefined
  const given = valued("--cache-location", "the folder to keep the verdicts in")
  if (given !== undefined) return path.resolve(given)
  if (config.cacheLocation !== undefined) return config.cacheLocation
  for (let dir = process.cwd(); ; dir = path.dirname(dir)) {
    if (existsSync(path.join(dir, "package.json"))) return path.join(dir, "node_modules", ".cache", "tsverify")
    if (path.dirname(dir) === dir) return undefined
  }
})()
/** How long a verdict is kept unused: past it, the code it was of has changed. */
const KEPT_DAYS = 14
const opts: Options = {
  ...(bound ? { bound } : {}),
  ...(work ? { work } : {}),
  ...(cacheDir === undefined ? {} : { cache: verdictsIn(cacheDir) }),
}
/** Leaves with `code`, the folder of verdicts rid of what has not been asked for a while. */
const leave = (code: number): never => {
  if (cacheDir !== undefined) prune(cacheDir, KEPT_DAYS)
  process.exit(code)
}

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

/** Every TypeScript file under `dir`, outside `node_modules` and dot folders, declaration files left out. */
const typeScriptUnder = (dir: string): Array<string> =>
  readdirSync(dir, { withFileTypes: true }).flatMap((e) => {
    const p = path.join(dir, e.name)
    if (e.isDirectory()) return e.name === "node_modules" || e.name.startsWith(".") ? [] : typeScriptUnder(p)
    return e.isFile() && /\.tsx?$/.test(e.name) && !e.name.endsWith(".d.ts") ? [p] : []
  })

/** The file a relative import names, as TypeScript finds it: written whole, `.js` for `.ts`, or with an extension or `index` added. */
const imported = (from: string, specifier: string): string | undefined => {
  const base = path.resolve(path.dirname(from), specifier)
  const tried = [
    base,
    base.replace(/\.(c|m)?js$/, ".$1ts"),
    base.replace(/\.jsx$/, ".tsx"),
    `${base}.ts`,
    `${base}.tsx`,
    path.join(base, "index.ts"),
  ]
  return tried.find((f) => /\.tsx?$/.test(f) && existsSync(f) && statSync(f).isFile())
}

/**
 * Every file under `dir` that may hold a contract, whose program is then read to know: a TypeScript file that imports
 * tsverify, whatever its name, or that imports, by a relative path, a file that does, wherever that one is: the code of
 * a spec whose module gives it its type (`export type Shipping = Implementation<typeof shippingSpec>`) imports no
 * tsverify. A test named `*.spec.ts` that imports neither is never read.
 */
const contractFilesUnder = (dir: string): Array<string> => {
  const known = new Map<string, boolean>()
  const importsTsverify = (f: string): boolean => {
    let yes = known.get(f)
    if (yes === undefined) {
      yes = IMPORTS_TSVERIFY.test(readFileSync(f, "utf8"))
      known.set(f, yes)
    }
    return yes
  }
  return typeScriptUnder(dir).filter(
    (f) =>
      importsTsverify(f) ||
      ts.preProcessFile(readFileSync(f, "utf8"), true, true).importedFiles.some((i) => {
        if (!i.fileName.startsWith(".")) return false
        const target = imported(f, i.fileName)
        return target !== undefined && importsTsverify(target)
      }),
  )
}

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

const passed = (v: Verification) =>
  v.unsupported === undefined &&
  v.undecided === undefined &&
  v.laws.every((l) => l.status === "proved") &&
  v.obligations.every((o) => o.status === "proved")

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
    readonly undecided: number
    /** How many questions ended without an answer, the laws' and the contracts' own: each is said where it was asked. */
    readonly unanswered: number
  }
}
const printReport = (verdicts: ReadonlyArray<{ readonly file: string; readonly v: Verification }>) => {
  const contracts = verdicts.map(({ file, v }) => ({
    file: rel(file),
    ...v,
    laws: v.laws.map(plainArgs),
    obligations: v.obligations.map(plainArgs),
    cover: v.cover.map(plainArgs),
    ...(v.undecided === undefined
      ? {}
      : {
          undecided: {
            ...v.undecided,
            ...(v.undecided.args === undefined ? {} : { args: v.undecided.args.map(plain) }),
            ...(v.undecided.results === undefined
              ? {}
              : { results: [plain(v.undecided.results[0]), plain(v.undecided.results[1])] as const }),
          },
        }),
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
      undecided: contracts.filter((c) => c.undecided !== undefined).length,
      unanswered: contracts.reduce(
        (n, c) => n + (c.unanswered?.length ?? 0) + c.laws.reduce((m, l) => m + (l.unanswered?.length ?? 0), 0),
        0,
      ),
    },
  }
  console.log(JSON.stringify(out, null, 2))
}

/** A change the verdicts may follow: the project's TypeScript or its configuration, outside `node_modules` and dot folders. */
const relevant = (name: string): boolean => {
  const parts = name.split(/[\\/]/)
  if (parts.some((p) => p === "node_modules" || p.startsWith("."))) return false
  const base = parts.at(-1) ?? ""
  return (
    (/\.[cm]?tsx?$/.test(base) && !base.endsWith(".d.ts")) || base === "tsconfig.json" || base === "package.json" || base === CONFIG_FILE
  )
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
  const tsconfig =
    flag("--project") ??
    ts.findConfigFile(statSync(start, { throwIfNoEntry: false })?.isDirectory() ? start : path.dirname(start), (f) => ts.sys.fileExists(f))
  // Roots the config names are read from its folder, which holds them all.
  const root =
    positional.length === 0 && configFile !== undefined
      ? path.dirname(path.resolve(configFile))
      : tsconfig === undefined
        ? process.cwd()
        : path.dirname(path.resolve(tsconfig))
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

/** The report told what a file's verification tells, `file` as the report names it. */
const telling = (r: Run, file: string): Tell => ({
  file: (names) => r.file(rel(file), names),
  verifying: r.verifying,
  progress: r.progress,
  verified: r.verified,
})

// One contract, named: everything about it.
const [first, second] = positional
if (positional.length === 2 && first !== undefined && second !== undefined && !existsSync(second)) {
  const file = path.resolve(first)
  const tsconfig = tsconfigOf(file)
  const r = await reporting(1, true)
  await r.reading(rel(file))
  const project = loadProject([file], tsconfig)
  const v = await withZ3((z3) => verifyContract(z3, project, file, second, { ...opts, cover: true }, telling(r, file)))
  await r.end(1)
  if (json) printReport([{ file, v }])
  leave(passed(v) ? 0 : 1)
}

// Every contract of every file found.
const files = roots
  .flatMap((p) => {
    if (!existsSync(p)) {
      console.error(`${rel(p)}: no such file or folder\n${USAGE}`)
      process.exit(2)
    }
    return statSync(p).isDirectory() ? contractFilesUnder(path.resolve(p)) : [path.resolve(p)]
  })
  .sort()
if (files.length === 0) {
  console.error(`no file that imports tsverify under ${roots.map(rel).join(", ")}: name a file, or a folder that holds one\n${USAGE}`)
  process.exit(2)
}
// Each one's tsconfig.json found first, so a usage error is told before the report starts drawing.
const configs = new Map(files.map((f) => [f, tsconfigOf(f)]))

const r = await reporting(files.length, false)
const cover = json || verbose
const { found, filesRead } =
  workers > 1 && files.length > 1
    ? await verifyInWorkers(
        files,
        (file) => ({
          file,
          tsconfig: configs.get(file) ?? tsconfigOf(file),
          ...(bound ? { bound } : {}),
          ...(work ? { work } : {}),
          cover,
          ...(cacheDir === undefined ? {} : { cacheDir }),
        }),
        workers,
        r,
        rel,
      )
    : await withZ3(async (z3) => {
        const found: Array<{ readonly file: string; readonly v: Verification }> = []
        let filesRead = 0
        for (const file of files) {
          await r.reading(rel(file))
          const tell = telling(r, file)
          const vs = await verifyFile(
            z3,
            file,
            configs.get(file) ?? tsconfigOf(file),
            { ...opts, cover },
            {
              ...tell,
              file: (names) => {
                filesRead++
                tell.file(names)
              },
            },
          )
          for (const v of vs) found.push({ file, v })
        }
        return { found, filesRead }
      })
if (found.length === 0) {
  await r.quit()
  console.error(
    `no contract in ${files.map(rel).join(", ")}: a spec is verified through the function that implements it, typed \`Implementation<S>\` or by the type its spec's module exports: name the file that function is written in, or one that exports a \`contract\`, \`computation\` or lemma\n${USAGE}`,
  )
  process.exit(2)
}
await r.end(filesRead)
if (json) printReport(found)
leave(found.every(({ v }) => passed(v)) ? 0 : 1)

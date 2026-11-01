// The verdicts of contracts, kept between runs in a folder. A contract is keyed by what decides its verdict: the text of
// every file of the program it is read from (its own, each file it imports, the declarations of the packages and of
// JavaScript those bring in), the settings it is verified under, and the verifier itself. Verified again with nothing
// of that changed, it is answered from the folder and not verified. A change to any file its program reads, the code
// read in place, a law, an assumption, a type, verifies it again: a change cascades to every contract whose program
// holds the changed file, and stops at the contracts whose program does not. A verdict with something the solver ran out
// of work on is not kept; a fresh run asks it again.
//
// The key holds the verifier's own code and Z3's version, so a new tsverify, or a change to its source in a checkout,
// answers nothing from an older one's folder. A query's formula, printed by Z3, would key each query of a contract
// apart; it was measured at three quarters of a run answered from the folder, and keying the program's text costs
// milliseconds.
import { createHash } from "node:crypto"
import { mkdirSync, readdirSync, readFileSync, renameSync, rmSync, statSync, utimesSync, writeFileSync } from "node:fs"
import { createRequire } from "node:module"
import path from "node:path"
import { fileURLToPath } from "node:url"
import type ts from "typescript"
import type { Project } from "./project.ts"
import type { Options, Verification } from "./verify.ts"

/** Where the verdicts of contracts are kept: `verdictsIn` keeps them in a folder; a test may count what it is asked. */
export interface Cache {
  /** The verdict kept for the contract `key` names, or undefined: the contract is then verified, and its verdict set. */
  readonly get: (key: string) => Verification | undefined
  readonly set: (key: string, verdict: Verification) => void
}

/** What a kept verdict is written as: bumped when it changes, so an older folder answers nothing. */
const FORMAT = "tsverify-verdicts-1"

let ownCode: string | undefined
/**
 * The verifier's own code, and Z3's: a hash of every module beside this one (the source in a checkout, the build in a
 * package) and Z3's version. A verdict is kept under it, so a change to either answers nothing from before it.
 */
export const identity = (): string => {
  if (ownCode !== undefined) return ownCode
  const h = createHash("sha256").update(FORMAT)
  const root = path.dirname(fileURLToPath(import.meta.url))
  const walk = (dir: string): void => {
    for (const e of readdirSync(dir, { withFileTypes: true }).sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0))) {
      const at = path.join(dir, e.name)
      if (e.isDirectory()) walk(at)
      else if (/\.[cm]?[jt]s$/.test(e.name) && !e.name.endsWith(".d.ts"))
        h.update(path.relative(root, at)).update("\0").update(readFileSync(at)).update("\0")
    }
  }
  walk(root)
  h.update(`z3-solver ${z3Version()}`)
  ownCode = h.digest("hex")
  return ownCode
}

/** The version of the `z3-solver` package this one resolves. */
const z3Version = (): string => {
  let dir = path.dirname(createRequire(import.meta.url).resolve("z3-solver"))
  for (;;) {
    try {
      const manifest = JSON.parse(readFileSync(path.join(dir, "package.json"), "utf8")) as { name?: string; version?: string }
      if (manifest.name === "z3-solver") return manifest.version ?? "unknown"
    } catch {
      // No manifest here: look further up.
    }
    const up = path.dirname(dir)
    if (up === dir) return "unknown"
    dir = up
  }
}

/** Each file's text as its hash, read once a run: the programs of a folder's files share most of theirs. */
const hashed = new Map<string, { readonly text: string; readonly hash: string }>()
const hashOf = (sf: ts.SourceFile): string => {
  const known = hashed.get(sf.fileName)
  if (known !== undefined && known.text === sf.text) return known.hash
  const hash = createHash("sha256").update(sf.text).digest("hex")
  hashed.set(sf.fileName, { text: sf.text, hash })
  return hash
}

/**
 * What decides the verdict of contract `name` of `file`: every file of the program and its text, the compiler's
 * options, the settings it is verified under, and the folder its paths are said from.
 */
export const contractKey = (project: Project, file: string, name: string, opts: Options): string => {
  const h = createHash("sha256")
  h.update(
    JSON.stringify({
      file,
      name,
      cwd: process.cwd(),
      bound: opts.bound ?? null,
      work: opts.work ?? null,
      only: opts.only ?? null,
      within: opts.within ?? null,
      cover: opts.cover !== false,
      options: project.program.getCompilerOptions(),
    }),
  )
  const files = [...project.program.getSourceFiles()].sort((a, b) => (a.fileName < b.fileName ? -1 : 1))
  for (const sf of files) h.update("\0").update(sf.fileName).update("\0").update(hashOf(sf))
  return h.digest("hex")
}

/** Whether the solver ran out of work anywhere in `v`: such a verdict is not kept. */
const unfinished = (v: Verification): boolean =>
  v.laws.some((l) => l.status === "unknown") ||
  v.cover.some((c) => c.status === "unknown") ||
  v.obligations.some((o) => o.status === "unknown")

/**
 * Verdicts kept in `dir`, a file each, under the hash of the verifier's identity and the contract's key. Writing a file
 * whole and renaming it into place lets two runs share a folder. A file that cannot be read is no verdict.
 */
export const verdictsIn = (dir: string): Cache => {
  const fileOf = (key: string): string => {
    const name = createHash("sha256").update(identity()).update("\0").update(key).digest("hex")
    return path.join(dir, name.slice(0, 2), `${name}.json`)
  }
  return {
    get: (key) => {
      const file = fileOf(key)
      let kept: Verification
      try {
        kept = decode(JSON.parse(readFileSync(file, "utf8"))) as Verification
      } catch {
        return undefined
      }
      // Its time says when it was last used, which is what `prune` reads.
      try {
        const now = new Date()
        utimesSync(file, now, now)
      } catch {
        // A folder that cannot be written still answers what it holds.
      }
      return kept
    },
    set: (key, verdict) => {
      if (unfinished(verdict)) return
      const file = fileOf(key)
      try {
        mkdirSync(path.dirname(file), { recursive: true })
        const draft = `${file}.${process.pid}.${Math.random().toString(36).slice(2)}.tmp`
        writeFileSync(draft, JSON.stringify(encode(verdict)))
        renameSync(draft, file)
      } catch {
        // A verdict not kept is verified again next time.
      }
    },
  }
}

/** Removes from `dir` every verdict not used for `days` days: what code that has changed since asked. */
export const prune = (dir: string, days: number): void => {
  const before = Date.now() - days * 86_400_000
  let shards: Array<string>
  try {
    shards = readdirSync(dir)
  } catch {
    return
  }
  for (const shard of shards) {
    const at = path.join(dir, shard)
    let files: Array<string>
    try {
      files = readdirSync(at)
    } catch {
      continue
    }
    for (const f of files) {
      const file = path.join(at, f)
      try {
        if (statSync(file).mtimeMs < before) rmSync(file, { force: true })
      } catch {
        // Gone already, or another run's.
      }
    }
  }
}

/**
 * A verdict as JSON, its counterexamples' values among it: what JSON writes as itself (a string, a boolean, `null`, a finite number other
 * than -0) is left so, and anything else is a tagged pair, `["~kind", ...]`, an array among them, so a JSON array is
 * always a tag. Every kind of value a model is read back as (`./concrete.ts`) is one of these.
 */
const encode = (x: unknown): unknown => {
  if (x === null || typeof x === "string" || typeof x === "boolean") return x
  if (typeof x === "number") return Number.isFinite(x) && !Object.is(x, -0) ? x : ["~number", String(x === 0 ? "-0" : x)]
  if (x === undefined) return ["~undefined"]
  if (typeof x === "bigint") return ["~bigint", String(x)]
  if (typeof x === "symbol") return ["~symbol", x.description ?? ""]
  if (typeof x === "function") return ["~function"]
  if (Array.isArray(x)) return ["~array", x.map(encode)]
  if (x instanceof Date) return ["~date", encode(x.getTime())]
  if (x instanceof Map) return ["~map", [...x].map(([k, v]) => [encode(k), encode(v)])]
  if (x instanceof Set) return ["~set", [...x].map(encode)]
  return ["~object", Object.entries(x).map(([k, v]) => [k, encode(v)])]
}

const decode = (x: unknown): unknown => {
  if (!Array.isArray(x)) return x
  const [tag, v] = x as [unknown, unknown]
  switch (tag) {
    case "~number":
      return v === "-0" ? -0 : Number(v)
    case "~array":
      return (v as Array<unknown>).map(decode)
    case "~undefined":
      return undefined
    case "~bigint":
      return BigInt(v as string)
    case "~symbol":
      return Symbol(v as string)
    case "~function":
      return () => undefined
    case "~date":
      return new Date(decode(v) as number)
    case "~map":
      return new Map((v as Array<[unknown, unknown]>).map(([k, w]) => [decode(k), decode(w)]))
    case "~set":
      return new Set((v as Array<unknown>).map(decode))
    case "~object": {
      // Each its own property, `__proto__` among them, which an assignment would take for the prototype.
      const out: Record<string, unknown> = {}
      for (const [k, w] of v as Array<[string, unknown]>)
        Object.defineProperty(out, k, { value: decode(w), enumerable: true, writable: true, configurable: true })
      return out
    }
    default:
      throw new Error(`no kind of value is tagged ${String(tag)}`)
  }
}

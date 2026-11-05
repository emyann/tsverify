// The config file of a run: `tsverify.config.json` in the current folder, or the file `--config` names. Strict JSON, of
// these keys alone: the roots a run with none named verifies, and the options the command takes as flags. A flag beats
// a key, a root named beats the roots. Paths in it are read from its own folder. Anything else in it is a usage error,
// never dropped: a key misspelt would otherwise be a setting silently not set.
import { existsSync, readFileSync } from "node:fs"
import path from "node:path"

/** The name the command looks for in the current folder. */
export const CONFIG_FILE = "tsverify.config.json"

/** What a config file sets, its paths absolute. */
export interface Config {
  /** The folders and files verified when the command names none. */
  readonly roots?: ReadonlyArray<string>
  readonly bound?: number
  readonly work?: number
  /** How many processes verify the files. */
  readonly workers?: number
  /** Whether verdicts are kept between runs, as `--cache`. */
  readonly cache?: boolean
  /** Where they are kept, as `--cache-location`. */
  readonly cacheLocation?: string
}

/** The config file in `dir`, if there is one. */
export const configIn = (dir: string): string | undefined => {
  const file = path.join(dir, CONFIG_FILE)
  return existsSync(file) ? file : undefined
}

const positive = (x: unknown): x is number => typeof x === "number" && Number.isInteger(x) && x > 0
const KEYS: Readonly<Record<keyof Config, { readonly is: (x: unknown) => boolean; readonly what: string }>> = {
  roots: {
    is: (x) => Array.isArray(x) && x.length > 0 && x.every((r) => typeof r === "string" && r !== ""),
    what: "a list of one or more folders or files",
  },
  bound: { is: positive, what: "a positive whole number" },
  work: { is: positive, what: "a positive whole number" },
  workers: { is: positive, what: "a positive whole number" },
  cache: { is: (x) => typeof x === "boolean", what: "true or false" },
  cacheLocation: { is: (x) => typeof x === "string" && x !== "", what: "a folder" },
}

/** The config `file` sets, or what is wrong with it: never a setting dropped. */
export const readConfig = (file: string): { readonly config: Config } | { readonly error: string } => {
  let text: string
  try {
    text = readFileSync(file, "utf8")
  } catch {
    return { error: "no such file" }
  }
  let parsed: unknown
  try {
    parsed = JSON.parse(text)
  } catch (e) {
    return { error: `not JSON: ${e instanceof Error ? e.message : String(e)}` }
  }
  if (parsed === null || typeof parsed !== "object" || Array.isArray(parsed)) return { error: "not a JSON object" }
  const entries = Object.entries(parsed)
  for (const [key, value] of entries) {
    if (!Object.hasOwn(KEYS, key)) return { error: `no such key "${key}"; it takes ${Object.keys(KEYS).join(", ")}` }
    const rule = KEYS[key as keyof Config]
    if (!rule.is(value)) return { error: `"${key}" is ${rule.what}, not ${JSON.stringify(value)}` }
  }
  const given = parsed as {
    roots?: Array<string>
    bound?: number
    work?: number
    workers?: number
    cache?: boolean
    cacheLocation?: string
  }
  const from = path.dirname(path.resolve(file))
  return {
    config: {
      ...given,
      ...(given.roots === undefined ? {} : { roots: given.roots.map((r) => path.resolve(from, r)) }),
      ...(given.cacheLocation === undefined ? {} : { cacheLocation: path.resolve(from, given.cacheLocation) }),
    },
  }
}

// A spec's module imports nothing from the code that implements it: a spec is written, and type-checks, before the code
// exists. Held on what this package shows a reader: every `*.contract.ts` under `examples/`, and every spec a page of the
// documentation gives as a file. A module implements a spec when it imports from the spec's module; a spec that imports
// from such a module is refused, naming both. The types a spec's signature needs are declared in it, and a value both
// need lives in a module of its own (`examples/account/ledger.ts`).
import assert from "node:assert/strict"
import { readdirSync, readFileSync } from "node:fs"
import path from "node:path"
import { describe, it } from "node:test"

const root = path.resolve(import.meta.dirname, "..")

/** The modules `text` imports by a relative path, as written. */
const importsOf = (text: string): Array<string> => [...text.matchAll(/from "(\.{1,2}\/[^"]+)"/g)].map((m) => m[1] ?? "")

/** Each spec among `files` (a path and its text) that imports a module importing it back: a line each, naming both. */
const readsItsCode = (files: ReadonlyMap<string, string>): Array<string> =>
  [...files]
    .filter(([file]) => file.endsWith(".contract.ts"))
    .flatMap(([spec, text]) =>
      importsOf(text)
        .map((to) => path.posix.join(path.posix.dirname(spec), to))
        .filter((code) => importsOf(files.get(code) ?? "").some((back) => path.posix.join(path.posix.dirname(code), back) === spec))
        .map((code) => `${spec} imports ${code}, which implements it`),
    )

/** Every TypeScript file under `dir`, by its path from the package's root, with its text. */
const under = (dir: string): Map<string, string> =>
  new Map(
    readdirSync(path.join(root, dir), { recursive: true, encoding: "utf8" })
      .filter((f) => f.endsWith(".ts"))
      .map((f) => [path.posix.join(dir, f.split(path.sep).join("/")), readFileSync(path.join(root, dir, f), "utf8")] as const),
  )

/** The files a page gives, by the path each is marked with, a later block of one path replacing the earlier. */
const pageFiles = (page: string): Map<string, string> =>
  new Map(
    [...readFileSync(path.join(root, page), "utf8").matchAll(/<!-- file: (\S+) -->\n```[^\n]*\n([\s\S]*?)\n```/g)].map(
      (m) => [m[1] ?? "", m[2] ?? ""] as const,
    ),
  )

const PAGES = [
  "README.md",
  ...readdirSync(path.join(root, "docs"))
    .filter((f) => f.endsWith(".md"))
    .map((f) => `docs/${f}`),
]

describe("a spec's module imports nothing from the code that implements it", () => {
  it("no spec of the examples does", () => {
    assert.deepEqual(readsItsCode(under("examples")), [])
  })

  it("no spec a page of the documentation gives does", () => {
    assert.deepEqual(
      PAGES.flatMap((page) => readsItsCode(pageFiles(page)).map((line) => `${page}: ${line}`)),
      [],
    )
  })

  it("REFUSED: a spec that takes its types from the file typed by it", () => {
    const planted = new Map([
      ["src/parcel.contract.ts", 'import type { Parcel } from "./parcel.ts"\nexport type StatusOf = (p: Parcel) => string\n'],
      ["src/parcel.ts", 'import type { StatusOf } from "./parcel.contract.ts"\nexport interface Parcel {}\n'],
      ["src/users.ts", "export interface Users {}\n"],
    ])
    assert.deepEqual(readsItsCode(planted), ["src/parcel.contract.ts imports src/parcel.ts, which implements it"])
  })
})

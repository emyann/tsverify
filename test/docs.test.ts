// Every example of the documentation, run. Each page's files are written, in
// the order the page gives them, into a project of the page's own; each command
// the page shows is run there at that point, and what it prints and its exit
// code are compared with the page's. A page marks its blocks with comments the
// reader does not see:
//   <!-- file: src/charge.ts -->    the next block is that file's whole text (a later one replaces it)
//   <!-- run -->                    the next block is `$ npx tsverify ...` and what it prints, exit 0
//   <!-- run, exits 1 -->           the same, exit 1
// Timings are not compared. Once every block is applied, the project must
// type-check. The project sits under `.docs/` in this package (a dot folder no
// command scans) and holds no package.json, so it imports `tsverify` through
// this package's own condition, and `effect` and `lodash-es` from its
// node_modules, as an installed project would.
import assert from "node:assert/strict"
import { spawn } from "node:child_process"
import { mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import path from "node:path"
import { describe, it } from "node:test"

const root = path.resolve(import.meta.dirname, "..")
const PAGES = ["README.md", ...readdirSync(path.join(root, "docs")).filter((f) => f.endsWith(".md")).map((f) => `docs/${f}`)]

/** A page's tsconfig, when it gives none: the one the README tells a project to have. */
const TSCONFIG = {
  compilerOptions: { target: "es2023", module: "nodenext", moduleResolution: "nodenext", strict: true, noEmit: true, allowImportingTsExtensions: true, skipLibCheck: true, types: [] },
}

type Step = { readonly kind: "file"; readonly path: string; readonly text: string } | { readonly kind: "run"; readonly args: ReadonlyArray<string>; readonly out: string; readonly exits: number; readonly line: number }

const MARKED = /<!-- (?:file: (\S+)|run(?:, exits (\d))?) -->\n```[^\n]*\n([\s\S]*?)\n```/g
const stepsOf = (page: string): Array<Step> =>
  [...readFileSync(path.join(root, page), "utf8").matchAll(MARKED)].map((m) => {
    const [, file, exits, body] = m as unknown as [string, string | undefined, string | undefined, string]
    if (file !== undefined) return { kind: "file", path: file, text: `${body}\n` }
    const line = readFileSync(path.join(root, page), "utf8").slice(0, m.index).split("\n").length + 1
    const [command, ...out] = body.split("\n")
    const args = /^\$ npx tsverify(?: (.*))?$/.exec(command ?? "")
    assert.ok(args !== null, `${page}:${line}: a run block starts with \`$ npx tsverify ...\`, not ${JSON.stringify(command)}`)
    return { kind: "run", args: args[1]?.split(" ") ?? [], out: out.join("\n"), exits: Number(exits ?? 0), line }
  })

/** What a run prints, its timings and the spaces ending a line set aside. */
const normal = (s: string) =>
  s
    .replace(/\(\d+ ms\)/g, "(N ms)")
    .split("\n")
    .map((l) => l.trimEnd())
    .join("\n")
    .trim()

const { NODE_OPTIONS: _, ...env } = process.env
const ran = (args: ReadonlyArray<string>, cwd: string): Promise<{ code: number | null; out: string; err: string }> =>
  new Promise((resolve, reject) => {
    const child = spawn(process.execPath, args, { cwd, env })
    let out = ""
    let err = ""
    child.stdout.on("data", (d) => (out += d))
    child.stderr.on("data", (d) => (err += d))
    child.on("error", reject)
    child.on("close", (code) => resolve({ code, out, err }))
  })

const write = (dir: string, file: string, text: string) => {
  mkdirSync(path.dirname(path.join(dir, file)), { recursive: true })
  // The page's own tsconfig, with this package's condition: the stand-in for having installed it.
  const body = file === "tsconfig.json" ? JSON.stringify(withCondition(JSON.parse(text) as typeof TSCONFIG), null, 2) : text
  writeFileSync(path.join(dir, file), body)
}
const withCondition = (c: typeof TSCONFIG) => ({ ...c, compilerOptions: { ...c.compilerOptions, customConditions: ["tsverify-source"] } })

describe("the documentation's examples", { concurrency: true }, () => {
  for (const page of PAGES) {
    const steps = stepsOf(page)
    if (steps.length === 0) continue
    it(`${page}: ${steps.filter((s) => s.kind === "run").length} runs over ${new Set(steps.flatMap((s) => (s.kind === "file" ? [s.path] : []))).size} files`, async () => {
      mkdirSync(path.join(root, ".docs"), { recursive: true })
      const dir = mkdtempSync(path.join(root, ".docs", `${path.basename(page, ".md")}-`))
      try {
        write(dir, "tsconfig.json", JSON.stringify(TSCONFIG))
        for (const step of steps) {
          if (step.kind === "file") {
            write(dir, step.path, step.text)
            continue
          }
          const r = await ran(["--conditions=tsverify-source", path.join(root, "src/cli.ts"), ...step.args], dir)
          const command = ["npx tsverify", ...step.args].join(" ")
          assert.equal(normal(r.out), normal(step.out), `${page}:${step.line}: \`${command}\` printed otherwise\n${r.err}`)
          assert.equal(r.code, step.exits, `${page}:${step.line}: \`${command}\` exited ${r.code}\n${r.err}`)
        }
        const tsc = await ran([path.join(root, "node_modules/typescript/bin/tsc"), "-p", "."], dir)
        assert.equal(tsc.code, 0, `${page}: its files do not type-check\n${tsc.out}${tsc.err}`)
      } finally {
        rmSync(dir, { recursive: true, force: true })
      }
    })
  }
})

// The skill for coding agents (skills/tsverify/SKILL.md) stays true to the
// package: it is named as its folder is, says when to load it, and every page
// and every option of the command it names is one the package has.
import assert from "node:assert/strict"
import { readdirSync, readFileSync } from "node:fs"
import path from "node:path"
import { it } from "node:test"

const root = path.resolve(import.meta.dirname, "..")
const text = readFileSync(path.join(root, "skills/tsverify/SKILL.md"), "utf8")
const cli = readFileSync(path.join(root, "src/cli.ts"), "utf8")

it("is named as its folder, and says when to load it", () => {
  const front = /^---\nname: (\S+)\ndescription: "([^"]+)"\n---\n/.exec(text)
  assert.ok(front !== null, "a frontmatter block of name and description, first")
  assert.equal(front[1], "tsverify")
  assert.match(front[2]!, /Load it before/)
})

it("names only pages the package ships", () => {
  const pages = new Set(readdirSync(path.join(root, "docs")))
  const named = [...text.matchAll(/(?:docs\/)?\b([a-z-]+\.md)\b/g)].map((m) => m[1]!).filter((p) => p !== "SKILL.md")
  assert.ok(named.length > 0)
  for (const p of named) assert.ok(pages.has(p), `${p} is no page of docs/`)
})

it("names only options the command takes", () => {
  const named = [...new Set([...text.matchAll(/`[^`\n]*?(--[a-z][a-z-]*)/g)].map((m) => m[1]!))]
  assert.ok(named.includes("--watch") && named.includes("--cache"))
  for (const o of named) assert.ok(cli.includes(`"${o}"`), `${o} is no option of the command`)
})

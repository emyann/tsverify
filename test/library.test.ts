// What the lowering reads of JavaScript's library, held to the purity check and to the docs: every method and function
// it reads is one the purity check knows changes nothing (an array's `reverse`, which changes its array, being read as
// the statements read a change), and `docs/reads.md` names each.
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import path from "node:path"
import { describe, it } from "node:test"
import ts from "typescript"
import { methodCall } from "../src/effects.ts"
import { ARRAY_METHODS } from "../src/lower/arrays.ts"
import { LIBRARY_FUNCTIONS } from "../src/lower/library.ts"
import { STRING_METHODS } from "../src/lower/strings.ts"
import { loadProject } from "../src/project.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "test/.library-calls.ts")
const text = [
  "declare const xs: Array<number>",
  "declare const s: string",
  ...ARRAY_METHODS.map((m) => `xs.${m}()`),
  ...STRING_METHODS.map((m) => `s.${m}()`),
  ...LIBRARY_FUNCTIONS.map((f) => `${f}()`),
  "export {}",
].join("\n")
const project = loadProject([file], path.join(root, "tsconfig.json"), new Map([[file, text]]))
const calls = project.program
  .getSourceFile(file)!
  .statements.flatMap((st) =>
    ts.isExpressionStatement(st) && ts.isCallExpression(st.expression) && ts.isPropertyAccessExpression(st.expression.expression)
      ? [{ call: st.expression, callee: st.expression.expression }]
      : [],
  )

describe("what the lowering reads of the library", () => {
  it("is every name of its lists, each a call", () => {
    assert.equal(calls.length, ARRAY_METHODS.length + STRING_METHODS.length + LIBRARY_FUNCTIONS.length)
  })
  it("changes nothing, by the purity check: an array's `reverse` alone changes its array", () => {
    const said = calls.map(({ call, callee }) => [callee.getText(), methodCall(project.checker, callee, call.arguments).does])
    const changes = said.filter(([, does]) => does !== "nothing" && does !== "call")
    assert.deepEqual(changes, [["xs.reverse", "change"]])
  })
  it("is named in docs/reads.md", () => {
    const docs = readFileSync(path.join(root, "docs/reads.md"), "utf8")
    const unnamed = [...ARRAY_METHODS, ...STRING_METHODS, ...LIBRARY_FUNCTIONS].filter(
      (n) => ![`\`${n}\``, `\`.${n}\``, `\`${n}(`, `\`.${n}(`].some((spelt) => docs.includes(spelt)),
    )
    assert.deepEqual(unnamed, [])
  })
})

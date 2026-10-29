// The purity check: each impure fixture refused for its reason, and each pure
// one accepted. A fold that builds its state by changing it is accepted in
// test/account.test.ts.
import assert from "node:assert/strict"
import path from "node:path"
import { describe, it } from "node:test"
import ts from "typescript"
import { diagnostics, loadProject, sourceFile } from "../src/project.ts"
import { purityOf } from "../src/purity.ts"
import type { FunctionNode } from "../src/value.ts"

const root = path.resolve(import.meta.dirname, "..")
const file = path.join(root, "fixtures/purity.ts")
const project = loadProject([file], path.join(root, "tsconfig.json"))

/** The exported function `name` of `f`. */
const fnOf = (f: string, name: string): FunctionNode => {
  for (const s of sourceFile(project, f).statements) {
    if (ts.isFunctionDeclaration(s) && s.name?.text === name) return s
    if (ts.isVariableStatement(s))
      for (const d of s.declarationList.declarations)
        if (
          ts.isIdentifier(d.name) &&
          d.name.text === name &&
          d.initializer !== undefined &&
          (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer))
        )
          return d.initializer
  }
  throw new Error(`no function ${name} in ${f}`)
}
const purity = (f: string, name: string) => purityOf(project.checker, fnOf(f, name), () => undefined)

it("the fixtures type-check", () => {
  assert.deepEqual(diagnostics(project, file), [])
})

describe("impure, each for its reason", () => {
  const cases: ReadonlyArray<readonly [string, RegExp]> = [
    ["changesArgument", /changes its argument `xs`/],
    ["readsClock", /calls `Date\.now`/],
    ["rolls", /calls `Math\.random`/],
    ["counts", /changes `calls`, which is not its own/],
    ["logs", /calls `console\.log`/],
    ["changesThroughABox", /changes an object of type `string\[\]`, which may be a value of the caller's/],
    ["changesThroughHelpers", /changes an object of type `string\[\]`, which may be a value of the caller's/],
    ["changesANarrowedUnknown", /changes an object of type `object & Record<"k", unknown>`, which may be a value of the caller's/],
    ["passesItsArgumentOn", /changes its argument `xs`/],
    ["callsTheClockThroughAHelper", /calls `readsClock`, which is not pure: .*calls `Date\.now`/],
    ["appliesWhatItIsGiven", /calls `f`, a function it was given/],
    ["casts", /casts \(`as`\)/],
  ]
  for (const [name, why] of cases)
    it(name, () => {
      const p = purity(file, name)
      assert.equal(p.pure, false, `${name} was accepted`)
      if (!p.pure) assert.match(p.why, why)
    })
})

describe("pure", () => {
  for (const name of ["copies", "folds", "asks", "reduces", "recurses"])
    it(name, () => {
      const p = purity(file, name)
      assert.deepEqual(p.pure ? "pure" : p.why, "pure")
    })
})

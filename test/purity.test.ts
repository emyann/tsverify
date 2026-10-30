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
    ["casts", /casts \(`as`\)/],
    ["passesTheClock", /passes `stampOf`, which is not pure: .*calls `Date\.now`/],
    ["logsEach", /passes `console\.log`, a function it cannot read/],
    ["passesWhatChangesIt", /passes `changesArgument`, which changes or calls what it is given/],
  ]
  for (const [name, why] of cases)
    it(name, () => {
      const p = purity(file, name)
      assert.equal(p.pure, false, `${name} was accepted`)
      if (!p.pure) assert.match(p.why, why)
    })
})

describe("pure where what it is given is, naming the arguments it calls", () => {
  for (const [name, calls] of [
    ["appliesWhatItIsGiven", [0]],
    ["mapsWithWhatItIsGiven", [1]],
    ["passesItOn", [0]],
    ["defaultsIt", [1]],
  ] as const)
    it(name, () => {
      const p = purity(file, name)
      assert.deepEqual(p.pure ? p.calls : p.why, calls)
    })
})

describe("pure", () => {
  for (const name of ["copies", "folds", "asks", "reduces", "recurses", "sortsUnknowns"])
    it(name, () => {
      const p = purity(file, name)
      assert.deepEqual(p.pure ? (p.calls.length === 0 ? "pure" : p.calls) : p.why, "pure")
    })
})

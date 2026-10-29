// How much of a code base the verifier can read: every exported function of a
// TypeScript project, lowered with symbolic arguments (no solving), counted as
// read or refused, and the refusals grouped by reason.
//
//   node bench/coverage.ts <tsconfig.json> [--json out.json]
import path from "node:path"
import { writeFileSync } from "node:fs"
import ts from "typescript"
import { emptyEnv, type Lowering, lowerCall } from "../src/lower.ts"
import { loadProject } from "../src/project.ts"
import { symbolicOf } from "../src/symbolic.ts"
import { Universe } from "../src/universe.ts"
import { type FunctionNode, Unsupported } from "../src/value.ts"
import { withZ3 } from "../src/verify.ts"

const tsconfig = path.resolve(process.argv[2] ?? "tsconfig.json")
const jsonOut = process.argv.includes("--json") ? process.argv[process.argv.indexOf("--json") + 1] : undefined
const parsed = ts.parseJsonConfigFileContent(ts.readConfigFile(tsconfig, ts.sys.readFile).config, ts.sys, path.dirname(tsconfig))
const files = parsed.fileNames.filter((f) => !/\.test\.tsx?$|\/test\//.test(f) && !f.endsWith(".d.ts"))
const project = loadProject(files, tsconfig)

interface Fn {
  readonly name: string
  readonly node: FunctionNode
  readonly file: string
}

const exported = (sf: ts.SourceFile): Array<Fn> => {
  const out: Array<Fn> = []
  const isExported = (s: ts.Statement) => ts.getCombinedModifierFlags(s as unknown as ts.Declaration) & ts.ModifierFlags.Export
  for (const s of sf.statements) {
    if (ts.isFunctionDeclaration(s) && s.body !== undefined && s.name !== undefined && isExported(s))
      out.push({ name: s.name.text, node: s, file: sf.fileName })
    if (ts.isVariableStatement(s) && isExported(s))
      for (const d of s.declarationList.declarations)
        if (ts.isIdentifier(d.name) && d.initializer !== undefined && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer)))
          out.push({ name: d.name.text, node: d.initializer, file: sf.fileName })
  }
  return out
}

/** A refusal's reason with its location and names taken out, so like reasons group. */
const reasonOf = (e: Unsupported): string =>
  e.message
    .replace(/^.*?:\d+:\d+: /, "")
    .replace(/`[^`]*`/g, "`X`")
    .replace(/^[\w.[\]!?$#~-]+: /, "")
    .replace(/type .* is not modeled/, "type T is not modeled")
    .replace(/a union of .* is not modeled/, "a union of object types (or mixed kinds) is not modeled")
    .replace(/the intersection .* is not modeled/, "an intersection is not modeled")
    .replace(/\d+/g, "N")

const returnsEffect = (fn: FunctionNode): boolean => {
  const sig = project.checker.getSignatureFromDeclaration(fn)
  if (sig === undefined) return false
  const name = project.checker.typeToString(project.checker.getReturnTypeOfSignature(sig))
  return /^(Effect|Stream|Layer)\b|Effect\.Effect</.test(name)
}

await withZ3(async (z3) => {
  const fns = project.program.getSourceFiles().filter((sf) => files.includes(sf.fileName)).flatMap(exported)
  const reasons = new Map<string, { count: number; effect: number; example: string }>()
  let read = 0
  let readEffect = 0
  let effects = 0
  const crashes: Array<string> = []
  for (const f of fns) {
    const effect = returnsEffect(f.node)
    if (effect) effects++
    const u = new Universe(z3)
    const L: Lowering = { u, checker: project.checker, stack: [], constants: new Map() }
    try {
      const args = f.node.parameters.map((p, i) =>
        symbolicOf(L, project.checker.getTypeAtLocation(p), [ts.isIdentifier(p.name) ? p.name.text : `arg${i}`], [], p),
      )
      lowerCall(L, f.node, emptyEnv, args, f.node)
      read++
      if (effect) readEffect++
    } catch (e) {
      if (!(e instanceof Unsupported)) {
        crashes.push(`${path.relative(path.dirname(tsconfig), f.file)} ${f.name}: ${(e as Error).message.slice(0, 120)}`)
        continue
      }
      const r = reasonOf(e)
      const entry = reasons.get(r) ?? { count: 0, effect: 0, example: `${path.relative(path.dirname(tsconfig), f.file)} ${f.name}` }
      entry.count++
      if (effect) entry.effect++
      reasons.set(r, entry)
    }
  }
  const pct = (a: number, b: number) => `${b === 0 ? 0 : Math.round((100 * a) / b)}%`
  console.log(`${path.relative(process.cwd(), tsconfig)}: ${fns.length} exported functions in ${files.length} files`)
  console.log(`  read: ${read} (${pct(read, fns.length)})`)
  console.log(`  returning an Effect, Stream or Layer: ${effects}, of which read: ${readEffect}`)
  console.log(`  not returning one: ${fns.length - effects}, of which read: ${read - readEffect} (${pct(read - readEffect, fns.length - effects)})`)
  if (crashes.length > 0) console.log(`  verifier crashes: ${crashes.length}\n${crashes.slice(0, 5).map((c) => `    ${c}`).join("\n")}`)
  console.log("  first refusal, by reason (count, of which Effect-returning, an example):")
  for (const [r, e] of [...reasons].sort((a, b) => b[1].count - a[1].count).slice(0, 18))
    console.log(`    ${String(e.count).padStart(4)} ${String(e.effect).padStart(4)}  ${r}  — ${e.example}`)
  if (jsonOut !== undefined)
    writeFileSync(jsonOut, `${JSON.stringify({ tsconfig, functions: fns.length, read, effects, readEffect, crashes, reasons: Object.fromEntries(reasons) }, null, 2)}\n`)
})

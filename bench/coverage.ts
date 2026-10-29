// How much of a code base the verifier can read: every exported function of a
// TypeScript project, and every exported computation an adapter defines
// (`Effect.fn(...)(function* ...)`), lowered with symbolic arguments (no
// solving), counted as read or refused, and the refusals grouped by reason. A
// function that returns a computation is read only when that computation, run,
// is: its body is where the work is.
//
//   node bench/coverage.ts <tsconfig.json> [--modular] [--effect] [--names] [--json out.json]
//
// `--effect` counts the Effect computations alone; `--names` keeps the names in the reasons, so a reason that names a
// library function groups by that function.
//
// By default a function is read with every function it calls inlined, and a
// callee the verifier cannot read refuses it. With `--modular`, each function is
// read on its own: a callee of the program that the purity check finds pure is
// taken as declared `assume(callee, { pure: true })`, which is what a spec would
// write to read the caller without reading the callee.
import path from "node:path"
import { writeFileSync } from "node:fs"
import ts from "typescript"
import { emptyTrace, runBody } from "../src/computation.ts"
import { emptyEnv, type Lowering, lowerCall, lowering, trustOf } from "../src/lower.ts"
import { loadProject, unwrap } from "../src/project.ts"
import { purityOf } from "../src/purity.ts"
import type { AssumedFn, Assumptions } from "../src/trust.ts"
import { symbolicOf } from "../src/symbolic.ts"
import { Universe } from "../src/universe.ts"
import { type FunctionNode, Unsupported, type Val } from "../src/value.ts"
import { ADAPTERS, withZ3 } from "../src/verify.ts"

const tsconfig = path.resolve(process.argv[2] ?? "tsconfig.json")
const jsonOut = process.argv.includes("--json") ? process.argv[process.argv.indexOf("--json") + 1] : undefined
const modular = process.argv.includes("--modular")
const effectOnly = process.argv.includes("--effect")
const keepNames = process.argv.includes("--names")
const parsed = ts.parseJsonConfigFileContent(ts.readConfigFile(tsconfig, (f) => ts.sys.readFile(f)).config, ts.sys, path.dirname(tsconfig))
const files = parsed.fileNames.filter((f) => !/\.test\.tsx?$|\/test\//.test(f) && !f.endsWith(".d.ts"))
const project = loadProject(files, tsconfig)

interface Fn {
  readonly name: string
  /** A function, or the expression an adapter reads as a computation. */
  readonly node: FunctionNode | ts.Expression
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
        if (
          ts.isIdentifier(d.name) &&
          d.initializer !== undefined &&
          (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer) || ts.isCallExpression(d.initializer))
        )
          out.push({ name: d.name.text, node: d.initializer, file: sf.fileName })
  }
  return out
}

/** A refusal's reason with its location and names taken out, so like reasons group. */
const reasonOf = (e: Unsupported): string =>
  keepNames
    ? e.message
        .replace(/^.*?:\d+:\d+: /, "")
        .replace(/ \(.*$/, "")
        .slice(0, 140)
    : e.message
        .replace(/^.*?:\d+:\d+: /, "")
        .replace(/`[^`]*`/g, "`X`")
        .replace(/^[\w.[\]!?$#~-]+: /, "")
        .replace(/type .* is not modeled/, "type T is not modeled")
        .replace(/a union of .* is not modeled/, "a union of object types (or mixed kinds) is not modeled")
        .replace(/the intersection .* is not modeled/, "an intersection is not modeled")
        .replace(/\d+/g, "N")

const returnsEffect = (fn: FunctionNode | ts.Expression): boolean => {
  if (!ts.isFunctionLike(fn)) return true
  const sig = project.checker.getSignatureFromDeclaration(fn)
  if (sig === undefined) return false
  const name = project.checker.typeToString(project.checker.getReturnTypeOfSignature(sig))
  return /^(Effect|Stream|Layer)\b|Effect\.Effect</.test(name)
}

/** Every function of the program the purity check finds pure, declared `pure: true` with no law, as a spec would. */
const declaredPure = (): Assumptions => {
  const { checker } = project
  const memo = new Map<ts.Symbol, AssumedFn | undefined>()
  const bodyOf = (sym: ts.Symbol): FunctionNode | undefined => {
    const d = sym.valueDeclaration
    if (d === undefined || d.getSourceFile().isDeclarationFile || d.getSourceFile().fileName.includes("/node_modules/")) return undefined
    if (ts.isFunctionDeclaration(d) && d.body !== undefined) return d
    if (ts.isVariableDeclaration(d) && d.initializer !== undefined && (d.parent.flags & ts.NodeFlags.Const) !== 0) {
      const init = unwrap(d.initializer)
      if (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) return init
    }
    return undefined
  }
  const of = (callee: ts.Expression): AssumedFn | undefined => {
    let sym = checker.getSymbolAtLocation(ts.isPropertyAccessExpression(callee) ? callee.name : callee)
    if (sym !== undefined && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
    if (sym === undefined) return undefined
    if (memo.has(sym)) return memo.get(sym)
    memo.set(sym, undefined)
    const body = bodyOf(sym)
    const sig = body === undefined ? undefined : checker.getSignatureFromDeclaration(body)
    let a: AssumedFn | undefined
    if (body !== undefined && sig !== undefined && sig.typeParameters === undefined && purityOf(checker, body, of).pure)
      a = {
        symbol: sym,
        name: sym.name,
        body,
        pure: true,
        views: [{ where: "(probe)", params: sig.getParameters().map((p) => checker.getTypeOfSymbol(p)), ensures: [] }],
      }
    memo.set(sym, a)
    return a
  }
  return { all: [], of }
}
const trust = modular ? trustOf(declaredPure()) : undefined

await withZ3(async (z3) => {
  const recogniser = lowering({ u: new Universe(z3), checker: project.checker }, ADAPTERS)
  const computationOf = (L: Lowering, e: ts.Node) => L.adapters.map((a) => a.computation?.(L, e)).find((c) => c !== undefined)
  // An exported call counts when an adapter reads it as a computation; other calls (a `Context.Service` class, a table) are no function.
  const fns = project.program
    .getSourceFiles()
    .filter((sf) => files.includes(sf.fileName))
    .flatMap(exported)
    .filter((f) => {
      if (!ts.isCallExpression(f.node)) return true
      try {
        return computationOf(recogniser, f.node) !== undefined
      } catch (e) {
        // A computation the adapter recognises and refuses (`Effect.fn` with a pipeline after its body) still counts.
        if (e instanceof Unsupported) return true
        throw e
      }
    })
  /** A computation is read when it runs: its outcome and its calls. */
  const run = (L: Lowering, v: Val): void => {
    if (v.kind === "comp") v.run(emptyTrace(L))
  }
  const reasons = new Map<string, { count: number; effect: number; example: string }>()
  let read = 0
  const readNames: Array<string> = []
  let readEffect = 0
  let effects = 0
  const crashes: Array<string> = []
  for (const f of fns) {
    const effect = returnsEffect(f.node)
    if (effectOnly && !effect) continue
    if (effect) effects++
    const u = new Universe(z3)
    const L = lowering({ u, checker: project.checker }, ADAPTERS, trust)
    try {
      const c = ts.isCallExpression(f.node) ? computationOf(L, f.node) : undefined
      const fn = c?.node ?? (f.node as FunctionNode)
      const args = fn.parameters.map((p, i) =>
        symbolicOf(L, project.checker.getTypeAtLocation(p), [ts.isIdentifier(p.name) ? p.name.text : `arg${i}`], [], p),
      )
      if (c !== undefined) runBody(L, c.node, c.style, emptyEnv, args, emptyTrace(L), c.node)
      else run(L, lowerCall(L, fn, emptyEnv, args, fn))
      read++
      readNames.push(`${path.relative(path.dirname(tsconfig), f.file)} ${f.name}`)
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
  console.log(
    `${path.relative(process.cwd(), tsconfig)}: ${fns.length} exported functions and computations in ${files.length} files${modular ? ", each read on its own (--modular)" : ""}`,
  )
  console.log(`  read: ${read} (${pct(read, fns.length)})`)
  console.log(`  Effect computations (\`Effect.fn\`, or returning an Effect, Stream or Layer): ${effects}, of which read: ${readEffect}`)
  console.log(
    `  not returning one: ${fns.length - effects}, of which read: ${read - readEffect} (${pct(read - readEffect, fns.length - effects)})`,
  )
  if (crashes.length > 0)
    console.log(
      `  verifier crashes: ${crashes.length}\n${crashes
        .slice(0, 5)
        .map((c) => `    ${c}`)
        .join("\n")}`,
    )
  console.log("  first refusal, by reason (count, of which Effect-returning, an example):")
  for (const [r, e] of [...reasons].sort((a, b) => b[1].count - a[1].count).slice(0, 18))
    console.log(`    ${String(e.count).padStart(4)} ${String(e.effect).padStart(4)}  ${r}  — ${e.example}`)
  if (jsonOut !== undefined)
    writeFileSync(
      jsonOut,
      `${JSON.stringify({ tsconfig, functions: fns.length, read, readNames, effects, readEffect, crashes, reasons: Object.fromEntries(reasons) }, null, 2)}\n`,
    )
})

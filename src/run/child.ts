// The child of a run (`./runs.ts`): handed one plan, it loads the contract's module, with a hook that records every
// module loaded and lets a spec no module exports be read, and runs the laws on seeded inputs. Each law broken comes
// back with the first input that broke it, shrunk: the real function on it, the real law on its result. A generated
// function in it is shown by the calls it answered. Nothing here reads a clock: the same plan answers the same.
import module from "node:module"
import { realpathSync } from "node:fs"
import path from "node:path"
import { fileURLToPath, pathToFileURL } from "node:url"
import * as fc from "fast-check"
import { CALLS, type Drawn, drawsOf, isRecorded } from "./arbitrary.ts"
import type { RunPlan, RunResult } from "./runs.ts"

/** What the child answers: a run's result, but for what the parent knows better (the environment it gave, the time). */
export type Answer =
  | {
      readonly broken: RunResult["broken"]
      readonly saysSomething: RunResult["saysSomething"]
      readonly ran: {
        readonly ran: true
        readonly inputs: number
        readonly discarded: number
        readonly threw: number
        readonly modules: ReadonlyArray<string>
      }
    }
  | { readonly ran: false; readonly why: string }

/** The name a spec's module exports its spec under, appended by the loader's hook. */
const SPEC_EXPORT = "__tsverifySpec"

/** The most draws a run makes for each input it runs: past that, `requires` refuses too much and the run stops. */
const DRAWS_PER_INPUT = 10

type Predicate = (run: unknown) => unknown
type Fn = (...args: Array<unknown>) => unknown

/** An error's first line, after its code where it has one (`ERR_UNSUPPORTED_TYPESCRIPT_SYNTAX`). */
const firstLine = (e: unknown): string => {
  const line = (e instanceof Error ? e.message : String(e)).split("\n")[0] ?? ""
  const code = e instanceof Error ? (e as { code?: unknown }).code : undefined
  return typeof code === "string" && !line.includes(code) ? `${code}: ${line}` : line
}

/** The package a bare specifier names: `effect` of `effect/Schema`, `@emyann/tsverify` of `@emyann/tsverify/effect`. */
const packageOf = (specifier: string): string => {
  const parts = specifier.split("/")
  return specifier.startsWith("@") ? parts.slice(0, 2).join("/") : parts[0]!
}

/** The condition under which tsverify resolves to its own source. */
const SOURCE = "tsverify-source"

const isBare = (specifier: string): boolean =>
  !specifier.startsWith(".") && !specifier.startsWith("/") && !specifier.startsWith("#") && !/^[a-zA-Z][a-zA-Z0-9+.-]*:/.test(specifier)

/** How a module loaded is named: a package by its name, a file of the program relative to the current folder. */
const nameOf = (url: string, packages: ReadonlyMap<string, string>): string | undefined => {
  const named = packages.get(url)
  if (named !== undefined) return named
  if (!url.startsWith("file:")) return undefined
  const file = fileURLToPath(url)
  const inPackage = /[\\/]node_modules[\\/]((?:@[^\\/]+[\\/])?[^\\/]+)/.exec(file)
  if (inPackage !== null) return inPackage[1]!.replaceAll("\\", "/")
  return path.relative(process.cwd(), file).replaceAll("\\", "/")
}

/** A value as the parent is shown it: a generated function as the calls it answered, any other function as none. */
const shown = (v: unknown): unknown => {
  if (isRecorded(v)) return { "~calls": v[CALLS].map(([args, r]) => [args.map(shown), shown(r)]) }
  if (typeof v === "function") return "~function"
  if (Array.isArray(v)) return v.map(shown)
  if (v instanceof Map) return new Map([...v].map(([k, x]) => [shown(k), shown(x)]))
  if (v instanceof Set) return new Set([...v].map(shown))
  if (v !== null && typeof v === "object") return Object.fromEntries(Object.entries(v).map(([k, x]) => [k, shown(x)]))
  return v
}

/** Forgets the calls every generated function in `v` answered: before the run whose calls are shown. */
const forget = (v: unknown): void => {
  if (isRecorded(v)) v[CALLS].length = 0
  else if (Array.isArray(v)) v.forEach(forget)
  else if (v instanceof Map)
    for (const [k, x] of v) {
      forget(k)
      forget(x)
    }
  else if (v instanceof Set) v.forEach(forget)
  else if (v !== null && typeof v === "object") Object.values(v).forEach(forget)
}

/** A law as written: a predicate, or `{ description, condition }`. */
const predicateOf = (law: unknown): Predicate | undefined =>
  typeof law === "function"
    ? (law as Predicate)
    : law !== null && typeof law === "object" && typeof (law as { condition?: unknown }).condition === "function"
      ? (law as { condition: Predicate }).condition
      : undefined

/** Runs `plan`. Never throws: what cannot be loaded or read answers `ran: false`. */
export const runPlan = async (plan: RunPlan): Promise<Answer> => {
  const loaded: Array<string> = []
  const packages = new Map<string, string>()
  let failedAt: string | undefined
  const real = (file: string) => {
    try {
      return pathToFileURL(realpathSync(file)).href
    } catch {
      return pathToFileURL(file).href
    }
  }
  // The verifier may run from its source (a checkout, `--conditions=tsverify-source`) and the project import an installed
  // tsverify, which ships no source, or the other way round: a bare import not found under the conditions the child was
  // given is resolved once more with that condition turned the other way.
  const resolveEither: Parameters<typeof module.registerHooks>[0]["resolve"] & {} = (specifier, context, next) => {
    try {
      return next(specifier, context)
    } catch (e) {
      if (!isBare(specifier) || (e as { code?: unknown }).code !== "ERR_MODULE_NOT_FOUND") throw e
      const has = context.conditions.includes(SOURCE)
      return next(specifier, {
        ...context,
        conditions: has ? context.conditions.filter((c) => c !== SOURCE) : [...context.conditions, SOURCE],
      })
    }
  }
  const specUrl = plan.spec === undefined ? undefined : real(plan.spec.module)
  module.registerHooks({
    resolve(specifier, context, next) {
      const r = resolveEither(specifier, context, next)
      if (isBare(specifier) && !specifier.startsWith("node:")) packages.set(r.url, packageOf(specifier))
      return r
    },
    load(url, context, next) {
      let r: ReturnType<typeof next>
      try {
        r = next(url, context)
      } catch (e) {
        failedAt ??= url
        throw e
      }
      loaded.push(url)
      if (url === specUrl && r.source !== undefined && r.source !== null && plan.spec !== undefined)
        return {
          ...r,
          source: `${typeof r.source === "string" ? r.source : new TextDecoder().decode(r.source)}\nexport const ${SPEC_EXPORT} = ${plan.spec.name};\n`,
        }
      return r
    },
  })
  const modules = () => [...new Set(loaded.flatMap((u) => nameOf(u, packages) ?? []))].toSorted()
  const notRun = (why: string): Answer => ({ ran: false, why })

  const moduleUrl = real(plan.module)
  let mod: Record<string, unknown>
  let specMod: Record<string, unknown> | undefined
  try {
    mod = (await import(moduleUrl)) as Record<string, unknown>
    if (specUrl !== undefined) specMod = (await import(specUrl)) as Record<string, unknown>
  } catch (e) {
    // The module that failed: the one whose load threw, else the first module loaded that the error's stack names
    // (a module refused once loaded, by type stripping or its top level), else the contract's own.
    const stack = e instanceof Error ? (e.stack ?? "") : ""
    const named = loaded
      .flatMap((u) => {
        const at = Math.min(...[u, u.startsWith("file:") ? fileURLToPath(u) : u].map((s) => stack.indexOf(s)).filter((i) => i >= 0))
        return Number.isFinite(at) ? [{ u, at }] : []
      })
      .toSorted((a, b) => a.at - b.at)[0]?.u
    const failed = failedAt ?? named ?? moduleUrl
    const where = nameOf(failed, packages) ?? failed
    return notRun(`${where}: ${firstLine(e)}`)
  }

  // The function and its spec: a `contract(...)`'s, or an implementation's and the spec it is typed by.
  const exported = mod[plan.name]
  let fn: Fn
  let laws: { readonly requires?: unknown; readonly ensures?: unknown }
  if (typeof exported === "function") {
    const spec = specMod?.[SPEC_EXPORT]
    if (spec === null || typeof spec !== "object") return notRun(`no spec read for \`${plan.name}\``)
    fn = exported as Fn
    laws = spec
  } else if (exported !== null && typeof exported === "object" && typeof (exported as { fn?: unknown }).fn === "function") {
    fn = (exported as { fn: Fn }).fn
    laws = exported
  } else return notRun(`\`${plan.name}\` is neither a contract nor a function once loaded`)
  const requires = laws.requires === undefined ? undefined : predicateOf(laws.requires)
  if (laws.requires !== undefined && requires === undefined) return notRun("its `requires` is not a function once loaded")
  const ensures = (laws.ensures ?? {}) as Record<string, unknown>
  const preds: Array<Predicate> = []
  for (const l of plan.laws) {
    const p = predicateOf(ensures[l.name])
    if (p === undefined) return notRun(`its law \`${l.name}\` is not a function once loaded`)
    preds.push(p)
  }

  /** One input: refused by `requires`, thrown on, or the laws it breaks (by index) and the free results that break one. */
  const runOn = (
    d: Drawn,
  ):
    | "refused"
    | "threw"
    | { readonly threw: true; readonly says: ReadonlyArray<number> }
    | { readonly broken: ReadonlyArray<number>; readonly says: ReadonlyArray<number> } => {
    try {
      if (requires !== undefined && !requires({ input: d.args })) return "refused"
    } catch {
      return "threw"
    }
    // Whether a law says something is a question of the spec alone: asked before the code runs, so an input on which the
    // code throws still counts.
    const says: Array<number> = []
    preds.forEach((p, i) => {
      if (plan.laws[i]!.output === undefined) return
      try {
        if (!p({ input: d.args, output: d.free[i] })) says.push(i)
      } catch {
        // A law that throws on a free result says nothing there.
      }
    })
    const broken: Array<number> = []
    try {
      const output = fn(...d.args)
      preds.forEach((p, i) => {
        if (!p({ input: d.args, output })) broken.push(i)
      })
    } catch {
      return { threw: true, says }
    }
    return { broken, says }
  }

  const draws = drawsOf(
    plan.params,
    plan.laws.map((l) => l.output),
    plan.pool,
    plan.bound,
  )
  let inputs = 0
  let discarded = 0
  let threw = 0
  let drawn = 0
  const firstBroken = new Map<number, number>()
  const says = new Set<number>()
  // Draw after draw from the seed, until `runs` inputs met `requires` or ten times as many were drawn. A property that
  // answers false once the run is done ends the check there, unshrunk.
  try {
    fc.check(
      fc.property(draws, (d) => {
        if (inputs >= plan.runs) return false
        const at = drawn++
        const r = runOn(d)
        if (r === "refused") discarded++
        else if (r === "threw") threw++
        else if ("threw" in r) {
          threw++
          for (const i of r.says) says.add(i)
        } else {
          inputs++
          for (const i of r.broken) if (!firstBroken.has(i)) firstBroken.set(i, at)
          for (const i of r.says) says.add(i)
        }
        return true
      }),
      { seed: plan.seed, numRuns: plan.runs * DRAWS_PER_INPUT, endOnFailure: true },
    )
  } catch (e) {
    return notRun(`the run failed: ${firstLine(e)}`)
  }

  // Each law broken: its first counterexample shrunk, replayed from where it was drawn. Where `requires` refuses or
  // anything throws, the law is not broken: only a real counterexample is kept.
  const broken: Record<string, { readonly args: ReadonlyArray<unknown> }> = {}
  for (const [i, at] of [...firstBroken].toSorted((a, b) => a[0] - b[0])) {
    const p = preds[i]!
    const holds = (d: Drawn): boolean => {
      try {
        if (requires !== undefined && !requires({ input: d.args })) return true
        return Boolean(p({ input: d.args, output: fn(...d.args) }))
      } catch {
        return true
      }
    }
    const found = fc.check(fc.property(draws, holds), { seed: plan.seed, path: String(at), numRuns: plan.runs * DRAWS_PER_INPUT })
    const d = found.counterexample?.[0]
    if (d === undefined) continue
    // Once more on the input shrunk, for the calls each generated function answers there.
    forget(d.args)
    if (holds(d)) continue
    broken[plan.laws[i]!.name] = { args: shown(d.args) as ReadonlyArray<unknown> }
  }
  return {
    broken,
    saysSomething: plan.laws.flatMap((l, i) => (says.has(i) ? [l.name] : [])),
    ran: { ran: true, inputs, discarded, threw, modules: modules() },
  }
}

process.once("message", (plan: RunPlan) => {
  void runPlan(plan)
    .catch((e: unknown): Answer => ({ ran: false, why: `the run failed: ${firstLine(e)}` }))
    .then((answer) => {
      const send = (a: Answer) => process.send!(a, () => process.exit(0))
      try {
        send(answer)
      } catch (e) {
        send({ ran: false, why: `its answer could not be sent: ${firstLine(e)}` })
      }
    })
})

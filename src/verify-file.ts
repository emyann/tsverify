// One file of a run: its program read, its contracts listed and each verified, told as it goes. The command runs it in
// its own process, and each worker of `--workers` runs it in its own (`./worker.ts`): one loop, so a run says the same
// whichever process verified a file.
import path from "node:path"
import { contractsIn, loadProject, type Project } from "./project.ts"
import type { Ctx } from "./value.ts"
import { type Options, type Verification, verify } from "./verify.ts"

/** What a file's verification tells as it goes: the report's own calls (`Run` of `./view.ts`), but `reading` and `end`. */
export interface Tell {
  /** The file read, and the contracts it holds; not told of a file that holds none. */
  readonly file: (contracts: ReadonlyArray<string>) => void
  readonly verifying: (contract: string) => void
  readonly progress: (line: string) => void
  readonly verified: (v: Verification, ms: number) => void
}

/** The same verdict, each place it names relative to the current folder, as the files it reports are. */
const here = (s: string) => s.replaceAll(`${process.cwd()}${path.sep}`, "")
export const relative = (v: Verification): Verification => ({
  ...v,
  ...(v.unsupported !== undefined ? { unsupported: here(v.unsupported) } : {}),
  notes: v.notes.map(here),
  laws: v.laws.map((l) => (l.reason === undefined ? l : { ...l, reason: here(l.reason) })),
  obligations: v.obligations.map((o) => ({ ...o, at: here(o.at), ...(o.reason !== undefined ? { reason: here(o.reason) } : {}) })),
  trusted: v.trusted.map((t) => ({ ...t, declared: t.declared.map(here) })),
})

/** Verifies one contract of a program read, telling it as it goes, with how long it took. */
export const verifyContract = async (
  z3: Ctx,
  project: Project,
  file: string,
  name: string,
  opts: Options,
  tell: Tell,
): Promise<Verification> => {
  tell.verifying(name)
  const started = performance.now()
  const v = relative(await verify(z3, project, file, name, { ...opts, progress: tell.progress }))
  tell.verified(v, performance.now() - started)
  return v
}

/**
 * Every contract of `file`, read through `tsconfig`, verified in order. Each file is its own program, read once for all
 * its contracts: the declarations it imports (an implementation, through its spec) are in force for it alone.
 */
export const verifyFile = async (z3: Ctx, file: string, tsconfig: string, opts: Options, tell: Tell): Promise<Array<Verification>> => {
  const project = loadProject([file], tsconfig)
  const names = contractsIn(project, file)
  if (names.length === 0) return []
  tell.file(names)
  const out: Array<Verification> = []
  for (const name of names) out.push(await verifyContract(z3, project, file, name, opts, tell))
  return out
}

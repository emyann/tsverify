// `--workers N`: the files of a run verified in N processes of their own (`./worker.ts`), each handed the next file as
// it is free. What they tell is replayed into the report in the order of the files, a file's steps once every file
// before it is done, so the report, the verdicts and their order are the ones one process gives. A worker that fails
// fails the run when the report reaches its file, as one process would have there.
import { type ChildProcess, fork } from "node:child_process"
import path from "node:path"
import { fileURLToPath } from "node:url"
import { decodeVerdict } from "./cache.ts"
import type { Verification } from "./verify.ts"
import type { Run } from "./view.ts"

/** A file handed to a worker, with the settings it is verified under. */
export interface Job {
  readonly file: string
  readonly tsconfig: string
  readonly bound?: number
  readonly work?: number
  readonly cover: boolean
  /** Whether a pure function's laws are run first (`Options.run`). */
  readonly run: boolean
  readonly cacheDir?: string
}

/** What a worker tells of the file it was handed, in order, ending with `done` or `failed`. */
export type Said =
  | { readonly kind: "file"; readonly names: ReadonlyArray<string> }
  | { readonly kind: "verifying"; readonly name: string }
  | { readonly kind: "progress"; readonly line: string }
  | { readonly kind: "verified"; readonly v: unknown; readonly ms: number }
  | { readonly kind: "done" }
  | { readonly kind: "failed"; readonly error: string }

/** The worker's module beside this one: `.ts` in a checkout, `.js` in the package built. */
const WORKER = fileURLToPath(new URL(`./worker${path.extname(fileURLToPath(import.meta.url))}`, import.meta.url))

/** The failure of a worker, with the stack it failed with, as the command reports a failure of its own. */
const failure = (error: string): Error => {
  const e = new Error(error.split("\n")[0] ?? error)
  e.stack = error
  return e
}

/**
 * Verifies `files` in `n` workers, telling `r` each file's steps in their order, and answers every verdict, in the
 * order of the files and of their contracts, with how many files held one. Rejects with a worker's failure.
 */
export const verifyInWorkers = (
  files: ReadonlyArray<string>,
  job: (file: string) => Job,
  n: number,
  r: Run,
  shown: (file: string) => string,
): Promise<{ readonly found: Array<{ readonly file: string; readonly v: Verification }>; readonly filesRead: number }> =>
  new Promise((resolve, reject) => {
    const said: Array<Array<Said>> = files.map(() => [])
    const found: Array<{ readonly file: string; readonly v: Verification }> = []
    let filesRead = 0
    let handed = 0
    let cursor = 0
    let at = 0
    let opened = false
    let draining = false
    let over = false
    const workers: Array<ChildProcess> = []
    const signals = ["SIGINT", "SIGTERM", "SIGHUP"] as const
    const forward = (s: NodeJS.Signals) => () => {
      for (const w of workers) w.kill(s)
      for (const x of signals) process.removeAllListeners(x)
      process.kill(process.pid, s)
    }
    const handlers = signals.map((s) => [s, forward(s)] as const)
    for (const [s, h] of handlers) process.on(s, h)
    const stop = () => {
      over = true
      for (const [s, h] of handlers) process.off(s, h)
      for (const w of workers) if (w.connected) w.disconnect()
    }
    const fail = (e: unknown) => {
      if (over) return
      stop()
      for (const w of workers) w.kill()
      reject(e)
    }

    // The report told each step of the file at the cursor, and of the next once that one is done.
    const drain = async (): Promise<void> => {
      if (draining || over) return
      draining = true
      try {
        while (cursor < files.length) {
          const file = files[cursor]!
          if (!opened) {
            opened = true
            await r.reading(shown(file))
          }
          const m = said[cursor]![at]
          if (m === undefined) return
          at++
          switch (m.kind) {
            case "file":
              filesRead++
              r.file(shown(file), m.names)
              break
            case "verifying":
              r.verifying(m.name)
              break
            case "progress":
              r.progress(m.line)
              break
            case "verified": {
              const v = decodeVerdict(m.v)
              found.push({ file, v })
              r.verified(v, m.ms)
              break
            }
            case "done":
              said[cursor] = []
              cursor++
              at = 0
              opened = false
              break
            case "failed":
              throw failure(m.error)
          }
        }
        stop()
        resolve({ found, filesRead })
      } catch (e) {
        fail(e)
      } finally {
        draining = false
      }
    }

    const hand = (w: ChildProcess, mine: { index: number | undefined }) => {
      if (handed >= files.length) {
        mine.index = undefined
        return
      }
      mine.index = handed++
      w.send(job(files[mine.index]!))
    }
    for (let i = 0; i < Math.min(n, files.length); i++) {
      const w = fork(WORKER, [], { execArgv: process.execArgv, stdio: ["ignore", "inherit", "inherit", "ipc"] })
      workers.push(w)
      const mine: { index: number | undefined } = { index: undefined }
      w.on("message", (m: Said) => {
        const index = mine.index
        if (index === undefined) return
        // A step of a file not yet reported is kept for its turn; its progress, a passing line, is not.
        if (m.kind !== "progress" || index === cursor) said[index]!.push(m)
        if (m.kind === "done") hand(w, mine)
        if (m.kind === "failed") mine.index = undefined
        void drain()
      })
      w.on("exit", (code, signal) => {
        // A worker with no file in hand has told all it verified: one that failed has said so.
        const index = mine.index
        if (over || index === undefined) return
        mine.index = undefined
        const error = `a worker of tsverify stopped (${signal ?? `exit ${code}`}) while it verified ${files[index]}`
        said[index]!.push({ kind: "failed", error: new Error(error).stack ?? error })
        void drain()
      })
      w.on("error", fail)
      hand(w, mine)
    }
  })

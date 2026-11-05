// A worker of `--workers`: a process the command forks (`./pool.ts`), which verifies the files it is handed one at a
// time, in one Z3 of its own, and tells the command each step as it goes. It runs under the command's own flags, the
// steady collection among them, so its verdicts are the ones the command reaches alone.
import { encodeVerdict, verdictsIn } from "./cache.ts"
import type { Job, Said } from "./pool.ts"
import { verifyFile } from "./verify-file.ts"
import { withZ3 } from "./verify.ts"

const say = (m: Said): void => {
  process.send?.(m)
}

// A failure of the verifier is the command's to report: it says so when it reaches this file in its report.
process.on("uncaughtException", (e) => {
  const error = e instanceof Error ? (e.stack ?? e.message) : String(e)
  if (process.send === undefined || !process.connected) process.exit(3)
  process.send({ kind: "failed", error } satisfies Said, () => process.exit(3))
})
// The command is gone, or done with it.
process.on("disconnect", () => process.exit(0))

const jobs: Array<Job> = []
let waiting: ((j: Job) => void) | undefined
process.on("message", (j: Job) => {
  if (waiting === undefined) jobs.push(j)
  else {
    const w = waiting
    waiting = undefined
    w(j)
  }
})
const next = (): Promise<Job> => {
  const j = jobs.shift()
  return j !== undefined ? Promise.resolve(j) : new Promise<Job>((resolve) => (waiting = resolve))
}

await withZ3(async (z3) => {
  for (;;) {
    const { file, tsconfig, bound, work, cover, run, cacheDir } = await next()
    await verifyFile(
      z3,
      file,
      tsconfig,
      {
        ...(bound === undefined ? {} : { bound }),
        ...(work === undefined ? {} : { work }),
        ...(cacheDir === undefined ? {} : { cache: verdictsIn(cacheDir) }),
        cover,
        run,
      },
      {
        file: (names) => say({ kind: "file", names }),
        verifying: (name) => say({ kind: "verifying", name }),
        progress: (line) => say({ kind: "progress", line }),
        verified: (v, ms) => say({ kind: "verified", v: encodeVerdict(v), ms }),
      },
    )
    say({ kind: "done" })
  }
})

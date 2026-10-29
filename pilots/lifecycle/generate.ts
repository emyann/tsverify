// Random task states for the property-testing baseline and for checking the
// lowering against the code. Seeded, so a run repeats.
//
// The bias is a strong property tester's: short arrays, every literal of a
// union, and for `string` and `number` the edges a type-driven generator such
// as fast-check's reaches often (the empty string; NaN, -0, Infinity, a
// fraction, a negative), beside the values the runtime really writes.
import type { State } from "../../../hkb-v2/packages/agent-runtime/src/core/domain.ts"

export const random = (seed: number): (() => number) => {
  let a = seed >>> 0
  return () => {
    a = (a + 0x6d2b79f5) >>> 0
    let t = a
    t = Math.imul(t ^ (t >>> 15), t | 1)
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
}

const pick = <A>(r: () => number, xs: ReadonlyArray<A>): A => xs[Math.floor(r() * xs.length)]!

const OUTCOMES = ["succeeded", "failed", "stopped"] as const
const TURNS = [undefined, undefined, undefined, 0, 0, 1, 1, 2, 3, -1, 0.5, Number.NaN, -0, Number.POSITIVE_INFINITY]

export const state = (r: () => number): State => {
  const inputs = Array.from({ length: Math.floor(r() * 4) }, (_, k) => ({ at: `t${k}`, text: `answer ${k}` }))
  const attempts = Array.from({ length: Math.floor(r() * 5) }, (_, k) => {
    const turn = pick(r, TURNS)
    return {
      n: k + 1,
      startedAt: "2026-10-28T00:00:00.000Z",
      spawnedAt: pick(r, [null, "2026-10-28T00:00:01.000Z", "2026-10-28T00:00:01.000Z", ""]),
      ended: pick(r, [null, null, ...OUTCOMES]),
      endedAt: null,
      reason: null,
      nativeId: null,
      usage: null,
      exitCode: null,
      ...(turn === undefined ? {} : { turn }),
    }
  })
  return {
    taskId: "t",
    brief: "b",
    cwd: "/",
    attempts,
    said: [],
    inputs,
    closed: r() < 0.3,
    stopRequested: r() < 0.25,
    settled: pick(r, [null, null, ...OUTCOMES]),
    ...(r() < 0.5 ? { holdOpen: true as const } : {}),
  }
}

export const states = (seed: number, n: number): Array<State> => {
  const r = random(seed)
  return Array.from({ length: n }, () => state(r))
}

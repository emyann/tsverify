// Random orders, seeded so a run repeats: property testing's inputs, and the
// states the lowering is checked against. The bias is a strong property
// tester's: short arrays, every literal of a union, and the edges a type-driven
// generator reaches often (the empty string; NaN, -0, Infinity, a fraction).
import type { Order } from "./order.ts"

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

const OUTCOMES = ["delivered", "returned", "lost"] as const
const ROUNDS = [undefined, undefined, undefined, 0, 0, 1, 1, 2, 3, -1, 0.5, Number.NaN, -0, Number.POSITIVE_INFINITY]

export const order = (r: () => number): Order => {
  const reorders = Array.from({ length: Math.floor(r() * 4) }, (_, k) => ({ at: `t${k}` }))
  const shipments = Array.from({ length: Math.floor(r() * 5) }, () => {
    const round = pick(r, ROUNDS)
    return {
      carrier: "post",
      pickedUpAt: pick(r, [null, "2026-10-29T09:00:00.000Z", "2026-10-29T09:00:00.000Z", ""]),
      outcome: pick(r, [null, null, ...OUTCOMES]),
      ...(round === undefined ? {} : { round }),
    }
  })
  return {
    id: "o",
    resolution: pick(r, [null, null, "fulfilled", "refunded", "voided"] as const),
    cancelRequested: r() < 0.25,
    shipments,
    paused: r() < 0.3,
    reorders,
    ...(r() < 0.5 ? { subscription: true as const } : {}),
  }
}

export const orders = (seed: number, n: number): Array<Order> => {
  const r = random(seed)
  return Array.from({ length: n }, () => order(r))
}

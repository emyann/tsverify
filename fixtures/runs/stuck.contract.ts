// A pure function that never ends: a run of it is stopped by the clock.
import { contract } from "@emyann/tsverify"

export function forever(x: number): number {
  while (x === x || x !== x) {}
  return x
}

export const endless = contract(forever, { ensures: { any: ({ output }) => output === output } })

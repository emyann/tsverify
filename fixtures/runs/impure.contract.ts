// A function that reads a module's `let`: not pure, so not run.
import { contract } from "@emyann/tsverify"

let rate = 2

export function scaled(x: number): number {
  return x * rate
}

export const setRate = (r: number): void => {
  rate = r
}

export const scaledUp = contract(scaled, { ensures: { same: ({ input: [x], output }) => output === output || x !== x } })

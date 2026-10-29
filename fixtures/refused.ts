// Code the verifier must refuse, each with the reason in its name. A refused
// function leaves its contract unverified, never proved.
import { contract } from "../src/contract.ts"

const holds = () => true

export const cast = contract((s: string) => (s as "a") === "a", { ensures: { holds } })
export const nonNull = contract((xs: ReadonlyArray<string>) => xs.at(0)! === "a", { ensures: { holds } })
export const numberArithmetic = contract((x: number) => x + 1 > 0, { ensures: { holds } })
export const looseEquality = contract((s: string) => s == "a", { ensures: { holds } })

let limit = 10n
export const letCapture = contract((x: bigint) => x < limit, { ensures: { holds } })

function countdown(n: bigint): bigint {
  return n <= 0n ? 0n : countdown(n - 1n)
}
export const recursion = contract(countdown, { ensures: { holds } })

export const bigintDivision = contract((x: bigint) => x / 2n, { ensures: { holds } })

function sum(xs: ReadonlyArray<bigint>): bigint {
  let total = 0n
  for (const x of xs) total += x
  return total
}
export const loop = contract(sum, { ensures: { holds } })

export const elementAccess = contract((xs: ReadonlyArray<string>) => xs[0] === "a", { ensures: { holds } })
export const global = contract((x: number) => Math.max(x, 0) > 0, { ensures: { holds } })
export const stringLength = contract((s: string) => s.length > 0, { ensures: { holds } })

// A spec module that throws when imported. The verifier reads contracts from
// source, so it proves this one without ever running the file.
import { contract } from "../src/contract.ts"

if (typeof globalThis === "object") throw new Error("the verifier ran the module it judges")

export const sign = (x: bigint): bigint => (x > 0n ? 1n : x < 0n ? -1n : 0n)

export const signContract = contract(sign, {
  ensures: {
    oneOfThree: (_, s) => s === 1n || s === -1n || s === 0n,
    followsTheValue: (x, s) => (x > 0n) === (s === 1n),
  },
})

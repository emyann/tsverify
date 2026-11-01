// What a counterexample shows of what the world gave the code: only what its
// run read. A clock read on a branch the run did not take is no part of it.
// `test/fixtures.test.ts` asks.
import { contract } from "../src/contract.ts"

export const stamp = (late: boolean): string => (late ? new Date().toISOString() : "on time")
export const neverOnTime = contract(stamp, { ensures: { neverOnTime: ({ output }) => output !== "on time" } })
export const alwaysOnTime = contract(stamp, { ensures: { alwaysOnTime: ({ output }) => output === "on time" } })

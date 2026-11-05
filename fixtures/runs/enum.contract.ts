// The contract of code a run cannot load: its module holds an `enum`.
import { contract } from "@emyann/tsverify"
import { levelOf } from "./enum.ts"

export const leveled = contract(levelOf, { ensures: { known: ({ output }) => output === 0 || output === 1 } })

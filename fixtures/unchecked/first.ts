// Without `noUncheckedIndexedAccess`, `xs[0]` is typed as the element, there or not: the read is refused, its type
// being a claim the verifier would have to trust. `test/indexes.test.ts` asks it.
import { contract } from "../../src/contract.ts"

export const firstIsA = contract((xs: ReadonlyArray<string>) => xs[0] === "a", { ensures: { holds: () => true } })

/** So is a dictionary's entry, `t[k]`, unless a check of it narrowed it. */
export const entryIsA = contract((t: Readonly<Record<string, string>>, k: string) => t[k] === "a", { ensures: { holds: () => true } })
export const checkedEntryIsA = contract(
  (t: Readonly<Record<string, string | undefined>>, k: string) => t[k] === "a",
  { requires: ({ input: [t, k] }) => Object.hasOwn(t, k), ensures: { holds: () => true } },
)

// Without `noUncheckedIndexedAccess`, `xs[0]` is typed as the element, there or not: the read is refused, its type
// being a claim the verifier would have to trust. `test/indexes.test.ts` asks it.
import { contract } from "../../src/contract.ts"

export const firstIsA = contract((xs: ReadonlyArray<string>) => xs[0] === "a", { ensures: { holds: () => true } })

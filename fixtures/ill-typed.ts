// Code the type checker rejects, kept here behind @ts-expect-error: the verifier
// reads a possibly-undefined value as present only where the checker narrowed it.
import { contract } from "../src/contract.ts"

const firstIsA = (xs: ReadonlyArray<{ readonly name: string }>) => {
  const first = xs.at(0)
  // @ts-expect-error -- `first` may be undefined here
  return first.name === "a"
}

export const unnarrowed = contract(firstIsA, { ensures: { holds: () => true } })

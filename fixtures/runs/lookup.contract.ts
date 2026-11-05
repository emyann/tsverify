// A law broken only through the function a caller passes in: a run generates that function, and shows the calls it answered.
import { contract } from "@emyann/tsverify"

/** The label of a key, "a" for the empty key, else what `name` answers. */
export function label(k: string, name: (k: string) => "a" | "b"): "a" | "b" {
  return k === "" ? "a" : name(k)
}

export const labelled = contract(label, {
  ensures: {
    /** Broken where `name` answers "b". */
    alwaysA: ({ output }) => output === "a",
  },
})

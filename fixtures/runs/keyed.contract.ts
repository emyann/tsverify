// A law broken only behind a `requires` that asks every step's name to be a key of the record: a run meets it when the
// strings of one input are drawn from a few, so the steps' names and the record's keys collide.
import { contract } from "@emyann/tsverify"

export interface Step {
  readonly name: string
}

/** Names the program holds: what a run's strings are drawn from, many of them, so a blind draw rarely repeats one. */
export const NAMES = [
  "n00", "n01", "n02", "n03", "n04", "n05", "n06", "n07", "n08", "n09", "n10", "n11", "n12", "n13", "n14", "n15", "n16", "n17", "n18", "n19",
  "n20", "n21", "n22", "n23", "n24", "n25", "n26", "n27", "n28", "n29", "n30", "n31", "n32", "n33", "n34", "n35", "n36", "n37", "n38", "n39",
  "n40", "n41", "n42", "n43", "n44", "n45", "n46", "n47", "n48", "n49", "n50", "n51", "n52", "n53", "n54", "n55", "n56", "n57", "n58", "n59",
  "n60", "n61", "n62", "n63", "n64", "n65", "n66", "n67", "n68", "n69", "n70", "n71", "n72", "n73", "n74", "n75", "n76", "n77", "n78", "n79",
  "n80", "n81", "n82", "n83", "n84", "n85", "n86", "n87", "n88", "n89", "n90", "n91", "n92", "n93", "n94", "n95", "n96", "n97", "n98", "n99",
  "m00", "m01", "m02", "m03", "m04", "m05", "m06", "m07", "m08", "m09", "m10", "m11", "m12", "m13", "m14", "m15", "m16", "m17", "m18", "m19",
] as const

/** The weights of the steps, each read from the record. */
export function weigh(rec: Readonly<Record<string, number>>, steps: ReadonlyArray<Step>): number {
  let total = 0
  for (const s of steps) total += rec[s.name] ?? 0
  return total
}

export const weighed = contract(weigh, {
  requires: ({ input: [rec, steps] }) => steps.length >= 3 && steps.every((s) => Object.hasOwn(rec, s.name)),
  ensures: {
    /** Broken by any input `requires` lets in: three steps or more. */
    fewSteps: ({ input: [, steps] }) => steps.length < 3,
  },
})

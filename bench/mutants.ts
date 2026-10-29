// The benchmark: one-line bugs planted in the order example's three functions
// (examples/order/order.ts), each hunted by the solver and by property testing
// over the same laws. The original already fails `onItsWay`, so that law
// counts for neither. The harness is `tsverify/mutants`; this file is the suite.
//
//   node bench/mutants.ts [--runs 100,1000,10000] [--json bench/results.json]
import { writeFileSync } from "node:fs"
import path from "node:path"
import { orders } from "../examples/order/generate.ts"
import { status } from "../examples/order/order.spec.ts"
import { header, type Mutant, runMutants, tableRow } from "../src/mutants.ts"
import { withZ3 } from "../src/verify.ts"

const root = path.resolve(import.meta.dirname, "..")

const MUTANTS: ReadonlyArray<Mutant> = [
  { id: "S1", fn: "statusOf", find: 'order.resolution === "fulfilled" ? "complete"', replace: 'order.resolution === "voided" ? "complete"', note: "the wrong resolution completes" },
  { id: "S2", fn: "statusOf", find: 'order.resolution === "refunded" ? "refunded" : "void"', replace: 'order.resolution === "refunded" ? "void" : "refunded"', note: "refunded and voided swapped" },
  { id: "S3", fn: "statusOf", find: 'if (order.cancelRequested) return "canceling"', replace: 'if (order.cancelRequested && !order.paused) return "canceling"', note: "a paused order ignores a cancel" },
  { id: "S4", fn: "statusOf", find: 'if (order.cancelRequested) return "canceling"', replace: 'if (order.cancelRequested || order.paused) return "canceling"', note: "a pause reads as a cancel" },
  { id: "S5", fn: "statusOf", find: "if (last && last.outcome === null)", replace: 'if (last && last.outcome !== "delivered")', note: "a returned shipment reads as on its way" },
  { id: "S6", fn: "statusOf", find: 'if (order.subscription && order.paused) return "paused"', replace: 'if (order.subscription || order.paused) return "paused"', note: "paused without a subscription" },
  { id: "S7", fn: "statusOf", find: 'return roundOf(order).shipments.length > 0 ? "settling" : "placed"', replace: 'return roundOf(order).shipments.length > 1 ? "settling" : "placed"', note: "one shipment reads as none" },
  { id: "S8", fn: "statusOf", find: 'return roundOf(order).shipments.length > 0 ? "settling" : "placed"', replace: 'return roundOf(order, 0).shipments.length > 0 ? "settling" : "placed"', note: "always the first round" },
  { id: "S9", fn: "statusOf", find: 'if (awaitsReorder(order)) return "awaiting-reorder"', replace: 'if (awaitsReorder(order) || order.paused) return "awaiting-reorder"', note: "paused reads as waiting" },
  { id: "W1", fn: "awaitsReorder", find: "!order.paused &&", replace: "", note: "a paused subscription still waits" },
  { id: "W2", fn: "awaitsReorder", find: 'last?.outcome === "delivered"', replace: 'last?.outcome === "lost"', note: "waits after a loss, not a delivery" },
  { id: "W3", fn: "awaitsReorder", find: "(last.round ?? 0) === order.reorders.length", replace: "(last.round ?? 1) === order.reorders.length", note: "an unnumbered round is round 1" },
  { id: "W4", fn: "awaitsReorder", find: "(last.round ?? 0) === order.reorders.length", replace: "(last.round ?? 0) <= order.reorders.length", note: "an earlier round's delivery waits" },
  { id: "W5", fn: "awaitsReorder", find: "!order.resolution &&", replace: "", note: "a resolved order waits" },
  { id: "R1", fn: "roundOf", find: "(s.round ?? 0) === n", replace: "(s.round ?? 0) >= n", note: "later rounds count as this one" },
  { id: "R2", fn: "roundOf", find: "(s.round ?? 0) === n", replace: "s.round === n", note: "an unnumbered shipment is in no round" },
  { id: "R3", fn: "roundOf", find: "n = order.reorders.length", replace: "n = order.shipments.length", note: "the round counted by shipments" },
  { id: "E1", fn: "statusOf", find: "if (last && last.outcome === null)", replace: "if (last && !last.outcome)", note: "equivalent: `outcome` is an outcome or null (a control; nothing should catch it)" },
]

const arg = (flag: string): string | undefined => {
  const i = process.argv.indexOf(flag)
  return i < 0 ? undefined : process.argv[i + 1]
}

const suite = {
  tsconfig: path.join(root, "tsconfig.json"),
  spec: path.join(root, "examples/order/order.spec.ts"),
  contract: "status",
  laws: status.ensures,
  source: path.join(root, "examples/order/order.ts"),
  functions: ["statusOf", "awaitsReorder", "roundOf"],
  mutants: MUTANTS,
  inputs: (n: number) => orders(20261029, n).map((o) => [o]),
  budgets: (arg("--runs") ?? "100,1000,10000").split(",").map(Number),
  tmp: path.join(root, "bench/.tmp"),
} as const

await withZ3(async (z3) => {
  const report = await runMutants(z3, suite, {
    onOriginal: (original) => console.log(header(suite, original).join("\n")),
    onRow: (row) => console.log(tableRow(row)),
  })
  const out = arg("--json")
  if (out !== undefined)
    writeFileSync(out, `${JSON.stringify(report.rows.map((r) => ({ ...r.mutant, solver: r.solver, sampled: r.sampled })), null, 2)}\n`)
})

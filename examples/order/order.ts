// An order's status, derived from its record: what a shop shows its customer.
// Plain TypeScript with no dependencies. `order.contract.ts` states its laws, and
// `bench/mutants.ts` plants bugs in these three functions.

/** How a shipment ended. */
export type Outcome = "delivered" | "returned" | "lost"

export interface Shipment {
  readonly carrier: string
  /** When the carrier picked it up; `null` while it waits at the warehouse. */
  readonly pickedUpAt: string | null
  /** How it ended; `null` while it is on its way. */
  readonly outcome: Outcome | null
  /** The delivery round it belongs to: a subscription's later rounds count from 1. Absent reads as 0. */
  readonly round?: number
}

export interface Order {
  readonly id: string
  /** How the order was resolved, once it is. */
  readonly resolution: "fulfilled" | "refunded" | "voided" | null
  readonly cancelRequested: boolean
  readonly shipments: ReadonlyArray<Shipment>
  /** A subscription: delivered again each time the customer reorders. */
  readonly subscription?: true
  readonly paused: boolean
  /** Each time the customer asked for another round. */
  readonly reorders: ReadonlyArray<{ readonly at: string }>
}

export type Status =
  | "complete"
  | "refunded"
  | "void"
  | "canceling"
  | "in-transit"
  | "awaiting-pickup"
  | "paused"
  | "awaiting-reorder"
  | "settling"
  | "placed"

/** Round `n` of an order (the current one by default): its shipments. */
export function roundOf(order: Order, n = order.reorders.length) {
  return { n, shipments: order.shipments.filter((s) => (s.round ?? 0) === n) }
}

/** A subscription whose current round was delivered, not paused and not resolved: it waits for the customer to reorder. */
export function awaitsReorder(order: Order): boolean {
  const last = order.shipments.at(-1)
  return (
    order.subscription === true &&
    !order.resolution &&
    !order.paused &&
    last?.outcome === "delivered" &&
    (last.round ?? 0) === order.reorders.length
  )
}

/**
 * The status, the first rule that holds answering:
 *
 * 1. Resolved: the final status its resolution names, `complete`, `refunded` or `void`.
 * 2. The customer asked to cancel: `canceling`. It outranks everything but a resolution.
 * 3. Its last shipment is on its way: `in-transit` once picked up, else `awaiting-pickup`.
 * 4. A subscription the customer paused: `paused`.
 * 5. A subscription waiting for the customer (`awaitsReorder`): `awaiting-reorder`.
 * 6. Its current round has a shipment, all ended: `settling`; else `placed`.
 */
export function statusOf(order: Order): Status {
  if (order.resolution) return order.resolution === "fulfilled" ? "complete" : order.resolution === "refunded" ? "refunded" : "void"
  if (order.cancelRequested) return "canceling"
  const last = order.shipments.at(-1)
  if (last && last.outcome === null) return last.pickedUpAt ? "in-transit" : "awaiting-pickup"
  if (order.subscription && order.paused) return "paused"
  if (awaitsReorder(order)) return "awaiting-reorder"
  return roundOf(order).shipments.length > 0 ? "settling" : "placed"
}

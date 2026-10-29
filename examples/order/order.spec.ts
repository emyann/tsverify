// The status of an order, as `statusOf`'s doc comment states it, written as
// laws over (order, status) rather than as a second copy of the code.
import { contract } from "tsverify"
import { statusOf } from "./order.ts"

export const status = contract(statusOf, {
  ensures: {
    // 1. Resolved: the final status its resolution names, and only then.
    finalExactlyWhenResolved: (order, s) => (s === "complete" || s === "refunded" || s === "void") === (order.resolution !== null),
    fulfilledCompletes: (order, s) => order.resolution !== "fulfilled" || s === "complete",
    refundedRefunds: (order, s) => order.resolution !== "refunded" || s === "refunded",

    // 2. A cancel outranks everything but a resolution.
    cancelOutranks: (order, s) => order.resolution !== null || !order.cancelRequested || s === "canceling",
    cancelingOnlyWhenAsked: (order, s) => s !== "canceling" || order.cancelRequested,

    // 3. While the last shipment is on its way: in transit once picked up, else awaiting pickup.
    onItsWay: (order, s) => {
      const last = order.shipments.at(-1)
      if (order.resolution !== null || order.cancelRequested || last === undefined || last.outcome !== null) return true
      return s === (last.pickedUpAt !== null ? "in-transit" : "awaiting-pickup")
    },
    movingMeansAnOpenShipment: (order, s) => {
      const last = order.shipments.at(-1)
      return (s !== "in-transit" && s !== "awaiting-pickup") || (last !== undefined && last.outcome === null)
    },

    // 4–5. Only a subscription waits for a reorder, and only while not paused.
    awaitingNeedsASubscription: (order, s) => s !== "awaiting-reorder" || (order.subscription === true && !order.paused),
    noSubscriptionNeverWaits: (order, s) => order.subscription === true || s !== "awaiting-reorder",

    // 6. Placed: nothing has shipped in the current round.
    placedHasNoShipmentThisRound: (order, s) =>
      s !== "placed" || !order.shipments.some((x) => (x.round ?? 0) === order.reorders.length),
  },
})

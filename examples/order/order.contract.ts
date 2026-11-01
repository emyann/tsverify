// The status of an order, as `statusOf`'s doc comment states it, written as
// laws over (order, status) rather than as a second copy of the code.
import { contract } from "@emyann/tsverify"
import { statusOf } from "./order.ts"

export const status = contract(statusOf, {
  ensures: {
    // 1. Resolved: the final status its resolution names, and only then.
    finalExactlyWhenResolved: ({ input: [order], output }) =>
      (output === "complete" || output === "refunded" || output === "void") === (order.resolution !== null),
    fulfilledCompletes: ({ input: [order], output }) => order.resolution !== "fulfilled" || output === "complete",
    refundedRefunds: ({ input: [order], output }) => order.resolution !== "refunded" || output === "refunded",

    // 2. A cancel outranks everything but a resolution.
    cancelOutranks: ({ input: [order], output }) => order.resolution !== null || !order.cancelRequested || output === "canceling",
    cancelingOnlyWhenAsked: ({ input: [order], output }) => output !== "canceling" || order.cancelRequested,

    // 3. While the last shipment is on its way: in transit once picked up, else awaiting pickup.
    onItsWay: ({ input: [order], output }) => {
      const last = order.shipments.at(-1)
      if (order.resolution !== null || order.cancelRequested || last === undefined || last.outcome !== null) return true
      return output === (last.pickedUpAt !== null ? "in-transit" : "awaiting-pickup")
    },
    movingMeansAnOpenShipment: ({ input: [order], output }) => {
      const last = order.shipments.at(-1)
      return (output !== "in-transit" && output !== "awaiting-pickup") || (last !== undefined && last.outcome === null)
    },

    // 4–5. Only a subscription waits for a reorder, and only while not paused.
    awaitingNeedsASubscription: ({ input: [order], output }) =>
      output !== "awaiting-reorder" || (order.subscription === true && !order.paused),
    noSubscriptionNeverWaits: ({ input: [order], output }) => order.subscription === true || output !== "awaiting-reorder",

    // 6. Placed: nothing has shipped in the current round.
    placedHasNoShipmentThisRound: ({ input: [order], output }) =>
      output !== "placed" || !order.shipments.some((x) => (x.round ?? 0) === order.reorders.length),
  },
})

// The specs of the API's handlers, written before them: one pair for the
// async handlers, one for the Effect programs, the same laws in each
// (laws.ts).
import type { Effect } from "effect"
import { type Rejects, spec } from "tsverify"
import { spec as programSpec } from "tsverify/effect"
import * as laws from "./laws.ts"
import type * as Fx from "./users.effect.ts"
import type { Reply, StoreDown, UsersPort } from "./users.ts"

/** GET /users/:id, as an async function given the store. */
export const GetUserSpec = spec<(users: UsersPort, id: string) => Rejects<Reply, StoreDown>>({
  ensures: {
    readsTheUserOnce: (_users, id, out, calls) => laws.readsTheUserOnce(id, out, calls),
    answersWhatItFound: (_users, id, out, calls) => laws.answersWhatItFound(id, out, calls),
    failsAsTheStoreFails: (_users, id, out, calls) => laws.getFailsAsTheStoreFails(id, out, calls),
  },
})

/** PATCH /users/:id with `{ name }`, as an async function given the store. */
export const RenameUserSpec = spec<(users: UsersPort, id: string, name: string) => Rejects<Reply, StoreDown>>({
  ensures: {
    emptyNameTouchesNothing: (_users, id, name, out, calls) => laws.emptyNameTouchesNothing(id, name, out, calls),
    readsTheUserFirst: (_users, id, name, out, calls) => laws.readsTheUserFirst(id, name, out, calls),
    missingWritesNothing: (_users, id, name, out, calls) => laws.missingWritesNothing(id, name, out, calls),
    renamedAsWritten: (_users, id, name, out, calls) => laws.renamedAsWritten(id, name, out, calls),
    failsAsTheStoreFails: (_users, id, name, out, calls) => laws.renameFailsAsTheStoreFails(id, name, out, calls),
  },
})

/** GET /users/:id, as an Effect program requiring the store. */
export const GetUserProgram = programSpec<(id: string) => Effect.Effect<Reply, Fx.StoreDown, Fx.Users>>({
  ensures: {
    readsTheUserOnce: laws.readsTheUserOnce,
    answersWhatItFound: laws.answersWhatItFound,
    failsAsTheStoreFails: laws.getFailsAsTheStoreFails,
  },
})

/** PATCH /users/:id with `{ name }`, as an Effect program requiring the store. */
export const RenameUserProgram = programSpec<(id: string, name: string) => Effect.Effect<Reply, Fx.StoreDown, Fx.Users>>({
  ensures: {
    emptyNameTouchesNothing: laws.emptyNameTouchesNothing,
    readsTheUserFirst: laws.readsTheUserFirst,
    missingWritesNothing: laws.missingWritesNothing,
    renamedAsWritten: laws.renamedAsWritten,
    failsAsTheStoreFails: laws.renameFailsAsTheStoreFails,
  },
})

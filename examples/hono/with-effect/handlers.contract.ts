// The API's laws (../laws.ts), given the signature of an Effect program. The
// store is a service the program requires, not an argument, so the laws are
// held as they are written.
import type { Effect } from "effect"
import { spec } from "tsverify/effect"
import * as laws from "../laws.ts"
import type { Reply } from "../users.ts"
import type { StoreDown, Users } from "./store.ts"

/** GET /users/:id */
const getUserSpec = spec<(id: string) => Effect.Effect<Reply, StoreDown, Users>>({
  ensures: {
    readsTheUserOnce: laws.readsTheUserOnce,
    answersWhatItFound: laws.answersWhatItFound,
    failsAsTheStoreFails: laws.getFailsAsTheStoreFails,
  },
})
export type GetUserSpec = typeof getUserSpec

/** PATCH /users/:id with `{ name }` */
const renameUserSpec = spec<(id: string, name: string) => Effect.Effect<Reply, StoreDown, Users>>({
  ensures: {
    emptyNameTouchesNothing: laws.emptyNameTouchesNothing,
    readsTheUserFirst: laws.readsTheUserFirst,
    missingWritesNothing: laws.missingWritesNothing,
    renamedAsWritten: laws.renamedAsWritten,
    failsAsTheStoreFails: laws.renameFailsAsTheStoreFails,
  },
})
export type RenameUserSpec = typeof renameUserSpec

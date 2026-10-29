// The API's laws (../laws.ts), given the signature of an async handler. The
// store is handed in as the first argument, so each law is called without it.
import { type Rejects, spec } from "tsverify"
import * as laws from "../laws.ts"
import type { Reply } from "../users.ts"
import type { StoreDown, UsersPort } from "./store.ts"

/** GET /users/:id */
export const GetUserSpec = spec<(users: UsersPort, id: string) => Rejects<Reply, StoreDown>>({
  ensures: {
    readsTheUserOnce: (_users, id, out, calls) => laws.readsTheUserOnce(id, out, calls),
    answersWhatItFound: (_users, id, out, calls) => laws.answersWhatItFound(id, out, calls),
    failsAsTheStoreFails: (_users, id, out, calls) => laws.getFailsAsTheStoreFails(id, out, calls),
  },
})

/** PATCH /users/:id with `{ name }` */
export const RenameUserSpec = spec<(users: UsersPort, id: string, name: string) => Rejects<Reply, StoreDown>>({
  ensures: {
    emptyNameTouchesNothing: (_users, id, name, out, calls) => laws.emptyNameTouchesNothing(id, name, out, calls),
    readsTheUserFirst: (_users, id, name, out, calls) => laws.readsTheUserFirst(id, name, out, calls),
    missingWritesNothing: (_users, id, name, out, calls) => laws.missingWritesNothing(id, name, out, calls),
    renamedAsWritten: (_users, id, name, out, calls) => laws.renamedAsWritten(id, name, out, calls),
    failsAsTheStoreFails: (_users, id, name, out, calls) => laws.renameFailsAsTheStoreFails(id, name, out, calls),
  },
})

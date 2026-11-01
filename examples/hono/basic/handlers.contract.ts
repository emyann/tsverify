// The API's laws (../laws.ts), given the signature of an async handler. The
// store is handed in as the first argument, so each law is called without it.
import { type Rejects, spec } from "@emyann/tsverify"
import * as laws from "../laws.ts"
import type { Reply } from "../users.ts"
import type { StoreDown, UsersPort } from "./store.ts"

/** GET /users/:id */
const getUserSpec = spec<(users: UsersPort, id: string) => Rejects<Reply, StoreDown>>({
  ensures: {
    readsTheUserOnce: ({ input: [, id], output, calls }) => laws.readsTheUserOnce({ input: [id], output, calls }),
    answersWhatItFound: ({ input: [, id], output, calls }) => laws.answersWhatItFound({ input: [id], output, calls }),
    failsAsTheStoreFails: ({ input: [, id], output, calls }) => laws.getFailsAsTheStoreFails({ input: [id], output, calls }),
  },
})
export type GetUserSpec = typeof getUserSpec

/** PATCH /users/:id with `{ name }` */
const renameUserSpec = spec<(users: UsersPort, id: string, name: string) => Rejects<Reply, StoreDown>>({
  ensures: {
    emptyNameTouchesNothing: ({ input: [, id, name], output, calls }) => laws.emptyNameTouchesNothing({ input: [id, name], output, calls }),
    readsTheUserFirst: ({ input: [, id, name], output, calls }) => laws.readsTheUserFirst({ input: [id, name], output, calls }),
    missingWritesNothing: ({ input: [, id, name], output, calls }) => laws.missingWritesNothing({ input: [id, name], output, calls }),
    renamedAsWritten: ({ input: [, id, name], output, calls }) => laws.renamedAsWritten({ input: [id, name], output, calls }),
    failsAsTheStoreFails: ({ input: [, id, name], output, calls }) => laws.renameFailsAsTheStoreFails({ input: [id, name], output, calls }),
  },
})
export type RenameUserSpec = typeof renameUserSpec

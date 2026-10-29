// The handlers as Effect programs, the store a service they require. The
// routes (app.ts) run them; each takes its type from its spec
// (handlers.spec.ts).
import { Effect } from "effect"
import type { Implementation } from "tsverify"
import { emptyName, notFound, ok } from "../users.ts"
import type { GetUserSpec, RenameUserSpec } from "./handlers.spec.ts"
import { Users } from "./store.ts"

export const getUser: Implementation<typeof GetUserSpec> = Effect.fn("getUser")(function* (id) {
  const users = yield* Users
  const user = yield* users.get(id)
  return user === undefined ? notFound() : ok(user)
})

export const renameUser: Implementation<typeof RenameUserSpec> = Effect.fn("renameUser")(function* (id, name) {
  if (name === "") return emptyName()
  const users = yield* Users
  const user = yield* users.get(id)
  if (user === undefined) return notFound()
  const renamed = { ...user, name }
  yield* users.put(renamed)
  return ok(renamed)
})

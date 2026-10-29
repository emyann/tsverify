// The same handlers as Effect programs, the store a service they require.
// Hono's routes (app.effect.ts) run them; each takes its type from its spec.
import { Effect } from "effect"
import type { Implementation } from "tsverify"
import type { GetUserProgram, RenameUserProgram } from "./handlers.spec.ts"
import { Users } from "./users.effect.ts"
import { emptyName, notFound, ok } from "./users.ts"

export const getUser: Implementation<typeof GetUserProgram> = Effect.fn("getUser")(function* (id) {
  const users = yield* Users
  const user = yield* users.get(id)
  return user === undefined ? notFound() : ok(user)
})

export const renameUser: Implementation<typeof RenameUserProgram> = Effect.fn("renameUser")(function* (id, name) {
  if (name === "") return emptyName()
  const users = yield* Users
  const user = yield* users.get(id)
  if (user === undefined) return notFound()
  const renamed = { ...user, name }
  yield* users.put(renamed)
  return ok(renamed)
})

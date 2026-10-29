// The API's handlers as async functions over a store: what to answer, and
// what to read and write to answer it. Hono's routes (app.ts) call them;
// each takes its type from its spec (handlers.spec.ts).
import type { Implementation } from "tsverify"
import type { GetUserSpec, RenameUserSpec } from "./handlers.spec.ts"
import { emptyName, notFound, ok } from "./users.ts"

export const getUser: Implementation<typeof GetUserSpec> = async (users, id) => {
  const user = await users.get(id)
  return user === undefined ? notFound() : ok(user)
}

export const renameUser: Implementation<typeof RenameUserSpec> = async (users, id, name) => {
  if (name === "") return emptyName()
  const user = await users.get(id)
  if (user === undefined) return notFound()
  const renamed = { ...user, name }
  await users.put(renamed)
  return ok(renamed)
}

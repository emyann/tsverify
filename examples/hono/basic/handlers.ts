// The handlers as async functions over the store: what to answer, and what to
// read and write to answer it. The routes (app.ts) call them; each takes its
// type from its spec (handlers.contract.ts).
import type { Implementation } from "tsverify"
import { emptyName, notFound, ok } from "../users.ts"
import type { GetUserSpec, RenameUserSpec } from "./handlers.contract.ts"

export const getUser: Implementation<GetUserSpec> = async (users, id) => {
  const user = await users.get(id)
  return user === undefined ? notFound() : ok(user)
}

export const renameUser: Implementation<RenameUserSpec> = async (users, id, name) => {
  if (name === "") return emptyName()
  const user = await users.get(id)
  if (user === undefined) return notFound()
  const renamed = { ...user, name }
  await users.put(renamed)
  return ok(renamed)
}

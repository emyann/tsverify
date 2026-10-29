// What every build of the users API shares: a user, the replies a handler
// gives, and the check of a request's body at the edge. It knows no store, no
// error class, and neither async nor Effect: those are each build's own.

export interface User {
  readonly id: string
  readonly name: string
}

/** What a handler answers: the status, and the body Hono sends as JSON. */
export type Reply =
  | { readonly status: 200; readonly body: User }
  | { readonly status: 400 | 404; readonly body: { readonly error: string } }

export const ok = (user: User): Reply => ({ status: 200, body: user })
export const notFound = (): Reply => ({ status: 404, body: { error: "no such user" } })
export const emptyName = (): Reply => ({ status: 400, body: { error: "a name is not empty" } })

/** `{ "name": "..." }`'s name, or `undefined` for any other body: the edge, where a value from outside is checked. */
export const nameIn = (body: unknown): string | undefined =>
  typeof body === "object" && body !== null && "name" in body && typeof body.name === "string" ? body.name : undefined

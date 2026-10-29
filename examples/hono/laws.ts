// What each handler of the API must do, written once for every build of it.
// A law reads the request's values, the handler's outcome (a reply, or the
// store's failure) and the calls the handler made to the store, as the
// verifier records them; it says nothing of how the handler is written, async
// or Effect, nor of HTTP. A spec is a signature and the laws it holds: each
// build's handlers.spec.ts (basic/, with-effect/) gives these laws its own
// signature, and each build is proved against them.
import type { Outcome } from "tsverify"
import type { Reply, User } from "./users.ts"

type Failure = { readonly _tag: string }
type Out = Outcome<Reply, Failure>
export type UsersCall =
  | { readonly op: "get"; readonly args: readonly [string]; readonly outcome: Outcome<User | undefined, Failure> }
  | { readonly op: "put"; readonly args: readonly [User]; readonly outcome: Outcome<void, Failure> }

/** GET /users/:id */
type GetLaw = (id: string, out: Out, calls: ReadonlyArray<UsersCall>) => boolean

/** One read, of the user asked for. */
export const readsTheUserOnce: GetLaw = (id, _out, calls) => {
  const read = calls.at(0)
  return calls.length === 1 && read !== undefined && read.op === "get" && read.args[0] === id
}

/** Found, a 200 with the user read; missing, a 404. */
export const answersWhatItFound: GetLaw = (_id, out, calls) => {
  const read = calls.at(0)
  if (read === undefined || read.op !== "get" || read.outcome._tag !== "Success") return true
  const found = read.outcome.value
  if (out._tag !== "Success") return false
  if (found === undefined) return out.value.status === 404
  return out.value.status === 200 && out.value.body.id === found.id && out.value.body.name === found.name
}

/** PATCH /users/:id, `{ name }` */
type RenameLaw = (id: string, name: string, out: Out, calls: ReadonlyArray<UsersCall>) => boolean

/** An empty name is a 400, and the store is not touched. */
export const emptyNameTouchesNothing: RenameLaw = (_id, name, out, calls) =>
  name !== "" || (out._tag === "Success" && out.value.status === 400 && calls.length === 0)

/** A name is acted on by reading the user asked for, first. */
export const readsTheUserFirst: RenameLaw = (id, name, _out, calls) => {
  if (name === "") return true
  const read = calls.at(0)
  return read !== undefined && read.op === "get" && read.args[0] === id
}

/** A user not found is a 404, and nothing is written. */
export const missingWritesNothing: RenameLaw = (_id, _name, out, calls) => {
  const read = calls.at(0)
  if (read === undefined || read.op !== "get" || read.outcome._tag !== "Success" || read.outcome.value !== undefined) return true
  return out._tag === "Success" && out.value.status === 404 && calls.length === 1
}

/** A 200 is the user read, renamed, written once after the read, and sent back as written. */
export const renamedAsWritten: RenameLaw = (_id, name, out, calls) => {
  if (out._tag !== "Success" || out.value.status !== 200) return true
  const read = calls.at(0)
  const write = calls.at(1)
  if (read === undefined || read.op !== "get" || read.outcome._tag !== "Success" || read.outcome.value === undefined) return false
  if (calls.length !== 2 || write === undefined || write.op !== "put") return false
  const written = write.args[0]
  return written.id === read.outcome.value.id && written.name === name && out.value.body.id === written.id && out.value.body.name === written.name
}

/** A store that fails ends the handler with that failure: no call after it, no reply. Without one, there is a reply. */
const failureEndsIt = (out: Out, calls: ReadonlyArray<UsersCall>): boolean => {
  if (!calls.some((c) => c.outcome._tag === "Failure")) return out._tag === "Success"
  const last = calls.at(-1)
  return last !== undefined && last.outcome._tag === "Failure" && out._tag === "Failure" && out.error._tag === last.outcome.error._tag
}
export const getFailsAsTheStoreFails: GetLaw = (_id, out, calls) => failureEndsIt(out, calls)
export const renameFailsAsTheStoreFails: RenameLaw = (_id, _name, out, calls) => failureEndsIt(out, calls)

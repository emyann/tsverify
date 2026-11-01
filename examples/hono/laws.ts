// What each handler of the API must do, written once for every build of it.
// A law reads the request's values, the handler's outcome (a reply, or the
// store's failure) and the calls the handler made to the store, as the
// verifier records them; it says nothing of how the handler is written, async
// or Effect, nor of HTTP. A spec is a signature and the laws it holds: each
// build's handlers.contract.ts (basic/, with-effect/) gives these laws its own
// signature, and each build is proved against them.
import type { ComputationRun, Outcome } from "@emyann/tsverify"
import type { Reply, User } from "./users.ts"

type Failure = { readonly _tag: string }
type Out = Outcome<Reply, Failure>
export type UsersCall =
  | { readonly op: "get"; readonly args: readonly [string]; readonly outcome: Outcome<User | undefined, Failure> }
  | { readonly op: "put"; readonly args: readonly [User]; readonly outcome: Outcome<void, Failure> }

/** GET /users/:id */
type GetLaw = (run: ComputationRun<[id: string], Out, UsersCall>) => boolean

/** One read, of the user asked for. */
export const readsTheUserOnce: GetLaw = ({ input: [id], calls }) => {
  const read = calls.at(0)
  return calls.length === 1 && read !== undefined && read.op === "get" && read.args[0] === id
}

/** Found, a 200 with the user read; missing, a 404. */
export const answersWhatItFound: GetLaw = ({ output, calls }) => {
  const read = calls.at(0)
  if (read === undefined || read.op !== "get" || read.outcome._tag !== "Success") return true
  const found = read.outcome.value
  if (output._tag !== "Success") return false
  if (found === undefined) return output.value.status === 404
  return output.value.status === 200 && output.value.body.id === found.id && output.value.body.name === found.name
}

/** PATCH /users/:id, `{ name }` */
type RenameLaw = (run: ComputationRun<[id: string, name: string], Out, UsersCall>) => boolean

/** An empty name is a 400, and the store is not touched. */
export const emptyNameTouchesNothing: RenameLaw = ({ input: [, name], output, calls }) =>
  name !== "" || (output._tag === "Success" && output.value.status === 400 && calls.length === 0)

/** A name is acted on by reading the user asked for, first. */
export const readsTheUserFirst: RenameLaw = ({ input: [id, name], calls }) => {
  if (name === "") return true
  const read = calls.at(0)
  return read !== undefined && read.op === "get" && read.args[0] === id
}

/** A user not found is a 404, and nothing is written. */
export const missingWritesNothing: RenameLaw = ({ output, calls }) => {
  const read = calls.at(0)
  if (read === undefined || read.op !== "get" || read.outcome._tag !== "Success" || read.outcome.value !== undefined) return true
  return output._tag === "Success" && output.value.status === 404 && calls.length === 1
}

/** A 200 is the user read, renamed, written once after the read, and sent back as written. */
export const renamedAsWritten: RenameLaw = ({ input: [, name], output, calls }) => {
  if (output._tag !== "Success" || output.value.status !== 200) return true
  const read = calls.at(0)
  const write = calls.at(1)
  if (read === undefined || read.op !== "get" || read.outcome._tag !== "Success" || read.outcome.value === undefined) return false
  if (calls.length !== 2 || write === undefined || write.op !== "put") return false
  const written = write.args[0]
  return (
    written.id === read.outcome.value.id &&
    written.name === name &&
    output.value.body.id === written.id &&
    output.value.body.name === written.name
  )
}

/** A store that fails ends the handler with that failure: no call after it, no reply. Without one, there is a reply. */
const failureEndsIt = (out: Out, calls: ReadonlyArray<UsersCall>): boolean => {
  if (!calls.some((c) => c.outcome._tag === "Failure")) return out._tag === "Success"
  const last = calls.at(-1)
  return last !== undefined && last.outcome._tag === "Failure" && out._tag === "Failure" && out.error._tag === last.outcome.error._tag
}
export const getFailsAsTheStoreFails: GetLaw = ({ output, calls }) => failureEndsIt(output, calls)
export const renameFailsAsTheStoreFails: RenameLaw = ({ output, calls }) => failureEndsIt(output, calls)

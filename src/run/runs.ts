// The parent's half of running a contract's laws on generated inputs: the plan of a run, read from the checker in the
// verifier's process, and the child process it is handed to (`./child.ts`), which loads the code and the spec, runs
// them, and answers which laws broke on which input. The verifier's process never imports the user's code nor
// fast-check: the child does, with a throwaway HOME and TMPDIR, and is killed if it runs past `RUN_STUCK_MS`.
import type { Project, ContractSource } from "../project.ts"
import type { Trust } from "../lower.ts"
import type { Options } from "../verify.ts"
import type { Shape } from "./shape.ts"

/** Inputs run for each contract that meet `requires`: a count, never a time, so a run is the same on every machine. */
export const RUNS = 1_000

/** The clock that stops a child whose "pure" function never ends: the one stop that may differ between machines. */
export const RUN_STUCK_MS = 60_000

/** What the child is handed: what to load, what to generate, and the seed. Plain data, sent over ipc. */
export interface RunPlan {
  /** The contract's own module, absolute, and its exported name: a `contract(...)` object, or a spec's implementation. */
  readonly module: string
  readonly name: string
  /** For an implementation (`const f: Implementation<S>`): where the spec is declared, absolute, and its variable's name. */
  readonly spec?: { readonly module: string; readonly name: string }
  /** The laws, by name, in order, and for each the shape of the result a law reads (`output`), where it reads one. */
  readonly laws: ReadonlyArray<{ readonly name: string; readonly output?: Shape }>
  /** The shape of each parameter, in order. */
  readonly params: ReadonlyArray<Shape>
  /** The string literals of the program's own files: what generated strings are drawn from. */
  readonly pool: ReadonlyArray<string>
  readonly seed: number
  readonly runs: number
  /** The longest array, dictionary, `Map` or `Set` generated: `--bound`. */
  readonly bound: number
}

/** What a run did, or why there was none. */
export type Ran =
  | {
      readonly ran: true
      /** Inputs run that met `requires`. */
      readonly inputs: number
      /** Inputs `requires` refused. */
      readonly discarded: number
      /** Inputs on which the function or a law threw: skipped, never a counterexample. */
      readonly threw: number
      /** Every module the child loaded: the program's own files relative to the current folder, packages by name. */
      readonly modules: ReadonlyArray<string>
      /** The environment variables the child was given, by name. */
      readonly env: ReadonlyArray<string>
      readonly ms: number
    }
  | { readonly ran: false; readonly why: string; readonly stuck?: true }

export interface RunResult {
  /** Each law a run broke, with the input that breaks it, shrunk; a generated function shown as `{ "~calls": [[args, result], …] }`. */
  readonly broken: Readonly<Record<string, { readonly args: ReadonlyArray<unknown> }>>
  /** The laws a generated input meeting `requires`, with a generated free result, breaks: each says something. */
  readonly saysSomething: ReadonlyArray<string>
  readonly ran: Ran
}

/** The plan of a run of `source`, or why it is not run. */
export const planOf = (
  _project: Project,
  _source: ContractSource,
  _trust: Trust,
  _opts: Options,
  _seed: number,
): RunPlan | { readonly why: string } => ({ why: "not built yet" })

/** Runs `plan` in a child process of its own. Never rejects: a child that cannot load or run answers `ran: false`. */
export const runContract = async (_plan: RunPlan): Promise<RunResult> => ({
  broken: {},
  saysSomething: [],
  ran: { ran: false, why: "not built yet" },
})

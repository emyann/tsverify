// The verifier as a program calls it: load a project, verify a contract by name,
// read the verdicts. What a spec author writes is `@emyann/tsverify` (src/contract.ts)
// and, for Effect programs, `@emyann/tsverify/effect`.
export { diagnostics, loadProject, readContract, sourceFile, type ContractSource, type Project } from "./project.ts"
export { purityOf, type Purity } from "./purity.ts"
export { PURITY_TRUSTS, type Trusted } from "./trust.ts"
export type { Ctx, FunctionNode } from "./value.ts"
export {
  disagreements,
  lowerSide,
  openZ3,
  verify,
  withZ3,
  type CoverResult,
  type LawResult,
  type LawStatus,
  type ObligationResult,
  type Options,
  type Verification,
} from "./verify.ts"

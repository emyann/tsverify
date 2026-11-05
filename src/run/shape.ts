// The values of a TypeScript type, as plain JSON the child turns into generators: read from the checker in the
// verifier's process, sent over ipc. No Z3, no fast-check.

export type Shape =
  | { readonly kind: "literal"; readonly value: string | number | boolean }
  | { readonly kind: "bigint-literal"; readonly value: string }
  | { readonly kind: "boolean" }
  | { readonly kind: "number" }
  | { readonly kind: "bigint" }
  | { readonly kind: "string" }
  | { readonly kind: "null" }
  | { readonly kind: "undefined" }
  | { readonly kind: "union"; readonly of: ReadonlyArray<Shape> }
  | { readonly kind: "record"; readonly fields: Readonly<Record<string, Shape>>; readonly optional: ReadonlyArray<string> }
  | { readonly kind: "array"; readonly of: Shape }
  | { readonly kind: "tuple"; readonly of: ReadonlyArray<Shape>; readonly rest?: Shape }
  | { readonly kind: "dictionary"; readonly of: Shape }
  | { readonly kind: "map"; readonly key: Shape; readonly value: Shape }
  | { readonly kind: "set"; readonly of: Shape }
  | { readonly kind: "function"; readonly returns: Shape }

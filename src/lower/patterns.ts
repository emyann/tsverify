// Destructuring: a binding pattern bound to a value, its defaults and its rest, and a parameter's default.
import ts from "typescript"
import { undefinedOr } from "../ops.ts"
import { type Thunk, Unsupported, type Val, lazyRecord } from "../value.ts"
import { type Lowering, later, lowerExpr, member, shownPresent } from "../lower.ts"
import { callable } from "./closures.ts"
import { slice } from "./arrays.ts"

/** `value`, or what `fallback` gives where it is `undefined`: a default, of a parameter or of a pattern's name. */
export const defaulted = (L: Lowering, value: Thunk, fallback: Thunk | undefined, at: ts.Node): Thunk =>
  fallback === undefined
    ? value
    : later(L, () => {
        const given = value()
        // A function the caller may give, or leave to the default the code writes: the default called as written.
        const merged = given.kind === "maybe" && given.value?.kind === "builtin"
        return undefinedOr(L.u, given, merged ? () => callable(L, fallback()) : fallback, at)
      })

/**
 * What an object pattern's rest holds: every property of `v` but the keys the pattern named before it. As a spread,
 * it copies what the value's type says it holds, the value taken to be plain data.
 */
export const restOf = (L: Lowering, v: Val, named: ReadonlyArray<string>, at: ts.Node): Val => {
  const obj = v.kind === "maybe" ? (v.value ?? v) : v
  if (obj.kind !== "record") throw new Unsupported(`the rest of a ${obj.kind} is not modeled`, at)
  L.u.notes.add(
    "An object rest copies each property but those named before it: the value is taken to be plain data, its properties its own, none a getter.",
  )
  const left = new Set(named)
  // The keys named are known absent, whatever the value held: a spread of the rest never brings them back.
  return lazyRecord(
    (n) => (left.has(n) ? undefined : obj.field(n)),
    undefined,
    (n) => (left.has(n) ? L.u.z3.Bool.val(false) : obj.has?.(n)),
  )
}

/**
 * Element `k` of what an array pattern takes apart: an array's, `undefined` past its end, as `xs[k]` reads it, and
 * refused where its type says it is there and nothing says so (no `noUncheckedIndexedAccess`, no default); a tuple's
 * field `k`.
 */
export const patternElement = (L: Lowering, v: Val, k: number, el: ts.BindingElement): Val => {
  const z3 = L.u.z3
  const p = v.kind === "maybe" && v.value !== undefined ? v.value : v
  if (p.kind === "array") {
    const known = p.size !== undefined && k < p.size
    if (!known && el.initializer === undefined) {
      const t = L.checker.getTypeAtLocation(el)
      if (!(t.isUnion() ? t.types : [t]).some((m) => m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Any | ts.TypeFlags.Unknown)))
        throw new Unsupported(
          `\`${el.getText()}\` takes an element of an array where its type says it is there, which may be false: turn on \`noUncheckedIndexedAccess\`, or give it a default`,
          el,
        )
    }
    const i = z3.Int.val(k)
    return known ? p.elem(i) : { kind: "maybe", isNull: z3.Bool.val(false), isUndefined: z3.Not(i.lt(p.length)), value: p.elem(i) }
  }
  if (p.kind === "record") {
    const f = p.field(String(k))
    if (f === undefined) throw new Unsupported(`no element ${k} to take apart`, el)
    return f
  }
  throw new Unsupported(`an array pattern over a ${p.kind}`, el)
}

/** What `...rest` in an array pattern holds: the elements from `k` on, a copy, as `.slice(k)` gives them. */
export const patternRest = (L: Lowering, v: Val, k: number, el: ts.BindingElement): Val => {
  const p = v.kind === "maybe" && v.value !== undefined ? v.value : v
  if (p.kind !== "array") throw new Unsupported(`the rest of a ${p.kind} in an array pattern is not modeled`, el)
  return slice(L, p, [{ kind: "int", origin: "count", term: L.u.z3.Int.val(k) }], el)
}

/** The keys an object pattern names, each with its element, and its rest, if it has one. */
export const patternKeys = (
  pattern: ts.ObjectBindingPattern,
): { readonly keys: ReadonlyArray<{ readonly key: string; readonly el: ts.BindingElement }>; readonly rest?: ts.BindingElement } => {
  const keys: Array<{ key: string; el: ts.BindingElement }> = []
  let rest: ts.BindingElement | undefined
  for (const el of pattern.elements) {
    if (el.dotDotDotToken !== undefined) rest = el
    else keys.push({ key: el.propertyName === undefined ? (el.name as ts.Identifier).text : propertyKey(el.propertyName), el })
  }
  return rest === undefined ? { keys } : { keys, rest }
}

/** Binds a name or an object pattern to a value, each name read on first use; a default where its value is `undefined`. */
export const bind = (L: Lowering, name: ts.BindingName, value: Thunk, scope: Map<string, Thunk>): void => {
  if (ts.isIdentifier(name)) {
    scope.set(name.text, value)
    return
  }
  if (ts.isArrayBindingPattern(name)) {
    name.elements.forEach((el, k) => {
      if (ts.isOmittedExpression(el)) return
      if (el.dotDotDotToken !== undefined) {
        bind(
          L,
          el.name,
          later(L, () => patternRest(L, value(), k, el)),
          scope,
        )
        return
      }
      bind(
        L,
        el.name,
        defaulted(
          L,
          later(L, () => patternElement(L, value(), k, el)),
          el.initializer === undefined ? undefined : later(L, () => lowerExpr(L, el.initializer!, scope)),
          el,
        ),
        scope,
      )
    })
    return
  }
  const { keys, rest } = patternKeys(name)
  // Each name read at its type, as a property access is: a path where the object lacks the key reads `undefined` there.
  const objType = L.checker.getTypeAtLocation(name)
  const whole = (): Val => shownPresent(value(), objType)
  for (const { key, el } of keys)
    bind(
      L,
      el.name,
      defaulted(
        L,
        later(L, () => member(L, whole(), key, el, objType, L.checker.getTypeAtLocation(el))),
        el.initializer === undefined ? undefined : later(L, () => lowerExpr(L, el.initializer!, scope)),
        el,
      ),
      scope,
    )
  if (rest !== undefined)
    bind(
      L,
      rest.name,
      later(L, () =>
        restOf(
          L,
          whole(),
          keys.map((k) => k.key),
          rest,
        ),
      ),
      scope,
    )
}

export const propertyKey = (name: ts.PropertyName): string => {
  if (ts.isIdentifier(name) || ts.isStringLiteral(name) || ts.isNoSubstitutionTemplateLiteral(name)) return name.text
  // A number names the key JavaScript writes it as: `0x10` is "16", `1.50` is "1.5".
  if (ts.isNumericLiteral(name)) return String(Number(name.text.replaceAll("_", "")))
  throw new Unsupported("a computed property name is not modeled", name)
}

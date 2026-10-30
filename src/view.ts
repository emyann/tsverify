// The command's report, drawn with Ink: each file, then each of its contracts, a line for one whose laws all hold, and
// under one with something to look at, those laws and that proof code, each with why. A run of one file, `--verbose` and
// one contract named list every law. In a terminal it is drawn live, what is done fixed above a line for what is being
// verified, each line wrapped to the window between its words, under its own first word. Piped, it is the same text,
// wrapped nowhere, in colour only when `FORCE_COLOR` asks. The command loads this file only for text: `--json` never
// loads Ink.
import { styleText } from "node:util"
import { Box, render, renderToString, Static, type StaticProps, Text, useAnimation } from "ink"
import { createElement as h, type ReactNode } from "react"
import type { Trusted } from "./trust.ts"
import { MODELS } from "./exec.ts"
import type { LawResult, LawStatus, ObligationResult, Verification } from "./verify.ts"

/** Whether to colour: Node's own answer for stdout, which reads `NO_COLOR`, `FORCE_COLOR` and whether it is a terminal. */
const colour = styleText("red", "x") !== "x"

interface Style {
  readonly color?: "green" | "red" | "yellow" | "magenta" | "cyan"
  readonly bold?: boolean
  readonly dimColor?: boolean
  readonly inverse?: boolean
  readonly underline?: boolean
}
const DIM: Style = { dimColor: true }
const BOLD: Style = { bold: true }
const styled = (style: Style, ...children: Array<ReactNode>): ReactNode => h(Text, colour ? style : {}, ...children)

/** Each verdict's mark and colour, the one that most needs a look first: red broken, yellow neither, magenta not read. */
const VERDICTS: Readonly<Record<LawStatus, { readonly mark: string; readonly style: Style }>> = {
  inconsistent: { mark: "!", style: { color: "magenta", bold: true, inverse: true } },
  counterexample: { mark: "✗", style: { color: "red", bold: true } },
  unsupported: { mark: "!", style: { color: "magenta" } },
  unknown: { mark: "?", style: { color: "yellow" } },
  bounded: { mark: "~", style: { color: "yellow" } },
  vacuous: { mark: "○", style: { color: "yellow" } },
  proved: { mark: "✓", style: { color: "green" } },
}
const WORST_FIRST = Object.keys(VERDICTS) as ReadonlyArray<LawStatus>
const worst = (statuses: ReadonlyArray<LawStatus>): LawStatus => WORST_FIRST.find((s) => statuses.includes(s)) ?? "proved"
/** How many of each verdict, the worst first. */
const tally = (statuses: ReadonlyArray<LawStatus>): Array<readonly [LawStatus, number]> =>
  WORST_FIRST.flatMap((s) => {
    const n = statuses.filter((x) => x === s).length
    return n === 0 ? [] : [[s, n] as const]
  })
const plural = (n: number, word: string) => `${n} ${word}${n === 1 ? "" : "s"}`

/** A piece of a line: its text, and how it is styled. A line's pieces are joined by a space; an empty one adds a space. */
type Piece = string | readonly [Style, string]
/**
 * A line that wraps between its words, each wrapped line starting with a word: Ink's own wrapping keeps the space it
 * breaks at, which would start the next line.
 */
const line = (...pieces: ReadonlyArray<Piece>): ReactNode =>
  h(
    Box,
    { flexWrap: "wrap" },
    ...pieces.flatMap((p) => {
      const [style, text] = typeof p === "string" ? [{}, p] : p
      return text.split(" ").map((word) => styled(style, `${word} `))
    }),
  )
/** A mark, and beside it lines that wrap under their own first word, never under the mark. */
const beside = (mark: ReactNode, ...lines: ReadonlyArray<ReactNode>): ReactNode =>
  h(
    Box,
    null,
    // Ink takes text only inside a `Text`: a mark given as a string is put in one.
    h(Box, { flexShrink: 0, marginRight: 1 }, typeof mark === "string" ? h(Text, null, mark) : mark),
    h(Box, { flexDirection: "column", flexShrink: 1 }, ...lines),
  )
const marked = (s: LawStatus, ...lines: ReadonlyArray<ReactNode>): ReactNode =>
  beside(styled(VERDICTS[s].style, VERDICTS[s].mark), ...lines)
const indented = (...lines: ReadonlyArray<ReactNode>): ReactNode => h(Box, { flexDirection: "column", paddingLeft: 2 }, ...lines)

/** A value as JavaScript writes it, so a counterexample can be pasted into a call: `0n`, `"a"`, `[1, NaN]`, `{ id: "a" }`. */
const literal = (x: unknown): string =>
  typeof x === "bigint"
    ? `${x}n`
    : typeof x === "number"
      ? Object.is(x, -0)
        ? "-0"
        : String(x)
      : typeof x === "string"
        ? JSON.stringify(x)
        : x === undefined
          ? "undefined"
          : Array.isArray(x)
            ? `[${x.map(literal).join(", ")}]`
            : x !== null && typeof x === "object"
              ? Object.keys(x).length === 0
                ? "{}"
                : `{ ${Object.entries(x)
                    .map(([k, v]) => `${/^[A-Za-z_$][\w$]*$/.test(k) ? k : JSON.stringify(k)}: ${literal(v)}`)
                    .join(", ")} }`
              : x === null || typeof x === "boolean"
                ? String(x)
                : `<${typeof x}>`

/** What the world gave the code on a counterexample's run: each operation's outcome, each declared function's result. */
const given = (world: Readonly<Record<string, unknown>>) =>
  Object.entries(world)
    .map(([key, x]) => {
      const what = key.replace(/!\d+$/, "")
      if (x !== null && typeof x === "object" && "_tag" in x) {
        const o = x as { readonly _tag: unknown; readonly value?: unknown; readonly error?: unknown }
        if (o._tag === "Failure") return `${what} failed with ${literal(o.error)}`
        if (o._tag === "Success") return "value" in o ? `${what} gave ${literal(o.value)}` : `${what} succeeded`
      }
      return `${what} gave ${literal(x)}`
    })
    .join(", ")

/** A counterexample: the arguments, as the call that takes them would write them, and what the world gave on that run. */
const witness = (r: { readonly args?: ReadonlyArray<unknown>; readonly world?: Readonly<Record<string, unknown>> }): Array<ReactNode> => [
  ...(r.args === undefined ? [] : [line([DIM, "e.g."], [{ color: "cyan" }, `(${r.args.map(literal).join(", ")})`])]),
  ...(r.world === undefined || Object.keys(r.world).length === 0 ? [] : [line([DIM, "where"], given(r.world))]),
]

/** A law: its sentence, or its name; then why, or an input that breaks it. */
const law = (l: LawResult): ReactNode =>
  marked(
    l.status,
    line([BOLD, l.says ?? l.name], "", [DIM, `(${l.says === undefined ? "" : `${l.name}, `}${Math.round(l.ms)} ms)`]),
    ...witness(l),
    ...(l.abstract === undefined
      ? []
      : [line(`leans on what is declared of ${l.abstract.join(", ")}: true of them as declared, maybe not as they are`)]),
    ...(l.reason === undefined ? [] : [line(l.reason)]),
  )

const asked = (o: ObligationResult): string =>
  o.kind === "invariant"
    ? `invariant ${o.phase === "entry" ? "on entry" : "kept by each iteration"}`
    : o.kind === "requires"
      ? "lemma's requires"
      : o.kind === "division"
        ? "divisor not 0n"
        : o.kind === "write"
          ? "inside the array"
          : o.kind === "exact"
            ? "exact"
            : o.kind
const obligation = (o: ObligationResult): ReactNode =>
  marked(
    o.status,
    line(`${asked(o)}: ${o.text}`, "", [DIM, `(${o.at})`]),
    ...witness(o),
    ...(o.reason === undefined ? [] : [line(o.reason)]),
  )

/** What the proof code asked, then each division's divisor: proved where it runs, or the input that makes it 0n. */
const proofCode = (os: ReadonlyArray<ObligationResult>): Array<ReactNode> =>
  (
    [
      ["proof code:", os.filter((o) => !MODELS.has(o.kind))],
      ["divisions:", os.filter((o) => o.kind === "division")],
      ["element writes:", os.filter((o) => o.kind === "write")],
      ["arithmetic:", os.filter((o) => o.kind === "exact")],
    ] as const
  ).flatMap(([heading, xs]) => (xs.length === 0 ? [] : [styled(DIM, heading), indented(...xs.map(obligation))]))

const purity = (t: Trusted): string =>
  t.purity === "checked"
    ? `pure, checked from source (read ${t.read?.join(", ") ?? "nothing"})`
    : t.purity === "unchecked"
      ? "pure, unchecked: no source"
      : "not pure: a fresh result per call"
const trusted = (ts: ReadonlyArray<Trusted>, full: boolean): Array<ReactNode> =>
  ts.length === 0
    ? []
    : full
      ? [
          line("trusted (declared, not proved):"),
          indented(
            ...ts.map((t) =>
              beside(
                "-",
                line(`${t.name}: ${purity(t)}${t.laws.length > 0 ? `; laws ${t.laws.join(", ")}` : ""} — ${t.declared.join(", ")}`),
              ),
            ),
          ),
        ]
      : [
          line(
            `trusted: ${ts.map((t) => `${t.name} (${t.purity === "impure" ? "not pure" : `pure, ${t.purity}`}${t.laws.length > 0 ? `; ${plural(t.laws.length, "law")}` : ""})`).join(", ")}`,
          ),
        ]

/** How a contract is shown. */
export interface Shape {
  /** Each law and each obligation, or only those with something to look at. */
  readonly every: boolean
  /** Also what it trusted in full, what its result reaches, and what was assumed. */
  readonly full: boolean
  /** The width its name is padded to, so that its file's summaries line up. */
  readonly width: number
}

/** A contract's summary: its laws, or how many of each verdict; then its obligations'; then, kept short, what it trusts. */
const summary = (v: Verification, trusts: boolean): Array<Piece> => {
  const counts = (xs: ReadonlyArray<LawStatus>): Array<Piece> =>
    tally(xs).map(([s, n], i, all) => [VERDICTS[s].style, `${n} ${s}${i < all.length - 1 ? "," : ""}`] as const)
  const laws = v.laws.map((l) => l.status)
  const obligations = v.obligations.map((o) => o.status)
  const groups: Array<Array<Piece>> = [
    laws.every((s) => s === "proved") ? [plural(laws.length, "law")] : counts(laws),
    ...(obligations.length === 0
      ? []
      : [obligations.every((s) => s === "proved") ? [plural(obligations.length, "obligation")] : ["obligations", ...counts(obligations)]]),
    ...(trusts && v.trusted.length > 0 ? [[`trusts ${v.trusted.map((t) => t.name).join(", ")}`]] : []),
  ]
  return groups.flatMap((g, i) => (i === 0 ? g : [[DIM, "·"] as const, ...g]))
}

/** A contract verified, in how long it took. */
export interface Verified {
  readonly v: Verification
  readonly ms: number
}

/** A contract: a line with its mark and summary, then what `shape` shows of it. */
export const contract = ({ v, ms }: Verified, { every, full, width }: Shape): ReactNode => {
  const name = [BOLD, v.contract.padEnd(width)] as const
  if (v.unsupported !== undefined)
    return marked("unsupported", line(name, "", [VERDICTS.unsupported.style, "not verified"]), line(v.unsupported))
  const shown = (s: LawStatus) => every || s !== "proved"
  return marked(
    worst([...v.laws.map((l) => l.status), ...v.obligations.map((o) => o.status)]),
    line(name, "", ...summary(v, !every), "", [DIM, `(${Math.round(ms)} ms)`]),
    ...v.laws.filter((l) => shown(l.status)).map(law),
    ...proofCode(v.obligations.filter((o) => shown(o.status))),
    ...(every ? trusted(v.trusted, full) : []),
    ...(full && v.cover.length > 0
      ? [line(`reaches: ${v.cover.map((c) => (c.status === "reachable" ? c.value : `${c.value} (${c.status})`)).join(", ")}`)]
      : []),
    ...(full ? [line("assumed:"), indented(...v.notes.map((n) => beside("-", line(n))))] : []),
  )
}

/** The last lines: what needs a look, by verdict, then what was proved, then how much was verified and how long it took. */
const totals = (all: ReadonlyArray<Verification>, files: number, seconds: number): ReactNode => {
  const laws = all.flatMap((v) => v.laws.map((l) => l.status))
  const obligations = all.flatMap((v) => v.obligations.map((o) => o.status))
  const unread = all.filter((v) => v.unsupported !== undefined).length
  const item = (s: LawStatus, text: string): Array<Piece> => [
    [VERDICTS[s].style, VERDICTS[s].mark],
    [VERDICTS[s].style, text],
  ]
  const look: Array<Array<Piece>> = [
    ...tally(laws)
      .filter(([s]) => s !== "proved")
      .map(([s, n]) => item(s, `${n} ${s}`)),
    ...tally(obligations)
      .filter(([s]) => s !== "proved")
      .map(([s, n]) => item(s, `${n} ${s} among obligations`)),
    ...(unread > 0 ? [item("unsupported", `${unread} not verified`)] : []),
  ]
  const proved = [
    [laws.filter((s) => s === "proved").length, "law"],
    [obligations.filter((s) => s === "proved").length, "obligation"],
  ] as const
  const held = proved.filter(([n]) => n > 0).map(([n, word]) => plural(n, word))
  return h(
    Box,
    { flexDirection: "column", marginTop: 1 },
    ...(look.length === 0 ? [] : [line(...look.flatMap((pieces, i) => (i === 0 ? pieces : [[DIM, "·"] as const, ...pieces])))]),
    ...(held.length === 0 ? [] : [marked("proved", line(`${held.join(", ")} proved`))]),
    h(Box, { paddingLeft: 2 }, line([DIM, `${plural(all.length, "contract")} in ${plural(files, "file")} · ${seconds.toFixed(1)} s`])),
  )
}

/** What is being done while it is: one line for it, one for how far the run is. */
interface Doing {
  readonly what: string
  readonly last?: string
  readonly read: number
  readonly files: number
  readonly contracts: number
}
const SPINNER = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"]
const Live = (d: Doing): ReactNode => {
  const { frame } = useAnimation({ interval: 80 })
  return h(
    Box,
    { flexDirection: "column" },
    h(
      Text,
      { wrap: "truncate-end" },
      styled({ color: "cyan" }, SPINNER[frame % SPINNER.length]),
      ` ${d.what}`,
      d.last === undefined ? "" : styled(DIM, `  ${d.last}`),
    ),
    h(
      Text,
      { wrap: "truncate-end" },
      styled(
        DIM,
        `  ${d.read} of ${plural(d.files, "file")} read · ${plural(d.contracts, "contract")} verified · ${(performance.now() / 1000).toFixed(1)} s`,
      ),
    ),
  )
}

/** Where the report goes: a terminal, drawn live, or anything else, as text. */
interface Out {
  /** Writes what is done, which is never drawn again. */
  readonly done: (node: ReactNode) => void
  /** Shows what is being done, below what is done, until the next call. */
  readonly doing: (d: Doing) => void
  /** Settles once what was asked is on the screen: called before work that holds the thread. */
  readonly drawn: () => Promise<void>
  /** Writes the last of it, and lets the terminal go. */
  readonly end: (last?: ReactNode) => Promise<void>
}

/** Ink's `Static`, over nodes: `createElement` cannot infer what its items are. */
const Fixed: (props: StaticProps<ReactNode>) => ReactNode = Static
const View = ({ done, doing, last }: { readonly done: Array<ReactNode>; readonly doing?: Doing; readonly last?: ReactNode }): ReactNode =>
  h(
    Box,
    { flexDirection: "column" },
    // Ink lays `Static` out apart from the rest, as wide as its widest line unless told: held to the window, its lines wrap.
    h(Fixed, { items: done, style: { width: "100%" }, children: (node, i) => h(Box, { key: i, flexDirection: "column" }, node) }),
    doing === undefined ? null : h(Live, doing),
    last ?? null,
  )
const live = (): Out => {
  const done: Array<ReactNode> = []
  let doing: Doing | undefined
  let last: ReactNode
  const view = () => h(View, { done: [...done], ...(doing === undefined ? {} : { doing }), last })
  const ink = render(view(), { patchConsole: false })
  return {
    done: (node) => {
      done.push(node)
      ink.rerender(view())
    },
    doing: (d) => {
      doing = d
      ink.rerender(view())
    },
    drawn: () => ink.waitUntilRenderFlush(),
    end: async (node) => {
      doing = undefined
      last = node
      ink.rerender(view())
      ink.unmount()
      await ink.waitUntilExit()
    },
  }
}

/**
 * A node as text, at a width no line of it reaches. Ink lays text out in a grid as wide as it is told, so the cost grows
 * with the width: a node is drawn at 1000 columns, and again, wider than all its text, only when it holds more text than
 * that.
 */
const text = (node: ReactNode): string => {
  const narrow = renderToString(node, { columns: 1000 })
  return narrow.length + 50 <= 1000 ? narrow : renderToString(node, { columns: narrow.length + 50 })
}
const piped = (): Out => ({
  done: (node) => process.stdout.write(`${text(node)}\n`),
  doing: () => {},
  drawn: () => Promise.resolve(),
  end: (node) => {
    if (node !== undefined) process.stdout.write(`${text(node)}\n`)
    return Promise.resolve()
  },
})

/** What the command tells the report as it goes. */
export interface Run {
  /** A file is about to be read, which holds the thread while its program is built. */
  readonly reading: (file: string) => Promise<void>
  /** A file read, and the contracts it holds, before the first is verified. */
  readonly file: (file: string, contracts: ReadonlyArray<string>) => void
  /** A contract is about to be verified. */
  readonly verifying: (contract: string) => void
  /** What its verification decided last (`Options.progress`). */
  readonly progress: (line: string) => void
  /** A contract verified, in `ms`. */
  readonly verified: (v: Verification, ms: number) => void
  /** The run is over: the totals, of the files that held a contract, and the terminal let go. */
  readonly end: (files: number) => Promise<void>
  /** The run stops with nothing more to show: the terminal let go. */
  readonly quit: () => Promise<void>
}

/**
 * The report of a run over `files` files, drawn live when `live`. A run of one file lists every law, and so does one
 * that is `verbose`; a run of several lists, under each contract, only what has something to look at. Which it is is
 * known once a second file holds a contract, so the first file's lines wait until then. One contract named (`single`)
 * is shown in full, with no file and no totals.
 */
export const run = ({
  live: drawnLive,
  files,
  verbose,
  single,
}: {
  readonly live: boolean
  readonly files: number
  readonly verbose: boolean
  readonly single: boolean
}): Run => {
  const out = drawnLive ? live() : piped()
  const all: Array<Verification> = []
  let every: boolean | undefined = verbose || single || files <= 1 ? true : undefined
  const full = verbose || single
  let read = 0
  let holding = 0
  let width = 0
  let what = ""
  /** The first file's lines, while it is not known whether the run lists every law. */
  let held: { readonly file: string; readonly width: number; readonly contracts: Array<Verified> } | undefined
  const show = (c: Verified, w: number, all: boolean) => {
    const node = contract(c, { every: all, full, width: w })
    out.done(single ? node : indented(node))
  }
  const heading = (file: string) => styled({ underline: true }, file)
  const flush = (all: boolean) => {
    if (held === undefined) return
    out.done(heading(held.file))
    for (const c of held.contracts) show(c, held.width, all)
    held = undefined
  }
  const doing = (last?: string) => out.doing({ what, read, files, contracts: all.length, ...(last === undefined ? {} : { last }) })
  return {
    reading: (file) => {
      read++
      what = `reading ${file}`
      doing()
      return out.drawn()
    },
    file: (file, contracts) => {
      holding++
      if (every === undefined && holding === 2) {
        every = false
        flush(false)
      }
      width = Math.max(0, ...contracts.map((c) => c.length))
      if (every === undefined) held = { file, width, contracts: [] }
      else if (!single) out.done(heading(file))
    },
    verifying: (name) => {
      what = name
      doing()
    },
    progress: (line) => doing(line),
    verified: (v, ms) => {
      all.push(v)
      if (held !== undefined) held.contracts.push({ v, ms })
      else show({ v, ms }, width, every ?? true)
    },
    end: (filesRead) => {
      flush(true)
      return out.end(single ? undefined : totals(all, filesRead, performance.now() / 1000))
    },
    quit: () => out.end(),
  }
}

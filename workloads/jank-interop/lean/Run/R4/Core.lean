import Jank.R4.Core.Search

/-! Round 4 driver: core (clojure.core functions no round covered, and the bundled namespaces).

`jank4-core all` runs every census to completion; `jank4-core <name>` runs one. -/

open Determinismo Jank.R4.Core Jank.R4.Core.Search Jank.R3.Search

def census (name : String) (body : WM Unit) (maxRuns : Nat := 50000000) : IO Unit := do
  let t0 ← IO.monoMsNow
  let c := censusUnder (runW body) #[] maxRuns
  printCensus name c
  let t1 ← IO.monoMsNow
  IO.println s!"   ({(t1 - t0) / 1000} s)"

def examples : IO Unit := do
  IO.println "== examples (replica outputs)"
  let pr := fun (a b : V) =>
    IO.println s!"   (clojure.data/diff {a.src} {b.src}): Clojure {(Diff.triple (Diff.cljDiff a b)).code}, jank {(Diff.triple (Diff.jankDiff a b)).code}"
  pr (.map [(k "a", i 1), (k "b", i 2)]) (.map [(k "a", i 1), (k "b", i 3)])
  pr (.vec [i 1, i 2, i 3]) (.vec [i 1, i 5, i 3])
  pr (.set [i 1, i 2]) (.set [i 2, i 3])
  for (f, args) in [("%d", [Format.Arg.long 5]), ("%s-%s", [.str "a", .str "b"]), ("{}", [.long 5]),
      ("{}", []), ("100%", []), ("{", [])] do
    IO.println s!"   (format \"{f}\"{String.join (args.map (" " ++ ·.code))}): Clojure {(Format.javaFormat f args).show}, jank {(Format.jankFormat f args).show}"
  for s in ["00000000000000000000000000000000", "{00000000-0000-0000-0000-000000000000}",
      "0-0000000-0000-0000-0000-000000000000", "1-1-1-1-1", "00000000-0000-0000-0000-000000000000"] do
    IO.println s!"   (parse-uuid \"{s}\"): JDK {(Uuid.jdkFromString s).isSome}, documented grammar {(Uuid.canonical s).isSome}, jank {(Uuid.stduuidFromString s).isSome}"
  for w in Json.writeCases do
    IO.println s!"   (json/write-str {w.src}): data.json {w.clj}, jank {w.jank}"
  for v in [(2 : Int) ^ 63, 2 ^ 64 - 1, 2 ^ 64, -(2 ^ 63) - 1] do
    IO.println s!"   (json/read-str \"{v}\"): data.json {(Json.cljReadInteger v).code}, jank {(Json.jankReadInteger v).code}"

def main (args : List String) : IO Unit := do
  let which := args.headD "all"
  let run := fun (n : String) => which == "all" || which == n
  if run "examples" then examples
  if run "diff" then census "clojure.data/diff, every ordered pair of 21 values" diffPair
  if run "format" then census "format: strings of ≤5 chars over % s d a { }, 5 argument lists" (fmtCase 5)
  if run "uuid" then census "parse-uuid: 5 templates, ≤2 edits (insert/delete/replace over 0 f F - { } g +)" (uuidCase 2)
  if run "ex" then census "ex-message/ex-data on non-exceptions; Throwable->map and printing over chains of 1–4" exCase
  if run "pred" then census "counted?, bounded-count (n ≤ 4), shuffle over 22 object types" predCase
  if run "entry" then census "map-entry? over 10 values" entryCase
  if run "walk" then census "postwalk identity: metadata over 9 forms" walkCase
  if run "strings" then census "trim-newline, starts-with?, ends-with?, includes?: strings ≤3 chars over a é \\n \\r 😀 (UTF-8 bytes vs chars)" (strCase 3)
  if run "cycle" then census "cycle: take n ≤ 12 of 1–4 elements" cycleCase
  if run "json" then do
    census "data.json read-str of integers at the 2^62..2^65 boundaries (both signs)" jsonIntCase
    census "data.json read-str :bigdec true of m/10^k, m ≤ 200, k ≤ 3" jsonDecCase

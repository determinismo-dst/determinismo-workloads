import Jank.R3.Search.Common
import Jank.R3.Search.Analyzer
import Jank.R3.Search.Reader
import Jank.R3.Search.Core
import Jank.R3.Search.Strings
import Jank.R3.Search.Core2
import Jank.R3.Search.Seq

/-! Round 3 driver: search widening and residual searches over round 2's areas.
`jank3-search <search> [args]`; each search prints its bounds, timelines and result. -/

open Determinismo Jank.R3.Search

namespace Run.R3.Search

section
open Jank.R3.Search.Analyzer
open Jank.Analyzer (Features)

def tinyLits : List Jank.Analyzer.Obj :=
  [Jank.Analyzer.I 0, Jank.Analyzer.D 1.5, Jank.Analyzer.B true, .nil]

def anSize : IO Unit := do
  IO.println "== analyzer: round 2's tiny grammar (literals 0 1.5 true nil, names x when), exact sizes"
  for d in [0, 1, 2] do
    IO.println s!"   depth {d}: {r2Count 4 2 d 0} programs"
  -- The count checked against exhaust at depth 1 and against Knuth's estimate at depth 2.
  let tiny : Features := { lits := tinyLits, names := ["x", "when"] }
  let r1 := Jank.Analyzer.runOne tiny 1 [] {}
  match exhaust (fun s => { (r1 s) with violation := none }) 100000 with
  | .complete n => IO.println s!"   depth 1 by exhaust: {n} timelines"
  | _ => IO.println "   depth 1 by exhaust: did not complete"
  let r2 := fun s => { (Jank.Analyzer.runOne tiny 2 [] {} s) with violation := none }
  let (e, decs) := estimate r2 3000
  IO.println s!"   depth 2 by Knuth's estimate (3000 paths): {fmtFloat e} programs, {fmtFloat decs} decisions on average"
  IO.println s!"   round 2's exhaust stopped at 1,500,000 of these, all under the first top-level kind's first options"
  IO.println s!"   by the top kind (round 2's first decision): {r2KindCounts 4 2 1}"
  -- The reduced grammar of round 2 at depth 1, for the record.
  IO.println s!"   round 2's reduced grammar (6 literals, 3 names) at depth 1: {r2Count 6 3 1 0} programs (round 2 ran 76,731)"

def gAll (budget depth : Nat) (lits : List Jank.Analyzer.Obj := Jank.Analyzer.literals)
    (names : List String := Jank.Analyzer.namePool) (kinds : List String := allKinds)
    (inner : Option (List String) := none) : Grammar :=
  { lits, names, kinds, innerKinds := inner, budget, depth }

def anSizes : IO Unit := do
  IO.println "== analyzer, round 3 grammars: Knuth's estimates of their sizes (2000 paths each)"
  let gs : List (String × Grammar) := [
    ("budget 1, all kinds, 12 literals, 4 names", gAll 1 1),
    ("budget 2, all kinds, 12 literals, 4 names", gAll 2 2),
    ("budget 2, all kinds, tiny literals, 2 names", gAll 2 2 tinyLits ["x", "when"]),
    ("budget 2, all kinds, 6 literals, 3 names", gAll 2 2 [Jank.Analyzer.I 0, Jank.Analyzer.I 2147483648, Jank.Analyzer.D 1.5, Jank.Analyzer.B true, .nil, Jank.Analyzer.str "s"] ["x", "f", "when"]),
    ("budget 3, all kinds, tiny literals, 2 names", gAll 3 3 tinyLits ["x", "when"]) ]
  for (label, g) in gs do
    let r := fun s => { (runOne g [] {} s) with violation := none }
    let (e, decs) := estimate r 2000
    IO.println s!"   {label}: about {fmtFloat e} programs ({fmtFloat decs} decisions on average)"

def anRun (args : List String) : IO Unit := do
  match args with
  | ["size"] => anSize; anSizes
  | ["examples"] =>
    let open_ := fun (n : String) => Jank.Analyzer.S n
    let L := Jank.Analyzer.L
    let V := Jank.Analyzer.V
    let I := Jank.Analyzer.I
    let K := Jank.Analyzer.K
    let progs : List (String × List Jank.Analyzer.Obj) := [
      ("W3: a local bound to a literal, called in a branch never taken",
        [L [open_ "let*", V [open_ "x", I 1], L [open_ "if", Jank.Analyzer.B false, L [open_ "x"], K "ok"]]]),
      ("W3: the same with a double literal",
        [L [open_ "let*", V [open_ "x", Jank.Analyzer.D 1.5], L [open_ "if", L [open_ "=", I 1, I 2], L [open_ "x", I 1], K "ok"]]]),
      ("W3: round 2's shrunk program (tag native-callee)",
        [L [open_ "let*", V [open_ "when", L [open_ "quote", I 0]], L [open_ "if", I 0, I 0, L [open_ "when", I 0, open_ "when"]]]]),
      ("W3: a loop local bound to a literal, then to a keyword, called (no dead code)",
        [L [open_ "loop*", V [open_ "f", I 2147483647, open_ "k", I 0],
          L [open_ "if", L [open_ "=", open_ "k", I 1], L [open_ "f", I 2147483647], L [open_ "recur", K "k", I 1]]]]),
      ("W3: a let-bound boolean literal, called in a branch never taken",
        [L [open_ "let*", V [open_ "x", Jank.Analyzer.B true], L [open_ "if", Jank.Analyzer.B false, L [open_ "x"], K "ok"]]]),
      ("probe: letfn, fn named when, parameter when",
        [L [open_ "letfn*", V [open_ "when", L [open_ "fn*", open_ "when", V [open_ "when"], L [open_ "and", Jank.Analyzer.str "s", L [open_ "when", Jank.Analyzer.B true, open_ "when"]]]], L [open_ "when", I 0]]]),
      ("probe: fn named when, parameter when, no letfn",
        [L [L [open_ "fn*", open_ "when", V [open_ "when"], L [open_ "when", Jank.Analyzer.B true, open_ "when"]], I 0]]),
      ("probe: letfn f, parameter when",
        [L [open_ "letfn*", V [open_ "f", L [open_ "fn*", open_ "f", V [open_ "when"], L [open_ "when", Jank.Analyzer.B true, open_ "when"]]], L [open_ "f", I 0]]]),
      ("probe: letfn named when, parameter x, calls when",
        [L [open_ "letfn*", V [open_ "when", L [open_ "fn*", open_ "when", V [open_ "x"], L [open_ "when", Jank.Analyzer.B false, open_ "x"]]], L [open_ "when", I 0]]]),
      ("probe: fn named when, parameter when, through and",
        [L [L [open_ "fn*", open_ "when", V [open_ "when"], L [open_ "and", Jank.Analyzer.str "s", L [open_ "when", Jank.Analyzer.B true, open_ "when"]]], I 0]]),
      ("probe: case, a var branch and a def in the default",
        [L [open_ "case", I 1, I 1, L [open_ "var", open_ "when"], L [open_ "do", L [open_ "def", open_ "when", I 1], I 2]]]),
      ("probe: case, a var branch and a def in the other branch",
        [L [open_ "case", I 1, I 1, L [open_ "var", open_ "when"], I 2, L [open_ "do", L [open_ "def", open_ "when", I 1], I 2], I 3]]),
      ("probe W4: case, a def in a clause, the default calls it",
        [L [open_ "case", I 1, I 1, L [open_ "def", open_ "h", I 1], L [open_ "h"]]]),
      ("probe W4: case, a def of inc in a clause, the default calls inc",
        [L [open_ "case", I 2, I 1, L [open_ "do", L [open_ "def", open_ "inc", I 5], open_ "inc"], L [open_ "inc", I 1]]]),
      ("probe: fn params [& when], (and x (when …))",
        [L [L [open_ "fn*", V [open_ "&", open_ "when"], L [open_ "and", I 1, L [open_ "when", Jank.Analyzer.B true, I 7]]], I (-1)]]),
      ("probe: fn params [when], (and x (when …))",
        [L [L [open_ "fn*", V [open_ "when"], L [open_ "and", I 1, L [open_ "when", Jank.Analyzer.B true, I 7]]], I (-1)]]),
      ("probe: fn params [when], (if x (when …))",
        [L [L [open_ "fn*", V [open_ "when"], L [open_ "if", I 1, L [open_ "when", Jank.Analyzer.B true, I 7]]], I (-1)]]),
      ("probe: fn params [when], (let* [g x] (when …))",
        [L [L [open_ "fn*", V [open_ "when"], L [open_ "let*", V [open_ "g", I 1], L [open_ "when", Jank.Analyzer.B true, I 7]]], I (-1)]]),
      ("probe: let [when 0], (and 1 (when …))",
        [L [open_ "let*", V [open_ "when", I 0], L [open_ "and", I 1, L [open_ "when", Jank.Analyzer.B true, I 7]]]]),
      ("probe: let [when :k], (or nil (when …))",
        [L [open_ "let*", V [open_ "when", K "k"], L [open_ "or", .nil, L [open_ "when", Jank.Analyzer.B true, I 7]]]]),
      ("control: a local bound to a fn, called",
        [L [open_ "let*", V [open_ "x", L [open_ "fn*", V [], K "ok"]], L [open_ "x"]]]),
      ("control: a local bound to a literal, called (both throw)",
        [L [open_ "let*", V [open_ "x", I 1], L [open_ "x"]]]) ]
    IO.println "== analyzer examples (jank: the replica's analysis then evaluation; Clojure: the spec)"
    for (name, forms) in progs do
      let j := Jank.Analyzer.runJank forms
      let c := Jank.Analyzer.runClojure forms
      IO.println s!"   {name}: {" ".intercalate (forms.map Jank.Analyzer.Obj.pr)}\n      jank {j.outcome.show}; Clojure {c.show}; agree {agrees3 j.outcome c}; tags {j.tags}"
  | ["r2tiny", k] =>
    -- Round 2's tiny depth-2 world, partition k of its first decision (the top kind).
    let tiny : Features := { lits := tinyLits, names := ["x", "when"] }
    let run := Jank.Analyzer.runOne tiny 2 known {}
    let _ ← Jank.R3.Search.report s!"analyzer: round 2's tiny grammar, depth 2, top kind {k}, R23–R36 set aside" run 0 40000000 #[k.toNat!]
  | ["tally", b, d, which] =>
    let g := match which with
      | "tiny" => gAll b.toNat! d.toNat! tinyLits ["x", "when"]
      | "six" => gAll b.toNat! d.toNat! [Jank.Analyzer.I 0, Jank.Analyzer.I 2147483648, Jank.Analyzer.D 1.5, Jank.Analyzer.B true, .nil, Jank.Analyzer.str "s"] ["x", "f", "when"]
      | "tinyb" => gAll b.toNat! d.toNat! [Jank.Analyzer.I 2147483647, Jank.Analyzer.I 2147483648, Jank.Analyzer.K "k", Jank.Analyzer.str "s"] ["f", "inc"]
      | "tinyc" => gAll b.toNat! d.toNat! [Jank.Analyzer.I (-1), Jank.Analyzer.D 0.0, Jank.Analyzer.B false, Jank.Analyzer.I 1] ["x", "inc"]
      | _ => gAll b.toNat! d.toNat!
    let t0 ← IO.monoMsNow
    let t := tallyUnder g #[] 60000000
    printTally s!"analyzer tally, budget {b}, depth {d}, {which} literals, every kind" t
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["tally-part", b, d, which, k] =>
    let g := match which with
      | "tiny" => gAll b.toNat! d.toNat! tinyLits ["x", "when"]
      | "tinyb" => gAll b.toNat! d.toNat! [Jank.Analyzer.I 2147483647, Jank.Analyzer.I 2147483648, Jank.Analyzer.K "k", Jank.Analyzer.str "s"] ["f", "inc"]
      | "tinyc" => gAll b.toNat! d.toNat! [Jank.Analyzer.I (-1), Jank.Analyzer.D 0.0, Jank.Analyzer.B false, Jank.Analyzer.I 1] ["x", "inc"]
      | _ => gAll b.toNat! d.toNat!
    let t0 ← IO.monoMsNow
    let t := tallyUnder g #[k.toNat!] 60000000
    printTally s!"analyzer tally, budget {b}, depth {d}, {which} literals, every kind, top kind {k}" t
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["exhaust", b, d, which, k] =>
    let g := match which with
      | "tiny" => gAll b.toNat! d.toNat! tinyLits ["x", "when"]
      | "six" => gAll b.toNat! d.toNat! [Jank.Analyzer.I 0, Jank.Analyzer.I 2147483648, Jank.Analyzer.D 1.5, Jank.Analyzer.B true, .nil, Jank.Analyzer.str "s"] ["x", "f", "when"]
      | _ => gAll b.toNat! d.toNat!
    let pfx := if k == "all" then #[] else #[k.toNat!]
    let _ ← Jank.R3.Search.report s!"analyzer exhaust, budget {b}, depth {d}, {which} literals, every kind, top kind {k}, R23–R36 set aside" (runOne g known) 0 60000000 pfx
  | ["sample", b, d, n, first] =>
    let g := gAll b.toNat! d.toNat!
    let t0 ← IO.monoMsNow
    let t := tallySeeds3 g n.toNat! first.toNat!
    printTally s!"analyzer sample, budget {b}, depth {d}, 12 literals, 4 names, every kind, {n} mixed seeds from {first}" t
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["explore", b, d, n, first] =>
    let g := gAll b.toNat! d.toNat!
    let t0 ← IO.monoMsNow
    match exploreMixed (runOne g known) n.toNat! first.toNat! with
    | some c =>
      IO.println s!"== analyzer explore, budget {b}, depth {d}, seeds {first}+{n}: {describe c}"
      let s := shrink (runOne g known) c
      IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    | none => IO.println s!"== analyzer explore, budget {b}, depth {d}, seeds {first}+{n}: nothing"
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | _ => IO.println s!"analyzer: unknown arguments {args}"
end

section
open Jank.R3.Search.Reader Jank.ReaderSearch Jank.LexBytes Jank.ReadValue

def alphaOf : String → List Nat
  | "numbers" => alphaNumbers
  | "strings" => alphaStrings
  | "strings-nonul" => alphaStrings.filter (· != 0)
  | "chars" => alphaChars
  | "symbols" => alphaSymbols
  | "delims" => alphaDelims
  | "numbers2" => codesOf "0178aefxXEM.N/-r "
  | "chars2" => codesOf "\\uUo0789fFxspacenwlrbt"
  | "strings2" => codesOf "\"\\u0789abfnrtUx"
  | "symbols2" => codesOf ":/a.#%'`~@&*+-!?<>=_1 "
  | "delims2" => codesOf "()[]{}#_'`~@^;,\"1a: "
  | "dispatch" => codesOf "#?!=<_'\"^{}()[]:a1 "
  | "symbolic" => codesOf "#IinfNa- "
  | s => codesOf s

def rdRun (args : List String) : IO Unit := do
  match args with
  | ["total5", b] =>
    let _ ← Jank.R3.Search.report s!"read is total without NUL: byte strings of length 5 starting with byte #{b} of {(totalBytes.filter (· != 0)).length}" (runW (totalNoNul 5)) 0 3000000 #[5, b.toNat!]
  | ["census", a, len] =>
    let alpha := alphaOf a
    let t0 ← IO.monoMsNow
    let c := censusUnder (censusWorld alpha len.toNat!) #[] 400000000
    printCensus s!"reader agreement, every string of length ≤ {len} over {showCodes alpha} (classes: round 2's R n; unexplained; accepts invalid counted)" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["census-range", a, len, lo, hi] =>
    let alpha := alphaOf a
    for k in [lo.toNat!:hi.toNat! + 1] do
      let t0 ← IO.monoMsNow
      let c := censusUnder (censusWorld alpha len.toNat!) #[len.toNat!, k] 60000000
      printCensus s!"reader agreement, strings of length {len} over {showCodes alpha} starting with character #{k}" c
      IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
      (← IO.getStdout).flush
  | ["total5-range", lo, hi] =>
    for b in [lo.toNat!:hi.toNat! + 1] do
      let _ ← Jank.R3.Search.report s!"read is total without NUL: byte strings of length 5 starting with byte #{b} of {(totalBytes.filter (· != 0)).length}" (runW (totalNoNul 5)) 0 3000000 #[5, b]
      (← IO.getStdout).flush
  | ["census", a, len, first] =>
    let alpha := alphaOf a
    let t0 ← IO.monoMsNow
    let c := censusUnder (censusWorld alpha len.toNat!) #[len.toNat!, first.toNat!] 60000000
    printCensus s!"reader agreement, strings of length {len} over {showCodes alpha} starting with character #{first}" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["residual", a, len] =>
    let alpha := alphaOf a
    let _ ← Jank.R3.Search.report s!"reader residual: strings ≤ {len} over {showCodes alpha}, R1–R22 explained and set aside" (strict alpha len.toNat!) 0 60000000
  | ["sq-part", splice, depth, k, bound] =>
    let o : SQOpts := { depth := depth.toNat!, setSplice := splice == "set", syms := sqResidualSyms }
    let t0 ← IO.monoMsNow
    let c := censusUnder (runW (sqBody o)) #[k.toNat!] bound.toNat!
    printCensus s!"syntax quote, depth {depth}, symbols without dots and `new` (R19 first part aside), set-literal splice {splice}, top kind {k}" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["sq-size", splice, depth] =>
    let o : SQOpts := { depth := depth.toNat!, setSplice := splice == "set", syms := sqResidualSyms }
    let (e, decs) := estimate (fun s => { (runW (sqBody o) s) with violation := none }) 4000
    IO.println s!"== syntax quote world, depth {depth}, set splice {splice}: about {fmtFloat e} timelines ({fmtFloat decs} decisions on average)"
  | ["sq", splice, depth] =>
    let o : SQOpts := { depth := depth.toNat!, setSplice := splice == "set", syms := sqResidualSyms }
    let _ ← Jank.R3.Search.report s!"syntax quote, depth {depth}, symbols without dots and `new` (R19 first part aside), set-literal splice {splice}" (runW (sqBody o)) 3000 60000000
  | ["sq-all", depth] =>
    let o : SQOpts := { depth := depth.toNat! }
    let _ ← Jank.R3.Search.report s!"syntax quote, depth {depth}, every symbol and splice" (runW (sqBody o)) 3000 60000000
  | ["rt"] =>
    IO.println s!"== roundtrip, widened: (read-string (pr-str x)) with jank's printer and reader, {rtValues3.length} values × 2 double formats"
    let mut counts : List (String × Nat) := []
    let mut typeChanged := 0
    let mut total := 0
    for v in rtValues3 do
      for which in [0, 1] do
        total := total + 1
        let txt := Jank.ReadRoundtrip.jankPr which v
        let back := jankReadB txt
        let ok := match back with
          | .ok [w] => w == Jank.ReadRoundtrip.canon (flatNames v)
          | _ => false
        if !ok then
          let sameEq := match back with
            | .ok [w] => Jank.Read.jankEqual w v
            | _ => false
          let cls := if sameEq then "= holds, another type" else (rtExplain v).getD "UNEXPLAINED"
          counts := match counts.lookup cls with
            | some n => (cls, n + 1) :: counts.filter (·.1 != cls)
            | none => (cls, 1) :: counts
          if cls == "UNEXPLAINED" || cls == "= holds, another type" then
            IO.println s!"  {cls}: {v.show}: printed {showBytes txt}, read back {back.show}"
          if cls == "= holds, another type" then typeChanged := typeChanged + 1
    IO.println s!"  {total} printed texts; not read back, by class: {counts}"
  | _ => IO.println s!"reader: unknown arguments {args}"
end

section
open Jank.R3.Search.Core

def coreRun (args : List String) : IO Unit := do
  match args with
  | ["compare"] =>
    let t0 ← IO.monoMsNow
    let c := censusUnder (runW comparePair3) #[] 1000000
    printCensus s!"compare, every ordered pair of a {universe3.length}-value universe (round 2: 24 values)" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["sort", n] =>
    let t0 ← IO.monoMsNow
    let c := censusUnder (runW (sortVec3 n.toNat!)) #[] 60000000
    printCensus s!"sort, every vector of ≤ {n} of {sortAtoms3.length} atoms (round 2: ≤ 3 of 9)" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["sortfn", n] =>
    let t0 ← IO.monoMsNow
    let c := censusUnder (runW (sortFn3 n.toNat!)) #[] 60000000
    printCensus s!"sort with a comparator fn, every kind × every vector of ≤ {n} of {fnLongs3.length} longs (round 2: ≤ 3 of 5)" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["multi", d, m, p] =>
    let t0 ← IO.monoMsNow
    let c := censusUnder (multiCensusRun d.toNat! m.toNat! p.toNat!) #[] 200000000
    printCensus s!"multimethods: {d} derives, {m} defmethods, {p} prefer-methods, a call (4 tags); every disagreement is R100's walk" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["multi-order", d, m, p] =>
    let t0 ← IO.monoMsNow
    let c := censusUnder (orderRun d.toNat! m.toNat! p.toNat!) #[] 200000000
    printCensus s!"multimethods, Clojure's own dispatch under every order of the method table: {d} derives, {m} defmethods, {p} prefer-methods, a call" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["ns", n] =>
    let t0 ← IO.monoMsNow
    let c := censusUnder (nsFixedRun n.toNat!) #[] 60000000
    printCensus s!"namespaces (fork C's world): {n} operations in user, R102 and R103 replaced by Clojure's (round 2: 3)" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["nsextra", n] =>
    let t0 ← IO.monoMsNow
    let c := censusUnder (nsExtraRun n.toNat!) #[] 60000000
    printCensus s!"namespaces (def, ns reload, alias, find-var, ns-resolve, resolve, in-ns): {n} operations, the first disagreement named by its operation's class (round 2: 3, first finding only)" c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | _ => IO.println s!"core: unknown arguments {args}"
end

section
open Jank.R3.Search.Strings

def strRun (args : List String) : IO Unit := do
  match args with
  | ["table", n, m] =>
    let t0 ← IO.monoMsNow
    let t := tallyAll n.toNat! m.toNat!
    IO.println s!"== strings and characters (non-regex): every question with texts ≤ {n} code points over {Jank.Str.alphabet.length} code points, compare ≤ {m} × ≤ {m}, both locales (round 2: ≤ 3, compare ≤ 2)"
    IO.println s!"   {t.total} questions, {t.agree} agree; explained by round 2's classes: {t.byClass}; unexplained: {t.unexplainedCount}"
    for e in t.unexplained do IO.println s!"     unexplained: {e}"
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["print"] =>
    let (total, r69, un, ex) := printTable
    IO.println s!"== printing: str of {total} values of depth ≤ 3 (round 2: 130 of depth ≤ 2): {r69} differ by R69 (a collection holding a string or character), {un} unexplained"
    for e in ex do IO.println s!"     unexplained: {e}"
  | _ => IO.println s!"strings: unknown arguments {args}"
end

section
open Jank.R3.Search.Core2

def core2Run (args : List String) : IO Unit := do
  let timed := fun (label : String) (run : Source → Ended) (pfx : Array Nat) => do
    let t0 ← IO.monoMsNow
    let c := censusUnder run pfx 200000000
    printCensus label c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  match args with
  | ["smap", n, o] => timed s!"sorted map: (sorted-map …) of 0–{n} entries over {keyAtoms3.length} keys, every operation, the second map of `=` 0–{o} entries (round 2: 0–2 over 9)" (runS (mapBody3 n.toNat! o.toNat!)) #[]
  | ["sset", n, o] => timed s!"sorted set: (sorted-set …) of 0–{n} elements over {keyAtoms3.length} keys, every operation, the second set of `=` 0–{o} elements (round 2: 0–2 over 9)" (runS (setBody3 n.toNat! o.toNat!)) #[]
  | ["destr-size", b, v] =>
    let (e, decs) := estimate (fun s => { (destrRun b.toNat! v.toNat! false s) with violation := none }) 4000
    IO.println s!"== destructuring, forms nested {b}, values nested {v}: about {fmtFloat e} programs ({fmtFloat decs} decisions on average)"
  | ["destr-explore", b, v, n] =>
    let t0 ← IO.monoMsNow
    let strictRun := fun src => let e := destrRun b.toNat! v.toNat! false src
      match e.violation with
      | some ("unexplained", _) => e
      | _ => { e with violation := none }
    match exploreMixed strictRun n.toNat! with
    | some c => IO.println s!"== destructuring explore, forms nested {b}, values nested {v}, no trailing (seq m), {n} mixed seeds: {describe c}"
    | none => IO.println s!"== destructuring explore, forms nested {b}, values nested {v}, no trailing (seq m), R107's conj path set aside, {n} mixed seeds: nothing"
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  | ["destr", b, v, sq] =>
    timed s!"destructuring: (let [form 'value] [a b c]), forms nested {b}, values nested {v}, trailing (seq m) {sq}" (destrRun b.toNat! v.toNat! (sq == "with")) #[]
  | ["destr", b, v, sq, k] =>
    timed s!"destructuring: (let [form 'value] [a b c]), forms nested {b}, values nested {v}, trailing (seq m) {sq}, first decision {k}" (destrRun b.toNat! v.toNat! (sq == "with")) #[k.toNat!]
  | _ => IO.println s!"core2: unknown arguments {args}"
end

section
open Jank.R3.Search.Seq

def seqRun (args : List String) : IO Unit := do
  let timed := fun (label : String) (run : Source → Ended) => do
    let t0 ← IO.monoMsNow
    let c := censusUnder run #[] 200000000
    printCensus label c
    IO.println s!"  ({((← IO.monoMsNow) - t0) / 1000} s)"
  match args with
  | ["intrange"] => timed s!"integer range: every call of 1–3 arguments over {interesting3.length} values, {fuel3} elements and count (round 2: 17 values, 8 elements)" intRun
  | ["range"] => timed s!"real-end range: {starts3.length} starts × {steps3.length} steps × {offsets3.length} end offsets, 80 elements (round 2: 8 × 6 × 10)" realRun
  | ["transducers", x, l] => timed s!"transducers: pipelines of 1–{x} of 15, inputs of length ≤ {l} over 0..2, 3 reducing fns (round 2: 1–2, ≤ 3, table)" (tdRun x.toNat! l.toNat!)
  | ["chunked"] =>
    let (total, r119, un, ex) := chunkedTable
    IO.println s!"== chunked seqs: (first (map f … (range 0.0 n))) for n in 0..200, map depth 1–4 ({total} programs; round 2: 8 lengths × 2 depths): {r119} R119 (more calls of f than Clojure), {un} unexplained"
    for e in ex do IO.println s!"     unexplained: {e}"
  | _ => IO.println s!"seq: unknown arguments {args}"
end

def main (args : List String) : IO UInt32 := do
  match args with
  | "seq" :: rest => seqRun rest
  | "core2" :: rest => core2Run rest
  | "analyzer" :: rest => anRun rest
  | "reader" :: rest => rdRun rest
  | "core" :: rest => coreRun rest
  | "strings" :: rest => strRun rest
  | _ => IO.println s!"unknown search {args}"
  return 0

end Run.R3.Search

def main (args : List String) : IO UInt32 := Run.R3.Search.main args

import Jank.R4.Nrepl.Seg
import Jank.R4.Nrepl.Grammars
import Jank.R4.Nrepl.Pos
import Jank.R4.Nrepl.Term
import Jank.R4.Nrepl.Theorems

/-!
# Round 4 driver: nREPL

`jank4-nrepl t-estimate <scenario> <budget> <probes>`: Knuth's size estimate of a World T tree.
`jank4-nrepl t-seg <scenario> <budget> <seconds> [path,...]`: a census segment from a resume path.
`jank4-nrepl s-census <grammar> <repl|load> <aside> <len> <maxRuns> [prefix,...]`: World S (round 4
copy of round 3's, with `try`, `binding` and loops) census.
`jank4-nrepl pos-census <maxLen>`: the line/column counters of jank and Clojure over every code
string up to `maxLen` characters and every request (line, column).
-/

open Determinismo Jank.R4.Nrepl

def flushOut : IO Unit := do (← IO.getStdout).flush

def parsePath (p : String) : Array Nat :=
  ((p.splitOn ",").filter (· != "")).map String.toNat! |>.toArray

def showPath (p : Array Nat) : String := ",".intercalate (p.toList.map toString)

def tRunner (k budget : Nat) : Option (String × (Source → Ended) × (Array Nat → Array String)) :=
  match Jank.R3.Nrepl.tScenarios[k]? with
  | some s => some (s.name, fun src => (Jank.R3.Nrepl.runTWith (some budget) s.cfg s.aside s.scripts src).1,
                    fun t => (Jank.R3.Nrepl.runTWith (some budget) s.cfg s.aside s.scripts (Source.path t)).2.log)
  | none => none

def tEstimate (k budget probes : Nat) : IO Unit := do
  let some (name, run, _) := tRunner k budget | IO.println "no scenario"
  let t0 ← IO.monoMsNow
  let (mean, lo, hi) := Seg.estimate run probes
  IO.println s!"== Knuth estimate, ≤ {budget} preemptions: {name}"
  IO.println s!"  {probes} random paths (mixed seeds): mean {mean} timelines (min {lo}, max {hi})"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

/-- A census segment: every timeline from `start` on, in `nextPath` order, until the end of the
tree or the deadline (checked every 500 timelines). -/
def segment (run : Source → Ended) (start : Array Nat) (deadlineMs : Nat) : IO Seg.SegOut := do
  let t0 ← IO.monoMsNow
  let mut path := start
  let mut c : Seg.SegOut := {}
  for i in [0:1000000000] do
    if i % 500 == 0 && (← IO.monoMsNow) - t0 > deadlineMs then
      return { c with next := some path }
    let o := run (Source.path path)
    c := { c with runs := i + 1 }
    if let some (p, d) := o.violation then
      let counts := match c.counts.lookup p with
        | some n => (p, n + 1) :: c.counts.filter (·.1 != p)
        | none => (p, 1) :: c.counts
      let examples := if (c.examples.lookup p).isSome then c.examples else c.examples ++ [(p, d)]
      let tapes := if (c.tapes.lookup p).isSome then c.tapes else c.tapes ++ [(p, o.taken.map (·.value))]
      c := { c with counts, examples, tapes }
    match nextPath o.taken with
    | none => return { c with complete := true }
    | some q => path := q
  return { c with next := some path }

def tSeg (k budget secs : Nat) (start : Array Nat) : IO Unit := do
  let some (name, run, replay) := tRunner k budget | IO.println "no scenario"
  let t0 ← IO.monoMsNow
  IO.println s!"== World T census segment, ≤ {budget} preemptions: {name}"
  IO.println s!"  start {showPath start}"
  let c ← segment run start (secs * 1000)
  IO.println s!"  {c.runs} timelines; {if c.complete then "END OF TREE" else "stopped (deadline)"}"
  if let some n := c.next then IO.println s!"  NEXT {showPath n}"
  for (p, n) in c.counts.reverse do
    IO.println s!"  {p}: {n}"
    if let some d := c.examples.lookup p then IO.println s!"      e.g. {d}"
    if let some t := c.tapes.lookup p then
      IO.println s!"      path {showPath t}"
      for l in replay t do IO.println s!"        {l}"
  if c.counts.isEmpty then IO.println "  nothing"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut


/-! ## World S (round 4 copy) -/

def modeOf (s : String) : SpecMode := if s == "load" then .loadString else .repl

def asideOf (s : String) : Aside :=
  let has (k : String) := (s.splitOn k).length > 1 || (s.splitOn "all").length > 1
  let v : Variant := { noTopDoSplit := has "topdo", inNsNil := has "inns", nsPrintName := has "nsprint",
                       printOutLost := has "printlost" }
  { blankOut := has "blank", sessions := has "sessions", lookupKnown := has "lookups", variant := v,
    lookupFallback := has "fallback", loadNs := has "loadns" }

def sCensus (g : Grammar) (mode : SpecMode) (aside : Aside) (len maxRuns : Nat) (pre : Array Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let g := { g with len }
  IO.println s!"== World S census {g.name} mode={repr mode} aside={repr aside} len={len} prefix={pre} max {maxRuns}"
  let c := censusS g mode aside maxRuns pre
  IO.println s!"  {if c.complete then "complete" else "stopped"} at {c.runs} timelines; outside the model: {c.outside} {c.outsideEx}"
  for (p, n) in c.counts.reverse do
    IO.println s!"  {p}: {n}"
    if let some d := c.examples.lookup p then IO.println s!"      e.g. {d}"
    if let some t := c.tapes.lookup p then
      IO.println s!"      path {showPath t}; story:"
      for l in (runS g mode aside (Source.path t)).2.log do IO.println s!"        {l}"
  if c.counts.isEmpty then IO.println "  nothing"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

/-- One timeline's story (a path of decisions). -/
def sStory (g : Grammar) (mode : SpecMode) (aside : Aside) (len : Nat) (path : Array Nat) : IO Unit := do
  let g := { g with len }
  let (o, w) := runS g mode aside (Source.path path)
  IO.println s!"== story {g.name} {showPath path}: {o.violation}"
  for l in w.log do IO.println s!"    {l}"
  flushOut

/-! ## line/column: jank's lexer against Clojure's reader -/

/-- Every code string over `( ) a space \n \r é 😀` up to `maxLen` characters, every request
(line, column) in {1, 7} × {1, 4}: where the two sides place each list's `(`. Classes by what
precedes the first disagreeing `(`. -/
def posCensus (maxLen : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let alpha : List Char := ['(', ')', 'a', ' ', '\n', '\r', 'é', '😀']
  let mut strs : List String := [""]
  let mut all : List String := []
  for _ in [0:maxLen] do
    strs := strs.flatMap fun s => alpha.map fun c => s.push c
    all := all ++ strs
  let mut runs := 0
  let mut agree := 0
  let mut counts : List (String × Nat) := []
  let mut examples : List (String × String) := []
  let mut metaDiffer := 0
  for code in all do
    for line in [1, 7] do
      for col in [1, 4] do
        let start : Pos.P := { line, col }
        runs := runs + 1
        let ls := Pos.listStarts start code
        if !ls.isEmpty then metaDiffer := metaDiffer + 1
        match ls.find? (fun (j, c) => j != c) with
        | none => agree := agree + 1
        | some (j, c) =>
          let cls :=
            if code.toList.contains '\r' && j.line != c.line then "CR ends a line on Clojure only"
            else if code.toList.any (·.toNat ≥ 0x80) then "non-ASCII: jank counts bytes, Clojure UTF-16 units"
            else "UNEXPLAINED"
          counts := match counts.lookup cls with
            | some n => (cls, n + 1) :: counts.filter (·.1 != cls)
            | none => (cls, 1) :: counts
          if (examples.lookup cls).isNone then
            examples := examples ++ [(cls, s!"code {repr code} start ({line},{col}): jank ({j.line},{j.col}) Clojure ({c.line},{c.col})")]
  IO.println s!"== line/column census: {all.length} code strings ≤ {maxLen} chars × 4 starts = {runs}, complete"
  IO.println s!"  every list: (:line (meta form)) jank nil, Clojure its line: {metaDiffer} inputs with a list"
  IO.println s!"  :jank/source positions agree with Clojure's: {agree}"
  for (k, n) in counts.reverse do
    IO.println s!"  {k}: {n}"
    if let some e := examples.lookup k then IO.println s!"      e.g. {e}"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut


/-! ## The terminal REPL -/

/-- Every sequence of `k` lines from `termLines`: what the REPL shows, jank against
clojure.main/repl. A mismatch is labelled by the triggers it holds (the first that applies):
`split` (a line holding half a form), `*e` (an error, then `(nil? *e)`), `forms` (a line of several
forms, or a closer after a form: REPORT-3 S75's terminal side). -/
def termCensus (k : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let mut seqs : List (List String) := [[]]
  for _ in [0:k] do
    seqs := seqs.flatMap fun xs => termLines.map fun l => xs ++ [l]
  let mut counts : List (String × Nat) := []
  let mut examples : List (String × String) := []
  let mut outside := 0
  let mut agree := 0
  for ls in seqs do
    let (j, ju) := jankTerm ls
    let (c, cu) := cljTerm ls
    if ju.isSome || cu.isSome then outside := outside + 1; continue
    if j == c then agree := agree + 1; continue
    -- a line holding half a form, followed by another line: Clojure reads on across the lines
    let hasSplit := match ls.findIdx? (· == "(+ a") with
      | some i => decide (i + 1 < ls.length)
      | none => false
    -- `*e` only: the same shows, except a `(nil? *e)` line's value
    let onlyE := j.length == c.length && ((j.zip c).zip (ls.filter fun l => !l.trimAscii.toString.isEmpty && l != ";; c")).all
      fun ((a, b), _) => a == b || (a == .value "true" && b == .value "false")
    let errIdx := ls.findIdx? (· == "(throw (ex-info \"e\" {}))")
    let eAfter := match errIdx with
      | some i => (ls.drop (i + 1)).contains "(nil? *e)"
      | none => false
    let multi := ls.contains "1 2"
    let _ := eAfter
    let cls := if hasSplit then "E4 a form spanning lines: each line is read alone"
      else if onlyE then "E3 *e is never set by the terminal REPL"
      else if multi || ls.contains " 2)" then "S75 (terminal) one input, one value: several forms (or a form and a stray closer) on a line"
      else "UNEXPLAINED"
    counts := match counts.lookup cls with
      | some n => (cls, n + 1) :: counts.filter (·.1 != cls)
      | none => (cls, 1) :: counts
    if (examples.lookup cls).isNone then
      examples := examples ++ [(cls, s!"lines {repr ls}: jank {repr j}; Clojure {repr c}")]
  IO.println s!"== terminal REPL census: {seqs.length} sequences of {k} lines, complete"
  IO.println s!"  agree {agree}; outside the model {outside}"
  for (cl, n) in counts.reverse do
    IO.println s!"  {cl}: {n}"
    if let some e := examples.lookup cl then IO.println s!"      e.g. {e}"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

def main (args : List String) : IO UInt32 := do
  match args with
  | ["t-estimate", k, b, probes] => tEstimate k.toNat! b.toNat! probes.toNat!
  | ["t-seg", k, b, secs] => tSeg k.toNat! b.toNat! secs.toNat! #[]
  | ["t-seg", k, b, secs, p] => tSeg k.toNat! b.toNat! secs.toNat! (parsePath p)
  | "s-census" :: gn :: m :: a :: len :: maxRuns :: rest =>
    let pre := match rest with
      | [p] => parsePath p
      | _ => #[]
    match grammar? gn with
    | some g => sCensus g (modeOf m) (asideOf a) len.toNat! maxRuns.toNat! pre
    | none => IO.println s!"no grammar {gn}"
  | ["s-story", gn, m, a, len, p] =>
    match grammar? gn with
    | some g => sStory g (modeOf m) (asideOf a) len.toNat! (parsePath p)
    | none => IO.println s!"no grammar {gn}"
  | ["pos-census", n] => posCensus n.toNat!
  | ["term-census", k] => termCensus k.toNat!
  | _ => IO.println "usage: jank4-nrepl t-estimate|t-seg|s-census|s-story|pos-census ..."
  return 0

import Jank.R3.Nrepl.Search
import Jank.R3.Nrepl.ThreadSearch

/-!
# Round 3 driver: nREPL evaluation wired to the reader, analyzer and evaluator replicas

`jank3-nrepl s-explore <grammar> <repl|load> <aside> <seeds> [first]`
`jank3-nrepl s-census <grammar> <repl|load> <aside> <len> <maxRuns> [prefix,...]`
where `<aside>` is `none`, `blank`, `sessions` or `blank+sessions`.
-/

open Determinismo Jank.R3.Nrepl

def modeOf (s : String) : SpecMode := if s == "load" then .loadString else .repl

/-- `none`, or `+`-joined flags: `blank` (R136), `sessions` (R127), `lookups` (R111/R131/R138),
`topdo` (N1), `inns` (R112), `nsprint`, `all`. -/
def asideOf (s : String) : Aside :=
  let has (k : String) := (s.splitOn k).length > 1 || (s.splitOn "all").length > 1
  let v : Variant := { noTopDoSplit := has "topdo", inNsNil := has "inns", nsPrintName := has "nsprint",
                       printOutLost := has "printlost" }
  { blankOut := has "blank", sessions := has "sessions", lookupKnown := has "lookups", variant := v,
    lookupFallback := has "fallback", loadNs := has "loadns" }

def flushOut : IO Unit := do (← IO.getStdout).flush

def story (lines : Array String) : IO Unit := do
  for l in lines do IO.println s!"      {l}"

def sExplore (g : Grammar) (mode : SpecMode) (aside : Aside) (seeds first : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let run := fun src => (runS g mode aside src).1
  IO.println s!"== World S explore {g.name} mode={repr mode} aside={repr aside} len={g.len} seeds {first}..{first + seeds - 1}"
  match exploreMixed run seeds first with
  | some c =>
    IO.println s!"  found after {c.runs} timelines: {c.property}"
    IO.println s!"    {c.detail}"
    let c := shrink run c
    IO.println s!"  shrunk to {c.taken.size} decisions: {c.detail}"
    IO.println s!"  tape:"
    for l in (tape c.taken).splitOn "\n" do IO.println s!"      {l}"
    IO.println "  story:"
    story (runS g mode aside (Source.path c.values)).2.log
  | none => IO.println s!"  nothing in {seeds} timelines"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

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
      IO.println s!"      path {",".intercalate (t.toList.map toString)}; story:"
      story ((runS g mode aside (Source.path t)).2.log.map ("  " ++ ·))
  if c.counts.isEmpty then IO.println "  nothing"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

/-- `censusRun` in IO with a wall-clock deadline: a run that would outlast its job's alarm stops and
says so (with its count) instead of being killed silently. -/
def censusIO (run : Source → Ended) (maxRuns : Nat) (pre : Array Nat) (deadlineMs : Nat := 1150000) : IO Census := do
  let t0 ← IO.monoMsNow
  let mut path : Array Nat := pre
  let mut c : Census := {}
  for i in List.range maxRuns do
    if i % 1000 == 0 && (← IO.monoMsNow) - t0 > deadlineMs then
      IO.println s!"  (time limit after {i} timelines)"
      return c
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
    | some q =>
      if q.size < pre.size || (q.extract 0 pre.size) != pre then return { c with complete := true }
      path := q
  return c

/-- An exact partition of a search tree: the all-zero timeline, and for each decision `i` of it in
`[i0, i1)` and each value `j ≥ 1`, the subtree under the prefix `0^i j`. The union over all `i`
is the whole tree; each part is a complete census or says it stopped. -/
def partitionCensus (run : Source → Ended) (i0 i1 maxRuns : Nat) (deadlineMs : Nat := 1150000) : IO (Census × Nat) := do
  let t0 ← IO.monoMsNow
  let base := run (Source.path #[])
  let mut total : Census := { complete := true }
  let addOne (c : Census) (p : String) (d : String) (t : Array Nat) : Census :=
    let counts := match c.counts.lookup p with
      | some n => (p, n + 1) :: c.counts.filter (·.1 != p)
      | none => (p, 1) :: c.counts
    let examples := if (c.examples.lookup p).isSome then c.examples else c.examples ++ [(p, d)]
    let tapes := if (c.tapes.lookup p).isSome then c.tapes else c.tapes ++ [(p, t)]
    { c with counts, examples, tapes }
  if i0 == 0 then
    total := { total with runs := 1 }
    if let some (p, d) := base.violation then total := addOne total p d (base.taken.map (·.value))
  let n := base.taken.size
  let mut parts := 0
  for i in [i0:min i1 n] do
    let opts := base.taken[i]!.options
    for j in [1:opts] do
      let elapsed := (← IO.monoMsNow) - t0
      if elapsed > deadlineMs then
        IO.println s!"  (time limit at decision {i}, value {j})"
        return ({ total with complete := false }, n)
      let pre := (Array.replicate i 0).push j
      let c ← censusIO run maxRuns pre (deadlineMs - elapsed)
      parts := parts + 1
      total := { total with runs := total.runs + c.runs, complete := total.complete && c.complete }
      for (p, k) in c.counts do
        let cur := (total.counts.lookup p).getD 0
        total := { total with counts := (p, cur + k) :: total.counts.filter (·.1 != p)
                              examples := if (total.examples.lookup p).isSome then total.examples else total.examples ++ (c.examples.filter (·.1 == p))
                              tapes := if (total.tapes.lookup p).isSome then total.tapes else total.tapes ++ (c.tapes.filter (·.1 == p)) }
  IO.println s!"  partition: decisions {i0}..{min i1 n} of {n} on the all-zero timeline ({parts} subtrees)"
  return (total, n)

def printCensus (c : Census) (replay : Array Nat → Array String) : IO Unit := do
  IO.println s!"  {if c.complete then "complete" else "stopped"} at {c.runs} timelines"
  for (p, n) in c.counts.reverse do
    IO.println s!"  {p}: {n}"
    if let some d := c.examples.lookup p then IO.println s!"      e.g. {d}"
    if let some t := c.tapes.lookup p then
      IO.println s!"      path {",".intercalate (t.toList.map toString)}; story:"
      story ((replay t).map ("  " ++ ·))
  if c.counts.isEmpty then IO.println "  nothing"
  flushOut

def tExplore (k seeds : Nat) : IO Unit := do
  let some s := tScenarios[k]? | IO.println "no scenario"
  let t0 ← IO.monoMsNow
  let run := fun src => (runTWith none s.cfg s.aside s.scripts src).1
  IO.println s!"== World T explore (random schedules) {s.name}: {seeds} seeds"
  match exploreMixed run seeds with
  | some c =>
    IO.println s!"  found after {c.runs} timelines: {c.property}: {c.detail}"
    let c := shrink run c
    IO.println s!"  shrunk to {c.taken.size} decisions: {c.detail}"
    IO.println "  tape:"
    for l in (tape c.taken).splitOn "\n" do IO.println s!"      {l}"
    IO.println "  story:"
    story (runTWith none s.cfg s.aside s.scripts (Source.path c.values)).2.log
  | none => IO.println s!"  nothing in {seeds} timelines"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

def tExhaust (k budget maxRuns : Nat) (pre : Array Nat) : IO Unit := do
  let some s := tScenarios[k]? | IO.println "no scenario"
  let t0 ← IO.monoMsNow
  let run := fun src => (runTWith (some budget) s.cfg s.aside s.scripts src).1
  IO.println s!"== World T census, ≤ {budget} preemptions from round robin: {s.name} prefix={pre}"
  printCensus (← censusIO run maxRuns pre) fun t => (runTWith (some budget) s.cfg s.aside s.scripts (Source.path t)).2.log
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"

def r2Control (k budget maxRuns : Nat) (pre : Array Nat) (whole : Bool := false) : IO Unit := do
  let some s := r2Controls[k]? | IO.println "no scenario"
  let s := if whole then { s with cfg := { s.cfg with partialReads := false } } else s
  let t0 ← IO.monoMsNow
  IO.println s!"== round 2 scenario on round 2's model, ≤ {budget} preemptions from round robin{if whole then ", whole-message reads" else ""}: {s.name} prefix={pre}"
  printCensus (← censusIO (runR2PB s budget) maxRuns pre) fun _ => #[]
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"

/-- Round 2's scenario with round 2's own (unbounded) scheduler, census to completion. -/
def r2Full (k maxRuns : Nat) (pre : Array Nat) : IO Unit := do
  let some s := r2Controls[k]? | IO.println "no scenario"
  let t0 ← IO.monoMsNow
  IO.println s!"== round 2 scenario on round 2's model, every interleaving (Determinismo.interleave): {s.name} prefix={pre}"
  printCensus (← censusIO s.run maxRuns pre) fun _ => #[]
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"

/-- World T scenario with the unbounded scheduler, census. -/
def tFull (k maxRuns : Nat) (pre : Array Nat) : IO Unit := do
  let some s := tScenarios[k]? | IO.println "no scenario"
  let t0 ← IO.monoMsNow
  let run := fun src => (runTWith none s.cfg s.aside s.scripts src).1
  IO.println s!"== World T census, every interleaving: {s.name} prefix={pre}"
  printCensus (← censusIO run maxRuns pre) fun t => (runTWith none s.cfg s.aside s.scripts (Source.path t)).2.log
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"

def tRange (k budget i0 i1 maxRuns : Nat) : IO Unit := do
  let some s := tScenarios[k]? | IO.println "no scenario"
  let t0 ← IO.monoMsNow
  let run := fun src => (runTWith (some budget) s.cfg s.aside s.scripts src).1
  IO.println s!"== World T census, ≤ {budget} preemptions from round robin, partition {i0}..{i1}: {s.name}"
  let (c, _) ← partitionCensus run i0 i1 maxRuns
  printCensus c fun t => (runTWith (some budget) s.cfg s.aside s.scripts (Source.path t)).2.log
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"

def r2Range (k budget i0 i1 maxRuns : Nat) : IO Unit := do
  let some s := r2Controls[k]? | IO.println "no scenario"
  let t0 ← IO.monoMsNow
  IO.println s!"== round 2 scenario on round 2's model, ≤ {budget} preemptions from round robin, partition {i0}..{i1}: {s.name}"
  let (c, _) ← partitionCensus (runR2PB s budget) i0 i1 maxRuns
  printCensus c fun _ => #[]
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"

def parsePre (rest : List String) : Array Nat :=
  match rest with
  | [p] => ((p.splitOn ",").filter (· != "")).map String.toNat! |>.toArray
  | _ => #[]

def main (args : List String) : IO UInt32 := do
  match args with
  | ["t-explore", k, seeds] => tExplore k.toNat! seeds.toNat!
  | "t-exhaust" :: k :: b :: maxRuns :: rest => tExhaust k.toNat! b.toNat! maxRuns.toNat! (parsePre rest)
  | "r2-control" :: k :: b :: maxRuns :: rest => r2Control k.toNat! b.toNat! maxRuns.toNat! (parsePre rest)
  | "r2-whole" :: k :: b :: maxRuns :: rest => r2Control k.toNat! b.toNat! maxRuns.toNat! (parsePre rest) true
  | "r2-full" :: k :: maxRuns :: rest => r2Full k.toNat! maxRuns.toNat! (parsePre rest)
  | "t-full" :: k :: maxRuns :: rest => tFull k.toNat! maxRuns.toNat! (parsePre rest)
  | ["t-range", k, b, i0, i1] => tRange k.toNat! b.toNat! i0.toNat! i1.toNat! 3000000
  | ["r2-range", k, b, i0, i1] => r2Range k.toNat! b.toNat! i0.toNat! i1.toNat! 3000000
  | ["r2-list"] => for (s, i) in r2Controls.zipIdx do IO.println s!"{i}: {s.name}"
  | ["t-list"] => for (s, i) in tScenarios.zipIdx do IO.println s!"{i}: {s.name}"
  | ["s-explore", gn, m, a, seeds] | ["s-explore", gn, m, a, seeds, _] =>
    let first := (args.getD 5 "0").toNat!
    match grammar? gn with
    | some g => sExplore g (modeOf m) (asideOf a) seeds.toNat! first
    | none => IO.println s!"no grammar {gn}"
  | "s-census" :: gn :: m :: a :: len :: maxRuns :: rest =>
    let pre := match rest with
      | [p] => ((p.splitOn ",").filter (· != "")).map String.toNat! |>.toArray
      | _ => #[]
    match grammar? gn with
    | some g => sCensus g (modeOf m) (asideOf a) len.toNat! maxRuns.toNat! pre
    | none => IO.println s!"no grammar {gn}"
  | _ => IO.println "usage: jank3-nrepl s-explore|s-census ..."
  return 0

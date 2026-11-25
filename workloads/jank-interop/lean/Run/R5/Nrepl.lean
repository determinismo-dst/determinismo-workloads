import Jank.R5.Nrepl.Reduce
import Jank.R5.Nrepl.Interrupt
import Jank.R5.Nrepl.ParseK

/-!
# Round 5 driver: the nREPL (`jank5-nrepl <part> ...`)

- `t7-bytes`: T7's request bytes (`specEncode ∘ tReqMap`) against `Chunk.t7Msgs`, and the hypotheses
  of `chunking_independent` on every prefix, both `char` signednesses.
- `whole <budget> <seconds> [path]`: a census segment of T7 with whole-message reads (the reduced
  world), every timeline's final-state fingerprint collected.
- `stutter <budget> <seconds>`: the reduced world walked with every reachable pre-read state checked
  by `stutterCheck` (every split point, every chunk length).
- `cuts <budget> <cuts> <seconds>`: round 3's T7 itself (partial reads) walked completely among the
  timelines with at most `cuts` partial reads, each final state compared with the reduced world's.
- `estimate <budget> <probes> <whole|chunked>`: Knuth's estimate of either world's size.
- `interrupt`: World I, the interrupt op (Interrupt.lean).
-/

open Determinismo Jank.R3.Nrepl Jank.R5.Nrepl Jank.NreplServer

def flushOut : IO Unit := do (← IO.getStdout).flush

def parsePath (p : String) : Array Nat :=
  ((p.splitOn ",").filter (· != "")).map String.toNat! |>.toArray

def showPath (p : Array Nat) : String := ",".intercalate (p.toList.map toString)

def t7Script : List TReq := t7.scripts.headD []

def t7Bytes : IO Unit := do
  let c0 : TClient := { cid := 0, script := t7Script.toArray }
  let c1 : TClient := { c0 with sessions := #["uuid-0"] }
  let mut k := 0
  let mut ms : List Bytes := []
  for r in t7Script do
    let c := if k == 0 then c0 else c1
    let (msg, _) := tReqMap c (tReqId 0 k) r
    ms := ms ++ [(specEncode msg).getD []]
    k := k + 1
  IO.println s!"== T7's requests (specEncode ∘ tReqMap) equal Chunk.t7Msgs: {ms == t7Msgs}"
  for m in ms do IO.println s!"  {m.length} bytes: {showBytes m}"
  for (name, p) in [("signed char", ({} : Platform)), ("unsigned char", { signedChar := false })] do
    let prefixes := ms.foldl (fun n m => n + m.length) 0
    IO.println s!"  {name}: every message nonempty, its {prefixes} proper prefixes parse to nil, it parses whole: {hypsHold p ms}"
  flushOut

/-- The first index at which a decision named in `names` took a nonzero value. -/
def firstNonzero (names : List String) (taken : Array Taken) : Option Nat := Id.run do
  for i in [0:taken.size] do
    let t := taken[i]!
    if names.contains t.name && t.value != 0 then return some i
  return none

def minOpt : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- A census segment with final fingerprints. -/
def walk (run : Source → Ended × Process TMem TTh) (start : Array Nat) (deadlineMs : Nat)
    (cuts : Option Nat := none) (zeroNames : List String := []) : IO (Walk × Nat) := do
  let t0 ← IO.monoMsNow
  let mut path := start
  let mut w : Walk := {}
  let mut pruned := 0
  for i in [0:1000000000] do
    if i % 200 == 0 && (← IO.monoMsNow) - t0 > deadlineMs then
      return ({ w with next := some path }, pruned)
    let (o, p) := run (Source.path path)
    let over := minOpt (match cuts with
      | some c => overCut c o.taken
      | none => none) (firstNonzero zeroNames o.taken)
    match over with
    | some j =>
      pruned := pruned + 1
      match nextPath (o.taken.extract 0 (j + 1)) with
      | none => return ({ w with complete := true }, pruned)
      | some q => path := q
    | none =>
      w := { w.record o (fpMem p.memory) with runs := w.runs + 1 }
      match nextPath o.taken with
      | none => return ({ w with complete := true }, pruned)
      | some q => path := q
  return ({ w with next := some path }, pruned)

def printWalk (w : Walk) : IO Unit := do
  IO.println s!"  {w.runs} timelines; {if w.complete then "END OF TREE (complete)" else "stopped (deadline)"}"
  if let some n := w.next then IO.println s!"  NEXT {showPath n}"
  for (p, n) in w.counts.reverse do
    IO.println s!"  {p}: {n}"
    if let some d := w.examples.lookup p then IO.println s!"      e.g. {d}"
    if let some t := w.tapes.lookup p then IO.println s!"      path {showPath t}"
  if w.counts.isEmpty then IO.println "  violations: nothing"
  IO.println s!"  distinct final states: {w.finals.length}"
  for (fp, n) in w.finals do
    IO.println s!"    {n} timelines end in: {(fp.take 600)}{if fp.length > 600 then "…" else ""}"

def wholeCmd (budget secs : Nat) (start : Array Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"== T7 with whole-message reads (the reduced world), ≤ {budget} preemptions"
  IO.println s!"  start {showPath start}"
  let (w, _) ← walk (runT budget t7Whole) start (secs * 1000)
  printWalk w
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

/-- The whole-read world with every `net.read.eintr` decision held at 0. Round 3's `tConnStep` draws
that decision whenever a read finds the inbox empty, even with `eintr` off: Lean lifts the
`(← decideRare …)` in `m.cfg.eintr && (← decideRare …)` (Threads.lean 251) out of the `&&`, and with
`eintr` false its value is never used. A timeline that differs only in such a value is the same
timeline step for step, so holding it at 0 loses nothing. -/
def whole0Cmd (budget secs : Nat) (start : Array Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"== T7 with whole-message reads, `net.read.eintr` (unused with eintr off) held at 0, ≤ {budget} preemptions"
  IO.println s!"  start {showPath start}"
  let (w, pruned) ← walk (runT budget t7Whole) start (secs * 1000) none ["net.read.eintr"]
  IO.println s!"  ({pruned} runs that drew `net.read.eintr` = 1 skipped with their subtrees)"
  printWalk w
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

def stutterCmd (budget secs : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"== Stutter checks at every reachable pre-read state of the reduced world, ≤ {budget} preemptions"
  let mut path : Array Nat := #[]
  let mut runs := 0
  let mut seen : Std.HashSet String := {}
  let mut checked := 0
  let mut stepRuns := 0
  let mut failures : List String := []
  let mut complete := false
  for _ in [0:1000000000] do
    if (← IO.monoMsNow) - t0 > secs * 1000 then break
    let (o, _, snaps) := runTObs budget t7Whole (Source.path path)
    runs := runs + 1
    for (t, c, p) in snaps do
      let key := s!"{t}|{fpConn c}|{fpMem p.memory}"
      if !seen.contains key then
        seen := seen.insert key
        checked := checked + 1
        match stutterCheck t c p with
        | .ok n => stepRuns := stepRuns + n
        | .error e => failures := failures ++ [s!"{e} (state {key.take 300})"]
    match nextPath o.taken with
    | none => complete := true; break
    | some q => path := q
  IO.println s!"  {runs} timelines walked; {if complete then "complete" else s!"stopped, NEXT {showPath path}"}"
  IO.println s!"  {checked} distinct pre-read states checked, {stepRuns} step runs of tConnStep"
  if failures.isEmpty then IO.println "  every incomplete read and its `.top none` kept α; every completing read gave the whole read's state"
  else for f in failures.take 10 do IO.println s!"  FAIL {f}"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

def cutsCmd (budget cuts secs : Nat) (start : Array Nat := #[]) : IO Unit := do
  let t0 ← IO.monoMsNow
  IO.println s!"== T7 (partial reads) with at most {cuts} partial reads, ≤ {budget} preemptions, against the reduced world"
  let (ww, _) ← walk (runT budget t7Whole) #[] (secs * 1000)
  IO.println s!"  reduced world: {ww.runs} timelines, complete {ww.complete}, {ww.finals.length} final states, violations {ww.counts}"
  IO.println s!"  start {showPath start}"
  let (wc, pruned) ← walk (runT budget t7) start (secs * 1000) (some cuts)
  IO.println s!"  chunked world: {wc.runs} timelines with ≤ {cuts} partial reads ({pruned} runs past the bound skipped with their subtrees); {if wc.complete then "complete" else s!"stopped, NEXT {(wc.next.map showPath).getD ""}"}"
  printWalk { wc with finals := [] }
  let outside := wc.finals.filter fun (fp, _) => (ww.finals.lookup fp).isNone
  IO.println s!"  chunked final states: {wc.finals.length}; not among the reduced world's: {outside.length}"
  for (fp, n) in outside.take 3 do IO.println s!"    {n}: {fp.take 600}"
  IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  flushOut

/-- The decisions of the first (all-zero) timeline of either world, by name. -/
def namesCmd (budget : Nat) (which : String) : IO Unit := do
  let s := if which == "whole" then t7Whole else t7
  let (o, _) := runT budget s (Source.path #[])
  let names := o.taken.foldl (fun (acc : List (String × Nat × Nat)) t =>
    match acc.lookup t.name with
    | some (n, k) => (t.name, n + 1, max k t.options) :: acc.filter (·.1 != t.name)
    | none => (t.name, 1, t.options) :: acc) []
  IO.println s!"== decisions of T7 {which}'s first timeline, ≤ {budget}: {o.taken.size}"
  for (n, c, k) in names.reverse do IO.println s!"  {n}: {c} decisions, up to {k} options"
  flushOut

def estimateCmd (budget probes : Nat) (which : String) : IO Unit := do
  let s := if which == "whole" then t7Whole else t7
  let t0 ← IO.monoMsNow
  let (mean, lo, hi) := Jank.R4.Nrepl.Seg.estimate (fun src => (runT budget s src).1) probes
  IO.println s!"== Knuth estimate, T7 {which}, ≤ {budget} preemptions, {probes} paths: mean {mean} (min {lo}, max {hi}) ({(← IO.monoMsNow) - t0} ms)"
  flushOut

def main (args : List String) : IO Unit := do
  match args with
  | ["t7-bytes"] => t7Bytes
  | ["whole", b, secs] => wholeCmd b.toNat! secs.toNat! #[]
  | ["whole", b, secs, p] => wholeCmd b.toNat! secs.toNat! (parsePath p)
  | ["whole0", b, secs] => whole0Cmd b.toNat! secs.toNat! #[]
  | ["whole0", b, secs, p] => whole0Cmd b.toNat! secs.toNat! (parsePath p)
  | ["stutter", b, secs] => stutterCmd b.toNat! secs.toNat!
  | ["cuts", b, c, secs] => cutsCmd b.toNat! c.toNat! secs.toNat!
  | ["cuts", b, c, secs, p] => cutsCmd b.toNat! c.toNat! secs.toNat! (parsePath p)
  | ["names", b, w] => namesCmd b.toNat! w
  | ["estimate", b, n, w] => estimateCmd b.toNat! n.toNat! w
  | "interrupt" :: rest => Jank.R5.Nrepl.Interrupt.main rest
  | _ => IO.println "usage: jank5-nrepl t7-bytes | whole B SECS [PATH] | stutter B SECS | cuts B C SECS | estimate B N whole|chunked | names B whole|chunked | whole0 B SECS [PATH] | interrupt [B]"

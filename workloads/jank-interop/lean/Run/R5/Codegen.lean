import Jank.R5.Codegen.Gen
import Jank.R5.Codegen.Distinct
import Jank.R3.Codegen.Census
import Jank.R5.Codegen.Visit

/-! Round 5 driver: codegen (`jank5-codegen <part> ...`).

- `size`: the exact sizes of the clean worlds (timelines and distinct programs), per root kind.
- `check1`: the restated generator against round 2's on every depth-1 timeline.
- `check2 SEEDS`: the same on random depth-2 timelines (mixed seeds).
- `checkpart K`: the same on every depth-2 timeline whose root kind is K.
- `seg MODE START BOUND SECS`: a resumable census of the depth-2 control world through jank's
  pipeline and Clojure's spec (round 2's `ProgSearch.run cfg 2 _ true`), from the path START
  (comma-separated decision values; its first value is the root kind, the partition) until the
  partition ends, BOUND timelines or SECS seconds. Prints the next path to resume from.
-/

open Determinismo Jank.R5.Codegen Jank.Codegen

def modes : List (String × Jank.Codegen.Config) :=
  [("eval -O0", ({} : Jank.Codegen.Config)),
   ("module (AOT)", { target := .module, runtime := { dynamic := false } })]

def kindNames : List String :=
  ["int", "keyword", "local", "literal", "(log e)", "(identity e)", "(vector a b)", "let", "let2",
   "loop", "if", "do", "fn call", "def", "try", "case", "loop2", "list?", "3", "case1"]

def origForm (depth : Nat) (src : Source) : Option (Form × Array Taken) :=
  match (Jank.Codegen.ProgSearch.genE depth { clean := true } true).run { decisions := { source := src, limit := 400 } } with
  | .ok f w => some (f, w.decisions.taken)
  | .error _ _ => none

def takenOf (ds : List (String × Nat × Nat)) : Array Taken :=
  (ds.map fun (n, o, v) => ({ name := n, options := o, value := v } : Taken)).toArray

/-- Compare the restatement with the original on one path. -/
def agreeOn (depth : Nat) (path : List Nat) : Option String :=
  match origForm depth (Source.path path.toArray), DT.walk (genT depth root true) path with
  | some (f, t), some (g, ds) =>
    if f.code != g.code then some s!"form: {f.code} vs {g.code} on {path}"
    else if t != takenOf ds then some s!"decisions differ on {path}"
    else none
  | _, _ => some s!"no form on {path}"

def check1 : IO Unit := do
  let all := DT.all (genT 1 root true)
  let mut bad := 0
  for (_, p) in all do
    if let some e := agreeOn 1 p then
      bad := bad + 1
      if bad ≤ 5 then IO.println s!"  {e}"
  let codes := (all.map fun (f, _) => f.code).eraseDups
  IO.println s!"== check1: {all.length} depth-1 timelines, {bad} differ; {codes.length} distinct programs (distinctCount 1 []: {distinctCount 1 []})"

def check2 (seeds : Nat) (withVerdict : Bool) : IO Unit := do
  let mut bad := 0
  let mut badV := 0
  for i in [0:seeds] do
    let src : Source := { gen := mkStdGen (mixSeed (i + 1)) }
    match origForm 2 src with
    | some (f, t) =>
      let path := (t.map (·.value)).toList
      match DT.walk (genT 2 root true) path with
      | some (g, ds) =>
        if f.code != g.code || t != takenOf ds then
          bad := bad + 1
          if bad ≤ 5 then IO.println s!"  differ on {path}: {f.code} vs {g.code}"
        if withVerdict then
          for (_, cfg) in modes do
            let o := Jank.Codegen.ProgSearch.run cfg 2 (Source.path path.toArray) true
            let v := match verdict cfg g with | .violate .. => true | _ => false
            if o.violation.isSome != v then
              badV := badV + 1
              if badV ≤ 5 then IO.println s!"  verdict differs on {path}"
      | none => bad := bad + 1
    | none => bad := bad + 1
  IO.println s!"== check2: {seeds} random depth-2 timelines (mixed seeds 1..{seeds}), {bad} differ{if withVerdict then s!"; verdict copy vs ProgSearch.run in both modes: {badV} differ" else ""}"

def checkPart (k : Nat) : IO Unit := do
  let sub := kindT (genT 1) 2 root true k
  let all := DT.all sub
  let mut bad := 0
  for (_, p) in all do
    if let some e := agreeOn 2 (k :: p) then
      bad := bad + 1
      if bad ≤ 5 then IO.println s!"  {e}"
  let codes := (all.map fun (f, _) => f.code).eraseDups
  IO.println s!"== checkpart {k} ({kindNames.getD k "?"}): {all.length} depth-2 timelines (cnt: {kindCount (cnt 1) 0 k}), {bad} differ; {codes.length} distinct programs (count: {kindDistinct 1 2 [] k})"

def size : IO Unit := do
  for d in [0:4] do
    IO.println s!"depth {d}: {cnt d 0} timelines, {distinctCount d []} distinct programs"
  IO.println "depth 2, per root kind (timelines / distinct programs):"
  let mut tot := 0
  for k in [0:20] do
    let n := kindCount (cnt 1) 0 k
    tot := tot + n
    IO.println s!"  {k} {kindNames.getD k "?"}: {n} / {kindDistinct 1 2 [] k}"
  IO.println s!"  total {tot}"

structure Hit where
  cls : String
  count : Nat
  first : String

def parsePath (s : String) : Array Nat :=
  ((s.splitOn ",").filter (· != "")).map String.toNat! |>.toArray

def seg (m : Nat) (start : Array Nat) (bound secs : Nat) : IO Unit := do
  let (name, cfg) := modes[m]!
  let run := fun (src : Source) => Jank.Codegen.ProgSearch.run cfg 2 src true
  let pre := start.extract 0 1
  let t0 ← IO.monoMsNow
  let mut path := start
  let mut runs := 0
  let mut hits : Array Hit := #[]
  let mut next : Option (Array Nat) := some start
  while runs < bound do
    let o := run (Source.path path)
    runs := runs + 1
    if let some (p, d) := o.violation then
      let cls := Jank.R3.Codegen.bracketClass p
      match hits.findIdx? (·.cls == cls) with
      | some i => hits := hits.modify i fun h => { h with count := h.count + 1 }
      | none => hits := hits.push { cls, count := 1, first := s!"{d} (path {(o.taken.map (·.value)).toList})" }
    match Jank.R3.Codegen.nextPathWithin pre o.taken with
    | none => next := none; break
    | some p =>
      path := p; next := some p
      if runs % 2000 == 0 then
        if (← IO.monoMsNow) - t0 > secs * 1000 then break
  let el := ((← IO.monoMsNow) - t0) / 1000
  let nx := match next with | none => "END" | some p => ",".intercalate (p.toList.map toString)
  IO.println s!"== seg {name} kind {start[0]!} from {",".intercalate (start.toList.map toString)}: {runs} timelines, {hits.foldl (· + ·.count) 0} violate, {el} s; next {nx}"
  for h in hits do IO.println s!"   [{h.cls}] {h.count}; first: {h.first}"
  (← IO.getStdout).flush

/-- A resumable segment of the sub-world (`Sub.lean`) through `verdict`. -/
def sub (m : Nat) (start : Array Nat) (bound secs : Nat) : IO Unit := do
  let (name, cfg) := modes[m]!
  let t0 ← IO.monoMsNow
  let runs ← IO.mkRef 0
  let gaps ← IO.mkRef 0
  let hits ← IO.mkRef (#[] : Array Hit)
  let firstGap ← IO.mkRef ""
  let next ← DT.visitFrom subWorld start.toList #[] fun e p => do
    let r ← runs.get
    if r ≥ bound then return false
    if r % 2000 == 0 && r > 0 then
      if (← IO.monoMsNow) - t0 > secs * 1000 then return false
    runs.set (r + 1)
    match verdict cfg e with
    | .agree => pure ()
    | .gap d => do
      gaps.modify (· + 1)
      if (← firstGap.get).isEmpty then firstGap.set s!"{d} (path {p.toList})"
    | .violate cls d => do
      let hs ← hits.get
      match hs.findIdx? (·.cls == cls) with
      | some i => hits.set (hs.modify i fun h => { h with count := h.count + 1 })
      | none => hits.set (hs.push { cls, count := 1, first := s!"{d} (path {p.toList})" })
    return true
  let el := ((← IO.monoMsNow) - t0) / 1000
  let nx := match next with | none => "END" | some p => ",".intercalate (p.toList.map toString)
  let hs ← hits.get
  IO.println s!"== sub {name} from {",".intercalate (start.toList.map toString)}: {← runs.get} timelines, {hs.foldl (· + ·.count) 0} violate, {← gaps.get} model gaps, {el} s; next {nx}"
  for h in hs do IO.println s!"   [{h.cls}] {h.count}; first: {h.first}"
  if (← gaps.get) > 0 then IO.println s!"   first gap: {← firstGap.get}"
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  match args with
  | ["size"] => size
  | ["check1"] => check1
  | ["check2", n] => check2 n.toNat! false
  | ["check2v", n] => check2 n.toNat! true
  | ["sub", m, start, bound, secs] => sub m.toNat! (parsePath start) bound.toNat! secs.toNat!
  | ["subsize"] => IO.println s!"sub-world: {DT.leaves subWorld} timelines (cntK1 0/1/2 = {cntK1 0}/{cntK1 1}/{cntK1 2})"
  | ["checkpart", k] => checkPart k.toNat!
  | ["seg", m, start, bound, secs] => seg m.toNat! (parsePath start) bound.toNat! secs.toNat!
  | _ => IO.println "usage: jank5-codegen size | check1 | check2 N | checkpart K | seg MODE START BOUND SECS"

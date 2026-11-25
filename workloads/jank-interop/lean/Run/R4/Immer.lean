import Jank.R3.Immer.Maps
import Jank.R3.Immer.HashInv
import Jank.R3.Search.Common
import Jank.R4.Immer.SeqObjects
import Jank.R4.Immer.ArrayMapCtor

/-! Round 4 driver: Immer and collections. `jank4-immer <mode>`.

- `estimate`: Knuth's estimate of the worlds round 3 stopped (M4, M5, S3).
- `maps <ID>[@v][>path]`, `sets <ID>…`: the round-3 designed-hash censuses, resumable, as round 3
  ran them (the same configurations, copied from Run/R3/Immer.lean).
-/

open Jank.R3.Immer
open Jank.R4.Immer
open Jank.Equality (V)

namespace Run.R4.Immer

def lv (h hi : UInt32) : V := .int (HashInv.longValue h hi)
/-- Round 3's designed-hash alphabet (Run/R3/Immer.lean `kH`). -/
def kH : List V := [lv 0x00000001 0, lv 0x00000021 0, lv 0x80000001 0, lv 0x00000001 1, lv 0x00000001 2, lv 0x40000001 0, .kw "a"]
def startsH : List (String × List (V × V) × Bool) :=
  [("(hash-map)", [], true), (s!"(hash-map {(lv 0x00000001 0).code} 0 {(lv 0x00000021 0).code} 0 {(lv 0x80000001 0).code} 0)",
     [(lv 0x00000001 0, .int 0), (lv 0x00000021 0, .int 0), (lv 0x80000001 0, .int 0)], true)]
def persistentOps : List Maps.Op := [.assoc, .dissoc, .hashMap]
def transientOps : List Maps.Op := [.transient, .assocBang, .dissocBang, .persistentBang, .deadRead, .assoc]
def sOpsP : List Maps.SOp := [.conj, .disj, .hashSet]
def sOpsT : List Maps.SOp := [.transient, .conjBang, .disjBang, .persistentBang, .deadRead, .conj]

def m4 : Maps.Cfg := { keys := kH, ops := persistentOps, steps := 4, starts := startsH }
def m5 : Maps.Cfg := { keys := kH, ops := transientOps, steps := 4, starts := startsH, pairs := false, aside := ["dead-read"] }
def s3 : Maps.SCfg := { keys := kH, ops := sOpsP ++ sOpsT, steps := 4, starts := [("#{}", [])] }

def selOn (sel : List String) (id : String) : Bool :=
  sel.isEmpty || sel.any fun x => x == id || x.startsWith (id ++ "@") || x.startsWith (id ++ ">")
def parseDotted (s : String) : Array Nat := ((s.splitOn ".").filter (· ≠ "")).map String.toNat! |>.toArray
def selPart (sel : List String) (id : String) : Array Nat :=
  match sel.find? (·.startsWith (id ++ "@")) with
  | some x => parseDotted ((((x.splitOn ">").getD 0 "").splitOn "@").getD 1 "")
  | none => #[]
def selResume (sel : List String) (id : String) : Option (Array Nat) :=
  match sel.find? (fun x => x.startsWith (id ++ ">") || (x.startsWith (id ++ "@") && x.contains '>')) with
  | some x => some (parseDotted ((x.splitOn ">").getD 1 ""))
  | none => none

def m4s3 : Maps.Cfg := { m4 with steps := 3 }
def m4s2 : Maps.Cfg := { m4 with steps := 2 }
def s3s3 : Maps.SCfg := { s3 with steps := 3 }

def estimates (samples : Nat) : IO Unit := do
  for (name, run) in [("M4", Maps.run m4), ("M5", Maps.run m5), ("S3", Maps.srun s3),
      ("M4-3", Maps.run m4s3), ("S3-3", Maps.srun s3s3)] do
    let (n, d) := Jank.R3.Search.estimate run samples
    IO.println s!"{name}: estimated {n} timelines, mean {d} decisions ({samples} samples)"
    (← IO.getStdout).flush

def stopped (sel : List String) : IO Unit := do
  let big := 1000000000
  if selOn sel "M4" then
    discard <| Kit.reportCensus "M4 CHAMP: persistent ops, designed-hash keys (depths 1, 6, collision nodes), 4 steps" (Maps.run m4) big (selPart sel "M4") (selResume sel "M4")
  if selOn sel "M5" then
    discard <| Kit.reportCensus "M5 CHAMP transients: designed-hash keys, 4 steps (dead-read set aside)" (Maps.run m5) big (selPart sel "M5") (selResume sel "M5")
  if selOn sel "M4-2" then
    discard <| Kit.reportCensus "M4-2 CHAMP: M4 at 2 steps (persistent ops, designed-hash keys)" (Maps.run m4s2) big (selPart sel "M4-2") (selResume sel "M4-2")
  if selOn sel "M4-3" then
    discard <| Kit.reportCensus "M4-3 CHAMP: M4 at 3 steps (persistent ops, designed-hash keys)" (Maps.run m4s3) big (selPart sel "M4-3") (selResume sel "M4-3")
  if selOn sel "S3-3" then
    discard <| Kit.reportCensus "S3-3 sets: S3 at 3 steps (designed-hash keys, all operations)" (Maps.srun s3s3) big (selPart sel "S3-3") (selResume sel "S3-3")
  if selOn sel "S3" then
    discard <| Kit.reportCensus "S3 sets: designed-hash keys, all operations, 4 steps" (Maps.srun s3) big (selPart sel "S3") (selResume sel "S3")

/-- The sequence-object world: censuses at 1, 2 and 3 steps, then residuals with each class
found set aside. -/
def seqObjects (sel : List String) : IO Unit := do
  let big := 1000000000
  let allCls := ["hang", "nth-index", "realized", "transient", "pop-meta", "seq-meta", "meta-mutated", "meta", "result"]
  if selOn sel "Q1" then
    discard <| Kit.reportCensus "Q1 seq objects: 9 starts, 22 operations, 1 step" (SeqObj.run 1 []) big
  if selOn sel "Q2" then
    discard <| Kit.reportCensus "Q2 seq objects: 2 steps" (SeqObj.run 2 []) big
  if selOn sel "Q3" then
    discard <| Kit.reportCensus "Q3 seq objects: 3 steps" (SeqObj.run 3 []) big (selPart sel "Q3") (selResume sel "Q3")
  if selOn sel "Q3r" then
    discard <| Kit.reportCensus "Q3r residual: 3 steps, every class of Q1-Q3 set aside, and the meta that C1 leaves behind (results only)"
      (SeqObj.run 3 (allCls.filter (fun c => c != "result"))) big (selPart sel "Q3r") (selResume sel "Q3r")
  if selOn sel "Q3m" then
    discard <| Kit.reportCensus "Q3m residual for meta: 3 steps, without the triggers of C1, C5, C6 (no (repeat 7) start, no seq/pop on lists), classes of results set aside"
      (SeqObj.run 3 ["hang", "nth-index", "realized", "transient"]
        (SeqObj.starts.filter (fun s => s.code != "(repeat 7)"))
        (SeqObj.ops.filter (fun o => o != .seq && o != .pop))) big (selPart sel "Q3m") (selResume sel "Q3m")
  if selOn sel "Q4r" then
    discard <| Kit.reportCensus "Q4r residual: 4 steps, every class set aside (results only)"
      (SeqObj.run 4 (allCls.filter (fun c => c != "result"))) big (selPart sel "Q4r") (selResume sel "Q4r")

/-- `array-map`: a prefix of 0 to 8 distinct keys, then up to 5 pairs over a 4-key alphabet. -/
def arrayMap : IO Unit := do
  discard <| Kit.reportCensus "A1 array-map: prefix 0..8 distinct keys, then 0..5 pairs (keys 0, 1, 2, 100; values 0, 1)"
    (ArrayMap.run (List.range 9) 5) 1000000000
  discard <| Kit.reportCensus "A2 array-map: prefix 0..7 distinct keys, then 0..6 pairs (stays at or below 8 entries unless a 9th key comes)"
    (ArrayMap.run (List.range 8) 6) 1000000000

end Run.R4.Immer

def main (args : List String) : IO UInt32 := do
  match args with
  | ["estimate", n] => Run.R4.Immer.estimates n.toNat!
  | "stopped" :: sel => Run.R4.Immer.stopped sel
  | "seqobj" :: sel => Run.R4.Immer.seqObjects sel
  | ["arraymap"] => Run.R4.Immer.arrayMap
  | _ => IO.println "modes: estimate N | stopped ID[@v][>path]"
  pure 0

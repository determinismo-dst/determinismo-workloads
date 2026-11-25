import Jank.R3.Immer.Rbts
import Jank.R3.Immer.Champ
import Jank.R3.Immer.Maps
import Jank.R3.Immer.HashInv
import Jank.R3.Immer.Vectors

/-! Round 3 driver: Immer. `jank3-immer <mode>`. -/

open Jank.R3.Immer

namespace Run.R3.Immer

section selftest
open Champ
def cfg (f : Nat → Nat) : Cfg Nat Nat := { hashT := f, hashK := f, eqTT := (· == ·), eqTK := (· == ·) }

def runChamp (f : Nat → Nat) (ops : List (Bool × Nat)) (isMut : Bool) : Bool := Id.run do
  let mut c : Champ Nat := Champ.empty
  let mut model : List Nat := []
  let mut al : Al := {}
  let mut tok := 0
  if isMut then
    let (t, al') := (Champ.transient c).run al
    al := al'; tok := t.tok
  for (add, k) in ops do
    if add then
      let (c', al') := (if isMut then c.addMut (cfg f) tok k else c.add (cfg f) k).run al
      c := c'; al := al'
      if !model.contains k then model := model ++ [k]
    else
      let (c', al') := (if isMut then c.subMut (cfg f) tok k else c.sub (cfg f) k).run al
      c := c'; al := al'
      model := model.filter (· != k)
    let l := c.toList
    if l.length != model.length || c.size != model.length || !(model.all l.contains) then return false
    if !((List.range 40).all fun k => (c.get (cfg f) k).isSome == model.contains k) then return false
    if !c.checkChamp (cfg f) then return false
    if !wfNode 13 c.root then return false
  return true

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648
def opsOf (seed n : Nat) : List (Bool × Nat) := Id.run do
  let mut s := seed
  let mut out := []
  for _ in List.range n do
    s := lcg s
    let add := (s / 65536) % 3 != 0
    s := lcg s
    out := out ++ [(add, (s / 65536) % 40)]
  return out

def hashes : List (Nat → Nat) := [fun k => k, fun k => k / 4, fun k => (k % 3) * 0x100000 + (k / 3),
  fun k => (k % 2) <<< 31, fun _ => 7, fun k => (k * 2654435761) % 4294967296]

/-- The aliasing check fires when a transient owns a node a persistent value reaches: a transient
built with the persistent vector's own owner token (what `persistent() &&` without a reset, or a
reused token, would give). -/
def aliasingNegative : Bool :=
  let (v, n) := Vectors.buildVec 40 Rbts.firstId
  let tok := (v.reach.find? (fun p => p.2 != 0)).map (·.2) |>.getD 0
  let t : Rbts.Transient Nat := { tree := v, tok }
  let (t, _) := t.pushBack 99 n
  (Maps.aliasing [v.reach] [(t.tok, t.tree.reach)] []).isSome

def selftest : IO Unit := do
  IO.println s!"aliasing check fires on a shared owner token: {aliasingNegative}"
  IO.println s!"champ persistent: {hashes.map fun f => (List.range 200).all fun seed => runChamp f (opsOf seed 60) false}"
  IO.println s!"champ transient: {hashes.map fun f => (List.range 200).all fun seed => runChamp f (opsOf seed 60) true}"
end selftest

section maps
open Maps Objects Kit
open Jank.Equality (V)

/-- Identity alphabet: =-equal keys that jank stores or hashes differently. -/
def kA : List V := [.kw "a", .int 1, .big 1, .vec [.int 1], .list [.int 1], .real 0, .real 0x8000000000000000]
/-- The same without round 1's D12 pairs (1 and 1N, 0.0 and -0.0). -/
def kA' : List V := [.kw "a", .int 1, .vec [.int 1], .list [.int 1], .real 0]
def lv (h hi : UInt32) : V := .int (HashInv.longValue h hi)
/-- Hash-structure alphabet: longs with hashes 1, 0x21 (shares 5 bits: depth 1), 0x80000001 and
0x40000001 (share 30 bits: split at depth 6 by bits 30-31), and two more longs hashing to 1
(full collisions: collision node at depth 13). -/
def kH : List V := [lv 0x00000001 0, lv 0x00000021 0, lv 0x80000001 0, lv 0x00000001 1, lv 0x00000001 2, lv 0x40000001 0, .kw "a"]
def fillers (n : Nat) : List (V × V) := (List.range n).map fun i => (.kw s!"f{i}", .int 0)
def fillersCode (n : Nat) : String := "{" ++ " ".intercalate ((List.range n).map fun i => s!":f{i} 0") ++ "}"

def startsA : List (String × List (V × V) × Bool) :=
  [("(hash-map)", [], true), (fillersCode 8, fillers 8, false)]
def startsP : List (String × List (V × V) × Bool) :=
  [("(assoc " ++ fillersCode 7 ++ " '(1) 0)", fillers 7 ++ [(.list [.int 1], .int 0)], false),
   ("(assoc " ++ fillersCode 7 ++ " 1 0)", fillers 7 ++ [(.int 1, .int 0)], false)]
def startsH : List (String × List (V × V) × Bool) :=
  [("(hash-map)", [], true), (s!"(hash-map {(lv 0x00000001 0).code} 0 {(lv 0x00000021 0).code} 0 {(lv 0x80000001 0).code} 0)",
     [(lv 0x00000001 0, .int 0), (lv 0x00000021 0, .int 0), (lv 0x80000001 0, .int 0)], true)]

def persistentOps : List Maps.Op := [.assoc, .dissoc, .hashMap]
def transientOps : List Maps.Op := [.transient, .assocBang, .dissocBang, .persistentBang, .deadRead, .assoc]

/-- `ID` selects a search; `ID@v` the partition of its timelines whose first decision is `v`;
`ID>a.b.c` continues its census from the path a.b.c (printed as `resume:` by a job that ran out
of its time budget). -/
def selOn (sel : List String) (id : String) : Bool :=
  sel.isEmpty || sel.any fun x => x == id || x.startsWith (id ++ "@") || x.startsWith (id ++ ">")

def parseDotted (s : String) : Array Nat := ((s.splitOn ".").filter (· ≠ "")).map String.toNat! |>.toArray

def selPart (sel : List String) (id : String) : Array Nat :=
  match sel.find? (·.startsWith (id ++ "@")) with
  | some x => #[((x.drop (id.length + 1)).takeWhile Char.isDigit).toNat!]
  | none => #[]

def selResume (sel : List String) (id : String) : Option (Array Nat) :=
  match sel.find? (fun x => x.startsWith (id ++ ">") || (x.startsWith (id ++ "@") && x.contains '>')) with
  | some x => some (parseDotted ((x.splitOn ">").getD 1 ""))
  | none => none

def mapsSearch (quick : Bool) (sel : List String := []) : IO Unit := do
  let on (id : String) : Bool := selOn sel id
  IO.println s!"designed hashes (jank hash, key): {kH.map fun k => (jHash k, k.code)}"
  let big := if quick then 200000 else 1000000000
  let seeds := if quick then 2000 else 20000
  -- M1: persistent operations over the identity alphabet
  let m1 : Maps.Cfg := { keys := kA, ops := persistentOps, steps := 3, starts := startsA }
  if on "M1" then
    discard <| reportCensus "M1 maps: assoc/dissoc/hash-map, identity keys (7), starts (hash-map) and an 8-entry array map, 3 steps" (Maps.run m1) big (selPart sel "M1") (selResume sel "M1")
  if on "M1r1" then
    discard <| reportCensus "M1r1: D12 keys removed (1N, -0.0); find-key (R123) set aside" (Maps.run { m1 with keys := kA', aside := ["find-key"] }) big (selPart sel "M1r1") (selResume sel "M1r1")
  if on "M1r2" then
    discard <| reportCensus "M1r2: and key-identity set aside" (Maps.run { m1 with keys := kA', aside := ["find-key", "key-identity"] }) big (selPart sel "M1r2") (selResume sel "M1r2")
  if on "M1d" then
    discard <| reportCensus "M1d: D12 keys kept; count, get, find-key, key-identity, entries set aside (what D12 does to = and hash on maps)"
      (Maps.run { m1 with aside := ["find-key", "key-identity", "count", "get", "entries"] }) big (selPart sel "M1d") (selResume sel "M1d")
  -- M2: transients
  let m2 : Maps.Cfg := { keys := kA, ops := transientOps, steps := 4, starts := startsA }
  if on "M2" then
    discard <| reportCensus "M2 maps: transient/assoc!/dissoc!/persistent!/reads after persistent!/assoc, identity keys, 4 steps" (Maps.run m2) big (selPart sel "M2") (selResume sel "M2")
  if on "M2r1" then
    discard <| reportCensus "M2r1: D12 keys removed; find-key set aside" (Maps.run { m2 with keys := kA', aside := ["find-key"] }) big (selPart sel "M2r1") (selResume sel "M2r1")
  if on "M2r2" then
    discard <| reportCensus "M2r2: and dead-read, key-identity set aside" (Maps.run { m2 with keys := kA', aside := ["find-key", "dead-read", "key-identity"] }) big (selPart sel "M2r2") (selResume sel "M2r2")
  -- M3: promotion past the array-map threshold with an equal key present
  let m3 : Maps.Cfg := { keys := kA, ops := [.assoc, .dissoc, .transient, .assocBang, .persistentBang], steps := 3, starts := startsP, aside := ["find-key"] }
  if on "M3" then
    discard <| reportCensus "M3 promotion: 8-entry array maps holding '(1) or 1, identity keys, 3 steps (find-key set aside: it holds at the start)" (Maps.run m3) big (selPart sel "M3") (selResume sel "M3")
  if on "M3r" then
    discard <| reportCensus "M3r: D12 keys removed; find-key and key-identity set aside" (Maps.run { m3 with keys := kA', aside := ["find-key", "key-identity"] }) big (selPart sel "M3r") (selResume sel "M3r")
  -- M4: CHAMP structure: collisions at chosen depths and full collisions
  let m4 : Maps.Cfg := { keys := kH, ops := persistentOps, steps := 4, starts := startsH }
  if on "M4" then
    discard <| reportCensus "M4 CHAMP: persistent ops, designed-hash keys (depths 1, 6, collision nodes), 4 steps" (Maps.run m4) big (selPart sel "M4") (selResume sel "M4")
  let m5 : Maps.Cfg := { keys := kH, ops := transientOps, steps := 4, starts := startsH, pairs := false }
  if on "M5" then
    discard <| reportCensus "M5 CHAMP transients: designed-hash keys, 4 steps (dead-read set aside)" (Maps.run { m5 with aside := ["dead-read"] }) big (selPart sel "M5") (selResume sel "M5")
  if on "M6" then
    report "M6 explore: all operations, identity and designed keys together, 8 steps (find-key, D12 keys, key-identity, dead-read set aside)"
      (Maps.run { keys := kA' ++ kH, ops := persistentOps ++ transientOps, steps := 8, starts := startsA ++ startsH,
                  aside := ["find-key", "key-identity", "dead-read"] }) seeds 0

def sOpsP : List Maps.SOp := [.conj, .disj, .hashSet]
def sOpsT : List Maps.SOp := [.transient, .conjBang, .disjBang, .persistentBang, .deadRead, .conj]

def setsSearch (quick : Bool) (sel : List String := []) : IO Unit := do
  let on (id : String) : Bool := selOn sel id
  let big := if quick then 200000 else 1000000000
  let seeds := if quick then 2000 else 20000
  let s1 : Maps.SCfg := { keys := kA, ops := sOpsP, steps := 3, starts := [("#{}", [])] }
  if on "S1" then
    discard <| reportCensus "S1 sets: conj/disj/hash-set, identity keys, 3 steps" (Maps.srun s1) big (selPart sel "S1") (selResume sel "S1")
  if on "S1r1" then
    discard <| reportCensus "S1r1: D12 keys removed" (Maps.srun { s1 with keys := kA' }) big (selPart sel "S1r1") (selResume sel "S1r1")
  if on "S1r2" then
    discard <| reportCensus "S1r2: and key-identity set aside" (Maps.srun { s1 with keys := kA', aside := ["key-identity"] }) big (selPart sel "S1r2") (selResume sel "S1r2")
  let s2 : Maps.SCfg := { keys := kA, ops := sOpsT, steps := 4, starts := [("#{}", []), ("#{:a '(1)}", [.kw "a", .list [.int 1]])] }
  if on "S2" then
    discard <| reportCensus "S2 sets: transients, identity keys, 4 steps" (Maps.srun s2) big (selPart sel "S2") (selResume sel "S2")
  if on "S2r" then
    discard <| reportCensus "S2r: D12 keys removed; key-identity set aside" (Maps.srun { s2 with keys := kA', aside := ["key-identity"] }) big (selPart sel "S2r") (selResume sel "S2r")
  let s3 : Maps.SCfg := { keys := kH, ops := sOpsP ++ sOpsT, steps := 4, starts := [("#{}", [])] }
  if on "S3" then
    discard <| reportCensus "S3 sets: designed-hash keys, all operations, 4 steps" (Maps.srun s3) big (selPart sel "S3") (selResume sel "S3")
  if on "S4" then
    report "S4 explore: all operations, identity and designed keys, 8 steps (key-identity set aside)"
      (Maps.srun { keys := kA' ++ kH, ops := sOpsP ++ sOpsT, steps := 8, starts := [("#{}", [])], aside := ["key-identity"] }) seeds 0
end maps

section vectors
open Kit
def allVecOps : List Vectors.Op := [.conj, .assoc, .pop, .subvec, .into, .transient, .conjBang, .assocBang, .popBang, .persistentBang, .deadRead]
def smallStarts : List Nat := [0, 1, 31, 32, 33, 63, 64, 65, 1024, 1055, 1056, 1057, 1088, 1089]
def bigStarts : List Nat := [32767, 32768, 32799, 32800, 32801, 32832, 32833]
def hugeStarts : List Nat := [1048608, 1048609]

def vecSearch (quick : Bool) (sel : List String := []) : IO Unit := do
  let on (id : String) : Bool := selOn sel id
  let big := if quick then 100000 else 1000000000
  let seeds := if quick then 2000 else 30000
  let v1 : Vectors.Cfg := { starts := smallStarts, ops := allVecOps, steps := 2 }
  let c1 := Vectors.mkCache v1
  if on "V1" then
    discard <| reportCensus "V1 vectors: 14 starts at the leaf/tail/depth boundaries (two builders), all 11 operations, 2 steps" (Vectors.run v1 c1) big (selPart sel "V1") (selResume sel "V1")
  if on "V1b" then
    let v1b : Vectors.Cfg := { starts := [31, 32, 33, 1056, 1057], ops := allVecOps, steps := 3 }
    discard <| reportCensus "V1b vectors: starts 31, 32, 33, 1056, 1057 (two builders), all 11 operations, 3 steps" (Vectors.run v1b (Vectors.mkCache v1b)) big (selPart sel "V1b") (selResume sel "V1b")
  if on "V2" then
    report "V2 vectors: the same starts, all operations, 6 steps" (Vectors.run { v1 with steps := 6 } c1) seeds 0
  let v3 : Vectors.Cfg := { starts := bigStarts, ops := allVecOps, steps := 4, batches := [1, 32, 33, 1024] }
  let c3 := Vectors.mkCache v3
  if on "V3" then
    report "V3 vectors: starts around 32768 (shift 10 to 15), all operations, 4 steps" (Vectors.run v3 c3) (seeds / 20) 0
  let v4 : Vectors.Cfg := { starts := hugeStarts, ops := allVecOps, steps := 3, batches := [1, 32, 33] }
  let c4 := Vectors.mkCache v4
  if on "V4" then
    report "V4 vectors: starts 1048608 and 1048609 (shift 15 to 20), all operations, 3 steps" (Vectors.run v4 c4) (if quick then 10 else 200) 0
end vectors

end Run.R3.Immer

def main (args : List String) : IO UInt32 := do
  match args with
  | ["selftest"] => Run.R3.Immer.selftest
  | ["maps-quick"] => Run.R3.Immer.mapsSearch true
  | "maps" :: sel => Run.R3.Immer.mapsSearch false sel
  | ["sets-quick"] => Run.R3.Immer.setsSearch true
  | "sets" :: sel => Run.R3.Immer.setsSearch false sel
  | ["vectors-quick"] => Run.R3.Immer.vecSearch true
  | "vectors" :: sel => Run.R3.Immer.vecSearch false sel
  | _ => IO.println "modes: selftest"
  pure 0

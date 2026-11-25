import Jank.R3.Search.Common
import Jank.Core.Sorted
import Jank.Core.Destructure

/-!
# Round 3: sorted collections and destructuring, widened

Sorted collections (round 2: maps of 0–2 entries over 9 keys, sets of 0–2 elements): here maps of
0–3 entries and sets of 0–3 elements over 12 keys (adding `-1`, `1M`, `""` and `[]`, so that
BigDecimals, an empty string and an empty vector meet the comparator), every operation, with
`=`, `find` and `select-keys` judged apart (R104, R105) and the rest required to agree.

Destructuring (round 2: forms and values nested once, 435,132 programs): here forms nested twice
against values nested once, and forms once against values twice, partitioned by the first
decisions, with the trailing `(seq m)` in keyword arguments removed (R107 aside).
-/

namespace Jank.R3.Search.Core2

open Determinismo Jank.Compare
open Jank.Core.Sorted (MapOp SetOp mapOps setOps runMapOp runSetOp knownOrConstruction knownSet)

def keyAtoms3 : List CV :=
  [.long 0, .long 1, Jank.Core.Sorted.d1, .long 2, .long (-1), .dec 1 0, .str "", .str "a", .str "b",
   .kw "" "a", .kw "" "b", .vec [.long 1]]

def drawKey3 (name : String) : EStateM Stop Jank.Core.Sorted.World CV := do
  pure (keyAtoms3.getD (← decide (σ := Jank.Core.Sorted.World) name keyAtoms3.length) .nil)

/-- Round 2's `cvEq` with BigDecimals (same unscaled value and scale): its keys never held one. -/
partial def cvEq3 : CV → CV → Bool
  | .dec a s, .dec b t => a == b && s == t
  | .vec xs, .vec ys => xs.length == ys.length && (xs.zip ys).all fun (x, y) => cvEq3 x y
  | a, b => Jank.Core.Sorted.cvEq a b

def obsSame3 : Jank.Core.Sorted.Obs → Jank.Core.Sorted.Obs → Bool
  | .v a, .v b => cvEq3 a b
  | .coll a, .coll b => a.length == b.length && (a.zip b).all fun (x, y) => cvEq3 x y
  | a, b => a.same b

/-- R104 (`=` throws on incomparable keys) and R105 (`find`/`select-keys` return the queried key)
as their classes; everything else must agree. -/
def mapClass : MapOp → Option String
  | .equal => some "R104"
  | .find | .selectKeys => some "R105"
  | _ => none

def mapBody3 (maxSize : Nat) (otherMax : Nat := 2) : EStateM Stop Jank.Core.Sorted.World Unit := do
  let n ← decide (σ := Jank.Core.Sorted.World) "smap.size" (maxSize + 1)
  let mut kvs : List CV := []
  for i in [0:n] do
    kvs := kvs ++ [← drawKey3 s!"smap.key{i}", ← Jank.Core.Sorted.drawVal s!"smap.val{i}"]
  let op := mapOps.getD (← decide (σ := Jank.Core.Sorted.World) "smap.op" mapOps.length) .get
  let k ← drawKey3 "smap.arg.key"
  let v ← Jank.Core.Sorted.drawVal "smap.arg.val"
  let other ← if op == .equal then do
      let m ← decide (σ := Jank.Core.Sorted.World) "smap.other.size" (otherMax + 1)
      let mut o : List CV := []
      for i in [0:m] do
        o := o ++ [← drawKey3 s!"smap.other.key{i}", ← Jank.Core.Sorted.drawVal s!"smap.other.val{i}"]
      pure o
    else pure []
  let (j, c, code) := runMapOp kvs op k v other
  if op.extension then pure ()
  else if knownOrConstruction j c kvs other op then pure ()
  else if !obsSame3 j c then
    violate (σ := Jank.Core.Sorted.World) ((mapClass op).getD "unexplained") s!"{code}: Clojure {c.code}, jank {j.code}"

def setBody3 (maxSize : Nat) (otherMax : Nat := 3) : EStateM Stop Jank.Core.Sorted.World Unit := do
  let n ← decide (σ := Jank.Core.Sorted.World) "sset.size" (maxSize + 1)
  let mut xs : List CV := []
  for i in [0:n] do xs := xs ++ [← drawKey3 s!"sset.elem{i}"]
  let op := setOps.getD (← decide (σ := Jank.Core.Sorted.World) "sset.op" setOps.length) .get
  let e ← drawKey3 "sset.arg"
  let other ← if op == .equal then do
      let m ← decide (σ := Jank.Core.Sorted.World) "sset.other.size" (otherMax + 1)
      let mut o : List CV := []
      for i in [0:m] do o := o ++ [← drawKey3 s!"sset.other.elem{i}"]
      pure o
    else pure []
  let (j, c, code) := runSetOp xs op e other
  if op == .tConj then pure ()
  else if knownSet j c xs other op then pure ()
  else if !obsSame3 j c then
    violate (σ := Jank.Core.Sorted.World) (if op == .equal then "R104" else "unexplained") s!"{code}: Clojure {c.code}, jank {j.code}"

def runS (body : EStateM Stop Jank.Core.Sorted.World Unit) (source : Source) : Ended :=
  Jank.Core.Sorted.runBody body source

/-! ## Destructuring -/

section
open Jank.Core.Destructure

def destrRun (bindDepth valDepth : Nat) (entrySeq : Bool) (source : Source) : Ended :=
  let e := Jank.Core.Destructure.runBody (bindBody bindDepth valDepth entrySeq) source
  match e.violation with
  | some (_, d) =>
    -- R107's path: base_persistent_map.cpp `conj` (169) of a trailing element that is neither nil, a
    -- map nor a two-element vector (a seq of entries, an empty list): "invalid map entry".
    let cls := if (d.splitOn "invalid map entry").length > 1 then "R107" else "unexplained"
    { e with violation := some (cls, d) }
  | none => e
end

/-! ## W2 (an instance of R107): map `conj` of an empty list -/

section
open Jank.Core.Destructure

/-- base_persistent_map.cpp 169-186 (replica `rtMapConj`): `(conj {:a 1} ())` throws. -/
theorem w2_jank_conj_empty_list_throws :
    (rtMapConj [(.kw "" "a", .int 1)] (.list [])).toBool = false := by decide

/-- Clojure (`createAsIfByAssoc` with APersistentMap.cons): a trailing `()` adds nothing. -/
theorem w2_clj_trailing_empty_list :
    (match cljCreateAsIfByAssoc [.kw "" "a", .int 1, .list []] with
     | .ok (.map kvs) => kvs.length == 1
     | _ => false) = true := by decide
end

end Jank.R3.Search.Core2

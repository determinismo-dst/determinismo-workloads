import Jank.R3.Search.Common
import Jank.Seq.IntRange
import Jank.Seq.Range
import Jank.Seq.Transducers
import Jank.Seq.Chunked

/-!
# Round 3: sequences, widened, with round 2's classes named per disagreement

Round 2 checked each sequence world against "the fix" (jank's code with the found difference
replaced by Clojure's), which is Clojure's code again, so those runs could not find anything
else. Here every disagreement of jank's replica with Clojure's is named by the condition its
class needs, and anything else is reported:

- integer `range` (31 values, every 1-, 2- and 3-argument call, 40 elements): R114 when
  `count()` throws (the overflow check), R115 when `end - start` wraps;
- real `range` (more starts, steps, end offsets; 80 elements): R116 when some `start + k·step`
  within the elements and one chunk ahead leaves the i32 range;
- transducers (pipelines of 1–3 of the 15 transducers, inputs of length ≤ 5 over 0..2, three
  reducing functions): R118 when the pipeline holds `partition-by`.
-/

namespace Jank.R3.Search.Seq

open Determinismo

/-! ## Integer ranges -/

section
open Jank.Seq.IntRange

def interesting3 : List I64 :=
  interesting ++ [0xFFFFFFFF80000000 /- -2^31 -/, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF7FFFFFFF, 0x100000000,
    10, 0xFFFFFFFFFFFFFFF6 /- -10 -/, 7, 100, 0x3FFFFFFFFFFFFFFF, 0xBFFFFFFFFFFFFFFF, i64Min + 2, 9,
    0xFFFFFFFFFFFFFFFB /- -5 -/]

def fuel3 : Nat := 40

/-- The class of an integer-range disagreement, or none. -/
def intClass (q : Question) : Option String :=
  match q.jank with
  | .range r =>
    if BitVec.ssubOverflow r.finish r.start then some "R115"
    else match (walk fuel3 q.jank).ending with
      | .throws _ => some "R114"
      | _ => if (count r).toBool == false then some "R114" else none
  | _ => none

def intVerdict (q : Question) : Option (String × String) :=
  let j := q.jank
  let (s, e, st) := q.clj
  let jw := walk fuel3 j
  let cw := cljWalk s e st fuel3
  let d := if jw != cw then some s!"{q.program}: Clojure {cw.show}, jank {jw.show}"
    else match cljCount s e st, seqCount j with
      | some c, .ok jc => if c != jc then some s!"(count {q.program}): Clojure {c}, jank {jc}" else none
      | some c, .error m => some s!"(count {q.program}): Clojure {c}, jank throws {m}"
      | none, _ => none
  d.map fun d => ((intClass q).getD "unexplained", d)

def intBody : EStateM Stop World Unit := do
  let arity := (← decide (σ := World) "range.arity" 3) + 1
  let mut args := []
  for i in [0:arity] do
    let v ← pick (σ := World) s!"range.arg{i}" interesting3
    args := args ++ [v.getD 0]
  if let some (cls, d) := intVerdict { args } then violate (σ := World) cls d

def intRun (source : Source) : Ended :=
  match intBody.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
end

/-! ## Real ranges -/

section
open Jank.Seq.Range

def starts3 : List Int := starts ++ [-5, 1, 2147483000, -2147483640, 1073741823, 4294967295]
def steps3 : List Int := steps ++ [5, -2, 7, 1073741823, -1073741824, 2147483647]
def offsets3 : List Int := offsets ++ [0, 2, 3, 62, 66, 127, 128, 130, -1, -64, -66, -129]

def i32 (v : Int) : Bool := -2147483648 ≤ v && v ≤ 2147483647

def realClass (q : Question) (fuel : Nat) : Option String :=
  -- Elements Clojure produces, then one chunk (32) ahead: any outside i32 is R116's wrap.
  let n := (cljWalk fuel q.start q.step q.e).1.length + 33
  if (List.range n).any (fun k => !i32 (q.start + k * q.step)) then some "R116" else none

def realBody : EStateM Stop World Unit := do
  let s := (← pick (σ := World) "range.start" starts3).getD 0
  let st := (← pick (σ := World) "range.step" steps3).getD 1
  let off := (← pick (σ := World) "range.end_offset" offsets3).getD 1
  let q : Question := { start := s, step := st, e := ⟨2 * s + off⟩ }
  if let some d := q.verdict 80 then violate (σ := World) ((realClass q 80).getD "unexplained") d

def realRun (source : Source) : Ended :=
  match realBody.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
end

/-! ## Transducers -/

section
open Jank.Seq.Transducers

def tdBody (maxXf maxLen : Nat) : EStateM Stop World Unit := do
  let k := (← decide (σ := World) "xf.count" maxXf) + 1
  let mut xfs := []
  for i in [0:k] do
    xfs := xfs ++ [(← pick (σ := World) s!"xf.{i}" xforms).getD .map]
  let len ← decide (σ := World) "coll.length" (maxLen + 1)
  let mut coll := []
  for i in [0:len] do
    coll := coll ++ [Int.ofNat (← decide (σ := World) s!"coll.{i}" 3)]
  let stop ← decide (σ := World) "rf.stop" 3
  let q : Question := { xfs, coll, stop := if stop == 0 then none else some stop }
  if let some d := q.verdict then
    violate (σ := World) (if xfs.contains .partitionBy then "R118" else "unexplained") d

def tdRun (maxXf maxLen : Nat) (source : Source) : Ended :=
  match (tdBody maxXf maxLen).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
end

/-! ## Chunked seqs: `(first (map f … (range 0.0 n)))` for every n ≤ 200 and depth ≤ 4 -/

section
open Jank.Seq.Chunked

/-- Every source length 0..200 (and no end, capped by the model's fuel), map depth 1..4; R119 when
jank's answer is Clojure's first element with more calls of `f` (or it does not end). -/
def chunkedTable : Nat × Nat × Nat × List String := Id.run do
  let mut total := 0
  let mut r119 := 0
  let mut un : List String := []
  for n in (List.range 201).map some do
    for depth in [1, 2, 3, 4] do
      total := total + 1
      let c := program .clj n depth
      let j := program .jank n depth
      match j, c with
      | .ok a, .ok b =>
        if a != b then
          if a.1 == b.1 && a.2 > b.2 then r119 := r119 + 1
          else un := un ++ [s!"{code n depth}: Clojure {b.1} after {b.2} calls; jank {a.1} after {a.2} calls"]
      | .error e, .ok _ => un := un ++ [s!"{code n depth}: jank error {e}"]
      | _, .error e => un := un ++ [s!"{code n depth}: Clojure error {e}"]
  return (total, r119, un.length, un.take 10)
end

end Jank.R3.Search.Seq

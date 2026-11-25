import Jank.R3.Search.Common
import Jank.Compare
import Jank.Multi
import Jank.Ns
import Jank.Core.NsExtra

/-!
# Round 3: compare and sort, widened

Round 2 compared every ordered pair of a 24-value universe and sorted vectors of ≤ 3 atoms.
Here the universe has 47 values (both signed zeros, infinities, the long extremes, more
BigDecimals, strings, characters, keywords, symbols, vectors holding each kind, two equal lists
that are distinct objects), sorts run to 5 atoms over 12, and comparator sorts to 5 longs.

Each disagreement is put to a round-2 class:
- R96: a boolean is compared (at the top or inside vectors);
- R97: a keyword against a non-keyword (undefined behavior in jank);
- R98: the same object on both sides (Clojure's identity shortcut);
- R99: a BigDecimal against a double;
- a sort disagreement is explained when a pair of its elements has an explained compare
  disagreement, or the comparator kind is the long-difference one with an int overflow (RC4).
-/

namespace Jank.R3.Search.Core

open Determinismo Jank.Compare

def big : Int := 10 ^ 400

def universe3 : List CV :=
  [ .nil, .bool true, .bool false,
    .long 0, .long 1, .long (-1), .long 9007199254740993, .long 9223372036854775807, .long (-9223372036854775808),
    d 0.0 0 1 "0.0", d (-0.0) 0 1 "-0.0", d 1.5 3 2 "1.5", d (-1.5) (-3) 2 "-1.5", d 1.0 1 1 "1.0",
    d 0.1 3602879701896397 (2 ^ 55) "0.1", d (0.0 / 0.0) 0 1 "##NaN",
    d 9007199254740992.0 9007199254740992 1 "9007199254740992.0",
    d (1.0 / 0.0) big 1 "##Inf", d (-1.0 / 0.0) (-big) 1 "##-Inf",
    .dec 1 1, .dec 1 0, .dec 10 1, .dec (-5) 1, .dec 0 0,
    .str "", .str "a", .str "b", .str "ab", .str "B",
    .char 'a', .char 'b', .char 'A',
    .kw "" "a", .kw "x" "a", .kw "" "b", .kw "a" "b",
    .sym "" "a", .sym "" "b", .sym "x" "a",
    .vec [], .vec [.long 1], .vec [.long 1, .long 2], .vec [.kw "" "a"], .vec [d 1.0 1 1 "1.0"],
    .vec [.nil], .vec [.str "a"], .vec [.vec [.long 1]],
    .other 1 "'(1)", .other 2 "{}", .other 3 "'(1)" ]

partial def hasBool : CV → Bool
  | .bool _ => true
  | .vec xs => xs.any hasBool
  | _ => false

partial def isKw : CV → Bool
  | .kw .. => true
  | _ => false

def isDec : CV → Bool | .dec .. => true | _ => false
def isDbl : CV → Bool | .dbl .. => true | _ => false

/-- The round-2 class of a compare disagreement (top level or at the first differing vector
position), or none. -/
partial def explainCmp (a b : CV) (j c : Cmp) : Option String :=
  if hasBool a || hasBool b then some "R96"
  else match j with
  | .ub _ => if isKw a || isKw b || (match a, b with | .vec _, .vec _ => true | _, _ => false) then some "R97" else none
  | _ =>
    if identical a b then some "R98"
    else if (isDec a && isDbl b) || (isDbl a && isDec b) then some "R99"
    else match a, b with
    | .vec xs, .vec ys =>
      if xs.length != ys.length then none
      else
        -- the first position where both sides do not answer 0
        let rec go : List CV → List CV → Option String
          | x :: xs', y :: ys' =>
            let jx := jankCompare fuel x y
            let cx := cljCompare fuel x y
            if !jx.same cx then explainCmp x y jx cx
            else match jx with
              | .ok 0 => go xs' ys'
              | _ => none
          | _, _ => none
        go xs ys
    | _, _ => none

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev WM := EStateM Stop W

def runW (body : WM Unit) (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }

/-- `(compare a b)` over the widened universe; a class per disagreement (census), `unexplained`
otherwise. -/
def comparePair3 : WM Unit := do
  let n := universe3.length
  let a := universe3.getD (← decide (σ := W) "compare.a" n) .nil
  let b := universe3.getD (← decide (σ := W) "compare.b" n) .nil
  let jr := jankCompare fuel a b
  let cr := cljCompare fuel a b
  if !jr.same cr then
    let cls := (explainCmp a b jr cr).getD "unexplained"
    violate (σ := W) cls s!"(compare {a.code} {b.code}): Clojure {showCmp cr}, jank {showCmp jr}"

def sortAtoms3 : List CV :=
  [ .long 1, .long 0, .long (-1), .bool true, .kw "" "a", .kw "" "b", .str "a", .str "b", .nil,
    d 1.5 3 2 "1.5", d 1.0 1 1 "1.0", .dec 1 0 ]

/-- `(sort [xs])`, lengths ≤ `maxLen`; explained when some pair has an explained compare
disagreement. -/
def sortVec3 (maxLen : Nat) : WM Unit := do
  let len ← decide (σ := W) "sort.length" (maxLen + 1)
  let mut xs : List CV := []
  for _ in [0:len] do
    xs := xs ++ [sortAtoms3.getD (← decide (σ := W) "sort.elem" sortAtoms3.length) .nil]
  let jr := jankSort xs
  let cr := cljSort xs
  let same := match jr, cr with
    | .ok a, .ok b => a.map CV.code == b.map CV.code
    | .error a, .error b => a.same b
    | _, _ => false
  if !same then
    let pairs := xs.flatMap fun a => xs.map fun b => (a, b)
    let cls := pairs.findSome? fun (a, b) =>
      let j := jankCompare fuel a b
      let c := cljCompare fuel a b
      if j.same c then none else explainCmp a b j c
    violate (σ := W) (cls.getD "unexplained")
      s!"(sort [{" ".intercalate (xs.map CV.code)}]): Clojure {showSort cr}, jank {showSort jr}"

def fnLongs3 : List Int := [0, 1, 2, -1, 3000000000, -3000000000]

/-- `(sort f [xs])` with each comparator kind, lengths ≤ `maxLen`. -/
def sortFn3 (maxLen : Nat) : WM Unit := do
  let k := fnKinds.getD (← decide (σ := W) "sortfn.kind" fnKinds.length) .lt
  let len ← decide (σ := W) "sortfn.length" (maxLen + 1)
  let mut xs : List Int := []
  for _ in [0:len] do
    xs := xs ++ [fnLongs3.getD (← decide (σ := W) "sortfn.elem" fnLongs3.length) 0]
  let jr := insertionSort (jankFnLess k) xs
  let cr := timSortSmall (cljFnCompare k) xs
  let same := match jr, cr with
    | .ok a, .ok b => a == b
    | .error a, .error b => a.same b
    | _, _ => false
  if !same then
    let narrowing := k == .diff && xs.any (fun a => xs.any fun b => a - b ≥ 2 ^ 31 ∨ a - b < -(2 ^ 31))
    let shw := fun (r : Except Cmp (List Int)) => match r with
      | .ok l => s!"{l}" | .error c => showCmp c
    violate (σ := W) (if narrowing then "RC4 (Clojure narrows a long comparator result to int)" else "unexplained")
      s!"(sort {k.code} {xs}): Clojure {shw cr}, jank {shw jr}"

/-! ## Multimethods: census of R100 over wider programs -/

def multiCensusRun (derives defs prefs : Nat) (source : Source) : Ended :=
  let e := Jank.Multi.run derives defs prefs source
  match e.violation with
  | some (_, d) => { e with violation := some ("R100", d) }
  | none => e

def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun l => (List.range (l.length + 1)).map fun i => l.take i ++ [x] ++ l.drop i

/-- Dispatch depends on the method table's iteration order (in Clojure's own algorithm, and so in
jank's, whose table is another hash map with other hashes): programs whose call ends differently
under some permutation of the methods. Census class "order-dependent". -/
def orderBody (derives defs prefs : Nat) : EStateM Stop Jank.Multi.World Unit := do
  let mut h : Jank.Multi.H := {}
  let mut lines : Array String := #["(defmulti f identity)"]
  for _ in [0:derives] do
    let c ← decide (σ := Jank.Multi.World) "multi.derive.child" Jank.Multi.tags
    let p ← decide (σ := Jank.Multi.World) "multi.derive.parent" Jank.Multi.tags
    if let some h' := Jank.Multi.derive h c p then
      h := h'
      lines := lines.push s!"(derive {Jank.Multi.tagCode c} {Jank.Multi.tagCode p})"
  let mut mm : Jank.Multi.MM := {}
  for _ in [0:defs] do
    let k ← decide (σ := Jank.Multi.World) "multi.defmethod" Jank.Multi.tags
    if !mm.methods.contains (some k) then
      mm := { mm with methods := mm.methods ++ [some k] }
      lines := lines.push s!"(defmethod f {Jank.Multi.tagCode k} ...)"
  for _ in [0:prefs] do
    let x ← decide (σ := Jank.Multi.World) "multi.prefer.x" Jank.Multi.tags
    let y ← decide (σ := Jank.Multi.World) "multi.prefer.y" Jank.Multi.tags
    if x != y && !Jank.Multi.prefers mm (some h) 16 y x then
      mm := { mm with prefers := Jank.Multi.put mm.prefers x ((Jank.Multi.look mm.prefers x) ++ [y]) }
      lines := lines.push s!"(prefer-method f {Jank.Multi.tagCode x} {Jank.Multi.tagCode y})"
  let dv ← decide (σ := Jank.Multi.World) "multi.call" Jank.Multi.tags
  let perms := perms mm.methods
  let outs := perms.map fun ms => Jank.Multi.cljCall { mm with methods := ms } h dv
  match outs with
  | o :: rest =>
    if rest.any (· != o) then
      let shown := (perms.zip outs).map fun (ms, out) =>
        s!"{ms.map fun (m : Option Nat) => (m.map Jank.Multi.tagCode).getD ":default"} → {out.code}"
      violate (σ := Jank.Multi.World) "order-dependent"
        s!"{" ".intercalate lines.toList} (f {Jank.Multi.tagCode dv}): {shown}"
  | [] => pure ()

def orderRun (d m p : Nat) (source : Source) : Ended :=
  match (orderBody d m p).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }

/-! ## Namespaces -/

/-- Fork C's namespace world with R102 (`intern` keeps a referred var) and R103 (`remove-ns`
of clojure.core) replaced by Clojure's behavior: `define`, `refer` and `ns-unmap` stay jank's. -/
def nsFixedRun (ops : Nat) (source : Source) : Ended := Jank.Ns.run ops source true

section
open Jank.Core.NsExtra in
/-- The class of the first disagreeing operation of the second namespace world. -/
def nsExtraClass : Op → String
  | .reloadNs => "R109"
  | .findVarCurrentInc | .findVarUnqualified | .findVarNoNs => "R110"
  | .nsResolveA | .resolveS => "R111"
  | .inNsB => "R112"
  | _ => "unexplained"

open Jank.Core.NsExtra in
def nsExtraBody (n : Nat) : EStateM Stop Jank.Core.NsExtra.World Unit := do
  let mut j := start
  let mut c := start
  let mut prog : List String := []
  for i in [0:n] do
    let op := ops.getD (← decide (σ := Jank.Core.NsExtra.World) s!"ns.op{i}" ops.length) .defInc
    prog := prog ++ [op.code j.current]
    let (j', oj) := step true j op
    let (c', oc) := step false c op
    j := j'
    c := c'
    if !sameOut oj oc then
      violate (σ := Jank.Core.NsExtra.World) (nsExtraClass op)
        s!"{" ".intercalate prog}: Clojure {showOut oc}, jank {showOut oj}"

def nsExtraRun (n : Nat) (source : Source) : Ended :=
  match (nsExtraBody n).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
end

end Jank.R3.Search.Core

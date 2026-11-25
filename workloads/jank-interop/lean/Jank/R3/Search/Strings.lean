import Jank.R3.Search.Common
import Jank.StrModel
import Jank.PrintModel

/-!
# Round 3: strings and characters (non-regex), one size beyond round 2

Round 2's table had texts of ≤ 3 code points (175,638 questions). Here every question of round
2's grammar with texts of ≤ 4 code points (both locales) is put to `explainStr`, which names the
round-2 class whose trigger the question carries, or none:

- R52 `count`/`nth`/`get`/`contains?`/`subs` on a non-ASCII text (bytes);
- R53 `seq`/`count (seq)`/`int (first)` (UTF-8 locale) with a supplementary code point;
- R55/R56 string-seq `=`/hash with a non-ASCII text (R56: any non-empty text);
- R57 `compare` with a supplementary code point in either text (for BMP text UTF-8 byte order is
  UTF-16 order);
- R58 `index-of`/`last-index-of` with a non-ASCII text or needle, or a start outside [0, count];
- R59 `trim`/`blank?` with a Java-only whitespace (U+001F, U+2003);
- R60 case mapping: `ß` or `Σ` in the text, or the C locale with a non-ASCII text;
- R61 `capitalize` with a non-ASCII first code point;
- R62 `replace ""` on a non-ASCII text; R63 `escape` with a non-ASCII key;
- R64 `int (first)` under the C locale with a non-ASCII first code point.
-/

namespace Jank.R3.Search.Strings

open Determinismo Jank.Str

def nonAscii (s : List Nat) : Bool := s.any (· ≥ 0x80)
def supp (s : List Nat) : Bool := s.any (· ≥ 0x10000)

/-! Byte specifications: Clojure's semantics with the UTF-8 bytes as the characters (jank's
documented string model). A byte-indexed answer that equals these is R52/R58; any other
disagreement is unexplained. -/

def bNth (s : List UInt8) (i : Int) : R :=
  if i < 0 ∨ s.length ≤ i.toNat then .err "out of bounds" else .chr [s.getD i.toNat 0]
def bGet (s : List UInt8) (i : Int) : R :=
  if i < 0 ∨ s.length ≤ i.toNat then .nil else .chr [s.getD i.toNat 0]
def bSubs (s : List UInt8) (start stop : Int) : R :=
  if start < 0 ∨ stop < start ∨ stop.toNat > s.length then .err "out of bounds"
  else .str ((s.drop start.toNat).take (stop - start).toNat)
def units (s : List UInt8) : List Nat := s.map (·.toNat)

/-- The byte-level answer of a question, when the operation has one. -/
def byteSpec (c : Case) : Option R :=
  let js := jstr c.s
  match c.op with
  | .count => some (.int js.length)
  | .nth i => some (bNth js i)
  | .get i => some (bGet js i)
  | .contains i => some (.bool (decide (0 ≤ i ∧ i.toNat < js.length)))
  | .subs1 i => some (bSubs js i js.length)
  | .subs2 i j => some (bSubs js i j)
  | .indexOf n f => some (cIndexOf (units js) (units (jstr n)) (f.getD 0))
  | .lastIndexOf n f => some (cLastIndexOf (units js) (units (jstr n)) (f.getD js.length))
  | .replaceEmpty => some (.str ([0x2D] ++ js.flatMap (fun b => [b, 0x2D])))
  | .seq => if c.s.isEmpty then some .nil else some (.chars (c.s.map utf8))
  | .seqCount => some (.int c.s.length)
  | _ => none

def explainStr (c : Case) (j : R) : Option String :=
  let s := c.s
  let bytewise := match byteSpec c with | some b => b.agrees j | none => false
  match c.op with
  | .count | .nth _ | .get _ | .contains _ | .subs1 _ | .subs2 .. =>
    if nonAscii s && bytewise then some "R52" else none
  | .seq | .seqCount => if supp s && bytewise then some "R53" else none
  | .firstInt =>
    if c.loc == .c && (s.head?.getD 0) ≥ 0x80 then some "R64"
    else if supp (s.take 1) then some "R53" else none
  | .seqSelfEq | .seqEqVec => if nonAscii s then some "R55" else none
  | .seqHashVec => if !s.isEmpty then some "R56" else none
  | .compare => if supp s || supp c.t then some "R57" else none
  | .indexOf _ f | .lastIndexOf _ f =>
    if bytewise then some "R58"
    else match f with
      | some k => if k < 0 || k > (jstr s).length then some "R58 (start outside [0, count])" else none
      | none => none
  | .trim | .triml | .trimr | .blank => if s.contains 0x1F || s.contains 0x2003 then some "R59" else none
  | .upper | .lower =>
    if s.contains 0xDF || s.contains 0x3A3 || (c.loc == .c && nonAscii s) then some "R60" else none
  | .capitalize =>
    if (s.head?.getD 0) ≥ 0x80 then some "R61"
    else if s.contains 0xDF || s.contains 0x3A3 || (c.loc == .c && nonAscii s) then some "R60" else none
  | .replaceEmpty => if nonAscii s && bytewise then some "R62" else none
  | .escape k => if k ≥ 0x80 then some "R63" else none
  | .reverse => none

structure Tally where
  total : Nat := 0
  agree : Nat := 0
  byClass : List (String × Nat) := []
  unexplained : Array String := #[]
  unexplainedCount : Nat := 0

/-- Every question with texts of ≤ `n` code points (compare: ≤ `m` × ≤ `m`). -/
def tallyAll (n m : Nat) : Tally := Id.run do
  let ts := texts n
  let ts2 := texts m
  let mut t : Tally := {}
  for loc in [Locale.utf8, Locale.c] do
    for s in ts do
      let cases := ((opsFor s).filter (fun op => loc == .utf8 || op.localeDependent)).map (fun op => ({ loc, op, s } : Case)) ++
        (if loc == .utf8 && s.length ≤ m then ts2.map fun u => ({ loc, op := .compare, s, t := u } : Case) else [])
      for c in cases do
        t := { t with total := t.total + 1 }
        let (j, cl) := c.eval
        if j.agrees cl then t := { t with agree := t.agree + 1 }
        else
          match explainStr c j with
          | some r =>
            t := { t with byClass := match t.byClass.lookup r with
              | some k => (r, k + 1) :: t.byClass.filter (·.1 != r)
              | none => (r, 1) :: t.byClass }
          | none =>
            t := { t with unexplainedCount := t.unexplainedCount + 1 }
            if t.unexplained.size < 20 then
              t := { t with unexplained := t.unexplained.push s!"{c.program} [{c.loc.name}]: Clojure {cl.show}, jank {j.show}" }
  return t

/-! ## `str` of collections, depth ≤ 3 -/

section
open Jank.Print

/-- Values of depth ≤ 3: round 2's depth-2 values, and vectors, lists, sets and one-entry maps
holding one of them. -/
def values3 : List PV :=
  values ++ values.flatMap fun v => [.vec [v], .list [v], .set [v], .map [(.kw "k", v)], .vec [.int 1, v]]

partial def holdsText : PV → Bool
  | .str _ | .chr _ => true
  | .vec xs | .list xs | .set xs => xs.any holdsText
  | .map kvs => kvs.any fun (k, v) => holdsText k || holdsText v
  | _ => false

def isColl : PV → Bool
  | .vec _ | .list _ | .set _ | .map _ => true
  | _ => false

/-- `str` (R69 when a collection holds a string or character) and `print-str`. -/
def printTable : Nat × Nat × Nat × List String := Id.run do
  let mut r69 := 0
  let mut unexplained : List String := []
  let mut total := 0
  for v in values3 do
    total := total + 1
    if jankStr v != cljStr v then
      if isColl v && holdsText v then r69 := r69 + 1
      else unexplained := unexplained ++ [s!"(str {codeString v}): Clojure {repr (cljStr v)}, jank {repr (jankStr v)}"]
  return (total, r69, unexplained.length, unexplained.take 10)
end

end Jank.R3.Search.Strings

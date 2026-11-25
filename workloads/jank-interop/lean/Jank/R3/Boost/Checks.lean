import Jank.R3.Boost.Num
import Jank.LexBytes

/-!
# Round 3, Boost: checks of the replica itself

- `pow2` table: the 256 `from_lst` lines of cpp_dec_float.hpp:2890-3146 parsed from the header
  and compared with the exact powers of two the replica builds.
- `cpp_int` decimal printing (`CppInt.str`) against `toString`, and `CppInt.toDouble` against
  the correctly rounded conversion.
- RA5: round 2's assumed `boostParse` (Jank/LexBytes.lean) against the replica
  `CppInt.assignString`, over every string up to a length over each character class.
-/

namespace Jank.R3.Boost.Checks

open Jank.R3.Boost Jank.R3.Boost.Dec

/-- The `from_lst( { a, b, ... }, e )` lines of the `pow2` table, in order. -/
def parsePow2Table (text : String) : List (List Nat × Int) := Id.run do
  let lines := text.splitOn "\n"
  let mut inTable := false
  let mut out : Array (List Nat × Int) := #[]
  for l in lines do
    if (l.splitOn "local_pow2_data").length > 1 then inTable := true
    if inTable && (l.splitOn "from_lst(").length > 1 then
      let afterOpen := (l.splitOn "{").getD 1 ""
      let inside := (afterOpen.splitOn "}").getD 0 ""
      let nums := (inside.splitOn ",").filterMap fun t =>
        let d := t.toList.filter Char.isDigit
        if d.isEmpty then none else some (String.ofList d).toNat!
      let rest := (afterOpen.splitOn "}").getD 1 ""
      let expTxt := ((rest.splitOn ")").getD 0 "").toList.filter (fun c => c.isDigit || c == '-')
      let e : Int := if expTxt.head? == some '-' then -((String.ofList (expTxt.drop 1)).toNat! : Int)
        else (String.ofList expTxt).toNat!
      out := out.push (nums, e)
    if inTable && (l.splitOn "}};").length > 1 then inTable := false
  return out.toList

def pow2TableMatchesHeader (text : String) : Nat × List String := Id.run do
  let table := parsePow2Table text
  let mut bad : Array String := #[]
  let mut i := 0
  for (nums, e) in table do
    let p : Int := (i : Int) - 128
    let mine := pow2 p
    let theirs := fromLst nums e
    if mine.data != theirs.data || mine.exp != theirs.exp then
      bad := bad.push s!"2^{p}: header {nums} e{e}, replica {mine.data.toList} e{mine.exp}"
    i := i + 1
  return (table.length, bad.toList)

/-- RA5: the round-2 assumption, exhaustively against the replica. Both read a NUL-free byte
string; values must agree and both must throw on the same strings. -/
def ra5Alphabet : List Nat := (Jank.R3.Boost.Dec.codes "0178x9aAfFgX-+ ")

partial def allStrings (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => [] :: (alphabet.flatMap fun c => (allStrings alphabet n).map (c :: ·))

/-- The `i`-th string of length `len` over `alphabet` (base-k digits of `i`). -/
def nthString (alphabet : Array Nat) (len i : Nat) : List Nat := Id.run do
  let k := alphabet.size
  let mut out : List Nat := []
  let mut j := i
  for _ in [0:len] do
    out := alphabet[j % k]! :: out
    j := j / k
  return out

/-- Every string of length ≤ `len`, each once, folded. -/
def foldStrings {β : Type} (alphabet : List Nat) (len : Nat) (init : β) (f : β → List Nat → β) : β := Id.run do
  let a := alphabet.toArray
  let mut acc := init
  for l in [0:len + 1] do
    for i in [0:a.size ^ l] do
      acc := f acc (nthString a l i)
  return acc

def ra5Check (len : Nat) : Nat × List String :=
  let (n, bad) := foldStrings ra5Alphabet len ((0 : Nat), (#[] : Array String)) fun (n, bad) s =>
    let r2 := Jank.LexBytes.boostParse (s.map (·.toUInt8))
    let r3 := CppInt.assignString s
    let ok := match r2, r3 with
      | .ok a, .ok b => a == b
      | .error _, .error _ => true
      | _, _ => false
    (n + 1, if ok then bad else bad.push s!"{String.ofList (s.map Char.ofNat)}: round 2 {reprStr r2}, replica {reprStr r3}")
  (n, bad.toList)

/-- `CppInt.str` against `toString` and `CppInt.toDouble` against the nearest double. -/
def cppIntChecks : Nat × List String := Id.run do
  let mut vals : Array Int := #[]
  for k in [0:300] do
    let base : Int := (7 : Int) ^ k
    vals := vals ++ #[base, -base, base - 1, base + 1, (2 : Int) ^ k, (2 : Int) ^ k + 1, (10 : Int) ^ (k % 120), -((2 : Int) ^ k) - 1]
  let mut bad : Array String := #[]
  for v in vals do
    if CppInt.str v != toString v then bad := bad.push s!"str {v}: {CppInt.str v}"
    let d := CppInt.toDouble v
    let want := Ieee.ofIntRN v
    if d.toBits != want.toBits then bad := bad.push s!"toDouble {v}: {d} vs {want}"
  return (vals.size, bad.toList)

/-- `rd_string` then `str()` round trip on exact decimals that fit, and `ofDouble` exactness on
doubles whose expansion fits 128 digits. -/
def decChecks : Nat × List String := Id.run do
  let mut bad : Array String := #[]
  let mut n := 0
  let samples : List String := ["1", "1.5", "0.1", "-2.5", "123456789.123456789", "1e10", "1e-10",
    "0.0001", "99999999", "100000000", "12345678901234567890", "-0.000123", "7e300", "1e-300"]
  for s in samples do
    n := n + 1
    match rdString (codes s), Java.BD.ofString (codes s) with
    | .ok x, .ok b =>
      match x.rat with
      | some r => if !Num.ratEq r b.rat then bad := bad.push s!"rd_string {s}: value {reprStr r}"
      | none => bad := bad.push s!"rd_string {s}: not finite"
    | _, _ => bad := bad.push s!"rd_string {s}: error"
  -- Doubles with short expansions convert exactly (2^-k·m with k ≤ 128).
  for k in [0:60] do
    for m in [1, 3, 5, 7, 12345, 9007199254740991] do
      n := n + 1
      let x : Float := Float.ofScientific m false 0 / (2.0 : Float) ^ (k.toFloat)
      let c := ofDouble x
      let (neg, p, q) := Ieee.exact x
      match c.rat with
      | some r => if !Num.ratEq r (if neg then -(p : Int) else p, q) then bad := bad.push s!"ofDouble {x}: not exact"
      | none => bad := bad.push s!"ofDouble {x}: not finite"
  return (n, bad.toList)

end Jank.R3.Boost.Checks

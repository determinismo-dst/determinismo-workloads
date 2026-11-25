import Jank.R3.Boost.Num
import Jank.Compare
import Jank.Numbers
import Jank.PrintModel

/-!
# Round 3, Boost: the round 1/2 assumptions against the replica

Each check runs a round 1/2 function (the assumed behavior) and the replica on the same inputs:

- RC2 (round 2, `Jank.Compare.cppNumCmp`): a BigDecimal against a double compares exactly.
- RB7 (round 2, `Jank.Print.jankDec`): `str()` prints the value with no trailing zeros, in fixed
  notation, plus `.0`.
- D7 (round 1, `Jank.Numbers.jankBigdecOfLong`): `(bigdec long)` is the long through a double.
- D8 (round 1, `Jank.Numbers.jankDecEq`): BigDecimal `=` is |a − b| < 2^-52 exactly.
-/

namespace Jank.R3.Boost.Assumptions

open Jank.R3.Boost Jank.R3.Boost.Dec Jank.R3.Boost.Num

def decLit (n : Int) (s : Nat) : String :=
  let a := n.natAbs
  let p := 10 ^ s
  let frac := toString (a % p)
  let frac := String.ofList (List.replicate (s - frac.length) '0') ++ frac
  (if n < 0 then "-" else "") ++ toString (a / p) ++ (if s == 0 then "" else "." ++ frac)

def rd (n : Int) (s : Nat) : CDF :=
  match rdString (bytes (decLit n s)) with | .ok x => x | .error _ => nanV

def dbls : List Float :=
  [0.0, 0.1, -0.1, 0.5, 1.0, 1.5, 0.3, 2.675, 1e-5, 1e23, -1e23, 1e300, 5e-324, 2.2250738585072014e-308,
   1.7976931348623157e308, 9007199254740993.0, 123.456, -7.25, 0.001, 3.141592653589793]

def mkDbl (x : Float) : Jank.Compare.Dbl :=
  let (neg, p, q) := Ieee.exact x
  { f := x, num := if neg then -(p : Int) else p, den := q, code := toString x }

/-- RC2: `cppNumCmp (.dec n s) (.dbl d)` against the replica's `(data < d) − (d < data)`. -/
def rc2 : Nat × List String := Id.run do
  let mut n := 0
  let mut bad : Array String := #[]
  for u in (List.range 121).map (fun (i : Nat) => (i : Int) - 60) do
    for s in [0, 1, 2, 3, 4] do
      for d in dbls do
        n := n + 1
        let r2 := Jank.Compare.cppNumCmp (.dec u s) (.dbl (mkDbl d))
        let x := rd u s
        let lt := dlt x (ofDouble d)
        let gt := dlt (ofDouble d) x
        let r3 : Int := (if gt then 1 else 0) - (if lt then 1 else 0)
        -- cppNumCmp returns sign(this − o) for (.dec, .dbl): -1 when this < o.
        let r3' : Int := if lt then -1 else if gt then 1 else 0
        let _ := r3
        if r2 != r3' then bad := bad.push s!"{decLit u s}M vs {d}: round 2 {r2}, replica {r3'}"
  return (n, bad.toList)

/-- RB7: round 2's `jankDec` against the replica's `to_string`. -/
def rb7 : Nat × List String := Id.run do
  let mut n := 0
  let mut bad : Array String := #[]
  for u in [0, 1, -1, 5, 12, 150, 1000, -2500, 123456789, 100000000, 99999999, 7] do
    for s in List.range 14 do
      n := n + 1
      let r2 := Jank.Print.jankDec ⟨u, s⟩
      let r3 := decStr (rd u s)
      if r2 != r3 then bad := bad.push s!"{decLit u s}M: round 2 {r2}, replica {r3}"
  return (n, bad.toList)

/-- D7: round 1's integral value of `(bigdec v)` against the replica's decimal. -/
def d7 : Nat × List String := Id.run do
  let mut n := 0
  let mut bad : Array String := #[]
  let mut vals : Array Int := #[]
  for k in [0:64] do
    for off in [-3, -1, 0, 1, 3] do
      let v : Int := (2 : Int) ^ k + off
      if CppInt.fitsI64 v then vals := vals.push v
      if CppInt.fitsI64 (-v) then vals := vals.push (-v)
  for v in vals do
    n := n + 1
    let r1 := Jank.Numbers.jankBigdecOfLong v
    match (ofDouble (Ieee.ofIntRN v)).rat with
    | some (p, q) => if p != r1 * (q : Int) then bad := bad.push s!"{v}: round 1 {r1}, replica {p}/{q}"
    | none => bad := bad.push s!"{v}: replica not finite"
  return (n, bad.toList)

/-- D8: round 1's `jankDecEq` against the replica's `big_decimal::equal`. -/
def d8 : Nat × List String := Id.run do
  let mut n := 0
  let mut bad : Array String := #[]
  let pts : List (Int × Nat) :=
    [(0, 0), (1, 0), (10000000000000000001, 19), (15, 17), (3, 16), (22204460492503131, 32),
     (22204460492503130, 32), (22204460492503132, 32), (-1, 0), (100000000000000000000001, 23),
     (1, 52), (-15, 17), (4440892098500626, 31), (4440892098500627, 31), (2220446049250313, 31)]
  for (a, sa) in pts do
    for (b, sb) in pts do
      n := n + 1
      let r1 := Jank.Numbers.jankDecEq ⟨a, sa⟩ ⟨b, sb⟩
      let r3 := jEqual (.dec (rd a sa)) (.dec (rd b sb))
      if r1 != r3 then bad := bad.push s!"{decLit a sa}M = {decLit b sb}M: round 1 {r1}, replica {r3}"
  return (n, bad.toList)

end Jank.R3.Boost.Assumptions

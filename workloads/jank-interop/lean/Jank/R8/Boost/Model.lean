import Jank.R3.Boost.DecFloat
import Jank.R3.Boost.Java

/-!
# Round 8, area B: boost's `cpp_dec_float<100>` as jank 94d32623 computes with it

jank's BigDecimal is `number<cpp_dec_float<100>, et_off>` (upstream-r5/compiler+runtime
include/cpp/jank/type.hpp 35). The limb-level replica is round 3's (`Jank.R3.Boost.Dec`,
cpp_dec_float.hpp at jank's pin, line by line): 16 limbs of 10^8 (`elem_number = 100/8 + 1 + 3`,
cpp_dec_float.hpp 116), an exponent that is a multiple of 8, `prec_elem` (how many limbs a
product reads), `rd_string` 2083-2395, `operator+=` 759-937, `operator-=` 940-948, `operator*=`
951-1012 with the school product 609-643 / 2643-2688, `operator/=` 1016-1047 and
`calculate_inv` 1222-1270 (Newton from a double estimate, precision 6/9/15/16 limbs), `str`
1913-2081 with `format_float_string` (number_base.hpp 1314-1466).

Round 8 adds what jank's paths put around it, so a line of the standalone boost program
`.r8-scratch/boost/check.cpp` has a Lean counterpart here:
- `sci`: `str(0, scientific)`, every stored digit (S2's exact_divide reads this text);
- `jankText`: big_decimal.cpp to_string → jtl string_builder.cpp 240-249: `str()`, then ".0"
  when the text has no '.';
- `exactDivide`: S2's `exact_divide` (fixes/S2.diff; .r8-scratch/merge/tree big_decimal.cpp
  179-273), whose quotient is built as text and read back by `rd_string`;
- `jankRem`: math.cpp rem 269-289 (`fmod` of the magnitudes, the dividend's sign).
-/

namespace Jank.R8.Boost

open Jank.R3.Boost.Dec

/-- A decimal string read by `rd_string` (the `native_big_decimal{ s.c_str() }` constructor). -/
def rd (s : String) : Except String CDF := rdString (codes s)

/-- `str(0, std::ios_base::scientific)`: every digit the 16 limbs hold, plus format_float_string's
scientific padding. -/
def sci (x : CDF) : String := x.str 0 { scientific := true }

/-- jank's text of a BigDecimal (string_builder.cpp 240-249). -/
def jankText (x : CDF) : String :=
  let s := x.str
  if s.toList.contains '.' then s else s ++ ".0"

/-- One output line of check.cpp for a decimal result. -/
def out (x : CDF) : String := sci x ++ "|" ++ jankText x

/-- `(b < a) - (a < b)`: boost's `<` on finite values is `compare(...) < 0`
(number_compare.hpp; default_ops eval_lt). jank's big_decimal::compare 182-190. -/
def cmp (a b : CDF) : Int :=
  (if b.compare a < 0 then 1 else 0) - (if a.compare b < 0 then 1 else 0)

/-- `std::stoll` of the exponent text `[+-]digits`. -/
def stoll (cs : List Char) : Int :=
  let (neg, rest) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let v : Int := (rest.takeWhile Char.isDigit).foldl (fun a c => a * 10 + (c.toNat - 48 : Nat)) 0
  if neg then -v else v

/-- S2's `to_exact_decimal` (fixes/S2.diff): the digits of `str(0, scientific)` without leading
zeros, as `digits × 10^(exponent − fraction_digits)`. A '.' is skipped (`continue`); every other
character before the 'e' counts as a fraction digit once the point was seen, a skipped leading
zero included. -/
def toExactDecimal (x : CDF) : Int × Int := Id.run do
  let text := (sci x).toList
  let mut i := 0
  let mut negative := false
  if text.length > 0 && (text[0]! == '-' || text[0]! == '+') then
    negative := text[0]! == '-'
    i := 1
  let mut digits : List Char := []
  let mut frac : Int := 0
  let mut after := false
  let mut fuel := text.length + 1
  while fuel > 0 && i < text.length && text[i]! != 'e' && text[i]! != 'E' do
    fuel := fuel - 1
    let c := text[i]!
    if c == '.' then
      after := true
    else
      if !(digits.isEmpty && c == '0') then digits := digits ++ [c]
      if after then frac := frac + 1
    i := i + 1
  let mut exponent : Int := 0
  if i + 1 < text.length then exponent := stoll (text.drop (i + 1))
  let dv : Nat := digits.foldl (fun a c => a * 10 + (c.toNat - 48)) 0
  return (if negative then -(dv : Int) else dv, exponent - frac)

/-- How many factors `p` divide `d > 0`, and the rest (exact_divide's two while loops). -/
def stripP (p : Nat) : (fuel d : Nat) → Nat × Nat
  | 0, d => (0, d)
  | fuel + 1, d =>
    if d ≠ 0 ∧ d % p = 0 then
      let r := stripP p fuel (d / p)
      (r.1 + 1, r.2)
    else (0, d)

def nonTerminating : String :=
  "Non-terminating decimal expansion; no exact representable decimal result."

/-- S2's `exact_divide(l, r)`: an error is S2's boxed throw. -/
def exactDivide (l r : CDF) : Except String CDF :=
  if !l.isfinite || !r.isfinite then .ok (l.div r)
  else if r.iszero then .error "Divide by zero"
  else
    let (ad, ae) := toExactDecimal l
    let (bd, be) := toExactDecimal r
    let g : Int := (Int.gcd ad bd : Nat)
    let n0 := ad / g
    let d0 := bd / g
    let (n, d) := if d0 < 0 then (-n0, -d0) else (n0, d0)
    let dn := d.toNat
    let (twos, d2) := stripP 2 dn dn
    let (fives, d5) := stripP 5 d2 d2
    if d5 != 1 then .error nonTerminating
    else
      let k := max twos fives
      let n' := n * ((2 : Int) ^ (k - twos)) * ((5 : Int) ^ (k - fives))
      let exponent : Int := ae - be - (k : Int)
      rd (toString n' ++ "e" ++ toString exponent)

/-- jank's `rem` of two BigDecimals (math.cpp 269-289). -/
def jankRem (l r : CDF) : Except String CDF :=
  if cmp r zero == 0 then .error "Division by zero is not permitted."
  else
    let result := fmod l.abs r.abs
    .ok (if cmp l zero < 0 then result.negate else result)

/-- The value of the 16 limbs as one 128-digit integer (`data[0]` most significant). -/
def limbsVal (x : CDF) : Nat := (List.range 16).foldl (fun a i => a * 100000000 + x.d i) 0

/-- One line of check.cpp's input: an operation and its operands. -/
structure Item where
  op : String
  a : String
  b : String := ""
  deriving Inhabited

def Item.line (it : Item) : String :=
  if it.b.isEmpty then it.op ++ "\t" ++ it.a else it.op ++ "\t" ++ it.a ++ "\t" ++ it.b

def outE (r : Except String CDF) : String :=
  match r with
  | .ok x => out x
  | .error m => "throw|" ++ m

def bind2 (a b : String) (f : CDF → CDF → Except String CDF) : Except String CDF := do
  let x ← rd a
  let y ← rd b
  f x y

def longOf (s : String) : Int := stoll s.toList

/-- The replica's answer to one line, in check.cpp's format. -/
def Item.eval (it : Item) : String :=
  match it.op with
  | "rd" => outE (rd it.a)
  | "add" => outE (bind2 it.a it.b fun x y => .ok (x.add y))
  | "sub" => outE (bind2 it.a it.b fun x y => .ok (x.sub y))
  | "mul" => outE (bind2 it.a it.b fun x y => .ok (x.mul y))
  | "div" => outE (bind2 it.a it.b fun x y => .ok (x.div y))
  | "divl" => outE (do let x ← rd it.a; pure (x.div (ofLL (longOf it.b))))
  | "xdiv" => outE (bind2 it.a it.b exactDivide)
  | "xdivl" => outE (do let x ← rd it.a; exactDivide x (ofLL (longOf it.b)))
  | "cmp" => match rd it.a, rd it.b with
    | .ok x, .ok y => toString (cmp x y)
    | .error m, _ => "throw|" ++ m
    | _, .error m => "throw|" ++ m
  | "pq" => outE (bind2 it.a it.b fun x p => .ok (p.mul (x.div p)))
  | "px" => outE (bind2 it.a it.b fun x p => do let q ← exactDivide x p; pure (p.mul q))
  | "rem" => outE (bind2 it.a it.b jankRem)
  | _ => "bad-op|" ++ it.op

/-! ## Clojure's side: java.math.BigDecimal (round 3's `Java.BD`, checked against JDK 23 in
round 7), exact. -/

open Jank.R3.Boost.Java in
def cljRead (s : String) : BD := match BD.ofString (codes s) with
  | .ok b => b
  | .error _ => ⟨0, 0⟩

end Jank.R8.Boost

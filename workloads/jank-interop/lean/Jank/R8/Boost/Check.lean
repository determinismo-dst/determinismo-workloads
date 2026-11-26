import Jank.R8.Boost.Model
import Jank.R8.Boost.Spec

/-!
# Round 8, area B: the checks

1. The replica against boost itself: `inputs` writes check.cpp's lines; `compare` reads boost's
   answers (built for x86-64, jank's platform, and arm64 with and without FMA contraction) and
   counts, per operation, the lines where the replica's text differs.
2. The replica against the value-level functions of `Spec` (S4's rules): `specCheck`.
3. The programs that see S4, on stock (Newton division) and with the combined patch (S2's exact
   division; D8's exact `=` is not observed: every program compares with `compare` or `str`), and
   Clojure's exact BigDecimal (`Java.BD`).
-/

namespace Jank.R8.Boost.Check

open Jank.R3.Boost.Dec Jank.R3.Boost.Java Jank.R8.Boost Jank.R8.Boost.Spec

/-- The sdk's `mixSeed` (Determinismo/Decide.lean 35-40): splitmix64's finalizer. -/
def mix (seed : Nat) : Nat :=
  let m := 2 ^ 64
  let z := (seed + 0x9E3779B97F4A7C15) % m
  let z := ((z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9) % m
  let z := ((z ^^^ (z >>> 27)) * 0x94D049BB133111EB) % m
  z ^^^ (z >>> 31)

/-- Draw `i` of the stream `s` (seeds are mixed, then offset). -/
def rnd (s i : Nat) : Nat := mix (mix s + i)

def rep (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)

/-- `L` random digits, the first nonzero. -/
def digitStr (s L : Nat) : String :=
  String.ofList ((List.range L).map fun i =>
    let v := rnd s i % 10
    Char.ofNat (48 + (if i == 0 then v % 9 + 1 else v)))

def natStr (n : Nat) : String := toString n

/-! ## Inputs -/

def readExps : List Int :=
  [-200, -131, -130, -125, -121, -120, -119, -64, -61, -60, -9, -8, -7, -1, 1, 7, 8, 9, 60, 61, 64,
   120, 121, 130]

/-- The digit patterns of each length. -/
def patterns (L : Nat) : List String :=
  [digitStr (1000 + L) L, digitStr (2000 + L) L, rep L '9', "1" ++ rep (L - 1) '0',
   if L ≥ 2 then "1" ++ rep (L - 2) '0' ++ "1" else "7"]

def insertPoint (ds : String) (p : Nat) : String :=
  String.ofList (ds.toList.take p ++ ['.'] ++ ds.toList.drop p)

/-- Every length from 1 to 200 digits, each pattern in integer, exponent, point and leading-zero
forms. -/
def readInputs : List Item := Id.run do
  let mut acc : Array Item := #[]
  for L in [1:201] do
    for ds in patterns L do
      acc := acc.push { op := "rd", a := ds }
      for e in readExps do
        acc := acc.push { op := "rd", a := ds ++ "e" ++ toString e }
      for p in [1, (L + 1) / 2, L - 1] do
        if 1 ≤ p && p < L then acc := acc.push { op := "rd", a := insertPoint ds p }
      for z in [0, 1, 7, 8] do
        acc := acc.push { op := "rd", a := "0." ++ rep z '0' ++ ds }
      acc := acc.push { op := "rd", a := "-" ++ ds ++ "e-3" }
  for k in [0:451] do
    acc := acc.push { op := "rd", a := natStr (2 ^ k) }
    acc := acc.push { op := "rd", a := natStr (3 ^ k) }
    acc := acc.push { op := "rd", a := natStr (7 ^ k) }
    if k ≥ 1 then acc := acc.push { op := "rd", a := natStr (5 ^ k) ++ "e-" ++ toString k }
  return acc.toList

def p200 : String := natStr (2 ^ 200)

def chosen : List String :=
  ["1", "2", "3", "6", "6.0", "3.0", "7", "10", "0.1", "0.5", "1.25", "1.75", "1.000", "4", "60",
   "1E-130", "1E130", "1E-121", "1E-120", "1E-125", "1E-128", "1E7", "12345678", "99999999",
   "0.99999999", "1E-8", "-1", "-6.0", "-0.1", "-1E-121",
   rep 121 '9', "0." ++ rep 121 '9', "0." ++ rep 130 '9', "1." ++ rep 120 '0' ++ "1",
   "1." ++ rep 119 '0' ++ "1", "1." ++ rep 60 '0' ++ "1", "1." ++ rep 59 '0' ++ "2",
   rep 50 '3', rep 130 '7', p200, natStr (5 ^ 200) ++ "e-200",
   natStr (2 ^ 30), natStr (3 ^ 100), natStr (7 ^ 100), natStr (3 ^ 300), natStr (2 ^ 400),
   natStr (5 ^ 30) ++ "e-30"]

def arithOps : List String := ["add", "sub", "mul", "div", "xdiv", "cmp"]

/-- A random operand: 1 to 200 digits, an exponent in [-150, 150], either sign. -/
def randOperand (s : Nat) : String :=
  let L := rnd s 0 % 200 + 1
  let e : Int := (rnd s 1 % 301 : Nat) - 150
  let sign := if rnd s 2 % 4 == 0 then "-" else ""
  sign ++ digitStr (mix s) L ++ "e" ++ toString e

/-- A random operand near `a`'s magnitude (for cancellation in sums). -/
def randNear (s : Nat) (aExp : Int) : String :=
  let L := rnd s 0 % 200 + 1
  let e : Int := aExp + ((rnd s 1 % 41 : Nat) : Int) - 20
  let sign := if rnd s 2 % 2 == 0 then "-" else ""
  sign ++ digitStr (mix s) L ++ "e" ++ toString e

def arithInputs (nRandom : Nat) : List Item := Id.run do
  let mut acc : Array Item := #[]
  for op in arithOps do
    for a in chosen do
      for b in chosen do
        acc := acc.push { op := op, a := a, b := b }
  for op in arithOps do
    for i in [0:nRandom] do
      let s := mix (hash op).toNat + i
      let a := randOperand (3 * s)
      let b := if i % 2 == 0 then randOperand (3 * s + 1)
        else randNear (3 * s + 1) ((rnd (3 * s) 1 % 301 : Nat) - 150)
      acc := acc.push { op := op, a := a, b := b }
  return acc.toList

/-- `(* P (/ a P))` on stock (`pq`) and with S2 (`px`), P a power of 2, 3, 5, 6 or 7. -/
def x8Inputs : List Item := Id.run do
  let mut acc : Array Item := #[]
  let ps : List String :=
    ((List.range 400).map fun k => natStr (2 ^ (k + 1))) ++
    ((List.range 200).map fun k => natStr (3 ^ (k + 1))) ++
    ((List.range 250).map fun k => natStr (5 ^ (k + 1))) ++
    ((List.range 100).map fun k => natStr (6 ^ (k + 1))) ++
    ((List.range 150).map fun k => natStr (7 ^ (k + 1)))
  for p in ps do
    for a in ["1", "3", "7"] do
      acc := acc.push { op := "pq", a := a, b := p }
      acc := acc.push { op := "px", a := a, b := p }
  return acc.toList

def longs : List Int := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 1024, -3, 9223372036854775807]

def longInputs (n : Nat) : List Item := Id.run do
  let mut acc : Array Item := #[]
  for i in [0:n] do
    let a := randOperand (777777 + i)
    let l := longs.getD (rnd 4242 i % longs.length) 1
    let l := if rnd 4343 i % 3 == 0 then ((rnd 4444 i % 2000000 : Nat) : Int) - 1000000 else l
    let l := if l == 0 then 13 else l
    acc := acc.push { op := "divl", a := a, b := toString l }
    acc := acc.push { op := "xdivl", a := a, b := toString l }
  return acc.toList

def remOperands : List String :=
  ["1E130", "7.5", "2", "3", "123456789.123456789", "0.1", "1.75", "0.5", "-7.5", "1E-130", "7.50"]

def remInputs : List Item := Id.run do
  let mut acc : Array Item := #[]
  for a in remOperands do
    for b in remOperands do
      acc := acc.push { op := "rem", a := a, b := b }
  return acc.toList

def allInputs : List Item :=
  readInputs ++ arithInputs 3000 ++ x8Inputs ++ longInputs 1000 ++ remInputs

/-! ## Replica against boost -/

structure Tally where
  op : String
  total : Nat := 0
  diffX86 : Nat := 0
  diffArm : Nat := 0
  diffArmNoFma : Nat := 0
  armVsX86 : Nat := 0
  examples : Array String := #[]

def bump (ts : Array Tally) (op : String) (f : Tally → Tally) : Array Tally :=
  match ts.findIdx? (·.op == op) with
  | some i => ts.modify i f
  | none => ts.push (f { op := op })

/-- Compare the replica with boost's three builds, line by line. -/
def compareLines (items : Array Item) (x86 arm armnf : Array String) : Array Tally := Id.run do
  let mut ts : Array Tally := #[]
  for i in [0:items.size] do
    let it := items[i]!
    let mine := it.eval
    let bx := x86.getD i "<missing>"
    let ba := arm.getD i "<missing>"
    let bn := armnf.getD i "<missing>"
    ts := bump ts it.op fun t =>
      let ex := if mine != bx && t.examples.size < 6 then
          t.examples.push s!"{it.line}\n    replica {mine}\n    boost   {bx}" else t.examples
      let ex := if ba != bx && ex.size < 8 then
          ex.push s!"{it.line}\n    arm64 {ba}\n    x86   {bx}" else ex
      { t with total := t.total + 1,
               diffX86 := t.diffX86 + (if mine != bx then 1 else 0),
               diffArm := t.diffArm + (if mine != ba then 1 else 0),
               diffArmNoFma := t.diffArmNoFma + (if mine != bn then 1 else 0),
               armVsX86 := t.armVsX86 + (if ba != bx then 1 else 0),
               examples := ex }
  return ts

/-! ## Replica against `Spec` -/

/-- The exact value of a finite CDF as a Java BigDecimal: `±A · 10^(exp − 120)`. -/
def exactOf (x : CDF) : BD :=
  if x.iszero then ⟨0, 0⟩ else ⟨(if x.neg then -1 else 1) * (limbsVal x : Int), 120 - x.exp⟩

def ndigits (n : Nat) : Nat := (Nat.toDigits 10 n).length

/-- The keep rule for an exact decimal: the mantissa and exponent `rd_string` must produce. -/
def expectRead (b : BD) : Option (Nat × Int) :=
  if b.u == 0 then none else
  let c := b.u.natAbs
  let L := ndigits c
  let o : Int := -b.s + L - 1
  let r := Int.emod o 8
  some (keepM c L r.toNat, o - r)

/-- Does the replica's read of `s` keep what `keepM` says? (decimal strings only) -/
def checkRead (s : String) : Option Bool :=
  match rd s, BD.ofString (codes s) with
  | .ok x, .ok b =>
    if !x.isfinite then none else
    match expectRead b with
    | none => some x.iszero
    | some (m, e) => some (limbsVal x == m && x.exp == e && x.neg == (b.u < 0))
  | _, _ => none

def finiteNonzero (x : CDF) : Bool := x.isfinite && !x.iszero

/-- Product: `mulSpec` of the operands' mantissas. -/
def checkMul (x y : CDF) : Option Bool :=
  if !(finiteNonzero x && finiteNonzero y) then none else
  let z := x.mul y
  let (m, d) := mulSpec (limbsVal x) (limbsVal y)
  some (limbsVal z == m && z.exp == x.exp + y.exp + 8 * (d : Int) && z.neg == (x.neg != y.neg))

/-- Sum with signs, `z` the replica's result for `x + y`: `addSpec` for equal signs, `subSpec`
for opposite ones (the operand with the larger magnitude first); the result compared by value at
the larger operand's grid. A difference `x - y` is checked as `x + (-y)`. -/
def checkSum (x y z : CDF) : Option Bool :=
  if !(finiteNonzero x && finiteNonzero y) then none else
  let bigFirst := x.exp > y.exp || (x.exp == y.exp && compareRanges x.data y.data ≥ 0)
  let (u, v) := if bigFirst then (x, y) else (y, x)
  let δ := ((u.exp - v.exp) / 8).toNat
  if u.neg == v.neg then
    let (m, c) := addSpec (limbsVal u) (limbsVal v) δ
    some (limbsVal z == m && z.exp == u.exp + 8 * (c : Int) && z.neg == u.neg)
  else
    let dm := subSpec (limbsVal u) (limbsVal v) δ
    if dm == 0 then some z.iszero
    else if z.iszero then some false
    else
      -- the justified result: the same value on a finer exponent
      let sh := u.exp - z.exp
      some (sh ≥ 0 && sh % 8 == 0 && limbsVal z == dm * 10 ^ sh.toNat && z.neg == u.neg)

/-- S2's exact quotient is the keep rule applied to the exact quotient of the stored operands. -/
def checkXdiv (x y : CDF) : Option Bool :=
  if !(finiteNonzero x && finiteNonzero y) then none else
  match exactDivide x y, BD.div (exactOf x) (exactOf y) with
  | .ok z, .ok q =>
    match expectRead q with
    | none => some z.iszero
    | some (m, e) => some (limbsVal z == m && z.exp == e && z.neg == (q.u < 0))
  | .error _, .error _ => some true
  | _, _ => some false

structure SpecTally where
  name : String
  checked : Nat := 0
  agree : Nat := 0
  examples : Array String := #[]

def specBump (ts : Array SpecTally) (name : String) (r : Option Bool) (ex : String) : Array SpecTally :=
  match r with
  | none => ts
  | some ok =>
    let f := fun (t : SpecTally) =>
      { t with checked := t.checked + 1, agree := t.agree + (if ok then 1 else 0),
               examples := if !ok && t.examples.size < 5 then t.examples.push ex else t.examples }
    match ts.findIdx? (·.name == name) with
    | some i => ts.modify i f
    | none => ts.push (f { name := name })

def specCheck (items : List Item) : Array SpecTally := Id.run do
  let mut ts : Array SpecTally := #[]
  for it in items do
    match it.op with
    | "rd" => ts := specBump ts "read = keepM" (checkRead it.a) it.line
    | "add" | "sub" | "mul" | "xdiv" =>
      match rd it.a, rd it.b with
      | .ok x, .ok y =>
        match it.op with
        | "mul" => ts := specBump ts "product = mulSpec" (checkMul x y) it.line
        | "add" => ts := specBump ts "sum = addSpec / subSpec" (checkSum x y (x.add y)) it.line
        | "sub" => ts := specBump ts "difference = addSpec / subSpec" (checkSum x y.negate (x.sub y)) it.line
        | _ => ts := specBump ts "S2 quotient = keepM of the exact quotient" (checkXdiv x y) it.line
      | _, _ => pure ()
    | _ => pure ()
  return ts

/-! ## Programs -/

inductive E where
  | lit (s : String)
  | add (a b : E)
  | sub (a b : E)
  | mul (a b : E)
  | div (a b : E)
  deriving Inhabited

/-- jank: stock (`patched = false`, boost's Newton division) or with the combined patch (S2's
exact_divide). The other operations are boost's on both. -/
def E.jank (patched : Bool) : E → Except String CDF
  | .lit s => rd s
  | .add a b => do let x ← a.jank patched; let y ← b.jank patched; pure (x.add y)
  | .sub a b => do let x ← a.jank patched; let y ← b.jank patched; pure (x.sub y)
  | .mul a b => do let x ← a.jank patched; let y ← b.jank patched; pure (x.mul y)
  | .div a b => do
    let x ← a.jank patched
    let y ← b.jank patched
    if patched then exactDivide x y else pure (x.div y)

def E.clj : E → Except String BD
  | .lit s => BD.ofString (codes s)
  | .add a b => do let x ← a.clj; let y ← b.clj; pure (x.add y)
  | .sub a b => do let x ← a.clj; let y ← b.clj; pure (x.sub y)
  | .mul a b => do let x ← a.clj; let y ← b.clj; pure (x.mul y)
  | .div a b => do let x ← a.clj; let y ← b.clj; x.div y

def E.src : E → String
  | .lit s => s ++ "M"
  | .add a b => s!"(+ {a.src} {b.src})"
  | .sub a b => s!"(- {a.src} {b.src})"
  | .mul a b => s!"(* {a.src} {b.src})"
  | .div a b => s!"(/ {a.src} {b.src})"

/-- What a program observes: `(compare a b)` or `(str a)`. -/
inductive Obs where
  | compare (a b : E)
  | str (a : E)

def Obs.src : Obs → String
  | .compare a b => s!"(compare {a.src} {b.src})"
  | .str a => s!"(str {a.src})"

def Obs.jank (patched : Bool) : Obs → String
  | .compare a b => match a.jank patched, b.jank patched with
    | .ok x, .ok y => toString (cmp x y)
    | .error m, _ => "throws " ++ m
    | _, .error m => "throws " ++ m
  | .str a => match a.jank patched with
    | .ok x => "\"" ++ jankText x ++ "\""
    | .error m => "throws " ++ m

def Obs.clj : Obs → String
  | .compare a b => match a.clj, b.clj with
    | .ok x, .ok y => toString (x.cmp y)
    | .error m, _ => "throws " ++ m
    | _, .error m => "throws " ++ m
  | .str a => match a.clj with
    | .ok x => "\"" ++ x.toString ++ "\""
    | .error m => "throws " ++ m

def one : E := .lit "1"
def pow2E (k : Nat) : E := .lit (natStr (2 ^ k))
def x8 (k : Nat) : Obs := .compare one (.mul (pow2E k) (.div one (pow2E k)))

/-- The programs of round 3's S4, round 7's X8 and the new minimal ones. -/
def programs : List (String × Obs) :=
  [("x8 (P = 2^200)", x8 200),
   ("read: 122 digits at order 0 (cut)", .compare (.lit ("1." ++ rep 120 '0' ++ "1")) one),
   ("read: 121 digits at order 0 (kept; control)", .compare (.lit ("1." ++ rep 119 '0' ++ "1")) one),
   ("read: 122 digits at order 7 (kept; control)",
      .compare (.lit ("10000000." ++ rep 113 '0' ++ "1")) (.lit "10000000")),
   ("read: 129 digits at order 7 (cut)",
      .compare (.lit ("10000000." ++ rep 120 '0' ++ "1")) (.lit "10000000")),
   ("sum: 1 + 1E-121 (cut)", .compare (.add one (.lit "1E-121")) one),
   ("sum: 1 + 1E-120 (kept; control)", .compare (.add one (.lit "1E-120")) one),
   ("round 3 S4: 1E130 + 1", .compare (.add (.lit "1E130") one) (.lit "1E130")),
   ("round 3 S4: 1 - 1E-130", .compare (.sub one (.lit "1E-130")) one),
   ("difference: 1 - 1E-121 (rounded up)", .compare (.sub one (.lit "1E-121")) one),
   ("difference: 1 - 0.(121 nines) is 1E-120", .compare (.sub one (.lit ("0." ++ rep 121 '9'))) (.lit "1E-121")),
   ("difference: 1 - 0.(130 nines)", .compare (.sub one (.lit ("0." ++ rep 130 '9'))) (.lit "1E-130")),
   ("product: (1 + 1E-61)^2 (cut)",
      .compare (.mul (.lit ("1." ++ rep 60 '0' ++ "1")) (.lit ("1." ++ rep 60 '0' ++ "1")))
               (.lit ("1." ++ rep 60 '0' ++ "2"))),
   ("product: (1 + 1E-60)^2 (kept; control)",
      .compare (.mul (.lit ("1." ++ rep 59 '0' ++ "1")) (.lit ("1." ++ rep 59 '0' ++ "1")))
               (.lit ("1." ++ rep 59 '0' ++ "2" ++ rep 59 '0' ++ "1"))),
   ("stock Newton inverse of 2^17 is inexact", .compare (.div one (pow2E 17)) (.lit "0.00000762939453125")),
   ("x8 with P = 2^17", x8 17),
   ("x8 with P = 2^177 (the smallest k where S2's quotient is cut)", x8 177),
   ("x8 with P = 2^176 (control)", x8 176),
   ("S2: (/ 6.0M 3.0M)", .str (.div (.lit "6.0") (.lit "3.0"))),
   ("S2: (/ 6M 3M)", .str (.div (.lit "6") (.lit "3")))]

end Jank.R8.Boost.Check

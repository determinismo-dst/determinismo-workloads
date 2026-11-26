import Jank.R9.Num.Theorems
/-!
Round 9, area N: the searches. `jank9-num check FILE` reads Clojure 1.12.3's own results
(.r9-scratch/num/corpus.txt, written by .r9-scratch/num/corpus.clj) and compares the models:
  F lines: V62's float_cast (`floatCastBits`) against RT.floatCast's Float bits or its throw;
  N lines: DEC8-1's negation (`fixNegBits`) against Java's `-x` (NaNs compared as NaNs);
  L lines: V60's long_cast (`longCastBits`) against RT.longCast; stock's x86-64 cast counted beside;
  I lines: DEC8-1's integer negation against LongOps.negate / negateP; stock's wrap counted beside.
-/
open Jank.R9.Num

def hexVal (s : String) : Nat :=
  s.foldl (fun acc c =>
    let d := if c.isDigit then c.toNat - '0'.toNat
             else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
             else c.toNat - 'A'.toNat + 10
    acc * 16 + d) 0

def parseInt (s : String) : Option Int :=
  if s.startsWith "-" then (s.drop 1).toNat?.map (fun n => -(n : Int)) else s.toNat?.map (·)

/-- IEEE subtraction `0.0 - x` for a non-NaN x: -x, except +0.0 - +0.0 = +0.0. -/
def stockNegBits (x : BitVec 64) : BitVec 64 := if x == 0#64 then 0#64 else fixNegBits x

structure Tally where
  n : Nat := 0
  bad : Nat := 0
  stockBad : Nat := 0
  examples : Array String := #[]

def Tally.add (t : Tally) (ok stockOk : Bool) (line : String) : Tally :=
  { n := t.n + 1, bad := t.bad + (if ok then 0 else 1), stockBad := t.stockBad + (if stockOk then 0 else 1),
    examples := if ok || t.examples.size ≥ 5 then t.examples else t.examples.push line }

def check (path : String) : IO Unit := do
  let text ← IO.FS.readFile path
  let mut f : Tally := {}
  let mut ng : Tally := {}
  let mut l : Tally := {}
  let mut i : Tally := {}
  let mut fThrows := 0
  let mut lThrows := 0
  for line in text.splitOn "\n" do
    match line.splitOn " " with
    | ["F", d, r] =>
      let x := BitVec.ofNat 64 (hexVal d)
      let mine := floatCastBits x
      let ok := match mine with
        | none => r == "throws"
        | some b => r != "throws" && b.toNat == hexVal r
      if r == "throws" then fThrows := fThrows + 1
      -- stock never rounds or throws: not tallied here (every non-float double differs)
      let stockOk := true
      f := f.add ok stockOk line
    | ["N", d, r] =>
      let x := BitVec.ofNat 64 (hexVal d)
      let c := BitVec.ofNat 64 (hexVal r)
      let ok := if isNaN64 c then isNaN64 (fixNegBits x) else fixNegBits x == c
      let stockOk := if isNaN64 c then isNaN64 (stockNegBits x) else stockNegBits x == c
      ng := ng.add ok stockOk line
    | ["L", d, r] =>
      let x := BitVec.ofNat 64 (hexVal d)
      let ok := match longCastBits x with
        | none => r == "throws"
        | some v => parseInt r == some v
      if r == "throws" then lThrows := lThrows + 1
      let stockOk := parseInt r == some (stockLongBits x)
      l := l.add ok stockOk line
    | ["I", xs, neg, negp] =>
      match parseInt xs with
      | none => pure ()
      | some x =>
        let expect : NegResult := if neg == "throws" then .throws else
          match parseInt neg with | some v => .long v | none => .throws
        let expectP : Option Int := parseInt (if negp.endsWith "N" then String.mk (negp.toList.take (negp.length - 1)) else negp)
        let small := i32min ≤ x ∧ x ≤ i32max
        let mine := if small then fixNegSmall x else fixNegInteger false x
        let mineP := if small then fixNegSmall x else fixNegInteger true x
        let okP := match mineP, expectP with
          | .long v, some w => v == w && !negp.endsWith "N"
          | .bigint v, some w => v == w && negp.endsWith "N"
          | _, _ => false
        let ok := mine == expect && okP
        let stock := if small then stockNegSmall x else stockNegInteger x
        i := i.add ok (stock == expect) line
    | _ => pure ()
  IO.println s!"F (float_cast vs RT.floatCast): {f.n} doubles, {fThrows} throw in Clojure, differ {f.bad}"
  IO.println s!"N (negate vs Numbers.minus on doubles): {ng.n} doubles, differ {ng.bad}; stock (- 0 x) differs {ng.stockBad}"
  IO.println s!"L (long_cast vs RT.longCast): {l.n} doubles, {lThrows} throw in Clojure, differ {l.bad}; stock x86-64 cast differs {l.stockBad}"
  IO.println s!"I (negate/promoting_negate vs LongOps): {i.n} longs, differ {i.bad}; stock (- 0 x) differs {i.stockBad}"
  for t in [f, ng, l, i] do
    for e in t.examples do IO.println s!"  mismatch: {e}"

def main (args : List String) : IO Unit := do
  match args with
  | ["check", path] => check path
  | _ => IO.println "usage: jank9-num check .r9-scratch/num/corpus.txt"

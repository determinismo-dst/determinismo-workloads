import Jank.R6.Num.Search

/-! Round 6 driver: numbers (`jank6-num int | fixed | minmax | all`). -/

open Jank.R6.Num Jank.R6.Num.Search Jank.R6.Num.MinMax

def countBy {α : Type} (xs : Array α) (key : α → String) : List (String × Nat) :=
  let m := xs.foldl (fun (m : Std.HashMap String Nat) x => m.insert (key x) (m.getD (key x) 0 + 1)) {}
  m.toList.mergeSort (fun a b => a.1 ≤ b.1)

def intWalk : IO Unit := do
  let rows := walk
  IO.println s!"== Integer walk: {rows.size} questions (complete over {ints.length} values × 3 sources × 14 operators)"
  for (k, n) in countBy rows (fun r => s!"{r.op.name} {reprStr r.v}") do
    IO.println s!"  {k}: {n}"
  IO.println "\n== Disagreements by operator, C++ operand types and path (3 examples each)"
  let bad := rows.filter (fun r => r.v != .agree)
  let mut seen : Std.HashMap String Nat := {}
  for (k, n) in countBy bad (fun r => s!"{r.op.name} [{r.repPair}] {r.pathName} {reprStr r.v}") do
    IO.println s!"  {k}: {n}"
  IO.println "\n== Examples"
  for r in bad do
    let k := s!"{r.op.name} [{r.repPair}] {r.pathName} {reprStr r.v}"
    let c := seen.getD k 0
    if c < 2 then
      IO.println s!"  {r.line}"
      seen := seen.insert k (c + 1)

def fixedWalk : IO Unit := do
  let rows := walk
  let fixed := rows.map (fun r => (r, answerFixed r.op r.x r.y r.sx r.sy))
  IO.println s!"== The fixed jank (LG2a + R5) against Clojure, the same {rows.size} questions"
  for (k, n) in countBy fixed (fun (r, f) => s!"{r.op.name} {reprStr (verdict f r.c)}") do
    IO.println s!"  {k}: {n}"
  IO.println "\n== Every remaining disagreement"
  for (r, f) in fixed do
    if verdict f r.c != .agree then
      IO.println s!"  {program r.op r.x r.y r.sx r.sy}  [{r.pathName}]  fixed jank {showOut f}  Clojure {showOut r.c}  {reprStr (verdict f r.c)}"

def mmWalk : IO Unit := do
  for op in ["min", "max", "<", "<=", "compare", "=="] do
    let qs := questions op
    let bad := qs.filter (fun q => !(q.answer.2.2))
    IO.println s!"== {op}: {qs.length} questions (complete: {(values true).length} values × 2 paths per operand), {bad.length} disagree"
    if op == "min" || op == "max" then
      for (k, n) in countBy bad.toArray (fun q => s!"{q.minmaxClass} / {q.path}") do
        IO.println s!"  {k}: {n}"
    else
      for (k, n) in countBy bad.toArray (fun q => s!"{q.x.j.kind}×{q.y.j.kind}") do
        IO.println s!"  {k}: {n}"
    let mut seen : Std.HashMap String Nat := {}
    for q in bad do
      let k := if op == "min" || op == "max" then s!"{q.minmaxClass} / {q.path}" else s!"{q.x.j.kind}×{q.y.j.kind}"
      let c := seen.getD k 0
      if c < 3 then
        let (j, cl, _) := q.answer
        IO.println s!"    {q.program}: jank {j}, Clojure {cl}"
        seen := seen.insert k (c + 1)

/-- The replica on each test's exact forms (.r6-scratch/num/tests.jank). -/
def testForms : IO Unit := do
  let mx : Int := 9223372036854775807
  let mn : Int := -9223372036854775808
  let q := fun (name : String) (op : IOp) (x y : CInt) (sx sy : Src) =>
    let (j, c) := answer op x y sx sy
    IO.println s!"  {name}: {program op x y sx sy}: jank {showOut j}, Clojure {showOut c} ({reprStr (verdict j c)})"
  IO.println "== Integer tests"
  q "vN1" (.bin .mul) (.long (-3)) (.long mx) .lit .lit
  q "vN1" (.bin .add) (.long mx) (.long 1) .lit .lit
  q "vN1" (.bin .sub) (.long (-9223372036854775807)) (.long 2) .lit .lit
  q "vN1b" (.bin .mul) (.long mx) (.long 2) .lit .lit
  q "vN1b" (.bin .mul) (.long 4294967296) (.long 2147483648) .lit .lit
  q "vN1b" (.bin .sub) (.long (2 - mx)) (.long mx) .lit .lit
  q "vN1c" (.bin .mul) (.long 3037000500) (.long 3037000500) .fnLit .fnLit
  q "vN1c" (.bin .add) (.long mx) (.long 1) .fnLit .fnLit
  q "vN1c" (.bin .sub) (.long (-9223372036854775807)) (.long 3) .fnLit .fnLit
  q "vN1d" (.bin .add) (.long 1) (.long mx) .fnLit .lit
  q "vN1e" .neg (.long mn) (.long mn) .fnVal .fnVal
  q "vN2" .dec (.long mn) (.long mn) .lit .lit
  q "vN2" (.bin .mul) (.long mn) (.long 2) .lit .lit
  q "vN2" (.bin .sub) (.long mn) (.long 2) .lit .lit
  q "vN2" .inc (.long mn) (.long mn) .lit .lit
  q "vN2" (.bin .mul) (.long mn) (.long 0) .lit .lit
  q "vN3" (.bin .mul) (.long 65536) (.long 65536) .lit .lit
  q "vN3" (.bin .add) (.long 2147483647) (.long 1) .lit .lit
  q "vN4" (.binP .sub) (.long mn) (.long 1) .fnVal .fnLit
  q "vN5" (.bin .sub) (.long (-1)) (.long mn) .fnLit .fnVal
  q "vN5" (.binP .sub) (.long (-1)) (.long mn) .fnLit .fnVal
  IO.println "== min/max tests"
  let m := fun (name op : String) (x y : Arg) =>
    let qq : Q := ⟨op, x, y⟩
    let (j, c, ok) := qq.answer
    IO.println s!"  {name}: {qq.program}: jank {j}, Clojure {c}{if ok then " (agree)" else ""}"
  m "vN6" "min" (dbl nan "##NaN" false) (lng 1 false)
  m "vN6" "max" (lng 1 false) (dbl nan "##NaN" false)
  m "vN6" "max" (dbl 1.0 "1.0" false) (dbl nan "##NaN" false)
  m "vN6b" "min" (dbl 1.0 "1.0" true) (dbl nan "##NaN" true)
  m "vN6b" "max" (lng 1 true) (dbl nan "##NaN" true)
  m "vN7" "max" (lng 1 false) (dbl 1.0 "1.0" false)
  m "vN7" "max" (lng 1 false) (bigA 1 false)
  m "vN7" "max" (dbl 0.0 "0.0" false) (dbl (-0.0) "-0.0" false)
  m "vN8" "min" (lng 1 true) (dbl 2.5 "2.5" true)
  m "vN8" "max" (lng 9007199254740993 true) (dbl 1.0 "1.0" true)
  m "vN8" "min" (dbl 0.0 "0.0" true) (dbl (-0.0) "-0.0" true)

def main (args : List String) : IO Unit := do
  match args with
  | ["int"] => intWalk
  | ["fixed"] => fixedWalk
  | ["minmax"] => mmWalk
  | ["tests"] => testForms
  | _ => do intWalk; fixedWalk; mmWalk

import Jank.R8.Dec.Java
import Jank.R8.Dec.Theorems

/-! Round 8, area D driver (`jank8-dec check CASES JVM OUT`): the Lean replica of fixes/R72.diff's and
fixes/X6.diff's decimal arithmetic (Jank.R8.Dec.Java) against Clojure 1.12.3's answers to the same
cases (`.r8-scratch/dec/check/cases.txt`, `jvm.out`). Double cases (`vod`, `dbl`) are left to the
C++ copy. -/

open Jank.R8.Dec

def countBy (xs : List String) : List (String × Nat) :=
  let m := xs.foldl (fun (m : Std.HashMap String Nat) k => m.insert k (m.getD k 0 + 1)) {}
  m.toList.mergeSort (fun a b => a.1 ≤ b.1)

def check (casesPath jvmPath outPath : String) : IO Unit := do
  let cases := (← IO.FS.readFile casesPath).splitOn "\n" |>.filter (· ≠ "")
  let jvm := (← IO.FS.readFile jvmPath).splitOn "\n" |>.filter (· ≠ "")
  if cases.length ≠ jvm.length then
    throw <| IO.userError s!"cases {cases.length} vs answers {jvm.length}"
  let mut checked : List String := []
  let mut skipped := 0
  let mut bad : Array String := #[]
  for (c, j) in cases.zip jvm do
    match c.splitOn " " with
    | [op, a, b, p, m] =>
      if op == "vod" || op == "dbl" then
        skipped := skipped + 1
      else
        let ctx := if p == "0" then "exact" else "context"
        checked := s!"{op} {ctx}" :: checked
        match answer op a b p.toNat! m with
        | some s => if s != j then bad := bad.push s!"{c} | jvm {j} | lean {s}"
        | none => bad := bad.push s!"{c} | unparsed"
    | _ => bad := bad.push s!"{c} | malformed"
  let lines :=
    [s!"cases {cases.length}: checked {checked.length}, left to the C++ copy (doubles) {skipped}",
     s!"disagreements with Clojure 1.12.3: {bad.size}"] ++
    (countBy checked).map (fun (k, n) => s!"  {k}: {n}") ++
    (bad.toList.take 50)
  IO.FS.writeFile outPath (String.intercalate "\n" lines ++ "\n")
  IO.println (String.intercalate "\n" (lines.take 2))

def main (args : List String) : IO Unit := do
  match args with
  | ["check", c, j, o] => check c j o
  | _ => IO.println "usage: jank8-dec check CASES JVM OUT"

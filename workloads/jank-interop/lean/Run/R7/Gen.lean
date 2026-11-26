import Jank.R7.Gen.Plan

/-! Round 7 driver, area G (`jank7-gen [emit JANK TSV SUMMARY]`): draws the generated differential
test from the round-6 models and writes the jank test file, the predictions TSV and the strata
summary (defaults: .r7-scratch/gen/generated_r7_test.jank, results/r7-gen-predictions.tsv,
.r7-scratch/gen/summary.txt). -/

open Jank.R7.Gen Jank.R7.Gen.Plan

def main (args : List String) : IO Unit := do
  if let ["bulk", per, path] := args then
    let (txt, n) := bulkFile (per.toNat?.getD 300)
    IO.FS.writeFile path txt
    IO.println s!"bulk: {n} forms (up to {per} draws per stratum, every path) written to {path}"
    return
  let (jp, tp, sp) := match args with
    | ["emit", a, b, c] => (a, b, c)
    | _ => (".r7-scratch/gen/generated_r7_test.jank", "results/r7-gen-predictions.tsv", ".r7-scratch/gen/summary.txt")
  let ss := strata
  let its := items ss
  IO.FS.writeFile jp (jankFile its)
  IO.FS.writeFile tp (tsvFile its)
  let sm := summary ss its
  IO.FS.writeFile sp sm
  IO.println sm

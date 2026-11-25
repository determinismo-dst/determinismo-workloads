import Jank.R5.Interop.World5
import Jank.R5.Interop.Theorems5

/-! Round 5 driver: Interop. World XXII: operator templates, `=`, `+=`, `aget`, the call operator,
`++` and unary `&`, with the value categories jank gives operands (`jank5-interop [table|search]`). -/

open Determinismo
open Jank.Interop
open Jank.Interop.Search (runW exploreMixed)
open Jank.R5.Interop.Ops5
open Jank.R5.Interop.World5

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

def main (args : List String) : IO UInt32 := do
  let only := args.headD "all"
  let t0 ← IO.monoMsNow
  IO.println "jank5-interop: round 5 (jank 94d32623 = 7135b7708's compiler+runtime, CppInterOp 28b0830d, Clang 23.1.0)"
  let cases := allCases
  if only == "all" || only == "table" then
    IO.println s!"== XXII. operators: {cases.length} cases ({binaryOps.length} binary operators × {operands.length}², {unaryOps.length} unary × {operands.length}, calls of each class object × {operands.length})"
    let bad := cases.filterMap (judge x86_64)
    let classes := bad.foldl (fun acc (c, _) => if acc.contains c then acc else acc ++ [c]) []
    IO.println s!"  table: {bad.length} of {cases.length} cases deviate; classes: {classes.map fun c => s!"{c} ({(bad.filter (·.1 == c)).length})"}"
    for c in classes do
      for (_, d) in (bad.filter (·.1 == c)).take 40 do IO.println s!"    [{c}] {(d.take 700).toString}"
    -- every mechanism set to C++'s rule: no case may still deviate
    let still := cases.filter fun c =>
      let (_, cpp) := outs x86_64 {} c
      !agree (jankOut x86_64 world allFix c.op c.args) cpp
    IO.println s!"  with every mechanism set to C++'s rule: {still.length} of {cases.length} still deviate"
    for c in still.take 20 do
      let (_, cpp) := outs x86_64 {} c
      IO.println s!"    {c.text}: C++ {cpp.show}; jank (all fixed) {(jankOut x86_64 world allFix c.op c.args).show}"
    -- agreement census by operator
    for (arity, (op, t)) in (binaryOps.map (2, ·)) ++ (unaryOps.map (1, ·)) ++ [(2, (.call, "()"))] do
      let cs := cases.filter fun c => c.op == op && c.args.length == arity
      let n := (cs.filter fun c => (judge x86_64 c).isSome).length
      IO.println s!"  {if arity == 1 then "unary " else ""}{t}: {n} of {cs.length} deviate"
    (← IO.getStdout).flush
  if only == "all" || only == "search" then
    IO.println "== XXII search (exhaust per class set aside, explore with mixed seeds)"
    let run := runW (body [])
    match exploreMixed run 3000 with
    | some c =>
      IO.println s!"  explore (3000 mixed seeds): {describe c}"
      let s := shrink run c
      IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
      IO.println s!"  tape:\n{indent (tape s.taken)}"
    | none => IO.println "  explore (3000 mixed seeds): nothing"
    for l in Jank.R3.Interop.Worlds.residual "XXII" body 20000 16 do IO.println s!"  {(l.take 600).toString}"
  IO.println "== theorems (proved at build time; no sorry, no native_decide)"
  for n in Jank.R5.Interop.Theorems5.names do IO.println s!"  {n}"
  let t1 ← IO.monoMsNow
  IO.println s!"== done in {(t1 - t0) / 1000} s"
  return 0

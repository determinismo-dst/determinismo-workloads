import Jank.Interop.Search
import Jank.Interop.Theorems

/-! Driver of `jank-interop`: every interop search, its exhaustive table, and the counterexamples'
tapes. -/

open Determinismo
open Jank.Interop Jank.Interop.Search

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

def report (name : String) (run : Source → Ended) (seeds : Nat) (maxRuns : Nat) : IO Unit := do
  let t ← IO.monoMsNow
  IO.eprintln s!"[{t}] {name}"
  (← IO.getStdout).flush
  IO.println s!"== {name}"
  match exploreMixed run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} mixed seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
  | none => IO.println s!"  explore ({seeds} mixed seeds): nothing"
  match exhaust run maxRuns with
  | .found c =>
    IO.println s!"  exhaust: found after {c.runs} timelines: {c.detail}"
  | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"

def table {α : Type} (name : String) (cases : List α) (judge : α → Option String) (shown : Nat := 12) : IO Unit := do
  let bad := cases.filterMap judge
  IO.println s!"  table ({name}): {bad.length} of {cases.length} cases deviate"
  for d in bad.take shown do IO.println s!"    {d}"

def emitted (params : List String) (src : String) : IO Unit := do
  IO.println s!"  emitted C++ for {src}:"
  for l in cppOf params src do IO.println s!"    {l}"

def main : IO UInt32 := do
  let t0 ← IO.monoMsNow
  IO.println "jank-interop: the C++ interop replica of jank 7135b7708 (upstream-main), searched against its spec"
  report "I. arithmetic on literals (+ - * < inc dec, inlined to jank::runtime templates)" (runW arithBody) 3000 20000
  table "every op × operand × literal/parameter" allArith ArithCase.judge 16
  emitted [] "(+ 2147483647 1)"
  report "II. loop/recur with a native loop local (one recur)" (runW loopBody) 3000 20000
  table "every init × step × value × literal/parameter" allLoops LoopCase.judge 16
  emitted [] "(loop [x 0 n 0] (if (< n 1) (recur (+ x 0.5) (inc n)) x))"
  IO.println s!"  (loop [x 0] (if (< x 10) (recur (+ x 0.5)) x)): jank {(runProgram [] "(loop [x 0] (if (< x 10) (recur (+ x 0.5)) x))").show}; Clojure 10.0"
  IO.println s!"  (loop [acc 0 i 0] (if (< i 2) (recur (+ acc x) (inc i)) acc)) with x = 1.5: jank {(runProgram [("x", Read.atom "1.5")] "(loop [acc 0 i 0] (if (< i 2) (recur (+ acc x) (inc i)) acc))").show}; Clojure 3.0"
  IO.println s!"  (loop [i 0 acc 0] (if (< i 100000) (recur (inc i) (+ acc i)) acc)): jank {(runProgram [] "(loop [i 0 acc 0] (if (< i 100000) (recur (inc i) (+ acc i)) acc))" 100001).show}; Clojure 4999950000"
  IO.println s!"  (loop [x 1 n 0] (if (< n 40) (recur (* x 2) (inc n)) x)): jank {(runProgram [] "(loop [x 1 n 0] (if (< n 40) (recur (* x 2) (inc n)) x))" 100).show}; Clojure 1099511627776"
  report "III. jank values passed to native parameters and returned" (runW paramBody) 3000 20000
  table "every parameter type × value × literal/parameter" allParams ParamCase.judge 40
  let lvp := paramFnNames.flatMap fun fn => paramVals.filterMap fun v => literalVsParam fn v
  IO.println s!"  literal vs function parameter, same value: {lvp.length} of {paramFnNames.length * paramVals.length} calls disagree"
  for d in lvp.take 12 do IO.println s!"    {d}"
  emitted ["x"] "(cpp/take_double x)"
  emitted [] "(cpp/take_double 4)"
  emitted ["s"] "(cpp/take_mut_cstr s)"
  IO.println s!"  cpp/UINT64_MAX: jank {(runProgram [] "cpp/UINT64_MAX").show}; its value 18446744073709551615"
  IO.println s!"  cpp/ONE_PLUS_LDBL_EPS (long double 1 + 2^-63): jank {(runProgram [] "cpp/ONE_PLUS_LDBL_EPS").show}"
  report "IV. `if` on native values" (runW condBody) 200 1000
  table "every condition" conds CondCase.judge
  emitted [] "(if cpp/red :t :f)"
  report "V. cpp/cast between native types" (runW castBody) 3000 20000
  table "every source × target type" allCasts CastCase.judge 40
  emitted [] "(let [v (cpp/cast (:* (:const cpp/void)) cpp/nullptr)] (let [r (cpp/cast (:* cpp/int) v)] 1))"
  report "VI. cpp/new vs constructing the type" (runW newBody) 500 2000
  table "every type × arguments" allNews NewCase.judge 40
  emitted [] "(let [p (cpp/new (std.vector cpp/int) 3)] 1)"
  report "VII. opaque boxes" (runW boxBody) 1000 2000
  table "every boxed × unboxed pointer type" (boxTypes.flatMap fun a => boxTypes.map fun b => (a, b)) (fun (a, b) => boxJudge a b) 20
  emitted [] "(let [v (cpp/cast (:* (:const base)) cpp/nullptr) b (cpp/box v) u (cpp/unbox (:* base) b)] 1)"
  report "VIII. DSL integer modifiers" (runW dslBody) 3000 20000
  table "every chain of ≤ 2 modifiers × base" allDsl (fun (ms, b) => dslJudge ms b) 40
  report "IX. `if` with native branches of different types" (runW branchBody) 3000 20000
  table "every then × else × condition" allBranches BranchCase.judge 20
  emitted [] "(if true 1 2.5)"
  Theorems.summary
  let t1 ← IO.monoMsNow
  IO.println s!"runtime: {t1 - t0} ms"
  return 0

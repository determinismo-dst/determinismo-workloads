import Jank.R4.Interop.Worlds
import Jank.R4.Interop.Theorems

/-! Round 4 driver: Interop. The S49/S57 feedback (top-level analysis and evaluation of the
round-3 test shapes), world XVI in both evaluation contexts, world XII rerun, operators with
CppInterOp's real `GetOperator` (XVIII), class-template constructor calls (XIX), lazily compiled
functions (XX), `cpp/delete` by pointer origin (XXI). -/

open Determinismo
open Jank.Interop
open Jank.Interop.Search (runW exploreMixed)

def describe (c : Counterexample) : String :=
  s!"{c.property} after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indent (s : String) : String := (s.splitOn "\n").map ("    " ++ ·) |> "\n".intercalate

def world {α : Type} (name : String) (body : List String → EStateM Stop Jank.Interop.Search.W Unit) (seeds maxRuns : Nat)
    (cases : List α) (judge : α → Option (String × String)) (shown : Nat := 12) : IO Unit := do
  IO.println s!"== {name}"
  let run := runW (body [])
  match exploreMixed run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} mixed seeds): {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"  tape:\n{indent (tape s.taken)}"
  | none => IO.println s!"  explore ({seeds} mixed seeds): nothing"
  let bad := cases.filterMap judge
  let classes := bad.foldl (fun acc (c, _) => if acc.contains c then acc else acc ++ [c]) []
  IO.println s!"  table: {bad.length} of {cases.length} cases deviate; classes: {classes.map fun c => s!"{c} ({(bad.filter (·.1 == c)).length})"}"
  for c in classes do
    for (_, d) in (bad.filter (·.1 == c)).take shown do IO.println s!"    [{c}] {(d.take 600).toString}"
  IO.println "  residual searches (exhaust, each found class set aside in turn):"
  for l in Jank.R3.Interop.Worlds.residual name body maxRuns do IO.println s!"    {(l.take 600).toString}"
  (← IO.getStdout).flush

def main (args : List String) : IO UInt32 := do
  let only := args.headD "all"
  let t0 ← IO.monoMsNow
  IO.println "jank4-interop: round 4 (jank 7135b7708, CppInterOp 28b0830d, Clang 23.1.0)"
  if only == "all" || only == "feedback" then
    IO.println "== feedback (prompted): the round-3 tests S49, S50, S53, S57 as written, and corrected"
    for it in Jank.R4.Interop.TopLevel.items do
      for l in Jank.R4.Interop.TopLevel.outcomeLine x86_64 it do IO.println l
    (← IO.getStdout).flush
    world "XVI'. if with native branches, at the top level (interpreted) and in a fn (compiled)"
      Jank.R4.Interop.Worlds4.ctxBody 2000 20000 Jank.R4.Interop.TopLevel.allCtx
      (fun c => (Jank.R4.Interop.TopLevel.ctxJudge x86_64 c).map fun (cls, d) => (Jank.R4.Interop.Worlds4.ctxClass c cls, d)) 40
    world "XII (rerun). function templates with explicit template arguments, called (compiled in both contexts)"
      Jank.R3.Interop.Worlds.tmplBody 3000 20000 Jank.R3.Interop.Worlds.allTmpl Jank.R3.Interop.Worlds.tmplJudge 6
  if only == "all" || only == "operators" then
    world "XVIII. operators: GetOperator's lookup (TU, ADL with using-directives, associated classes' members and hidden friends) vs [over.match.oper]"
      Jank.R4.Interop.Worlds4.opBody 3000 20000 Jank.R4.Interop.Operators.allCases (Jank.R4.Interop.Operators.judge x86_64) 12
  if only == "all" || only == "templates" then
    world "XIX. class template constructor calls (cpp/X. args): defaults vs class template argument deduction"
      Jank.R4.Interop.Worlds4.tBody 3000 20000 Jank.R4.Interop.Templates.allTCases (Jank.R4.Interop.Templates.tJudge x86_64) 20
  if only == "all" || only == "deferred" then
    IO.println "== XX. lazily compiled functions (deferred_cpp_function): programs of top-level defn/def/call/alter-var-root"
    for n in [1, 2, 3, 4, 5] do
      let r := Jank.R4.Interop.Deferred.run n
      match explore r 2000 with
      | some c =>
        IO.println s!"  length {n}: explore found after {c.runs}: {c.detail}"
        let s := shrink r c
        IO.println s!"    shrunk: {s.detail}\n    tape:\n{indent (tape s.taken)}"
      | none => IO.println s!"  length {n}: explore (2000 seeds): nothing"
      match exhaust r 100000 with
      | .found c => IO.println s!"  length {n}: exhaust found after {c.runs} timelines: {c.detail}"
      | .complete k => IO.println s!"  length {n}: exhaust complete, {k} timelines, nothing"
      | .stopped k => IO.println s!"  length {n}: exhaust stopped at {k}"
    -- the census: every program of length 4, 5 and 6, how many disagree (lazy, and with --eager)
    let ops := Jank.R4.Interop.Deferred.opsUniverse
    for n in [4, 5, 6] do
      let progs : List (List Jank.R4.Interop.Deferred.Op) :=
        (List.replicate n ops).foldr (fun os acc => os.flatMap fun o => acc.map (o :: ·)) [[]]
      let bad := progs.filter fun p => (Jank.R4.Interop.Deferred.runBoth p).any fun (_, a, b) => a != b
      let eagerBad := progs.filter fun p => Id.run do
        let mut s : Jank.R4.Interop.Deferred.St := {}
        let mut c : Jank.R4.Interop.Deferred.St := {}
        let mut d := false
        for op in p do
          let (s', a) := Jank.R4.Interop.Deferred.stepEager s op
          let (c', b) := Jank.R4.Interop.Deferred.stepClj c op
          s := s'; c := c'
          if a != b then d := true
        return d
      IO.println s!"  census, length {n}: {bad.length} of {progs.length} programs disagree (lazy); {eagerBad.length} with --eager"
      if let some p := bad.head? then
        IO.println s!"    first: {" ".intercalate (p.map Jank.R4.Interop.Deferred.Op.text)}"
  if only == "all" || only == "delete" then
    IO.println "== XXI. (cpp/delete p) by the pointer's origin: jank vs C++ delete"
    for (o, j, c) in Jank.R4.Interop.Worlds4.deleteRows do
      IO.println s!"  {reprStr o}: jank {j}; C++ {c}"
  IO.println "== theorems (proved at build time; no sorry, no native_decide)"
  for n in Jank.R4.Interop.Theorems.names do IO.println s!"  {n}"
  let t1 ← IO.monoMsNow
  IO.println s!"== done in {(t1 - t0) / 1000} s"
  return 0

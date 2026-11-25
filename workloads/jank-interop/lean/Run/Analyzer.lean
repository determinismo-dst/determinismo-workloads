import Jank.Analyzer.Search
import Jank.Analyzer.Theorems

open Jank.Analyzer Determinismo

/-- One minimal program per finding, and controls that agree. -/
def examples : List (String × List Obj) :=
  [ ("A1 if, int/double", [L [S "if", B true, I 1, D 2.5]]),
    ("A1 if, int/bool", [L [S "if", B false, I 0, B false]]),
    ("A1 if, as a test", [L [S "if", L [S "if", B false, I 0, B false], K "yes", K "no"]]),
    ("A1 (or true 0)", [L [S "or", B true, I 0]]),
    ("A1 (and false 5)", [L [S "and", B false, I 5]]),
    ("A1 (and false 5) as a test", [L [S "if", L [S "and", B false, I 5], K "yes", K "no"]]),
    ("A1 (or false 1.5)", [L [S "or", B false, D 1.5]]),
    ("A1 (and (pos? x) 5) as a test", [L [L [S "fn*", V [S "x"], L [S "if", L [S "and", L [S "pos?", S "x"], I 5], K "pos", K "non-pos"]], I (-1)]]),
    ("A2 loop int, recur double", [L [S "loop*", V [S "x", I 0, S "n", I 0], L [S "if", L [S "=", S "n", I 1], S "x", L [S "recur", D 1.5, I 1]]]]),
    ("A2 loop int, (+ x 0.5)", [L [S "loop*", V [S "x", I 0, S "n", I 0], L [S "if", L [S "=", S "n", I 3], S "x", L [S "recur", L [S "+", S "x", D 0.5], L [S "inc", S "n"]]]]]),
    ("A2 loop int, inc past 2^31", [L [S "loop*", V [S "x", I 2147483647, S "n", I 0], L [S "if", L [S "=", S "n", I 1], S "x", L [S "recur", L [S "inc", S "x"], I 1]]]]),
    ("A2 loop int, sum of doubles", [L [S "loop*", V [S "acc", I 0, S "xs", V [D 1.5, D 2.5]], L [S "if", L [S "first", S "xs"], L [S "recur", L [S "+", S "acc", L [S "first", S "xs"]], L [S "rest", S "xs"]], S "acc"]]]),
    ("A2 loop bool, recur nil", [L [S "loop*", V [S "x", B true, S "n", I 0], L [S "if", L [S "=", S "n", I 1], S "x", L [S "recur", .nil, I 1]]]]),
    ("A2 loop int, recur string", [L [S "loop*", V [S "x", I 0, S "n", I 0], L [S "if", L [S "=", S "n", I 1], S "x", L [S "recur", str "s", I 1]]]]),
    ("A2 loop int, recur a boolean object", [L [S "loop*", V [S "x", I 0, S "n", I 0], L [S "if", L [S "=", S "n", I 1], S "x", L [S "recur", L [S "=", I 1, I 1], I 1]]]]),
    ("A2 loop double, recur a long object", [L [S "loop*", V [S "x", D 0.5, S "n", I 0], L [S "if", L [S "=", S "n", I 1], S "x", L [S "recur", L [S "count", V [I 1, I 2]], I 1]]]]),
    ("A3 recur in fn in loop", [L [L [S "loop*", V [S "a", I 1, S "b", I 2], L [S "fn*", V [S "y"], L [S "if", S "y", L [S "recur", .nil], K "done"]]], I 5]]),
    ("A3 recur in fn in loop init", [L [S "loop*", V [S "f", L [S "fn*", V [S "n"], L [S "if", L [S "=", S "n", I 0], S "n", L [S "recur", I 0]]]], L [S "f", I 5]]]),
    ("A4 fn name vs outer local", [L [L [S "fn*", V [S "f"], L [L [S "fn*", S "f", V [S "n"], L [S "if", L [S "=", S "n", I 0], K "done", L [S "f", I 0]]], I 1]], I 7]]),
    ("A5 fn name vs macro", [L [L [S "fn*", S "when", V [S "n"], L [S "if", L [S "=", S "n", I 0], K "done", L [S "when", I 0]]], I 1]]),
    ("A6 &form", [L [S "form-of", I 1, I 2]]),
    ("A6 &env", [L [S "let*", V [S "a", I 1], L [S "env-count"]]]),
    ("A7 macro-made vector's meta", [L [S "meta", L [S "mk-vec", I 1, I 2]]]),
    ("A7 macro-made map's meta", [L [S "meta", L [S "mk-map", K "a", I 1]]]),
    ("A8 private var in a macro's argument", [L [S "when", B true, Obj.sym "other" "secret"]]),
    ("A8 private var from a macro", [L [Obj.sym "other" "secret-of"]]),
    ("A9 (+ true 1)", [L [S "+", B true, I 1]]),
    ("A9 (inc true)", [L [S "inc", B true]]),
    ("A10 (:k)", [L [K "k"]]),
    ("A11 catch without binding", [L [S "try", I 1, L [S "catch", K "default"]]]),
    ("A12 object loop local, recur int (oracle)", [L [S "loop*", V [S "x", .nil, S "n", I 0], L [S "if", L [S "=", S "n", I 1], S "x", L [S "recur", I 5, I 1]]]]),
    ("A14 (+ 2147483647 1)", [L [S "+", I 2147483647, I 1]]),
    ("A14 (* 100000 100000)", [L [S "*", I 100000, I 100000]]),
    ("A14 (+ 2147483648 1), a long literal", [L [S "+", I 2147483648, I 1]]),
    ("A13 case with a nil default", [L [S "case", I 1, I 1, I 0, I 2, .nil, .nil]]),
    ("A13 case, default int, branch double", [L [S "case", I 5, I 1, D 1.5, I 0]]),
    ("A13 case, branch then default", [L [S "case", I 1, I 1, I 2, D 3.5]]),
    ("A13 case, double branch then int branch", [L [S "case", I 1, I 1, D 1.5, I 2, I 7, I 0]]),
    ("A13 case, keyword branch then double branch", [L [S "case", I 1, I 1, K "a", I 2, D 1.5, I 0]]),
    ("A13 case, keyword branch then double branch, default taken", [L [S "case", I 3, I 1, K "a", I 2, D 1.5, I 0]]),
    ("control: case of keywords", [L [S "case", I 2, I 1, K "a", I 2, K "b", K "c"]]),
    ("control: case of ints", [L [S "case", I 2, I 1, I 10, I 2, I 20, I 30]]),
    ("control: closure capture", [L [S "let*", V [S "x", I 1, S "f", L [S "fn*", V [], S "x"], S "x", I 2], L [S "f"]]]),
    ("control: local shadows inline", [L [S "let*", V [S "inc", L [S "fn*", V [S "a"], S "a"]], L [S "inc", I 5]]]),
    ("control: def then call", [L [S "def", S "g", L [S "fn*", V [S "n"], L [S "+", S "n", I 1]]], L [S "g", I 41]]),
    ("control: loop of objects", [L [S "loop*", V [S "xs", V [I 1, I 2], S "acc", V []], L [S "if", L [S "first", S "xs"], L [S "recur", L [S "rest", S "xs"], L [S "vector", S "acc"]], S "acc"]]]) ]

def printTally (label : String) (t : Tally) (complete : Option Bool := none) : IO Unit := do
  let status := match complete with | some true => " (complete)" | some false => " (stopped)" | none => ""
  IO.println s!"== {label}: {t.runs} programs{status}, {t.agree} agree, {t.differ} differ"
  let allTags := (t.byTags.flatMap (·.1)).eraseDups
  let untagged := (t.byTags.filter (·.1.isEmpty)).foldl (fun acc (_, n, _) => acc + n) 0
  IO.println s!"   differing programs with no tag (unexplained): {untagged}"
  for (_, _, ex) in t.byTags.filter (·.1.isEmpty) do
    IO.println s!"     unexplained, e.g. {ex}"
  for tg in allTags do
    let only := (t.byTags.filter (·.1 == [tg])).foldl (fun acc (_, n, _) => acc + n) 0
    let any := (t.byTags.filter (·.1.contains tg)).foldl (fun acc (_, n, _) => acc + n) 0
    let ex := match t.byTags.find? (·.1 == [tg]) with
      | some (_, _, e) => e
      | none => ""
    IO.println s!"   {tg}: {any} differing programs take this path, {only} take only this one; e.g. {ex}"

def main : IO UInt32 := do
  let t0 ← IO.monoMsNow
  IO.println "== examples (jank: the replica's analysis, then the IR's meaning; Clojure: Compiler.java's rules)"
  for (name, forms) in examples do
    let j := runJank forms
    let c := runClojure forms
    let tag := if j.outcome.agrees c then "agree " else "DIFFER"
    IO.println s!"{tag} {name}: {" ".intercalate (forms.map Obj.pr)}\n         jank {j.outcome.show}\n         clj  {c.show}"
  -- Search: find a deviation, set its class (tags) aside, search again.
  let rounds (label : String) (f : Features) (depth seeds : Nat) (oracle : Oracle) : IO (List String) := do
    let mut known : List String := []
    for round in List.range 20 do
      let run := runOne f depth known oracle
      match explore run seeds with
      | none =>
        IO.println s!"== {label} round {round}: explore {seeds} seeds, depth {depth}: nothing new (set aside: {known})"
        break
      | some c =>
        let sh := shrink run c
        IO.println s!"== {label} round {round}: found after {c.runs} timelines; shrunk to {sh.taken.size} decisions: {sh.detail}"
        IO.println ((tape sh.taken).splitOn "\n" |>.map ("     " ++ ·) |> "\n".intercalate)
        let tagsStart := (sh.detail.splitOn "tags [").getD 1 ""
        let tags := ((tagsStart.splitOn "]").headD "").splitOn ", " |>.filter (· != "")
        if tags.isEmpty then
          IO.println "   (untagged: a new class; stopping)"
          break
        known := known ++ tags
    pure known
  let known ← rounds "all forms" {} 4 20000 {}
  let _ ← rounds "fns, lets, macros" { loops := false, privates := false, calls := false } 4 20000 {}
  let _ ← rounds "oracle: builtin = on objects" {} 4 20000 { classBuiltinAssign := true }
  -- Random tallies.
  printTally "tally, 20000 seeds, depth 4" (tallySeeds {} 4 20000)
  printTally "tally, 20000 seeds, depth 4, oracle builtin = on objects" (tallySeeds {} 4 20000 { classBuiltinAssign := true })
  -- Exhaustive over a reduced grammar: every program of depth ≤ 1.
  let small : Features := { lits := [I 0, I 2147483648, D 1.5, B true, .nil, str "s"], names := ["x", "f", "when"] }
  let (t1, c1) := tallyAll small 1 2000000
  printTally "exhaustive, reduced grammar, depth 1" t1 (some c1)
  match exhaust (runOne small 1 known {}) 2000000 with
  | .found c => IO.println s!"== exhaust, reduced grammar, depth 1, known classes set aside: found after {c.runs}: {c.detail}"
  | .complete n => IO.println s!"== exhaust, reduced grammar, depth 1, known classes set aside: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"== exhaust, reduced grammar, depth 1, known classes set aside: stopped at {n}, nothing"
  let tiny : Features := { lits := [I 0, D 1.5, B true, .nil], names := ["x", "when"] }
  match exhaust (runOne tiny 2 known {}) 1500000 with
  | .found c => IO.println s!"== exhaust, tiny grammar, depth 2, known set aside: found after {c.runs}: {c.detail}"
  | .complete n => IO.println s!"== exhaust, tiny grammar, depth 2, known set aside: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"== exhaust, tiny grammar, depth 2, known set aside: stopped at {n}, nothing"
  let t1' ← IO.monoMsNow
  IO.println s!"runtime {t1' - t0} ms"
  return 0

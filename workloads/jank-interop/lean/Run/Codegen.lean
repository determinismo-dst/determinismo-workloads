import Jank.Codegen.ConstSearch
import Jank.Codegen.ProgSearch
import Jank.Codegen.Theorems

/-! The code generator's searches (exe `jank-codegen`): `jank-codegen [doubles|constants|programs|hand]`. -/

open Determinismo Jank.Codegen Jank.Analyzer
open Jank.Codegen.Spec (Outcome)

def describe (c : Counterexample) : String :=
  s!"after {c.runs} timelines, {c.taken.size} decisions: {c.detail}"

def indentTape (t : Array Taken) : String :=
  (tape t).splitOn "\n" |>.map ("      " ++ ·) |> "\n".intercalate

/-- `explore`, then `shrink`, then `exhaust` within `maxRuns`: the report lines. -/
def report (name : String) (run : Source → Ended) (seeds maxRuns : Nat) (showTape := true) : IO Unit := do
  IO.println s!"== {name}"
  match explore run seeds with
  | some c =>
    IO.println s!"  explore ({seeds} seeds): found {describe c}"
    let s := shrink run c
    IO.println s!"  shrunk to {s.taken.size} decisions: {s.detail}"
    if showTape then IO.println s!"    tape:\n{indentTape s.taken}"
  | none => IO.println s!"  explore ({seeds} seeds): nothing"
  if maxRuns == 0 then return
  match exhaust run maxRuns with
  | .found c => IO.println s!"  exhaust: found after {c.runs} timelines: {c.detail}"
  | .complete n => IO.println s!"  exhaust: complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust: stopped at {n} timelines, nothing"

/-- Seeds `0..seeds-1`: how many timelines deviate, and the first of each class, shrunk. -/
def collect (name : String) (run : Source → Ended) (seeds : Nat) (cls : String → String) : IO Unit := do
  IO.println s!"== {name}: {seeds} seeds"
  let mut classes : List (String × Counterexample) := []
  let mut found := 0
  for i in List.range seeds do
    let o := run (Source.seeded i)
    if let some (p, d) := o.violation then
      found := found + 1
      let k := cls p
      if !(classes.any (·.1 == k)) then
        classes := classes ++ [(k, { taken := o.taken, property := p, detail := d, runs := i + 1 })]
  IO.println s!"  {found} of {seeds} timelines deviate; {classes.length} classes"
  for (k, c) in classes do
    let s := shrink run c
    IO.println s!"  [{k}] first at seed {c.runs - 1}; shrunk to {s.taken.size} decisions: {s.detail}"
    IO.println s!"    tape:\n{indentTape s.taken}"

/-- A constant deviation's class: the kind of its culprit part. -/
def constClass (p : String) : String :=
  String.ofList (((p.splitOn "[").getLast?.getD "").toList.takeWhile (· != ']'))

def doubles : IO Unit := do
  report "doubles: the printed text read back as C++ is the same double" ConstSearch.runDoubles 20000 0 (showTape := false)
  -- every exponent field with mantissas 0, 1, max (all binades, subnormals included)
  let mut bad := 0
  let mut total := 0
  for e in List.range 2048 do
    for m in [0, 1, 2, 2^51, 2^52 - 1] do
      for s in [0, 1] do
        let b : UInt64 := UInt64.ofNat (s * 2^63 + e * 2^52 + m)
        total := total + 1
        if (ConstSearch.doubleCheck b).isSome then bad := bad + 1
  IO.println s!"  table: {total} doubles (every exponent, mantissa 0/1/2/2^51/max, both signs): {bad} misread"
  for b in [(0x8000000000000000 : UInt64), 0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000,
            0xFFF8000000000000, 1, 0x4415AF1D78B58C40, 0x4480F0CF064DD592] do
    IO.println s!"    {b}: printed {Float.sbF64 b}"

def constants : IO Unit := do
  for (dyn, label) in [(false, "static runtime (AOT default)"), (true, "dynamic runtime")] do
    IO.println s!"== constants, module target (AOT), {label}: table"
    let rows := ConstSearch.table dyn
    let bad := rows.filter (·.2.isSome)
    IO.println s!"  {bad.length} of {rows.length} constants deviate"
    for (o, r) in bad do IO.println s!"    {o}: {r.getD ""}"
    collect s!"constants, module target, {label}: drawn" (ConstSearch.run dyn) 3000 constClass

/-- The class a property name carries in brackets. -/
def bracketClass (property : String) : String :=
  String.ofList (((property.splitOn "[").getLast?.getD "").toList.takeWhile (· != ']'))

/-- Every mode: seeds explored (one shrunk counterexample per class), then `exhaust` at depth 1. -/
def programs (seeds : Nat) : IO Unit := do
  for m in ProgSearch.modes do
    collectP s!"programs, {m.name}, depth 3" (ProgSearch.run m.cfg 3) seeds
    match exhaust (ProgSearch.run m.cfg 1) 300000 with
    | .found c => IO.println s!"  exhaust (depth 1): found after {c.runs} timelines: [{bracketClass c.property}] {c.detail}"
    | .complete n => IO.println s!"  exhaust (depth 1): complete, {n} timelines, nothing"
    | .stopped n => IO.println s!"  exhaust (depth 1): stopped at {n} timelines, nothing"
  -- the control: the productions of the known deviations left out, JIT -O0
  let clean := fun (dep : Nat) (src : Source) => ProgSearch.run {} dep src true
  collectP "control (known deviations left out), eval -O0, depth 3" (clean 3) seeds
  match exhaust (clean 1) 300000 with
  | .found c => IO.println s!"  exhaust (depth 1): found after {c.runs} timelines: [{bracketClass c.property}] {c.detail}"
  | .complete n => IO.println s!"  exhaust (depth 1): complete, {n} timelines, nothing"
  | .stopped n => IO.println s!"  exhaust (depth 1): stopped at {n} timelines, nothing"
where
  collectP (name : String) (run : Source → Ended) (seeds : Nat) : IO Unit := do
    IO.println s!"== {name}: {seeds} seeds"
    let mut classes : List (String × Counterexample) := []
    let mut found := 0
    for i in List.range seeds do
      let o := run (Source.seeded i)
      if let some (p, d) := o.violation then
        found := found + 1
        let k := bracketClass p
        if !(classes.any (·.1 == k)) then
          classes := classes ++ [(k, { taken := o.taken, property := p, detail := d, runs := i + 1 })]
    IO.println s!"  {found} of {seeds} timelines deviate; {classes.length} classes"
    for (k, c) in classes do
      let s := shrink run c
      IO.println s!"  [{k}] first at seed {c.runs - 1}; shrunk to {s.taken.size} decisions:\n    {s.detail}"

def kwF (n : String) : Form := .lit (.keyword "" n)
def intF (n : Int) : Form := .lit (Obj.ofInt n)

/-- The minimal programs of the report, each through both sides. -/
def hand : IO Unit := do
  IO.println "== minimal programs (Clojure | jank)"
  let o3 := { passes := Passes.ofLevel 3 : Jank.Codegen.Config }
  let o1 := { passes := Passes.ofLevel 1 : Jank.Codegen.Config }
  let aot := { target := .module, runtime := { dynamic := false } : Jank.Codegen.Config }
  let cases : List (String × List Form × Jank.Codegen.Config) := [
    ("G1 operator after operands", [.call (.do_ [.call (.sym "log") [kwF "f"], .sym "identity"]) [.do_ [.call (.sym "log") [kwF "a"], intF 1]]], {}),
    ("G2 munged let names", [.let_ [("a-b", intF 1), ("a_b", intF 2)] [.sym "a-b"]], {}),
    ("G2 munged fn params", [.call (.fn_ none ["a-b", "a_b"] [.sym "a-b"]) [intF 1, intF 2]], {}),
    ("G2 dotted fn param", [.call (.fn_ none ["a.b"] [.sym "a.b"]) [intF 1]], {}),
    ("G3 nested loop, outer recur", [.loop [("i", intF 0)] [.let_ [("z", .loop [("i", intF 5)] [.if_ (.call (.sym "lt") [.sym "i", intF 6]) (.recur [.call (.sym "inc") [.sym "i"]]) (some (.sym "i"))])] [.if_ (.call (.sym "lt") [.sym "i", intF 2]) (.recur [.call (.sym "inc") [.sym "i"]]) (some (.sym "i"))]]], {}),
    ("G3 inner loop, fn recur", [.def_ "f" [] (some (.fn_ (some "f") ["n", "acc"] [.let_ [("z", .loop [("n", intF 0)] [.if_ (.call (.sym "lt") [.sym "n", intF 1]) (.recur [.call (.sym "inc") [.sym "n"]]) (some (.sym "n"))])] [.if_ (.call (.sym "pos?") [.sym "n"]) (.recur [.call (.sym "dec") [.sym "n"], .call (.sym "inc") [.sym "acc"]]) (some (.sym "acc"))]])), .call (.sym "f") [intF 3, intF 0]], {}),
    ("G4 hyphenated self reference from a nested fn", [.call (.call (.fn_ (some "my-f") [] [.fn_ none [] [.sym "my-f"]]) []) []], {}),
    ("G4 control: unhyphenated", [.call (.call (.fn_ (some "self") [] [.fn_ none [] [.sym "self"]]) []) []], {}),
    ("G5 two letfns, forward reference in the first", [.letfn [("f", [], [.call (.sym "g") []]), ("g", [], [intF 1])] [.call (.sym "f") []], .letfn [("h", [], [intF 2])] [.call (.sym "h") []]], {}),
    ("G6 constants merged", [.let_ [("a", .vec [.vec []]), ("b", .vec [.lit (.persistentList none [])])] [.call (.sym "list?") [.call (.sym "first") [.sym "b"]]]], {}),
    ("G7 def metadata, AOT static", [.def_ "f" [("arglists", .list [.sym "" "quote" none, .list [.vec [.sym "" "x" none] none] none] none)] (some (.fn_ (some "f") ["x"] [.sym "x"])), .call (.sym "meta-of") [.varq "f"]], aot),
    ("G7 def metadata naming a local, JIT", [.let_ [("y", intF 5)] [.def_ "x" [("k", .sym "" "y" none)] (some (intF 1)), .call (.sym "meta-of") [.varq "x"]]], {}),
    ("G8 case on a long beyond i32", [.case_ (intF 4294967296) [(4294967296, kwF "yes")] (kwF "no")], {}),
    ("G8 case on Long/MIN_VALUE", [.case_ (intF (-9223372036854775808)) [(-9223372036854775808, kwF "yes")] (kwF "no")], {}),
    ("G9 -O3 var read twice across a redefinition", [.def_ "x" [] (some (intF 1)), .let_ [("a", .sym "x")] [.def_ "x" [] (some (intF 2)), .vec [.sym "a", .sym "x"]]], o3),
    ("G9 control at -O0", [.def_ "x" [] (some (intF 1)), .let_ [("a", .sym "x")] [.def_ "x" [] (some (intF 2)), .vec [.sym "a", .sym "x"]]], {}),
    ("G10 -O3 case on a var read twice", [.def_ "mode" [] (some (intF 1)), .vec [.sym "mode", .case_ (.sym "mode") [(1, kwF "one"), (2, kwF "two")] (kwF "other")]], o3),
    ("G10 -O1 case on a literal used twice", [.let_ [("a", intF 1)] [.call (.sym "log") [.sym "a"], .let_ [("m", intF 1)] [.case_ (.sym "m") [(1, kwF "one")] (kwF "other")]]], o1),
    ("G10 -O1 loop binding on an untyped literal used twice", [.let_ [("a", .lit (.bigInteger 1))] [.loop [("x", .lit (.bigInteger 1)), ("c", intF 0)] [.if_ (.call (.sym "lt") [.sym "c", intF 1]) (.recur [.sym "x", .call (.sym "inc") [.sym "c"]]) (some (.vec [.sym "a", .sym "x"]))]]], o1),
    ("G12 -O1 same constant in both branches inside a catch", [.try_ [.call (.sym "log") [intF 1], .throw_ (kwF "boom")] (some ("e", [.if_ (.call (.sym "log") [intF 2]) (kwF "x") (some (kwF "x"))])) none], o1),
    ("G12 -O1 same constant in both branches inside a finally", [.try_ [.call (.sym "log") [intF 1]] none (some [.if_ (.call (.sym "log") [intF 2]) (kwF "x") (some (kwF "x"))])], o1),
    ("G12 control at -O0", [.try_ [.call (.sym "log") [intF 1], .throw_ (kwF "boom")] (some ("e", [.if_ (.call (.sym "log") [intF 2]) (kwF "x") (some (kwF "x"))])) none], {}),
    ("G11 closure whose parameter shadows its name", [.let_ [("y", intF 1)] [.call (.fn_ (some "f") ["f"] [.sym "y"]) [intF 5]]], {}),
    ("G16 case branches of different types, the last one the default's type", [.case_ (intF 1) [(1, .lit (.persistentString "one")), (2, kwF "two")] (kwF "other")], {}),
    ("G16 control: the last branch differs from the default", [.case_ (intF 1) [(1, kwF "one"), (2, .lit (.persistentString "two"))] (kwF "other")], {}),
    ("D24 (round 1) catch and finally both throw", [.try_ [.try_ [.throw_ (kwF "a")] (some ("e", [.throw_ (kwF "b")])) (some [.throw_ (kwF "c")])] (some ("e", [.sym "e"])) none], {})
  ]
  for (name, p, cfg) in cases do
    let c := Spec.run p
    let (j, _) := jankRun p cfg
    let verdict := match agree c j with | some true => "agree" | some false => "DEVIATES" | none => "not comparable"
    IO.println s!"  {name}: {" ".intercalate (p.map Form.code)}\n    Clojure {c.show} | jank {j.show}  [{verdict}]"

/-- The generated C++ of one program (for the report). -/
def showCpp (p : List Form) (cfg : Jank.Codegen.Config := {}) : IO Unit := do
  let (_, tr) := jankRun p cfg true
  IO.println tr.cpp
  IO.println tr.expr

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  let t0 ← IO.monoMsNow
  if only.isNone || only == some "hand" then hand
  if only.isNone || only == some "doubles" then doubles
  if only.isNone || only == some "constants" then constants
  if only.isNone || only == some "programs" then programs 2000
  if only == some "cpp" then
    showCpp [.loop [("i", intF 0)] [.let_ [("z", .loop [("i", intF 5)] [.if_ (.call (.sym "lt") [.sym "i", intF 6]) (.recur [.call (.sym "inc") [.sym "i"]]) (some (.sym "i"))])] [.if_ (.call (.sym "lt") [.sym "i", intF 2]) (.recur [.call (.sym "inc") [.sym "i"]]) (some (.sym "i"))]]]
  let t1 ← IO.monoMsNow
  IO.println s!"(ran in {(t1 - t0) / 1000}.{((t1 - t0) % 1000) / 100} s)"
  return 0

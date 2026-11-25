import Jank.R3.Codegen.NativeSpec
import Jank.R3.Codegen.NativeSearch
import Jank.R3.Codegen.Census
import Jank.R3.Codegen.Variadic
import Jank.R3.Codegen.Literals
import Jank.R3.Codegen.Theorems
import Jank.Codegen.ProgSearch

/-! Round 3 driver: Codegen (exe `jank3-codegen`). `jank3-codegen [hand|...]`. -/

open Jank.R3.Codegen Determinismo

def lvls : List Lvl := [.o0, .o1, .o3]

def showRow (name : String) (f : NF) : IO Unit := do
  let c := runClojure f
  IO.println s!"  {name}: {f.code}"
  IO.println s!"    Clojure: {c.show}"
  for tgt in [Target.eval, .module] do
    for l in lvls do
      let j := runJank l tgt f
      let v := match agreeCJ c j.out with | some true => "agree" | some false => "DEVIATES" | none => "n/c"
      IO.println s!"    jank {if tgt == .eval then "JIT" else "AOT"} -O{l.n}: {j.out.show}  [{v}]"

def nativeHand : IO Unit := do
  IO.println "== native world: minimal programs"
  showRow "R24 loop local int, recur 0.5 steps" (.loop [("x", .int 0)] (.if_ (.op .lt (.sym "x") (.int 10)) (.recur [.op .add (.sym "x") (.dbl 0.5)]) (.sym "x")))
  showRow "infinite side-effect-free loop on a param" (.call (.fn_ [("x", .obj)] (.loop [] (.if_ (.sym "x") (.recur []) (.kw "done")))) [.bool true])
  showRow "recur of an out-of-range double into an int local" (.loop [("x", .int 0), ("n", .int 0)] (.if_ (.op .lt (.sym "n") (.int 1)) (.recur [.dbl 1e10, .op .add (.sym "n") (.int 1)]) (.sym "x")))
  showRow "(int 1e20)" (.toInt (.dbl 1e20))
  showRow "(int 3000000000)" (.toInt (.int 3000000000))
  showRow "int division overflow" (.let_ "x" (.op .sub (.int (-2147483647)) (.int 1)) (.op .div (.sym "x") (.int (-1))))
  showRow "(/ 1 0) (documented UB)" (.op .div (.int 1) (.int 0))
  showRow "top-level if merge (R23 example 1)" (.if_ (.bool true) (.int 1) (.dbl 2.5))
  showRow "if merge in a let" (.let_ "u" (.int 0) (.if_ (.bool true) (.int 1) (.dbl 2.5)))
  showRow "-2147483648 literal is long in C++" (.op .lt (.op .sub (.int (-2147483648)) (.int 1)) (.int 0))
  for f in [NF.op .lt (.op .sub (.int (-2147483648)) (.int 1)) (.int 0),
            .op .add (.op .sub (.int (-2147483648)) (.int 1)) (.dbl 0.5),
            .let_ "u" (.int 0) (.op .div (.int (-2147483648)) (.int (-1)))] do
    IO.println s!"    {f.code}: jank -O0 {(runJank .o0 .eval f).out.show}; round 2's model (the literal as an int) {(runJank .o0 .eval f (analyzerLiterals := true)).out.show}; Clojure {(runClojure f).show}"
  showRow "typed param + fn recur" (.call (.fn_ [("n", .long)] (.if_ (.op .lt (.sym "n") (.int 3)) (.recur [.op .add (.sym "n") (.int 1)]) (.sym "n"))) [.int 0])
  showRow "R25 (+ 2147483647 1)" (.op .add (.int 2147483647) (.int 1))
  showRow "closure over a native local" (.let_ "u" (.int 2147483647) (.call (.fn_ [("p", .obj)] (.op .add (.sym "u") (.int 1))) [.int 0]))
  showRow "fn recur on an object param, no side effect, never ends" (.call (.fn_ [("p", .obj)] (.if_ (.op .lt (.sym "p") (.int 10)) (.recur [.sym "p"]) (.sym "p"))) [.int 0])
  showRow "loop that never ends but logs (a side effect)" (.loop [("x", .int 0)] (.if_ (.op .lt (.sym "x") (.int 10)) (.recur [.log (.sym "x")]) (.sym "x")))
  showRow "object small integers wrap (round 1 D1)" (.call (.fn_ [("a", .obj)] (.op .add (.sym "a") (.int 1))) [.int 2147483647])

def indentTape (t : Array Taken) : String :=
  (tape t).splitOn "\n" |>.map ("      " ++ ·) |> "\n".intercalate

def printCensus (name : String) (run : Source → Ended) (c : Census) (showTape : Bool := false) : IO Unit := do
  IO.println s!"  {name}: {c.runs} timelines{if c.complete then " (complete)" else ""}, {c.violating} violate, {c.classes.length} classes"
  for h in c.classes do
    let s := shrink run h.first 600
    IO.println s!"    [{h.cls}] {h.count}x; shrunk to {s.taken.size} decisions: {s.detail}"
    if showTape then IO.println s!"{indentTape s.taken}"

/-- The classes the native world finds; `known` sets them aside for the residual search. -/
def nativeKnown : List String :=
  ["D2 (round 1): integer / is C++ division", "CG2 float-to-integer conversion out of range",
   "R33 booleans are numbers", "R24 loop local keeps the literal's type", "R23 if merges branch types",
   "CG2b int does not check the int range", "CG5 typed parameter + fn-level recur: invalid C++",
   "documented: integer division by zero is UB (book)", "R36 object loop local, native recur value",
   "jank ^cpp/int parameter (no Clojure counterpart)", "D1 (round 1): long overflow wraps (documented)",
   "R25 32-bit literal arithmetic", "CG1 forward progress", "D1 (round 1): small integers wrap at 32 bits", "D2 (round 1): INT_MIN / -1",
   "Clojure rejects (recur to a primitive parameter with another type)"]

def nativeSearch (seeds : Nat) : IO Unit := do
  IO.println s!"== native world: searches ({seeds} seeds per mode, depth 3; property 1 = jank vs Clojure, 2 = -On vs -O0)"
  for (tgt, tname) in [(Target.eval, "JIT (eval)"), (Target.module, "AOT (module)")] do
    for l in [Lvl.o0, .o1, .o2, .o3] do
      for prop in (if l == .o0 then [1] else [1, 2]) do
        let r := NativeSearch.run l tgt 3 [] prop
        printCensus s!"{tname} -O{l.n}, property {prop}, depth 3, {seeds} seeds" r (censusSeeds r seeds)

def nativeResidual (seeds : Nat) (exhaustRuns : Nat) : IO Unit := do
  IO.println "== native world: residual (every class found set aside)"
  for (tgt, tname) in [(Target.eval, "JIT (eval)"), (Target.module, "AOT (module)")] do
    for l in [Lvl.o0, .o3] do
      let r := NativeSearch.run l tgt 3 nativeKnown 0
      printCensus s!"{tname} -O{l.n}, depth 3, {seeds} seeds (both properties)" r (censusSeeds r seeds (first := 100000))
      if exhaustRuns > 0 then
        let r2 := fun src => NativeSearch.run l tgt 1 nativeKnown 0 src true
        printCensus s!"{tname} -O{l.n}, depth 1 (small pools), exhaustive (partitioned)" r2 (censusPartitioned r2 exhaustRuns)

/-- How many programs change outcome when the literal `-2147483648` is taken as an `int` (round
2's model) instead of the `long` its C++ text is. -/
def literalTypeCensus (seeds : Nat) : IO Unit := do
  IO.println s!"== the C++ type of the literal text -2147483648 (long) against round 2's model (int): {seeds} seeds, depth 3, JIT -O0"
  let mut differ := 0
  let mut first : Option String := none
  for i in [0:seeds] do
    let src : Source := { gen := mkStdGen (Jank.R3.Codegen.mixSeed i) }
    match (NativeSearch.genProg false 3).run { decisions := { source := src, limit := 200 } } with
    | .ok f _ =>
      let a := runJank .o0 .eval f
      let b := runJank .o0 .eval f (analyzerLiterals := true)
      if agreeJJ a.out b.out == some false then
        differ := differ + 1
        if first.isNone then first := some s!"{f.code}: jank {a.out.show}, round 2's model {b.out.show}, Clojure {(runClojure f).show}"
    | _ => pure ()
  IO.println s!"  {differ} of {seeds} programs differ"
  if let some e := first then IO.println s!"  first: {e}"

/-! ## Arity dispatch (variadic fns, calls with more than 10 arguments, `apply`) -/

def variadicCensus (maxFixed : Nat) (maxArgs : Nat) : IO Unit := do
  IO.println s!"== variadic world: every fn of fixed arities ⊆ [0, {maxFixed}] and at most one variadic arity (required 0..{maxFixed}), every call of 0..{maxArgs} arguments"
  let mut shapes := 0
  let mut calls := 0
  let mut classes : List (String × Nat × String) := []
  for mask in [0:(2 ^ (maxFixed + 1))] do
    let fixed := (List.range (maxFixed + 1)).filter fun i => (mask >>> i) % 2 == 1
    for v in [0:(maxFixed + 2)] do
      let ars : List Variadic.Ar := fixed.map (fun f => ⟨f, false⟩) ++ (if v == 0 then [] else [⟨v - 1, true⟩])
      if ars.isEmpty then continue
      shapes := shapes + 1
      for n in [0:(maxArgs + 1)] do
        calls := calls + 1
        let c := Variadic.cljCall ars n
        let j := Variadic.jankCall ars n
        let k := Variadic.classOf ars c j
        if k != "agree" then
          match classes.find? (·.1 == k) with
          | some _ => classes := classes.map fun (a, m, e) => if a == k then (a, m + 1, e) else (a, m, e)
          | none =>
            let shown := " ".intercalate (ars.map fun a => "[" ++ toString a.fixed ++ (if a.variadic then " & rest" else "") ++ "]")
            classes := classes ++ [(k, 1, s!"fn arities {shown}, {n} args: Clojure {repr c}, jank {repr j}")]
  IO.println s!"  {shapes} fns, {calls} calls (complete); {classes.length} classes"
  for (k, m, e) in classes do IO.println s!"    [{k}] {m}x; first: {e}"

def variadicResidual (maxFixed maxArgs : Nat) : IO Unit := do
  -- the same walk restricted to fns jank accepts (every parameter list of at most 10 symbols)
  let mut calls := 0
  let mut bad := 0
  for mask in [0:(2 ^ (maxFixed + 1))] do
    let fixed := (List.range (maxFixed + 1)).filter fun i => (mask >>> i) % 2 == 1
    for v in [0:(maxFixed + 2)] do
      let ars : List Variadic.Ar := fixed.map (fun f => ⟨f, false⟩) ++ (if v == 0 then [] else [⟨v - 1, true⟩])
      if ars.isEmpty || ars.any (·.size > 10) then continue
      for n in [0:(maxArgs + 1)] do
        calls := calls + 1
        let c := Variadic.cljCall ars n
        let j := Variadic.jankCall ars n
        let k := Variadic.classOf ars c j
        if k != "agree" && k != "arity exception reports 11 arguments" then bad := bad + 1
  IO.println s!"  residual (CG4 and the arity-exception count set aside): {calls} calls (complete), {bad} disagree"

/-! ## Map and set expressions with run-time keys -/

def literalsCensus (maxLen : Nat) (domain : Nat) : IO Unit := do
  IO.println s!"== map/set expressions: every key list of length 1..{maxLen} over {domain} values"
  let mut lists : List (List Nat) := [[]]
  let mut total := 0
  let mut cDup := 0
  let mut compiledDiff := 0
  let mut topDiff := 0
  let mut setDiff := 0
  let mut firstTop : Option String := none
  for _ in [0:maxLen] do
    lists := lists.flatMap fun l => (List.range domain).map (l ++ [·])
    for keys in lists do
      total := total + 1
      let c := Literals.cljMap keys
      let cj := Literals.jankCompiledMap keys
      let tj := Literals.jankTopMap keys
      if c != cj then compiledDiff := compiledDiff + 1
      if c != tj then
        topDiff := topDiff + 1
        if firstTop.isNone && tj.count != cj.count then
          firstTop := some s!"keys {keys}: Clojure {repr c}, compiled {repr cj}, top level {repr tj}"
      if Literals.cljSet keys != Literals.jankSet keys then setDiff := setDiff + 1
      if (match c with | .duplicate _ => true | _ => false) then cDup := cDup + 1
  IO.println s!"  {total} key lists (complete); Clojure throws Duplicate key for {cDup}"
  IO.println s!"  maps: compiled differs {compiledDiff}, top level differs {topDiff}; sets differ {setDiff}"
  if let some e := firstTop then IO.println s!"  top level keeps both pairs: {e}"
  -- residual: lists without a repeated key
  let mut res := 0
  let mut n := 0
  lists := [[]]
  for _ in [0:maxLen] do
    lists := lists.flatMap fun l => (List.range domain).map (l ++ [·])
    for keys in lists do
      if Literals.firstDup keys == none then
        n := n + 1
        if Literals.cljMap keys != Literals.jankCompiledMap keys || Literals.cljMap keys != Literals.jankTopMap keys
           || Literals.cljSet keys != Literals.jankSet keys then res := res + 1
  IO.println s!"  residual (no repeated key): {n} lists (complete), {res} disagree"

/-! ## Round 2's program world, rerun -/

def round2Programs (seeds : Nat) (exhaustRuns : Nat) : IO Unit := do
  IO.println s!"== round 2's program world (Jank.Codegen.ProgSearch), {seeds} seeds per mode, depth 3"
  for m in Jank.Codegen.ProgSearch.modes do
    let r := Jank.Codegen.ProgSearch.run m.cfg 3
    let c := censusSeeds r seeds (mixed := false)
    IO.println s!"  {m.name}: {c.runs} timelines, {c.violating} violate, {c.classes.length} classes: {c.classes.map (·.cls)}"
  let clean := fun (dep : Nat) (src : Source) => Jank.Codegen.ProgSearch.run {} dep src true
  let c := censusSeeds (clean 3) seeds (mixed := false)
  IO.println s!"  control (known classes left out), eval -O0, depth 3: {c.runs} timelines, {c.violating} violate"
  for (name, cfg) in [("eval -O0", ({} : Jank.Codegen.Config)),
                      ("module (AOT)", { target := .module, runtime := { dynamic := false } })] do
    let r := fun (src : Source) => Jank.Codegen.ProgSearch.run cfg 2 src true
    let e := censusPartitioned r exhaustRuns
    IO.println s!"  control, {name}, depth 2, exhaustive (partitioned by the first decision, ≤ {exhaustRuns} per partition): {e.runs} timelines{if e.complete then " (complete)" else " (stopped)"}, {e.violating} violate {e.classes.map (·.cls)}"

def flagsReport : IO Unit := do
  IO.println "== optimizer configuration (Flags): effective clang level, -fwrapv, mustprogress, per mode"
  for bt in [BuildType.debug, .release, .relWithDebInfo, .none] do
    for (cmd, cname) in [(Command.run, "run"), (.repl, "repl"), (.compile, "compile")] do
      for o in [none, some 0, some 1, some 2, some 3] do
        let c : Cli := { command := cmd, opt := o }
        let j := semanticsOf (jitArgs bt c)
        let a := semanticsOf (aotArgs bt c [] false)
        IO.println s!"  {repr bt} {cname} -O {o}: IR passes {repr c.irPasses}; JIT level {j.level} wraps {j.wraps} loops-mustprogress {j.loopsMustProgress} fns {j.functionsMustProgress} fptosi-poison {j.fptosiPoison}; AOT level {a.level} wraps {a.wraps} loops {a.loopsMustProgress} std {effectiveStd (aotArgs bt c [] false)}"

def main (args : List String) : IO UInt32 := do
  let only := args.head?
  let t0 ← IO.monoMsNow
  if only.isNone || only == some "hand" then nativeHand
  if only == some "flags" then flagsReport
  if only.isNone || only == some "native" then
    nativeSearch 2000
    literalTypeCensus 2000
  if only == some "residual" then nativeResidual 20000 0
  if only == some "exhaust" then nativeResidual 0 400000
  if only.isNone || only == some "variadic" then
    variadicCensus 12 16
    variadicResidual 12 16
  if only.isNone || only == some "literals" then literalsCensus 9 3
  if only == some "round2" then round2Programs 2000 20000
  let t1 ← IO.monoMsNow
  IO.println s!"(ran in {(t1 - t0) / 1000}.{((t1 - t0) % 1000) / 100} s)"
  return 0

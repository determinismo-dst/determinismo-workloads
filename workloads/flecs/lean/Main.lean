import FlecsLean.Search
import FlecsLean.Cases
import FlecsLean.Threads
import FlecsLean.Search2
import FlecsLean.Pipeline
import FlecsLean.QueryProps

open Flecs

def showFound (f : Found) (shrinkIt : Bool) : IO Unit := do
  let prop := (f.property.splitOn " | ").headD f.property
  IO.println s!"  signature: {f.property}"
  IO.println s!"  detail: {f.detail}"
  IO.println s!"  tape: {f.tape.toList}"
  let s := if shrinkIt then shrinkSig f.scenario f.property else f.scenario
  IO.println s!"  shrunk scenario: stages={s.stages} cfg={s.cfg} panicFirst={s.panicFirst}"
  for op in s.ops do
    IO.println s!"    {repr op}"
  let vs := checkAll s
  for v in vs do
    if v.property == prop then IO.println s!"  after shrink: {v.detail}"

def report (title : String) (st : RunStats) (shrinkIt : Bool) : IO Unit := do
  IO.println s!"== {title}: {st.programs} programs, {st.failures} failing"
  for (p, n) in st.byProperty do
    IO.println s!"  {p}: {n}"
  for f in st.first do
    showFound f shrinkIt

def findWith (mode : String) (run : Determinismo.Source → Determinismo.Ended) (n seed : Nat) :
    IO (Option Determinismo.Counterexample) := do
  if mode == "exhaust" then
    match Determinismo.exhaust run n with
    | .found c => return some c
    | .complete r => IO.println s!"  exhaust complete: {r} timelines, none broke the property"; return none
    | .stopped r => IO.println s!"  exhaust stopped at {r} timelines (bound not reached)"; return none
  else
    let r := Determinismo.explore run n seed
    if r.isNone then IO.println s!"  explore: {n} timelines from seed {seed}, none broke the property"
    return r

def greport {α} [Repr α] (title : String) (st : GStats α) (shrinkWith : Option (String → α → α)) : IO Unit := do
  IO.println s!"== {title}: {st.programs} programs, {st.failures} failing"
  for (p, n) in st.byProperty do
    IO.println s!"  {p}: {n}"
  for f in st.first do
    IO.println s!"  signature: {f.sig}"
    IO.println s!"  detail: {f.detail}"
    IO.println s!"  tape: {f.tape.toList}"
    match shrinkWith with
    | some sh => IO.println s!"  shrunk: {repr (sh f.sig f.prog)}"
    | none => IO.println s!"  program: {repr f.prog}"

def glib {α} [Repr α] [Inhabited α] (mode : String) (g : EStateM Determinismo.Stop Determinismo.Decisions α)
    (check : α → List (String × String)) (prop : String) (n seed : Nat)
    (shrinkWith : String → α → α) : IO Unit := do
  let props := if prop == "all" then [] else [prop]
  let run := gtimeline g check props
  let found ← findWith mode run n seed
  match found with
  | none => IO.println s!"== lib {mode} prop={prop}: no counterexample"
  | some c =>
    let c' := Determinismo.shrink run c
    IO.println s!"== lib {mode} prop={prop}: counterexample after {c.runs} timelines"
    IO.println s!"  property: {c'.property}"
    IO.println s!"  detail: {c'.detail}"
    let x := gprogOf g c'.values
    IO.println s!"  program (shrunk by decisions): {repr x}"
    IO.println s!"  program (shrunk by parts): {repr (shrinkWith c'.property x)}"
    IO.println "  tape:"
    IO.println (Determinismo.tape c'.taken)

def pipeMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : Pipe.Prog) => gshrink Pipe.shrinkCands Pipe.check sig p
  match args with
  | ["explore", seed, n, nsys, maxTerms] =>
    let g : TapeM Pipe.Prog := Pipe.genProg Pipe.idMenu nsys.toNat! maxTerms.toNat!
    greport s!"pipe explore seed={seed} n={n} nsys={nsys} maxTerms={maxTerms}"
      (gexplore g Pipe.check seed.toNat! n.toNat!) (some sh)
  | ["exhaust-small", limit, nsys, maxTerms] =>
    let g : TapeM Pipe.Prog := Pipe.genProgSmall Pipe.idMenu nsys.toNat! maxTerms.toNat!
    let (st, done) := gexhaust g Pipe.check limit.toNat!
    greport s!"pipe exhaust-small nsys={nsys} maxTerms={maxTerms} limit={limit} complete={done}" st (some sh)
  | ["exhaust-frame", limit, nsys] =>
    let g : TapeM Pipe.Prog := Pipe.genProgFrame nsys.toNat!
    let (st, done) := gexhaust g Pipe.check limit.toNat!
    greport s!"pipe exhaust-frame nsys={nsys} limit={limit} complete={done}" st (some sh)
  | ["lib", mode, kind, seed, n, nsys, maxTerms, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions Pipe.Prog :=
      if kind == "frame" then Pipe.genProgFrame nsys.toNat!
      else if kind == "small" then Pipe.genProgSmall Pipe.idMenu nsys.toNat! maxTerms.toNat!
      else Pipe.genProg Pipe.idMenu nsys.toNat! maxTerms.toNat!
    glib mode g Pipe.check prop n.toNat! seed.toNat! sh
  | _ => IO.println "usage: pipe explore SEED N NSYS MAXTERMS | exhaust-small LIMIT NSYS MAXTERMS | exhaust-frame LIMIT NSYS | lib MODE KIND SEED N NSYS MAXTERMS PROP"; return 1
  return 0

def queryMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : QProg) => gshrink shrinkQ checkQ sig p
  match args with
  | ["explore", seed, n, ents, len] =>
    let g : TapeM QProg := genQProg ents.toNat! len.toNat!
    greport s!"query explore seed={seed} n={n} ents={ents} len={len}"
      (gexplore g checkQ seed.toNat! n.toNat!) (some sh)
  | ["exhaust", limit, ents, len] =>
    let g : TapeM QProg := genQProg ents.toNat! len.toNat!
    let (st, done) := gexhaust g checkQ limit.toNat!
    greport s!"query exhaust ents={ents} len={len} limit={limit} complete={done}" st (some sh)
  | ["trace", name] =>
    for (nm, p) in qcases do
      if nm == name then
        for l in traceQProg p do IO.println l
  | ["cases"] =>
    for (name, p) in qcases do
      IO.println s!"== query case {name}"
      for (pr, d) in checkQ p do IO.println s!"  PROPERTY {pr}: {d}"
  | ["lib", mode, seed, n, ents, len, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions QProg := genQProg ents.toNat! len.toNat!
    glib mode g checkQ prop n.toNat! seed.toNat! sh
  | _ => IO.println "usage: query explore SEED N ENTS LEN | exhaust LIMIT ENTS LEN | lib MODE SEED N ENTS LEN PROP"; return 1
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["cases"] =>
    for (name, sc) in allCases do
      IO.println s!"== case {name}"
      let a := runScenario sc false
      IO.println s!"  merge/run: fail={repr (a.fail.map toString)}"
      IO.println s!"  final state: {repr a.state.toList}"
      for v in a.violations do IO.println s!"  violation: {v}"
      for l in a.log do IO.println s!"  log: {repr l}"
      for v in checkAll sc do IO.println s!"  PROPERTY {v.property}: {v.detail}"
  | ["explore", seed, n, ents, len] =>
    let g : TapeM Scenario := genScenario ents.toNat! len.toNat!
    report s!"explore seed={seed} n={n} ents={ents} len={len}" (explore g [] seed.toNat! n.toNat!) true
  | ["exhaust", limit, ents, len] =>
    let g : TapeM Scenario := genScenario ents.toNat! len.toNat!
    let (st, done) := exhaust g [] limit.toNat!
    report s!"exhaust ents={ents} len={len} limit={limit} complete={done}" st true
  | ["exhaust-small", limit, cfg, stages, ents, len, pf] =>
    let g : TapeM Scenario := genSmallScenario cfg.toNat! stages.toNat! ents.toNat! len.toNat! (pf == "1")
    let (st, done) := exhaust g [] limit.toNat!
    report s!"exhaust-small cfg={cfg} stages={stages} ents={ents} len={len} panicFirst={pf} limit={limit} complete={done}" st true
  | ["obs-explore", seed, n, ents, len] =>
    let g : TapeM Scenario := genObsScenario ents.toNat! len.toNat!
    report s!"observer explore seed={seed} n={n} ents={ents} len={len}" (explore g [] seed.toNat! n.toNat!) true
  | ["obs-exhaust", limit, ents, len] =>
    let g : TapeM Scenario := genObsScenario ents.toNat! len.toNat!
    let (st, done) := exhaust g [] limit.toNat!
    report s!"observer exhaust ents={ents} len={len} limit={limit} complete={done}" st true
  | ["isa-explore", seed, n, ents, len] =>
    let g : TapeM Scenario := genIsAScenario ents.toNat! len.toNat!
    report s!"IsA explore seed={seed} n={n} ents={ents} len={len}" (explore g [] seed.toNat! n.toNat!) true
  | ["isa-exhaust", limit, ents, len] =>
    let g : TapeM Scenario := genIsAScenario ents.toNat! len.toNat!
    let (st, done) := exhaust g [] limit.toNat!
    report s!"IsA exhaust ents={ents} len={len} limit={limit} complete={done}" st true
  | ["ei-explore", seed, n, len] =>
    let g : TapeM Scenario := genEIScenario len.toNat!
    report s!"entity-index explore seed={seed} n={n} len={len}" (explore g [] seed.toNat! n.toNat!) true
  | ["ei-exhaust", limit, len] =>
    let g : TapeM Scenario := genEIScenario len.toNat!
    let (st, done) := exhaust g [] limit.toNat!
    report s!"entity-index exhaust len={len} limit={limit} complete={done}" st true
  | ["lib", mode, seed, n, cfgOrEnts, len, prop] =>
    -- determinismo's explore/exhaust/shrink/tape on one property
    let g : EStateM Determinismo.Stop Determinismo.Decisions Scenario :=
      if mode == "obs" then genObsScenario cfgOrEnts.toNat! len.toNat!
      else if mode == "isa" then genIsAScenario cfgOrEnts.toNat! len.toNat!
      else if mode == "explore" then genScenario cfgOrEnts.toNat! len.toNat!
      else if mode == "ei" then genEIScenario len.toNat!
      else genSmallScenario cfgOrEnts.toNat! 1 2 len.toNat! true
    -- "xsmall": the small call menu, explored at random
    let mode := if mode == "xsmall" || mode == "obs" || mode == "isa" then "explore" else mode
    let props := if prop == "all" then [] else [prop]
    let run := timeline g props
    let found ← findWith mode run n.toNat! seed.toNat!
    match found with
    | none => IO.println s!"== lib {mode} prop={prop}: no counterexample"
    | some c =>
      let c' := Determinismo.shrink run c
      IO.println s!"== lib {mode} prop={prop}: counterexample after {c.runs} timelines"
      IO.println s!"  property: {c'.property}"
      IO.println s!"  detail: {c'.detail}"
      let s := scenarioOf g c'.values
      let s2 := shrinkSig s c'.property
      IO.println s!"  program (shrunk by decisions): stages={s.stages} cfg={s.cfg} panicFirst={s.panicFirst}"
      for op in s.ops do IO.println s!"    {repr op}"
      IO.println s!"  program (shrunk by calls): stages={s2.stages} cfg={s2.cfg} panicFirst={s2.panicFirst}"
      for op in s2.ops do IO.println s!"    {repr op}"
      IO.println "  tape:"
      IO.println (Determinismo.tape c'.taken)
  | ["threads", mode, seed, n, cfg, len] =>
    let run := threadTimeline cfg.toNat! 2 len.toNat!
    let found ← findWith mode run n.toNat! seed.toNat!
    match found with
    | none => IO.println s!"== threads {mode} cfg={cfg} len={len} n={n}: no counterexample"
    | some c =>
      let c' := Determinismo.shrink run c
      IO.println s!"== threads {mode} cfg={cfg}: counterexample after {c.runs} timelines"
      IO.println s!"  property: {c'.property}"
      IO.println s!"  detail: {c'.detail}"
      IO.println "  tape:"
      IO.println (Determinismo.tape c'.taken)
  | "pipe" :: rest => return (← pipeMain rest)
  | "query" :: rest => return (← queryMain rest)
  | _ =>
    IO.println "usage: flecs-search explore SEED N ENTS LEN | exhaust LIMIT ENTS LEN | ei-explore SEED N LEN | ei-exhaust LIMIT LEN"
    return 1
  return 0

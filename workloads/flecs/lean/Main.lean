import FlecsLean.Search
import FlecsLean.Cases
import FlecsLean.Threads

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
      if mode == "explore" then genScenario cfgOrEnts.toNat! len.toNat!
      else if mode == "ei" then genEIScenario len.toNat!
      else genSmallScenario cfgOrEnts.toNat! 1 2 len.toNat! true
    -- "xsmall": the small call menu, explored at random
    let mode := if mode == "xsmall" then "explore" else mode
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
  | _ =>
    IO.println "usage: flecs-search explore SEED N ENTS LEN | exhaust LIMIT ENTS LEN | ei-explore SEED N LEN | ei-exhaust LIMIT LEN"
    return 1
  return 0

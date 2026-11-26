import FlecsLean.Search
import FlecsLean.Cases
import FlecsLean.Threads
import FlecsLean.Search2
import FlecsLean.Pipeline
import FlecsLean.QueryProps
import FlecsLean.Workers
import FlecsLean.Activity
import FlecsLean.Validator
import FlecsLean.InhDF
import FlecsLean.PipeQ
import FlecsLean.WorkersCD
import FlecsLean.OrVM
import FlecsLean.OrVMFuel
import FlecsLean.Spawner
import FlecsLean.OnSetInh
import FlecsLean.Slices
import FlecsLean.WorkersSort

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
  | ["f17"] =>
    -- round 2's F17 programs, with and without ecs_init()'s ProgressTasks
    let a : Pipe.Prog := { sys := #[{ terms := [], immediate := true, effect := .disableSelf }, { terms := [] }] }
    let b : Pipe.Prog := { sys := #[{ terms := [], effect := .disableSelf }, { terms := [], immediate := true },
      { terms := [], effect := .disableSelf }] }
    for (nm, p) in [("Init(imm, disables itself), Update", a), ("A(disables itself), B(imm), C(disables itself)", b)] do
      for (w, q) in [("only these systems (ecs_mini + FlecsPipeline)", p),
                     ("ecs_init, systems in OnUpdate: ProgressTasks first", Pipe.withBuiltin p true),
                     ("ecs_init, systems in OnLoad: ProgressTasks last", Pipe.withBuiltin p false)] do
        IO.println s!"== {nm} | {w}: {Pipe.showProg q}"
        match Pipe.frameRuns q with
        | .ok rs => IO.println s!"  ran {rs}"
        | .error e => IO.println s!"  ASSERT {e}"
        for (pr, d) in Pipe.check q do IO.println s!"  PROPERTY {pr}: {d}"
  | ["exhaust-frame-builtin", limit, nsys, front] =>
    let g : TapeM Pipe.Prog := Pipe.genProgFrame nsys.toNat!
    let chk := fun (p : Pipe.Prog) => Pipe.check (Pipe.withBuiltin p (front == "1"))
    let (st, done) := gexhaust g chk limit.toNat!
    greport s!"pipe exhaust-frame with ProgressTasks front={front} nsys={nsys} limit={limit} complete={done}" st none
  | ["phase-exhaust", limit, nsys, builtin] =>
    let g : TapeM Pipe.Prog := Pipe.genProgPhase nsys.toNat!
    let chk := fun (p : Pipe.Prog) => Pipe.check (if builtin == "1" then Pipe.withBuiltin p true else p)
    let (st, done) := gexhaust g chk limit.toNat!
    greport s!"pipe phase-exhaust nsys={nsys} builtin={builtin} limit={limit} complete={done}" st (some sh)
  | ["phase-lib", mode, seed, n, nsys, builtin, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions Pipe.Prog := Pipe.genProgPhase nsys.toNat!
    let chk := fun (p : Pipe.Prog) => Pipe.check (if builtin == "1" then Pipe.withBuiltin p true else p)
    glib mode g chk prop n.toNat! seed.toNat! (fun sig p => gshrink Pipe.shrinkCands chk sig p)
  | ["phase-exhaust-noreorder", limit, nsys, builtin] =>
    -- the frames without a phase reorder: phase disabling only
    let g : TapeM Pipe.Prog := Pipe.genProgPhase nsys.toNat!
    let chk := fun (p : Pipe.Prog) =>
      if p.sys.any (fun s => match s.effect with | .reorder _ => true | _ => false) then []
      else Pipe.check (if builtin == "1" then Pipe.withBuiltin p true else p)
    let (st, done) := gexhaust g chk limit.toNat!
    greport s!"pipe phase-exhaust-noreorder nsys={nsys} builtin={builtin} limit={limit} complete={done}" st (some sh)
  | ["phase-cases"] =>
    for (nm, p) in Pipe.phaseCases do
      IO.println s!"== {nm}: {Pipe.showProg p}"
      match Pipe.frameRuns p with
      | .ok rs => IO.println s!"  ran {rs}"
      | .error e => IO.println s!"  ASSERT {e}"
      for (pr, d) in Pipe.check p do IO.println s!"  PROPERTY {pr}: {d}"
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
  | ["iter-exhaust", limit] =>
    let g : TapeM QProg := genIterProg
    let (st, done) := gexhaust g checkQ limit.toNat!
    greport s!"query iter-exhaust limit={limit} complete={done}" st (some sh)
  | ["iter-lib", mode, seed, n, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions QProg := genIterProg
    glib mode g checkQ prop n.toNat! seed.toNat! sh
  | ["iter5-explore", seed, n] =>
    let g : TapeM QProg := genIterProg5
    greport s!"query iter5-explore seed={seed} n={n}" (gexplore g checkQ seed.toNat! n.toNat!) (some sh)
  | ["iter5-exhaust", limit] =>
    let g : TapeM QProg := genIterProg5
    let (st, done) := gexhaust g checkQ limit.toNat!
    greport s!"query iter5-exhaust limit={limit} complete={done}" st (some sh)
  | ["iter6-desc-exhaust", limit] =>
    let g : TapeM QProg := genIterProg5 true
    let (st, done) := gexhaust g checkQ limit.toNat!
    greport s!"query iter6-desc-exhaust limit={limit} complete={done}" st (some sh)
  | ["iter6-desc-lib", mode, seed, n, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions QProg := genIterProg5 true
    glib mode g checkQ prop n.toNat! seed.toNat! sh
  | ["iter5-lib", mode, seed, n, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions QProg := genIterProg5
    glib mode g checkQ prop n.toNat! seed.toNat! sh
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

instance : Repr Activity.AProg := ⟨fun p _ => .text s!"kinds={p.kinds.toList} ops={p.ops.map (fun o => toString (repr o))}"⟩

def actMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : Activity.AProg) => gshrink Activity.shrinkA Activity.check sig p
  match args with
  | ["explore", seed, n, len] =>
    let g : TapeM Activity.AProg := Activity.genAProg len.toNat!
    greport s!"activity explore seed={seed} n={n} len={len}" (gexplore g Activity.check seed.toNat! n.toNat!) (some sh)
  | ["exhaust", limit, len] =>
    let g : TapeM Activity.AProg := Activity.genAProg len.toNat!
    let (st, done) := gexhaust g Activity.check limit.toNat!
    greport s!"activity exhaust len={len} limit={limit} complete={done}" st (some sh)
  | ["lib", mode, seed, n, len, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions Activity.AProg := Activity.genAProg len.toNat!
    glib mode g Activity.check prop n.toNat! seed.toNat! sh
  | _ => IO.println "usage: act explore SEED N LEN | exhaust LIMIT LEN | lib MODE SEED N LEN PROP"; return 1
  return 0

def valMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : Val.VProg) => gshrink Val.shrinkV Val.check sig p
  match args with
  | ["explore", seed, n, ncomp, len] =>
    let g : TapeM Val.VProg := Val.genVProg ncomp.toNat! len.toNat!
    greport s!"val explore seed={seed} n={n} ncomp={ncomp} len={len}" (gexplore g Val.check seed.toNat! n.toNat!) (some sh)
  | ["exhaust", limit, ncomp, len] =>
    let g : TapeM Val.VProg := Val.genVProg ncomp.toNat! len.toNat!
    let (st, done) := gexhaust g Val.check limit.toNat!
    greport s!"val exhaust ncomp={ncomp} len={len} limit={limit} complete={done}" st (some sh)
  | ["lib", mode, seed, n, ncomp, len, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions Val.VProg := Val.genVProg ncomp.toNat! len.toNat!
    glib mode g Val.check prop n.toNat! seed.toNat! sh
  | ["cases"] =>
    for (nm, p) in Val.cases do
      IO.println s!"== val case {nm}: {Val.showV p}"
      IO.println s!"  outcome: {repr (Val.createQuery p.storage p.terms p.kind p.hasEntity p.detect)}"
      for (pr, d) in Val.check p do IO.println s!"  PROPERTY {pr}: {d}"
  | _ => IO.println "usage: val explore SEED N NCOMP LEN | exhaust LIMIT NCOMP LEN | lib MODE SEED N NCOMP LEN PROP"; return 1
  return 0

def orMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : OrVM.Prog) => gshrink OrVM.shrink OrVM.check sig p
  match args with
  | ["explore", seed, n, ncomp, len, ntab] =>
    let g : TapeM OrVM.Prog := OrVM.genProg ncomp.toNat! len.toNat! ntab.toNat!
    greport s!"or explore seed={seed} n={n} ncomp={ncomp} len={len} ntab={ntab}" (gexplore g OrVM.check seed.toNat! n.toNat!) (some sh)
  | ["exhaust", limit, ncomp, len, ntab] =>
    let g : TapeM OrVM.Prog := OrVM.genProg ncomp.toNat! len.toNat! ntab.toNat!
    let (st, done) := gexhaust g OrVM.check limit.toNat!
    greport s!"or exhaust ncomp={ncomp} len={len} ntab={ntab} limit={limit} complete={done}" st (some sh)
    -- what the programs were: ran, skipped (F29, not partially cached), unmodelled
    let kinds := fun (p : OrVM.Prog) => [(OrVM.outcomeKind p, "")]
    let (st2, _) := gexhaust g kinds limit.toNat!
    IO.println "  outcomes:"
    for (k, c) in st2.byProperty do IO.println s!"    {k}: {c}"
  | ["agree", limit, ncomp, len, ntab] =>
    -- round 6: the fuel-indexed VM against the partial one
    let g : TapeM OrVM.Prog := OrVM.genProg ncomp.toNat! len.toNat! ntab.toNat!
    let (st, done) := gexhaust g OrVM.agree limit.toNat!
    greport s!"or agree ncomp={ncomp} len={len} ntab={ntab} limit={limit} complete={done}" st none
  | ["lib", mode, seed, n, ncomp, len, ntab, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions OrVM.Prog := OrVM.genProg ncomp.toNat! len.toNat! ntab.toNat!
    glib mode g OrVM.check prop n.toNat! seed.toNat! sh
  | ["cases"] =>
    for (nm, p) in OrVM.cases do
      IO.println s!"== or case {nm}"
      match OrVM.run p with
      | .ran ops got want oob marker =>
        IO.println s!"  ops: {OrVM.showOps ops}"
        IO.println s!"  yields tables {got}; the terms match tables {want}; marker reached {marker}"
        for o in oob do IO.println s!"  out of bounds: {o}"
      | .skipped w => IO.println s!"  skipped: {w}"
      | .unmodelled u => IO.println s!"  unmodelled: {u}"
      for (pr, d) in OrVM.check p do IO.println s!"  PROPERTY {pr}: {d}"
  | _ => IO.println "usage: or explore SEED N NCOMP LEN NTAB | exhaust LIMIT NCOMP LEN NTAB | lib MODE SEED N NCOMP LEN NTAB PROP | cases"; return 1
  return 0

def spMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : Spawn.Prog) => gshrink Spawn.shrink Spawn.check sig p
  match args with
  | ["exhaust", limit, ncomp, nchild, len] =>
    let g : TapeM Spawn.Prog := Spawn.genProg ncomp.toNat! nchild.toNat! len.toNat!
    let (st, done) := gexhaust g Spawn.check limit.toNat!
    greport s!"sp exhaust ncomp={ncomp} nchild={nchild} len={len} limit={limit} complete={done}" st (some sh)
  | ["lib", mode, seed, n, ncomp, nchild, len, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions Spawn.Prog := Spawn.genProg ncomp.toNat! nchild.toNat! len.toNat!
    glib mode g Spawn.check prop n.toNat! seed.toNat! sh
  | ["cases"] =>
    for (nm, p) in Spawn.cases do
      IO.println s!"== sp case {nm}"
      for (pr, d) in Spawn.check p do IO.println s!"  PROPERTY {pr}: {d}"
  | ["six-exhaust", limit, n] =>
    let g : TapeM Spawn6.Prog := Spawn6.genProg n.toNat!
    let sh6 := fun (sig : String) (p : Spawn6.Prog) => gshrink Spawn6.shrink Spawn6.check sig p
    let (st, done) := gexhaust g Spawn6.check limit.toNat!
    greport s!"sp six-exhaust nodes={n} limit={limit} complete={done}" st (some sh6)
  | ["six-lib", mode, seed, n, nodes, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions Spawn6.Prog := Spawn6.genProg nodes.toNat!
    glib mode g Spawn6.check prop n.toNat! seed.toNat! (fun sig p => gshrink Spawn6.shrink Spawn6.check sig p)
  | ["six-cases"] =>
    for (nm, p) in Spawn6.cases do
      IO.println s!"== sp6 case {nm}: {repr p}"
      IO.println s!"  instantiated nodes: {Spawn6.instantiated p}"
      for (pr, d) in Spawn6.check p do IO.println s!"  PROPERTY {pr}: {d}"
  | _ => IO.println "usage: sp exhaust LIMIT NCOMP NCHILD LEN | lib MODE SEED N NCOMP NCHILD LEN PROP | cases"; return 1
  return 0

def idfMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : IDF.Prog) => gshrink IDF.shrink IDF.check sig p
  match args with
  | ["explore", seed, n, ncomp, nents, len] =>
    let g : TapeM IDF.Prog := IDF.genProg ncomp.toNat! nents.toNat! len.toNat!
    greport s!"idf explore seed={seed} n={n} ncomp={ncomp} nents={nents} len={len}" (gexplore g IDF.check seed.toNat! n.toNat!) (some sh)
  | ["exhaust", limit, ncomp, nents, len] =>
    let g : TapeM IDF.Prog := IDF.genProg ncomp.toNat! nents.toNat! len.toNat!
    let (st, done) := gexhaust g IDF.check limit.toNat!
    greport s!"idf exhaust ncomp={ncomp} nents={nents} len={len} limit={limit} complete={done}" st (some sh)
  | ["lib", mode, seed, n, ncomp, nents, len, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions IDF.Prog := IDF.genProg ncomp.toNat! nents.toNat! len.toNat!
    glib mode g IDF.check prop n.toNat! seed.toNat! sh
  | ["auto-explore", seed, n, ncomp, nents, len] =>
    let g : TapeM IDF.Prog := IDF.genProgAuto ncomp.toNat! nents.toNat! len.toNat!
    greport s!"idf auto-explore seed={seed} n={n} ncomp={ncomp} nents={nents} len={len}" (gexplore g IDF.check seed.toNat! n.toNat!) (some sh)
  | ["auto-exhaust", limit, ncomp, nents, len] =>
    let g : TapeM IDF.Prog := IDF.genProgAuto ncomp.toNat! nents.toNat! len.toNat!
    let (st, done) := gexhaust g IDF.check limit.toNat!
    greport s!"idf auto-exhaust ncomp={ncomp} nents={nents} len={len} limit={limit} complete={done}" st (some sh)
  | ["auto-lib", mode, seed, n, ncomp, nents, len, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions IDF.Prog := IDF.genProgAuto ncomp.toNat! nents.toNat! len.toNat!
    glib mode g IDF.check prop n.toNat! seed.toNat! sh
  | ["cases"] =>
    for (nm, p) in IDF.cases do
      IO.println s!"== idf case {nm}"
      for (pr, d) in IDF.check p do IO.println s!"  PROPERTY {pr}: {d}"
  | _ => IO.println "usage: idf explore SEED N NCOMP NENTS LEN | exhaust LIMIT NCOMP NENTS LEN | lib MODE SEED N NCOMP NENTS LEN PROP"; return 1
  return 0

def pqMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : PipeQ.Prog) => gshrink PipeQ.shrink PipeQ.check sig p
  match args with
  | ["explore", seed, n, nsys, len] =>
    let g : TapeM PipeQ.Prog := PipeQ.genProg nsys.toNat! len.toNat!
    greport s!"pq explore seed={seed} n={n} nsys={nsys} len={len}" (gexplore g PipeQ.check seed.toNat! n.toNat!) (some sh)
  | ["exhaust", limit, nsys, len] =>
    let g : TapeM PipeQ.Prog := PipeQ.genProg nsys.toNat! len.toNat!
    let (st, done) := gexhaust g PipeQ.check limit.toNat!
    greport s!"pq exhaust nsys={nsys} len={len} limit={limit} complete={done}" st (some sh)
  | ["lib", mode, seed, n, nsys, len, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions PipeQ.Prog := PipeQ.genProg nsys.toNat! len.toNat!
    glib mode g PipeQ.check prop n.toNat! seed.toNat! sh
  | ["cases"] =>
    for (nm, p) in PipeQ.cases do
      IO.println s!"== pq case {nm}"
      for (pr, d) in PipeQ.check p do IO.println s!"  PROPERTY {pr}: {d}"
  | _ => IO.println "usage: pq explore SEED N NSYS LEN | exhaust LIMIT NSYS LEN | lib MODE SEED N NSYS LEN PROP"; return 1
  return 0

def wcdMain (args : List String) : IO UInt32 := do
  match args with
  | [mode, threads, tables, races, n, seed, filt] =>
    -- round 5: races "2" = no race reports, each table a new size class
    -- round 6: races "4" = size classes on pages of 2 classes, no race reports
    let cfg : WCD.Cfg := { threads := threads.toNat!, tables := tables.toNat!, races := races == "1",
                           sizeClasses := races == "2" || races == "3" || races == "4",
                           classesPerPage := if races == "4" then 2 else 0 }
    let cfg := if races == "3" then { cfg with races := true } else cfg
    let run := fun src =>
      let e := WCD.timeline cfg src
      match e.violation with
      | some (p, d) => if filt == "all" || ((p ++ " " ++ d).splitOn filt).length > 1 then e
                       else { e with violation := none }
      | none => e
    IO.println s!"== wcd {mode} threads={threads} tables={tables} races={races} filter={filt}"
    match (← findWith mode run n.toNat! seed.toNat!) with
    | none => IO.println "  no counterexample"
    | some c =>
      let c' := Determinismo.shrink run c
      IO.println s!"  counterexample after {c.runs} timelines"
      IO.println s!"  property: {c'.property}"
      IO.println s!"  detail: {c'.detail}"
      IO.println "  tape:"
      IO.println (Determinismo.tape c'.taken)
    return 0
  | _ => IO.println "usage: wcd explore|exhaust THREADS TABLES RACES N SEED FILTER"; return 1

def workersMain (args : List String) : IO UInt32 := do
  match args with
  | [mode, stages, ops, frames, spurious, n, seed, filt] =>
    let opsArr : Array Workers.POp := (ops.splitOn ",").toArray.map (fun o => { mt := o == "mt" })
    let cfg : Workers.Cfg := { stages := stages.toNat!, frames := frames.toNat!, spurious := spurious.toNat!, ops := opsArr }
    let run := fun src =>
      let e := Workers.timeline cfg src
      match e.violation with
      | some (p, d) => if filt == "all" || ((p ++ " " ++ d).splitOn filt).length > 1 then e
                       else { e with violation := none }
      | none => e
    IO.println s!"== workers {mode} stages={stages} ops={ops} frames={frames} spurious={spurious} filter={filt}"
    match (← findWith mode run n.toNat! seed.toNat!) with
    | none => IO.println "  no counterexample"
    | some c =>
      let c' := Determinismo.shrink run c
      IO.println s!"  counterexample after {c.runs} timelines"
      IO.println s!"  property: {c'.property}"
      IO.println s!"  detail: {c'.detail}"
      IO.println "  tape:"
      IO.println (Determinismo.tape c'.taken)
    return 0
  | _ => IO.println "usage: workers explore|exhaust STAGES OPS FRAMES SPURIOUS N SEED FILTER"; return 1

def osiMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : OSI.Prog) => gshrink OSI.shrink OSI.check sig p
  match args with
  | ["explore", seed, n, nents, len] =>
    let g : TapeM OSI.Prog := OSI.genProg nents.toNat! len.toNat!
    greport s!"osi explore seed={seed} n={n} nents={nents} len={len}" (gexplore g OSI.check seed.toNat! n.toNat!) (some sh)
  | ["exhaust", limit, nents, len] =>
    let g : TapeM OSI.Prog := OSI.genProg nents.toNat! len.toNat!
    let (st, done) := gexhaust g OSI.check limit.toNat!
    greport s!"osi exhaust nents={nents} len={len} limit={limit} complete={done}" st (some sh)
  | ["lib", mode, seed, n, nents, len, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions OSI.Prog := OSI.genProg nents.toNat! len.toNat!
    glib mode g OSI.check prop n.toNat! seed.toNat! sh
  | ["cases"] =>
    for (nm, p) in OSI.cases do
      IO.println s!"== osi case {nm}: {repr p}"
      IO.println s!"  events per call (entity, source): {OSI.trace p}"
      for (pr, d) in OSI.check p do IO.println s!"  PROPERTY {pr}: {d}"
  | _ => IO.println "usage: osi explore SEED N NENTS LEN | exhaust LIMIT NENTS LEN | lib MODE SEED N NENTS LEN PROP | cases"; return 1
  return 0

def slMain (args : List String) : IO UInt32 := do
  let sh := fun (sig : String) (p : Slices.Prog) => gshrink Slices.shrink Slices.check sig p
  match args with
  | ["explore", seed, n, ntags, ninit, ncalls] =>
    let g : TapeM Slices.Prog := Slices.genProg ntags.toNat! ninit.toNat! ncalls.toNat!
    greport s!"sl explore seed={seed} n={n} ntags={ntags} ninit={ninit} ncalls={ncalls}" (gexplore g Slices.check seed.toNat! n.toNat!) (some sh)
  | ["exhaust", limit, ntags, ninit, ncalls] =>
    let g : TapeM Slices.Prog := Slices.genProg ntags.toNat! ninit.toNat! ncalls.toNat!
    let (st, done) := gexhaust g Slices.check limit.toNat!
    greport s!"sl exhaust ntags={ntags} ninit={ninit} ncalls={ncalls} limit={limit} complete={done}" st (some sh)
  | ["lib", mode, seed, n, ntags, ninit, ncalls, prop] =>
    let g : EStateM Determinismo.Stop Determinismo.Decisions Slices.Prog := Slices.genProg ntags.toNat! ninit.toNat! ncalls.toNat!
    glib mode g Slices.check prop n.toNat! seed.toNat! sh
  | ["cases"] =>
    for (nm, p) in Slices.cases do
      IO.println s!"== sl case {nm}: {repr p}"
      let r := Slices.check p
      if r.isEmpty then IO.println "  no property broken"
      for (pr, d) in r do IO.println s!"  PROPERTY {pr}: {d}"
  | _ => IO.println "usage: sl explore SEED N NTAGS NINIT NCALLS | exhaust LIMIT NTAGS NINIT NCALLS | lib MODE SEED N NTAGS NINIT NCALLS PROP | cases"; return 1
  return 0

def wsortMain (args : List String) : IO UInt32 := do
  match args with
  | [mode, threads, rows, races, n, seed, filt] =>
    let cfg : WSort.Cfg := { threads := threads.toNat!, rows := rows.toNat!, races := races.toNat! }
    let run := fun src =>
      let e := WSort.timeline cfg src
      match e.violation with
      | some (p, d) => if filt == "all" || ((p ++ " " ++ d).splitOn filt).length > 1 then e
                       else { e with violation := none }
      | none => e
    IO.println s!"== wsort {mode} threads={threads} rows={rows} races={races} filter={filt}"
    match (← findWith mode run n.toNat! seed.toNat!) with
    | none => IO.println "  no counterexample"
    | some c =>
      let c' := Determinismo.shrink run c
      IO.println s!"  counterexample after {c.runs} timelines"
      IO.println s!"  property: {c'.property}"
      IO.println s!"  detail: {c'.detail}"
      IO.println "  tape:"
      IO.println (Determinismo.tape c'.taken)
    return 0
  | _ => IO.println "usage: wsort explore|exhaust THREADS ROWS RACES N SEED FILTER"; return 1

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
  | ["trace-case", name] =>
    for (nm, sc) in allCases do
      if nm != name then continue
      match W.initWorld sc false with
      | .error f => IO.println s!"init failed {f}"
      | .ok (w0, rs) =>
        let mut w := w0
        for op in sc.ops do
          match (W.runOp rs op).run w with
          | .error f => IO.println s!"{repr op}: FAIL {f}"; break
          | .ok ((), w') =>
            w := w'
            IO.println s!"{repr op}"
            for (id, c) in w.crs.toList do
              if isPair id && !isWildcard id && (pairFirst id == EcsIsA || pairFirst id == EcsChildOf) then
                IO.println s!"   cr ({pairFirst id}, {pairSecond id}) cur={c.reachCur} gen={c.reachGen} reach={repr (c.reach.map (fun e => (e.id, e.src, e.table)))}"
            for t in [0:w.tables.size] do
              let x := w.tables.getD t default
              if x.live && x.over.isSome then
                IO.println s!"   table {t} type={x.type} over={repr x.over} ents={x.ents.extract 0 x.count}"
            for e in w.slots do
              IO.println s!"   slot {e} rec={repr (w.ix.recOf e)}"
            IO.println s!"   state {repr (summarize w).toList} viol={w.viol}"
  | ["inh-explore", seed, n, ents, len, staged, props] =>
    let g : TapeM Scenario := genInhScenario ents.toNat! len.toNat! (staged == "1")
    let ps := if props == "all" then [] else props.splitOn ","
    report s!"inheritance explore seed={seed} n={n} ents={ents} len={len} staged={staged} props={props}" (explore g ps seed.toNat! n.toNat!) true
  | ["inh-exhaust", limit, ents, len, staged, props] =>
    let g : TapeM Scenario := genInhScenario ents.toNat! len.toNat! (staged == "1")
    let ps := if props == "all" then [] else props.splitOn ","
    let (st, done) := exhaust g ps limit.toNat!
    report s!"inheritance exhaust ents={ents} len={len} limit={limit} staged={staged} props={props} complete={done}" st true
  | ["range-inst", limit, ents, len] =>
    let g : TapeM Scenario := genRangeInst ents.toNat! len.toNat!
    let (st, done) := exhaust g [] limit.toNat!
    report s!"range+instantiate exhaust ents={ents} len={len} limit={limit} complete={done}" st true
  | ["inh-small", limit, len] =>
    let g : TapeM Scenario := genInhSmall len.toNat!
    let (st, done) := exhaust g [] limit.toNat!
    report s!"inheritance exhaust-small len={len} limit={limit} complete={done}" st true
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
      else if mode == "inh" then genInhScenario cfgOrEnts.toNat! len.toNat!
      else if mode == "inhw" then genInhScenario cfgOrEnts.toNat! len.toNat! false
      else if mode == "inhs" || mode == "inhsx" then genInhSmall len.toNat!
      else if mode == "rix" then genRangeInst cfgOrEnts.toNat! len.toNat!
      else if mode == "isa" then genIsAScenario cfgOrEnts.toNat! len.toNat!
      else if mode == "explore" then genScenario cfgOrEnts.toNat! len.toNat!
      else if mode == "ei" then genEIScenario len.toNat!
      else genSmallScenario cfgOrEnts.toNat! 1 2 len.toNat! true
    -- "xsmall": the small call menu, explored at random
    let mode := if mode == "xsmall" || mode == "obs" || mode == "isa" || mode == "inh" || mode == "inhw" || mode == "inhs" then "explore"
      else if mode == "inhsx" || mode == "rix" then "exhaust" else mode
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
  | "workers" :: rest => return (← workersMain rest)
  | "act" :: rest => return (← actMain rest)
  | "query" :: rest => return (← queryMain rest)
  | "val" :: rest => return (← valMain rest)
  | "idf" :: rest => return (← idfMain rest)
  | "pq" :: rest => return (← pqMain rest)
  | "wcd" :: rest => return (← wcdMain rest)
  | "or" :: rest => return (← orMain rest)
  | "sp" :: rest => return (← spMain rest)
  | "osi" :: rest => return (← osiMain rest)
  | "sl" :: rest => return (← slMain rest)
  | "wsort" :: rest => return (← wsortMain rest)
  | _ =>
    IO.println "usage: flecs-search explore SEED N ENTS LEN | exhaust LIMIT ENTS LEN | ei-explore SEED N LEN | ei-exhaust LIMIT LEN"
    return 1
  return 0

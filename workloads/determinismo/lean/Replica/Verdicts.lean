import Replica.Prelude
import Replica.Searching

/-!
# Property verdicts, replicated (platform 3939448)

Round 2: a property is its message and its kind (`Property.same`, events.zig:56-61, merged by it
in report.zig:519-528); a message cut to 192 bytes carries the whole message's hash
(events.zig:1483-1501, `identity` 50-54); a scenario's `sometimes` reached and never true waits
for the other scenarios (`unmet_here` 366-370, `failing_violations` 389-396, `sometimes_unmet`
400-407, main.zig:1106-1156 with `Catalog.made_true`, report.zig:140-145). The catalog stays
keyed by identity alone, its kind the first noted (report.zig:128-136). The hash here is the
whole message itself (Wyhash's collisions not modeled).

How assertions become a run's verdict, from the Zig:

- per timeline, `src/core/events.zig`: `on_assert` (1361), `declaration` (1372), `declare`
  (1377), `assertion_record` (1406), `property_get_or_put` (1457: one property per message, its
  first 192 bytes, `message_size_max`; a second kind for a message is an error, which ends the
  worker: main.zig:3659 `try vm.run_until_exit()`), `Property.passing` (47);
- across a scenario's timelines, `src/report.zig`: `Multiverse.merge` (491, by name only:
  `aggregate_find`, 481), `absorb` (508: workers' tables added), `Aggregate.unreached_here`
  (348), `Aggregate.failing` (356), `property_failing` (192), `failing_properties` (369),
  `catalog_reached` (713);
- across the scenarios explored, `src/main.zig:1097-1157`: a scenario with a failing property
  counts, then `Catalog.judge(every_scenario)` (report.zig:142); exit status 3 when any;
- serve's verdict of a run (one scenario), `src/store.zig:1145-1257` `properties_sql`: per
  (type, message) over the run's timelines: failing, unreached, or passing.

The documentation's semantics (Antithesis's, docs/ANTITHESIS.md: "Judged as Antithesis does"),
per property (a message with its kind) over every timeline of every scenario explored: an
`always` fails when false somewhere or never evaluated; `always_or_unreachable` when false
somewhere; `sometimes` when never true; `reachable` when never reached; `unreachable` when
reached. Declarations (`hit: false`) make a property known without evaluating it.
-/

namespace Replica.Verdicts

open Determinismo

inductive AKind where
  | always | always_or_unreachable | sometimes | reachable | unreachable
  deriving BEq, Repr, Inhabited, DecidableEq

def AKind.name : AKind → String
  | .always => "always" | .always_or_unreachable => "always_or_unreachable"
  | .sometimes => "sometimes" | .reachable => "reachable" | .unreachable => "unreachable"

/-- One assertion line a timeline emits (`{"assert": ...}`), or an event (no property). -/
inductive AEvent where
  | declare (kind : AKind) (message : String)
  | eval (kind : AKind) (message : String) (cond : Bool)
  | event (name : String)
  deriving BEq, Repr, Inhabited

structure Timeline where
  scenario : Nat
  events : List AEvent
  deriving Repr, Inhabited

/-- events.zig:21 `Property`. `full`: the whole message when it was cut (its hash's stand-in). -/
structure Property where
  kind : AKind
  name : String
  full : Option String := none
  hits : Nat := 0
  trues : Nat := 0
  deriving Repr, Inhabited

/-- events.zig:50-54 `identity`: the name, and the whole message's hash when cut. -/
def Property.identity (p : Property) : String :=
  match p.full with
  | some f => p.name ++ "#" ++ f
  | none => p.name

/-- events.zig:56-61 `same`: same kind, same hash, same name. -/
def Property.same (p q : Property) : Bool := p.kind == q.kind && p.full == q.full && p.name == q.name

/-- events.zig:47 `passing`: whether this timeline violates it. -/
def Property.passing (p : Property) : Bool :=
  match p.kind with
  | .always | .always_or_unreachable => p.trues == p.hits
  | .unreachable => p.hits == 0
  | .sometimes | .reachable => true

def messageSizeMax : Nat := 192

/-- events.zig:1457 `property_get_or_put` (its message cut to 192 bytes). -/
def getOrPut (props : Array Property) (kind : AKind) (message : String) : Except String (Array Property × Nat) :=
  let name := String.ofList (message.toList.take messageSizeMax)
  let full := if message.length > messageSizeMax then some message else none
  match props.findIdx? (fun p => p.name == name && p.full == full) with
  | some i =>
    if props[i]!.kind != kind then .error s!"the assertion \"{name}\" is both {props[i]!.kind.name} and {kind.name}"
    else .ok (props, i)
  | none => .ok (props.push { kind, name, full }, props.size)

/-- events.zig:1361 `on_assert` (and `emit`'s dispatch, events.zig:417): one line. An event
carries no property. -/
def step (props : Array Property) : AEvent → Except String (Array Property)
  | .declare k m => do
    let (ps, _) ← getOrPut props k m
    pure ps
  | .eval k m c => do
    let (ps, i) ← getOrPut props k m
    let p := ps[i]!
    pure (ps.set! i { p with hits := p.hits + 1, trues := p.trues + (if c then 1 else 0) })
  | .event _ => pure props

/-- A timeline's property table, or the error that ends the worker (`AssertionKindsDiffer`). -/
def timelineProps (t : Timeline) : Except String (Array Property) := t.events.foldlM step #[]

/-- report.zig:323 `Aggregate`. -/
structure Aggregate where
  property : Property
  branchesHit : Nat := 0
  branchesTrue : Nat := 0
  branchesFailing : Nat := 0
  deriving Repr, Inhabited

/-- report.zig:192 `property_failing`. -/
def propertyFailing (kind : AKind) (hit tru failing : Nat) : Bool :=
  match kind with
  | .always => failing > 0 || hit == 0
  | .always_or_unreachable | .unreachable => failing > 0
  | .sometimes => tru == 0
  | .reachable => hit == 0

def mustHit (k : AKind) : Bool := k == .always || k == .sometimes || k == .reachable

/-- report.zig:348 `unreached_here`. -/
def Aggregate.unreachedHere (a : Aggregate) : Bool := mustHit a.property.kind && a.branchesHit == 0

/-- report.zig:372 `failing`. -/
def Aggregate.failing (a : Aggregate) : Bool :=
  if a.unreachedHere then false
  else propertyFailing a.property.kind a.branchesHit a.branchesTrue a.branchesFailing

/-- report.zig:366-370 `unmet_here` (no run-level property modeled: run_failing null). -/
def Aggregate.unmetHere (a : Aggregate) : Bool :=
  a.property.kind == .sometimes && a.branchesHit > 0 && a.branchesTrue == 0

/-- report.zig:389-396 `failing_violations`. -/
def failingViolations (aggs : Array Aggregate) : Nat :=
  (aggs.filter fun a => a.failing && !a.unmetHere).size

/-- report.zig:400-407 `sometimes_unmet`: identities. -/
def sometimesUnmet (aggs : Array Aggregate) : List String :=
  (aggs.filter (·.unmetHere)).toList.map (·.property.identity)

/-- report.zig:519-528 `merge` (through `aggregate_find`: by `same`, kind included). -/
def merge (aggs : Array Aggregate) (p : Property) : Array Aggregate :=
  let (aggs, i) := match aggs.findIdx? (·.property.same p) with
    | some i => (aggs, i)
    | none => (aggs.push { property := p }, aggs.size)
  let a := aggs[i]!
  aggs.set! i { a with
    branchesHit := a.branchesHit + (if p.hits > 0 then 1 else 0)
    branchesTrue := a.branchesTrue + (if p.trues > 0 then 1 else 0)
    branchesFailing := a.branchesFailing + (if p.passing then 0 else 1) }

/-- The explorer's verdict on one scenario's timelines, in the order they ended: its aggregates
(none when a timeline's table erred: the worker ends). -/
def multiverse (ts : List Timeline) : Except String (Array Aggregate) := do
  let mut aggs : Array Aggregate := #[]
  for t in ts do
    let props ← timelineProps t
    for p in props do aggs := merge aggs p
  return aggs

/-- report.zig:125 `Catalog`: by message (first kind), reached anywhere. -/
def catalogNote (cat : List (String × AKind × Bool)) (kind : AKind) (name : String) (reached : Bool) :
    List (String × AKind × Bool) :=
  match cat.find? (·.1 == name) with
  | some _ => cat.map fun (n, k, r) => if n == name then (n, k, r || reached) else (n, k, r)
  | none => cat ++ [(name, kind, reached)]

/-- report.zig:752-765 `catalog_reached` (by identity). -/
def catalogReached (cat : List (String × AKind × Bool)) (aggs : Array Aggregate) : List (String × AKind × Bool) :=
  aggs.foldl (fun cat a =>
    let reached := a.branchesHit > 0 && !propertyFailing a.property.kind a.branchesHit a.branchesTrue 0
    catalogNote cat a.property.kind a.property.identity reached) cat

/-- report.zig:140-145 `made_true`: the entry by identity, whatever its kind. -/
def catalogMadeTrue (cat : List (String × AKind × Bool)) (identity : String) : Bool :=
  match cat.find? (·.1 == identity) with
  | some (_, _, r) => r
  | none => false

/-- report.zig:142 `judge`: how many unreached must-hit assertions fail. -/
def catalogJudge (cat : List (String × AKind × Bool)) (everyScenario : Bool) : Nat :=
  if !everyScenario then 0 else (cat.filter fun (_, k, r) => !r && mustHit k).length

/-- main.zig:1097-1157: the exploration's exit status (3: some property failed), or the error
that ended it. `scenarios`: the scenarios explored, each its timelines in the order they ended;
`all`: how many scenarios the program has. -/
def explorerExit (scenarios : List (List Timeline)) (all : Nat) : Except String Nat := do
  let mut failingScenarios := 0
  let mut cat : List (String × AKind × Bool) := []
  let mut unmet : List (List String) := []
  for ts in scenarios do
    let aggs ← multiverse ts
    cat := catalogReached cat aggs
    -- main.zig:1143-1147 (3939448)
    if failingViolations aggs > 0 then failingScenarios := failingScenarios + 1
    else unmet := unmet ++ [sometimesUnmet aggs]
  -- main.zig:1150-1155
  for messages in unmet do
    if messages.any (!catalogMadeTrue cat ·) then failingScenarios := failingScenarios + 1
  if catalogJudge cat (scenarios.length == all) > 0 then failingScenarios := failingScenarios + 1
  return if failingScenarios > 0 then 3 else 0

/-- serve's `properties_sql` (store.zig:1145): a run's properties by (type, message), each
failing, unreached or passing. A run is one scenario's timelines. -/
def serveStatuses (ts : List Timeline) : List (AKind × String × String) := Id.run do
  let keys := (ts.flatMap fun t => t.events.filterMap fun
    | .declare k m => some (k, m) | .eval k m _ => some (k, m) | .event _ => none).eraseDups
  let mut out := []
  for (k, m) in keys do
    -- Per timeline (timeline_properties): hits = evaluations, trues, failed when the type fails.
    let per := ts.map fun t =>
      let evals := t.events.filterMap fun
        | .eval k' m' c => if k' == k && m' == m then some c else none
        | _ => none
      let failed := match k with
        | .always | .always_or_unreachable => evals.any (!·)
        | .unreachable => !evals.isEmpty
        | _ => false
      (evals.length, (evals.filter id).length, failed)
    let hit := (per.filter fun (h, _, _) => h > 0).length
    let tru := (per.filter fun (_, tr, _) => tr > 0).length
    let failing := (per.filter fun (_, _, f) => f).length
    let status := if failing > 0 then "failing"
      else if mustHit k && hit == 0 then "unreached"
      else if k == .sometimes && tru == 0 then "failing" else "passing"
    out := out ++ [(k, m, status)]
  return out

/-- The documentation's semantics over every timeline explored: the properties that fail. -/
def specFailing (ts : List Timeline) (allScenariosExplored : Bool) : List (AKind × String) := Id.run do
  let keys := (ts.flatMap fun t => t.events.filterMap fun
    | .declare k m => some (k, m) | .eval k m _ => some (k, m) | .event _ => none).eraseDups
  let mut out := []
  for (k, m) in keys do
    let evals := ts.flatMap fun t => t.events.filterMap fun
      | .eval k' m' c => if k' == k && m' == m then some c else none
      | _ => none
    let fails := match k with
      | .always => evals.any (!·) || (evals.isEmpty && allScenariosExplored)
      | .always_or_unreachable => evals.any (!·)
      | .sometimes => !evals.any id && (allScenariosExplored || !evals.isEmpty)
      | .reachable => evals.isEmpty && allScenariosExplored
      | .unreachable => !evals.isEmpty
    if fails then out := out ++ [(k, m)]
  return out

/-! ## Worlds: timelines drawn from a menu of assertion lines -/

def longA : String := String.ofList (List.replicate 192 'x') ++ "a"
def longB : String := String.ofList (List.replicate 192 'x') ++ "b"

structure VWorld where
  label : String
  menu : List AEvent
  /-- Scenarios explored, and timelines per scenario. -/
  scenarios : Nat := 1
  perScenario : Nat := 2
  /-- Lines per timeline. -/
  lines : Nat := 1

/-- The timelines a world's decisions draw, and the order each scenario's ended. -/
structure Drawn where
  timelines : List (List Timeline)
  deriving Inhabited

structure VS where
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic VS where
  decisions s := s.decisions
  setDecisions _ d := { decisions := d }

def drawWorld (wd : VWorld) : EStateM Stop VS Drawn := do
  let mut scenarios := []
  for s in [0:wd.scenarios] do
    let mut ts := []
    for _ in [0:wd.perScenario] do
      let mut evs := []
      for _ in [0:wd.lines] do
        evs := evs ++ [wd.menu[(← below "world.assertion" wd.menu.length)]!]
      ts := ts ++ [{ scenario := s, events := evs : Timeline }]
    scenarios := scenarios ++ [ts]
  return { timelines := scenarios }

/-- The order the timelines ended in: a decision (workers and the tree end them in any order). -/
def drawOrder (ts : List Timeline) : EStateM Stop VS (List Timeline) := do
  let mut rest := ts.toArray
  let mut out := []
  while rest.size > 0 do
    let i ← below "world.order" rest.size
    out := out ++ [rest[i]!]
    rest := rest.eraseIdx! i
  return out

structure VProp where
  name : String
  source : String
  /-- The drawn timelines in their canonical order, and in the order they ended. -/
  check : Drawn → Drawn → Option String

def showExit : Except String Nat → String
  | .ok n => s!"exit {n}"
  | .error e => s!"error: {e}"

/-- An exit as the order-independence property compares it: an error (the worker ends, whichever
timeline's mistake it names) or a status. -/
def exitClass : Except String Nat → String
  | .ok n => s!"exit {n}"
  | .error _ => "an error"

def orderIndependent : VProp :=
  { name := "the exploration's verdict does not depend on the order its timelines end"
    source := "README_AI.md: \"Branches run on every CPU (--jobs, same timelines as one worker)\"; report.zig:506: \"the summary does not depend on which worker finished first\"; ARCHITECTURE.md M9: \"parallel = sequential\""
    check := fun canon ended =>
      let a := explorerExit canon.timelines canon.timelines.length
      let b := explorerExit ended.timelines ended.timelines.length
      if exitClass a == exitClass b then none
      else some s!"in one order {showExit a}, in another {showExit b}" }

def explorerAsDocumented : VProp :=
  { name := "the exploration fails exactly when a property fails as documented (all scenarios explored together)"
    source := "docs/ANTITHESIS.md (Assertions: \"Judged as Antithesis does\"; Assertion catalog: \"A test program's catalog spans its scenarios and is judged over all of them\"); SKILL.md (determinismo-workload): \"one never true fails the run\", \"An always never evaluated fails too\""
    check := fun _ ended =>
      match explorerExit ended.timelines ended.timelines.length with
      | .error _ => none -- said plainly: the worker ends
      | .ok code =>
        let spec := specFailing ended.timelines.flatten true
        if (code == 3) == !spec.isEmpty then none
        else some s!"explorer exit {code}; documented: {if spec.isEmpty then "passes" else s!"fails {spec.map fun (k, m) => (k.name, m.take 12)}"}; timelines {reprStr (ended.timelines.map (·.map (·.events)))}" }

def serveAsDocumented : VProp :=
  { name := "serve's run (one scenario) shows a failing property exactly when one fails as documented"
    source := "README_AI.md: \"curl localhost:7878/runs/1/properties # every property's verdict so far\"; store.zig:1112"
    check := fun _ ended => Id.run do
      for ts in ended.timelines do
        let serve := serveStatuses ts
        let spec := specFailing ts true
        -- "unreached" carries an error badge in the UI (index.html:1443): counted as failing.
        let serveFails := serve.any fun (_, _, st) => st == "failing" || st == "unreached"
        if serveFails != !spec.isEmpty then
          return some s!"serve {serve.map fun (k, m, st) => (k.name, m.take 12, st)}; documented fails {spec.map fun (k, m) => (k.name, m.take 12)}"
      return none }

def explorerMatchesServe : VProp :=
  { name := "the explorer's verdict of a one-scenario run and serve's agree"
    source := "store.zig:1112 (\"as Antithesis judges it (report.property_failing)\")"
    check := fun _ ended =>
      if ended.timelines.length != 1 then none else
      match explorerExit ended.timelines 1 with
      | .error _ => none
      | .ok code =>
        let serveFails := (serveStatuses ended.timelines[0]!).any fun (_, _, st) => st == "failing" || st == "unreached"
        if (code == 3) == serveFails then none
        else some s!"explorer exit {code}, serve {(serveStatuses ended.timelines[0]!).map fun (k, m, st) => (k.name, m.take 12, st)}" }

def eventsNoProperties : VProp :=
  { name := "events are not properties"
    source := "SKILL.md (determinismo-workload): \"is an `sdk.event`, searchable and no property\""
    check := fun _ ended =>
      let withEvents := explorerExit ended.timelines ended.timelines.length
      let without := explorerExit (ended.timelines.map (·.map fun t =>
        { t with events := t.events.filter fun | .event _ => false | _ => true })) ended.timelines.length
      if showExit withEvents == showExit without then none
      else some "an event changed the verdict" }

/-- serve.zig:5904-5918 `recorded_status`: a run's status from its record's last summary (a
summary per scenario; one scenario here): 3 when a summary line says `"failing":true` (each
aggregate's `failing()`, report.zig:830) or a timeline failed (`failing_branches`), else 0. What
an adopted run ends with (serve.zig:5983 in `runs_reap`, and 5821 in `runs_adopt`): the
explorer's own `exit` file (main.zig:1166-1175) is not read there. -/
def recordedStatus (ts : List Timeline) : Except String Nat := do
  let aggs ← multiverse ts
  let failingBranches := aggs.any (·.branchesFailing > 0)
  return if aggs.any (·.failing) || failingBranches then 3 else 0

def serveAdoptedAgrees : VProp :=
  { name := "a run's state is the same whether serve reaped its explorer or adopted it across a restart"
    source := "docs/AGENTS.md: \"A restarted serve adopts the runs still going\"; main.zig:1166-1170: \"How it ends, in its run's directory: serve learned it only from runs it reaped itself, and read the others' (... every run adopted across a restart) from their timelines' failing always properties alone\" (the exit file written for them); serve.zig:5912 \"A failing property fails the run, as explore exits\""
    check := fun _ ended =>
      if ended.timelines.length != 1 then none else
      match explorerExit ended.timelines 1, recordedStatus ended.timelines[0]! with
      | .ok reaped, .ok adopted =>
        if reaped == adopted then none
        else some s!"reaped: status {reaped} ({if reaped == 3 then "failed" else "passed"}); adopted: status {adopted} ({if adopted == 3 then "failed" else "passed"})"
      | _, _ => none }

def allVProps : List VProp :=
  [orderIndependent, explorerAsDocumented, serveAsDocumented, explorerMatchesServe, eventsNoProperties,
   serveAdoptedAgrees]

def judgeV (p : VProp) (wd : VWorld) (source : Source) : Ended :=
  match (do
      let d ← drawWorld wd
      let ordered ← d.timelines.mapM drawOrder
      pure (d, { timelines := ordered : Drawn })).run { decisions := { source } } with
  | .ok (canon, ended) s => { taken := s.decisions.taken, violation := (p.check canon ended).map fun d => (p.name, d) }
  | .error _ s => { taken := s.decisions.taken, violation := none }

def vstory (wd : VWorld) (source : Source) : List String :=
  match (do
      let d ← drawWorld wd
      let ordered ← d.timelines.mapM drawOrder
      pure (d, { timelines := ordered : Drawn })).run { decisions := { source } } with
  | .ok (_, ended) _ =>
    (ended.timelines.zipIdx.flatMap fun (ts, s) =>
      ts.zipIdx.map fun (t, i) => s!"scenario {s}, timeline {i} (in the order they ended): {reprStr (t.events.map fun
        | .declare k m => s!"declare {k.name} {m.take 20}"
        | .eval k m c => s!"{k.name}({c}) {m.take 20}"
        | .event n => s!"event {n}")}") ++
    [s!"explorer: {showExit (explorerExit ended.timelines ended.timelines.length)}",
     s!"serve: {ended.timelines.map fun ts => (serveStatuses ts).map fun (k, m, st) => (k.name, m.take 20, st)}",
     s!"documented: fails {(specFailing ended.timelines.flatten true).map fun (k, m) => (k.name, m.take 20)}"]
  | .error _ _ => ["(none)"]

def menuOne (m : String) : List AEvent :=
  [.eval .always m true, .eval .always m false, .eval .sometimes m true, .eval .sometimes m false,
   .eval .always_or_unreachable m false, .eval .reachable m true, .eval .unreachable m false,
   .declare .always m, .declare .sometimes m, .declare .reachable m, .event m]

def vworlds : List VWorld :=
  [ { label := "one scenario, two timelines, one line each, one message of one kind at a time (always)"
      menu := [.eval .always "m" true, .eval .always "m" false, .declare .always "m", .event "m"] },
    { label := "one scenario, two timelines, one line each, one message of one kind at a time (sometimes)"
      menu := [.eval .sometimes "m" true, .eval .sometimes "m" false, .declare .sometimes "m", .event "m"] },
    { label := "one scenario, two timelines, two lines each, every kind of one message"
      menu := menuOne "m", lines := 2 },
    { label := "two scenarios, two timelines each, a sometimes alone"
      menu := [.eval .sometimes "m" true, .eval .sometimes "m" false, .declare .sometimes "m"],
      scenarios := 2, perScenario := 2 },
    { label := "two scenarios, one timeline each, an always alone"
      menu := [.eval .always "m" true, .eval .always "m" false, .declare .always "m"],
      scenarios := 2, perScenario := 1 },
    { label := "one scenario, two timelines, two always messages sharing their first 192 bytes"
      menu := [.eval .always longA true, .eval .always longB false, .eval .always longB true, .declare .always longB],
      lines := 2 },
    -- Round 2's worlds.
    { label := "one scenario, two timelines, one line each: a sometimes never true, or the message under another kind"
      menu := [.eval .sometimes "m" false, .eval .always "m" true, .eval .always_or_unreachable "m" true,
               .eval .reachable "m" true] },
    { label := "one scenario, two timelines, one declaration each, of three kinds"
      menu := [.declare .always_or_unreachable "m", .declare .reachable "m", .declare .sometimes "m"] },
    { label := "two scenarios, one timeline each: a sometimes never true, or the message under another kind"
      menu := [.eval .sometimes "m" false, .eval .sometimes "m" true, .eval .reachable "m" true],
      scenarios := 2, perScenario := 1 },
    { label := "one scenario, one timeline, two lines: declared must-hit assertions, reached or not"
      menu := [.declare .reachable "m", .declare .always "m", .eval .reachable "n" true, .eval .always "n" true],
      perScenario := 1, lines := 2 } ]

/-- Every property over every world: each world's first counterexample (each world is one kind of
mistake the search may find). -/
def searchAll (exhaustRuns : Nat) : IO (List Found) := do
  let mut found := []
  for p in allVProps do
    say s!"== verdict property: {p.name}"
    say s!"   source: {p.source}"
    for wd in vworlds do
      if let some f ← exhaustSaid s!"{p.name} / {wd.label}" (judgeV p wd) exhaustRuns then
        printFound f (vstory wd)
        found := found ++ [f]
  return found

end Replica.Verdicts

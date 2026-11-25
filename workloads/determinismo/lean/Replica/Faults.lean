import Replica.Prelude
import Replica.Searching

/-!
# det-faults' rules, replicated (guest/runtime/faults.zig, platform 3939448)

Round 2: `links_collect` skips an excluded peer (faults.zig:1478-1490) and `outage_start` counts
the nodes recovering outside the outage (faults.zig:3080-3111, `outage_down_already` 2122-2132).

What decides when and to whom faults happen, function by function: the list of faults a system
allows (`faults_collect`, fault exclusions), the swarm over kinds (`swarm_select`), the next
fault (`fault_choose`, `fault_weighted`, `sdk.fault_aim`), the node layers and their overlap
(`node_admits`), the cap on nodes down (`node_start`, `outage_start`, `nodes_down`), the
recovery windows (`node_end`), quiet periods (`quiet_request`, the main loop's check), injected
faults (`inject`), the pacing's active and quiet stretches, and the stop's heal.

Not modeled: what a fault does to a node (the kernel's side), the quorum cap (`quorum_kept`:
always true here, as with no `quorum`), aftershocks and crash points (both go through
`node_start` and are refused in quiet periods), the regime's gaps and durations (one named
decision each, over a small menu), thread pauses, pods, disks, custom faults. Time in ms.
-/

namespace Replica.Faults

open Determinismo

/-- faults.zig:99 `Kind`, the kinds modeled, in the Zig's enum order (an EnumSet iterates so). -/
inductive FKind where
  | pause | isolate | partition | degrade | restart | crash | outage | durable_crash | sync_stall
  | wipe | stop | throttle | partition_groups | clog | swizzle | restore | clock_skip
  deriving BEq, Repr, Inhabited, DecidableEq

def FKind.all : List FKind :=
  [.pause, .isolate, .partition, .degrade, .restart, .crash, .outage, .durable_crash, .sync_stall,
   .wipe, .stop, .throttle, .partition_groups, .clog, .swizzle, .restore, .clock_skip]

def FKind.name : FKind → String
  | .pause => "pause" | .isolate => "isolate" | .partition => "partition" | .degrade => "degrade"
  | .restart => "restart" | .crash => "crash" | .outage => "outage" | .durable_crash => "durable_crash"
  | .sync_stall => "sync_stall" | .wipe => "wipe" | .stop => "stop" | .throttle => "throttle"
  | .partition_groups => "partition_groups" | .clog => "clog" | .swizzle => "swizzle"
  | .restore => "restore" | .clock_skip => "clock_skip"

/-- A node's allowed faults (schema.zig `Faults`, the fields modeled; defaults the Zig's). -/
structure NodeSpec where
  name : String
  pause : Bool := true
  isolate : Bool := true
  partition : Bool := true
  degrade : Bool := true
  restart : Bool := false
  crash : Bool := false
  wipe : Bool := false
  stop : Bool := false
  throttle : Bool := true
  syncStall : Bool := true
  outage : Bool := true
  runnerLinks : Bool := true
  deriving Repr, Inhabited

/-- faults.zig:199 `Fault`. Endpoints: the runner 0, node i at i + 1. -/
structure Fault where
  kind : FKind
  node : String := ""
  peer : String := ""
  endpoints : List Bool := []
  power : Bool := true
  deriving Repr, Inhabited, BEq

/-- What the scenario and the run set (schema.Scenario's fields, explore's options). -/
structure Setup where
  nodes : List NodeSpec
  /-- Names the exclusion pattern matches (regex.zig not modeled: its matches given). -/
  excluded : List String := []
  clockSkip : Bool := false
  nodesDownMax : Nat := 0
  /-- Scenario.quorum_recovery_ms: how long a node back from a fault still counts as down. -/
  recoveryMs : Nat := 15000
  activeMsMax : Nat := 0
  quietMsMax : Nat := 0
  swarmOff : Bool := false
  deriving Repr, Inhabited

def excluded (s : Setup) (name : String) : Bool := s.excluded.contains name

/-- faults.zig:1502 `faults_add`. -/
def links_add (node : NodeSpec) (peer : String) (peerPartition peerDegrade : Bool) : List Fault :=
  (if node.partition && peerPartition then [{ kind := .partition, node := node.name, peer }] else []) ++
  (if node.degrade && peerDegrade then
    [{ kind := .degrade, node := node.name, peer }, { kind := .degrade, node := peer, peer := node.name }]
  else [])

/-- faults.zig:1475 `links_collect`: node `index`'s links with the runner and every later node. -/
def links_collect (s : Setup) (nodes : List NodeSpec) (index : Nat) : List Fault :=
  let node := nodes[index]!
  (if node.runnerLinks then links_add node "runner" true true else []) ++
  -- faults.zig:1484-1489 (3939448): an excluded peer is in no link fault.
  ((nodes.drop (index + 1)).flatMap fun peer =>
    if excluded s peer.name then [] else links_add node peer.name peer.partition peer.degrade)

/-- faults.zig:1373 `faults_collect` (the kinds modeled). -/
def faults_collect (s : Setup) : List Fault := Id.run do
  let nodes := s.nodes
  let mut faults : List Fault := []
  for index in [0:nodes.length] do
    let node := nodes[index]!
    if excluded s node.name then continue -- faults.zig:1381
    if node.pause then faults := faults ++ [{ kind := .pause, node := node.name }]
    if node.isolate then faults := faults ++ [{ kind := .isolate, node := node.name }]
    if node.restart then faults := faults ++ [{ kind := .restart, node := node.name }]
    if node.crash then
      faults := faults ++ [{ kind := .crash, node := node.name }, { kind := .durable_crash, node := node.name }]
    if node.wipe then faults := faults ++ [{ kind := .wipe, node := node.name }]
    if node.stop then faults := faults ++ [{ kind := .stop, node := node.name }]
    if node.throttle then faults := faults ++ [{ kind := .throttle, node := node.name }]
    if node.syncStall then faults := faults ++ [{ kind := .sync_stall, node := node.name }]
    faults := faults ++ links_collect s nodes index
  let kept (n : NodeSpec) := !excluded s n.name
  let endpoints := true :: nodes.map fun n => n.partition && kept n
  let partitionable := (endpoints.filter id).length
  for n in nodes do
    if n.isolate && kept n then faults := faults ++ [{ kind := .clog, node := n.name }]
  let isolatable := false :: nodes.map fun n => n.isolate && kept n
  if partitionable ≥ 3 then faults := faults ++ [{ kind := .partition_groups, endpoints }]
  if (isolatable.filter id).length ≥ 2 then faults := faults ++ [{ kind := .swizzle, endpoints := isolatable }]
  let crashable := false :: nodes.map fun n => n.crash && n.outage && kept n
  let restartable := false :: nodes.map fun n => n.restart && n.outage && kept n
  if (crashable.filter id).length ≥ 2 then faults := faults ++ [{ kind := .outage, endpoints := crashable }]
  if (restartable.filter id).length ≥ 2 then
    faults := faults ++ [{ kind := .outage, endpoints := restartable, power := false }]
  if s.clockSkip then faults := faults ++ [{ kind := .clock_skip }]
  let networked := faults.any fun f =>
    f.kind == .isolate || f.kind == .partition || f.kind == .degrade || f.kind == .partition_groups ||
    f.kind == .clog || f.kind == .swizzle
  if networked then faults := faults ++ [{ kind := .restore }]
  return faults

/-- A fault's name as strategies read it (faults.zig:700 `fault_names`). -/
def Fault.label (f : Fault) : String :=
  let base := f.kind.name ++ (if f.kind == .outage && !f.power then " kill" else "")
  [f.node, f.peer].foldl (fun t part => if part.isEmpty then t else t ++ " " ++ part) base

/-- The endpoints' names (runner first). -/
def endpointNames (s : Setup) : List String := "runner" :: s.nodes.map (·.name)

/-- The nodes a fault involves by name: its node, its peer, the endpoints it may take. -/
def Fault.involves (s : Setup) (f : Fault) : List String :=
  let named := [f.node, f.peer].filter (!·.isEmpty)
  let fromEndpoints := ((endpointNames s).zip (f.endpoints ++ List.replicate 64 false)).filterMap
    fun (n, b) => if b && n != "runner" then some n else none
  named ++ fromEndpoints

def layerOf (k : FKind) : Nat := if k == .throttle || k == .sync_stall then 1 else 0

/-- faults.zig:2114 `takes_down`. -/
def takesDown (k : FKind) : Bool :=
  k == .restart || k == .crash || k == .stop || k == .wipe || k == .durable_crash || k == .outage

def isNodeFault (k : FKind) : Bool :=
  k == .pause || k == .restart || k == .crash || k == .durable_crash || k == .sync_stall ||
  k == .wipe || k == .stop || k == .throttle

def isNetworkFault (k : FKind) : Bool :=
  k == .isolate || k == .partition || k == .degrade || k == .partition_groups || k == .clog || k == .swizzle

/-- A fault applied (faults.zig:718 `Applied`, what is modeled of it). -/
structure Applied where
  kind : FKind
  node : String := ""
  peer : String := ""
  nodes : List String := []
  duration : Nat := 0
  injected : Bool := false
  deriving Repr, Inhabited

structure Slot where
  kind : FKind
  endT : Nat
  deriving Repr, Inhabited

/-- What the world sends the injector through its FIFO (faults.zig:4372 `requests_read`). -/
inductive Request where
  | quiet (ms : Nat)
  | inject (a : Applied)
  | aim (node : String)
  deriving Repr, Inhabited

inductive FEv where
  | fault (a : Applied) (t : Nat)
  | skipped (kind : FKind) (node : String) (why : String) (t : Nat)
  | ended (kind : FKind) (node : String) (t : Nat)
  | quiet (untilT : Nat) (t : Nat)
  | stopped (t : Nat)
  deriving Repr, Inhabited

structure S where
  decisions : Decisions := {}
  setup : Setup := { nodes := [] }
  now : Nat := 0
  /-- nodes_faulted: each node's process (0) and condition (1) slots. -/
  slots : Array (Array (Option Slot)) := #[]
  downRecoveringUntil : Array Nat := #[]
  network : List (Applied × Nat) := []
  quietUntil : Nat := 0
  quietPacing : Bool := false
  pacingQuietUntil : Nat := 0
  aim : String := ""
  overlapEighths : Nat := 0
  kindWeights : List (FKind × Nat) := []
  kindsWeighted : Bool := false
  stopping : Bool := false
  log : Array FEv := #[]
  /-- After each fault began: the nodes down by the literal rule and by the recovery rule. -/
  peaks : Array (Nat × Nat × Nat) := #[]
  deriving Inhabited

instance : Chaotic S where
  decisions s := s.decisions
  setDecisions s d := { s with decisions := d }

abbrev FM := EStateM Stop S

def femit (e : FEv) : FM Unit := modify fun s => { s with log := s.log.push e }

def nodeIndex (s : S) (name : String) : Option Nat := s.setup.nodes.findIdx? (·.name == name)

def slotOf (s : S) (i layer : Nat) : Option Slot := (s.slots[i]!)[layer]!

def setSlot (i layer : Nat) (v : Option Slot) : FM Unit :=
  modify fun s => { s with slots := s.slots.set! i ((s.slots[i]!).set! layer v) }

/-- Nodes down now: by the literal rule (a takes_down fault under way), and with the recovery
windows node_start counts too (faults.zig:2090). -/
def downCounts (s : S) : Nat × Nat := Id.run do
  let mut literal := 0
  let mut withRecovery := 0
  for i in [0:s.setup.nodes.length] do
    let active := match slotOf s i 0 with | some sl => takesDown sl.kind | none => false
    literal := literal + (if active then 1 else 0)
    withRecovery := withRecovery + (if active || s.downRecoveringUntil[i]! > s.now then 1 else 0)
  return (literal, withRecovery)

def notePeak : FM Unit := do
  let s ← get
  let (l, r) := downCounts s
  modify fun s => { s with peaks := s.peaks.push (s.now, l, r) }

/-- faults.zig:1620 `node_busy`. -/
def nodeBusy (s : S) (i : Nat) : Bool := (slotOf s i 0).isSome || (slotOf s i 1).isSome

/-- faults.zig:1627 `node_admits`. -/
def nodeAdmits (i layer : Nat) : FM Bool := do
  let s ← get
  if (slotOf s i layer).isSome then return false
  if !nodeBusy s i then return true
  return (← below "fault.overlap" 8) < s.overlapEighths

/-- faults.zig:2090 `nodes_down`: the others down (a takes_down fault, or recovering). -/
def nodesDown (s : S) (aimed : Nat) : Nat := Id.run do
  let mut down := 0
  for i in [0:s.setup.nodes.length] do
    if i == aimed then continue
    let active := match slotOf s i 0 with | some sl => takesDown sl.kind | none => false
    if active || s.downRecoveringUntil[i]! > s.now then down := down + 1
  return down

/-- faults.zig:2123 `node_start`. -/
def nodeStart (a : Applied) : FM Bool := do
  let s ← get
  let layer := layerOf a.kind
  let some i := nodeIndex s a.node | return false
  if !(← nodeAdmits i layer) then return false
  let s ← get
  if s.setup.nodesDownMax > 0 && takesDown a.kind then
    if nodesDown s i ≥ s.setup.nodesDownMax then
      femit (.skipped a.kind a.node "NodesDownMax" s.now)
      return false
  setSlot i layer (some { kind := a.kind, endT := s.now + a.duration })
  femit (.fault a s.now)
  notePeak
  return true

/-- faults.zig:3050 `outage_start`. -/
def outageStart (a : Applied) : FM Unit := do
  let s ← get
  let mut taken : List Nat := []
  for i in [0:s.setup.nodes.length] do
    if !a.nodes.contains s.setup.nodes[i]!.name then continue
    if ← nodeAdmits i 0 then taken := taken ++ [i]
  let s ← get
  if taken.length < 2 then
    femit (.skipped .outage "" "FewerThanTwoNodes" s.now)
    return
  if s.setup.nodesDownMax > 0 then
    -- faults.zig:3095-3109 (3939448): those already down and those recovering, outside it
    -- (`outage_down_already`, 2122-2132).
    let downAlready := (List.range s.setup.nodes.length).filter (fun i =>
      !taken.contains i &&
      ((match slotOf s i 0 with | some sl => takesDown sl.kind | none => false) ||
       s.downRecoveringUntil[i]! > s.now)) |>.length
    if downAlready + taken.length > s.setup.nodesDownMax then
      femit (.skipped .outage "" "NodesDownMax" s.now)
      return
  for i in taken do setSlot i 0 (some { kind := .outage, endT := s.now + a.duration })
  femit (.fault { a with nodes := taken.map fun i => s.setup.nodes[i]!.name } s.now)
  notePeak

/-- faults.zig:2200 `node_end` (what decides admissions: the slot freed, the recovery window). -/
def nodeEnd (i layer : Nat) : FM Unit := do
  let s ← get
  let some sl := slotOf s i layer | return
  setSlot i layer none
  if takesDown sl.kind then
    modify fun s => { s with downRecoveringUntil := s.downRecoveringUntil.set! i (s.now + s.setup.recoveryMs) }
  femit (.ended sl.kind s.setup.nodes[i]!.name s.now)

/-- faults.zig:2796 `node_expire` and 3994 `network_expire`. -/
def expire : FM Unit := do
  let s ← get
  for i in [0:s.setup.nodes.length] do
    for layer in [0:2] do
      match slotOf (← get) i layer with
      | some sl => if sl.endT ≤ (← get).now then nodeEnd i layer
      | none => pure ()
  modify fun s => { s with network := s.network.filter fun (_, e) => e > s.now }

/-- faults.zig:3033 `node_heal` and 3988 `network_heal`. -/
def heal : FM Unit := do
  let s ← get
  for i in [0:s.setup.nodes.length] do nodeEnd i 1
  for i in [0:s.setup.nodes.length] do nodeEnd i 0
  modify fun s => { s with network := [] }

/-- faults.zig:4474 `quiet_request`. -/
def quietRequest (ms : Nat) : FM Unit := do
  if ms > 0 then heal
  let s ← get
  if ms == 0 then
    let left := s.pacingQuietUntil > s.now
    modify fun s => { s with quietUntil := if left then s.pacingQuietUntil else 0, quietPacing := left }
    femit (.quiet (← get).quietUntil s.now)
    return
  modify fun s => { s with quietUntil := max s.quietUntil (s.now + ms) }
  femit (.quiet (← get).quietUntil s.now)

/-- faults.zig:1513 `apply` (the kinds modeled). -/
def apply (a : Applied) : FM Unit := do
  if isNodeFault a.kind then
    let _ ← nodeStart a
  else if a.kind == .outage then outageStart a
  else if isNetworkFault a.kind then
    modify fun s => { s with network := s.network ++ [(a, s.now + a.duration)] }
    femit (.fault a (← get).now)
  else if a.kind == .restore then
    if !(← get).network.isEmpty then
      modify fun s => { s with network := [] }
      femit (.fault a (← get).now)
  else if a.kind == .clock_skip then femit (.fault a (← get).now)

/-- faults.zig:4541 `inject`: applied at once (no quiet check, no exclusion check). -/
def inject (a : Applied) : FM Unit := apply { a with injected := true }

/-- The world's requests during a sleep (faults.zig:4294 `sleep_ns`): one decision a sleep,
taken as it begins. A quiet request ends the sleep (its return value counts it). -/
def requestMenu (s : Setup) : List (Option Request) :=
  let nodes := s.nodes.map (·.name)
  [none, some (.quiet 50), some (.quiet 0)] ++
  (nodes.map fun n => some (.inject { kind := .restart, node := n, duration := 20 })) ++
  (nodes.map fun n => some (.inject { kind := .pause, node := n, duration := 20 })) ++
  (if nodes.length ≥ 2 then [some (.inject { kind := .outage, nodes := nodes.take 2, duration := 20 })] else []) ++
  (nodes.map fun n => some (.aim n))

def sleepFor (ms : Nat) : FM Unit := do
  let s ← get
  let menu := requestMenu s.setup
  let r := menu[(← below "world.request" menu.length)]!
  let deadline := s.now + ms
  expire
  match r with
  | some (.quiet q) => quietRequest q; return
  | some (.inject a) => inject a
  | some (.aim n) => modify fun s => { s with aim := n }
  | none => pure ()
  -- To each fault's end, then the deadline.
  for _ in [0:64] do
    let s ← get
    if s.now ≥ deadline || s.stopping then return
    let ends := (s.slots.toList.flatMap fun row => row.toList.filterMap (·.map (·.endT))) ++
      s.network.map (·.2)
    let next := ends.foldl (fun m e => if e > s.now then min m e else m) deadline
    modify fun s => { s with now := next }
    expire

/-- faults.zig:495 `swarm_select`: the kinds kept first; how many faults. -/
def swarmSelect (faults : List Fault) : FM (List Fault) := do
  let s ← get
  if faults.isEmpty then return []
  if s.setup.swarmOff then return faults
  let allowed := FKind.all.filter fun k => faults.any (·.kind == k)
  let eighths := 1 + (← below "fault.swarm_p" 7)
  let mut kept : List FKind := []
  for k in allowed do
    if (← below s!"fault.swarm {k.name}" 8) < eighths then kept := kept ++ [k]
  if kept.isEmpty then
    let mut pickIndex ← below "fault.swarm_one" allowed.length
    for k in allowed do
      if pickIndex == 0 then kept := kept ++ [k]
      pickIndex := pickIndex - 1
  let mut weights : List (FKind × Nat) := []
  for k in kept do
    weights := weights ++ [(k, 2 ^ (← below s!"fault.weight {k.name}" 7))]
  modify fun s => { s with kindWeights := weights, kindsWeighted := true }
  return (faults.filter fun f => kept.contains f.kind)

/-- faults.zig:643 `fault_weighted`. -/
def faultWeighted (faults : List Fault) : FM Fault := do
  let s ← get
  if !s.kindsWeighted then return faults[(← below "fault" faults.length)]!
  let present := FKind.all.filter fun k => faults.any (·.kind == k)
  let weightOf (k : FKind) := max 1 ((s.kindWeights.lookup k).getD 0)
  let total := present.foldl (fun t k => t + weightOf k) 0
  let mut pick ← below "fault.kind" total
  let mut chosen := faults[0]!.kind
  for k in present do
    if pick < weightOf k then
      chosen := k
      break
    pick := pick - weightOf k
  let subset := faults.filter (·.kind == chosen)
  return subset[(← below "fault" subset.length)]!

/-- faults.zig:4448 `fault_choose` (no branch point). -/
def faultChoose (faults : List Fault) : FM Fault := do
  let s ← get
  if !s.aim.isEmpty then
    if (← below "fault.aim" 2) == 0 then
      let aimed := faults.filter fun f => f.node == s.aim || f.peer == s.aim
      if !aimed.isEmpty then return aimed[(← below "fault.aimed" aimed.length)]!
  faultWeighted faults

/-- faults.zig:1296 `outage_draw`. -/
def outageDraw (endpoints : List Bool) (names : List String) : FM (List String) := do
  let allowed := (names.zip endpoints).filterMap fun (n, b) => if b then some n else none
  if (← below "fault.outage_all" 2) == 0 then return allowed
  let count := allowed.length
  let size := 2 + (← below "fault.outage_size" (count - 1))
  let mut candidates := allowed.toArray
  let mut picked : List String := []
  for pos in [0:size] do
    let other := pos + (← below "random_below" (count - pos))
    let a := candidates[pos]!
    candidates := (candidates.set! pos candidates[other]!).set! other a
    picked := picked ++ [candidates[pos]!]
  return picked

/-- faults.zig:830 `draw` (durations over a menu, named as the Zig's). -/
def drawFault (f : Fault) : FM Applied := do
  let durations := [5, 40]
  let duration := durations[(← below "fault.duration_ns" durations.length)]!
  let names := endpointNames (← get).setup
  match f.kind with
  | .outage => pure { kind := .outage, nodes := ← outageDraw f.endpoints names, duration }
  | _ => pure { kind := f.kind, node := f.node, peer := f.peer, duration,
                nodes := (names.zip (f.endpoints ++ List.replicate 64 false)).filterMap
                  fun (n, b) => if b && n != "runner" then some n else none }

/-- faults.zig:465 `stretch_ns`. -/
def stretch (name : String) (maxMs : Nat) : FM Nat := do
  let floor := maxMs / 10
  return floor + (← below name (maxMs - floor + 1))

/-- faults.zig:300 `main`, from the faults' list on: `injections` faults, then the stop. -/
def injector (injections : Nat) : FM Unit := do
  let s ← get
  let n := s.setup.nodes.length
  modify fun s => { s with slots := Array.replicate n #[none, none], downRecoveringUntil := Array.replicate n 0 }
  let all := faults_collect s.setup
  if all.isEmpty then return
  let mixed ← swarmSelect all
  -- regime_draw's overlap share (faults.zig:1186); the fixed injector's is 0.
  if !s.setup.swarmOff then
    let o ← below "fault.overlap_eighths" 9
    modify fun s => { s with overlapEighths := o }
  let mut activeUntil : Option Nat := none
  if s.setup.activeMsMax > 0 then activeUntil := some ((← get).now + (← stretch "fault.active_ms" s.setup.activeMsMax))
  for _ in [0:injections] do
    let waits := [10, 30]
    sleepFor waits[(← below "fault.wait_ns" waits.length)]!
    if (← get).stopping then break
    if let some au := activeUntil then
      if (← get).now ≥ au then
        if s.setup.quietMsMax > 0 then
          let st ← stretch "fault.quiet_ms" s.setup.quietMsMax
          quietRequest st
          modify fun s => { s with quietPacing := true, pacingQuietUntil := s.now + st }
          let now := (← get).now
          if (← get).quietUntil > now then sleepFor ((← get).quietUntil - now)
        activeUntil := some ((max (← get).quietUntil (← get).now) + (← stretch "fault.active_ms" s.setup.activeMsMax))
    let chosen ← faultChoose mixed
    let applied ← drawFault chosen
    if (← get).now < (← get).quietUntil && applied.kind != .clock_skip then continue
    apply applied
  -- The stop (composer's SIGTERM): everything healed.
  modify fun s => { s with stopping := true }
  heal
  femit (.stopped (← get).now)

def runInjector (setup : Setup) (injections : Nat) (source : Source) : S × Option Stop :=
  let s0 : S := { decisions := { source }, setup }
  match (injector injections).run s0 with
  | .ok _ s => (s, none)
  | .error e s => (s, some e)

/-! ## The documented rules -/

structure FProp where
  name : String
  source : String
  check : S → Option String

def exclusionsHeld : FProp :=
  { name := "an excluded node gets no fault of its own and is in no partition, isolation or outage"
    source := "round 1's reading: docs/ANTITHESIS.md at 0dea225 (Fault exclusions): \"a node whose name matches gets no fault of its own and is in no partition, isolation or outage\"; at 3939448 the Custom faults row adds that an injected fault reaches \"a node --fault-exclusions leaves out (the scenario named it)\": documented since, so this strict form is no longer a promise"
    check := fun s => Id.run do
      for e in s.log do
        if let .fault a t := e then
          let names := ([a.node, a.peer] ++ a.nodes).filter (!·.isEmpty)
          for n in names do
            if excluded s.setup n && a.kind != .clock_skip then
              return some s!"{a.kind.name} node={a.node} peer={a.peer} nodes={a.nodes} at {t} ms{if a.injected then " (injected)" else ""} involves excluded {n}"
      return none }

def exclusionsDrawnHeld : FProp :=
  { exclusionsHeld with
    name := "an excluded node is in no drawn fault (injected ones aside)"
    source := "docs/ANTITHESIS.md at 3939448 (Fault exclusions; Custom faults: injected ones reach excluded nodes)"
    check := fun s => Id.run do
      for e in s.log do
        if let .fault a t := e then
          if a.injected then continue
          let names := ([a.node, a.peer] ++ a.nodes).filter (!·.isEmpty)
          for n in names do
            if excluded s.setup n && a.kind != .clock_skip then
              return some s!"{a.kind.name} node={a.node} peer={a.peer} nodes={a.nodes} at {t} ms involves excluded {n}"
      return none }

def nodesDownLiteral : FProp :=
  { name := "at most nodes_down_max nodes killed, powered off, stopped or wiped at once, outages counted"
    source := "docs/ANTITHESIS.md (A cap on nodes down at once)"
    check := fun s => Id.run do
      if s.setup.nodesDownMax == 0 then return none
      for (t, literal, _) in s.peaks do
        if literal > s.setup.nodesDownMax then
          return some s!"{literal} nodes down at {t} ms, nodes_down_max {s.setup.nodesDownMax}"
      return none }

def nodesDownRecovering : FProp :=
  { name := "at most nodes_down_max nodes down at once, a node back less than its recovery ago counted (as node_start counts it)"
    source := "docs/ANTITHESIS.md (A cap on nodes down at once: \"for a claim that covers a minority's failures ... a 2n+1 cluster surviving n\"); faults.zig:2087-2111, 2134-2148 (node_start counts recovering nodes)"
    check := fun s => Id.run do
      if s.setup.nodesDownMax == 0 then return none
      for (t, _, rec) in s.peaks do
        if rec > s.setup.nodesDownMax then
          return some s!"{rec} nodes down or recovering at {t} ms, nodes_down_max {s.setup.nodesDownMax}"
      return none }

def quietHeld : FProp :=
  { name := "in a quiet period no fault but a clock skip starts"
    source := "round 1's reading: docs/ANTITHESIS.md at 0dea225 (Pausing faults): \"none but clock skips start\"; at 3939448: \"no drawn fault but clock skips starts ... A fault a scenario asks for (sdk.fault, det-faults inject) still starts\": no longer a promise"
    check := fun s => Id.run do
      let mut quietUntil := 0
      for e in s.log do
        match e with
        | .quiet u _ => quietUntil := u
        | .fault a t =>
          if t < quietUntil && a.kind != .clock_skip then
            return some s!"{a.kind.name} {a.node}{a.nodes} starts at {t} ms in a quiet period until {quietUntil}{if a.injected then " (injected: sdk.fault)" else ""}"
        | _ => pure ()
      return none }

def quietDrawnHeld : FProp :=
  { quietHeld with
    name := "in a quiet period no drawn fault but a clock skip starts"
    source := "docs/ANTITHESIS.md at 3939448 (Pausing faults): \"no drawn fault but clock skips starts\""
    check := fun s => Id.run do
      let mut quietUntil := 0
      for e in s.log do
        match e with
        | .quiet u _ => quietUntil := u
        | .fault a t =>
          if !a.injected && t < quietUntil && a.kind != .clock_skip then
            return some s!"{a.kind.name} {a.node}{a.nodes} starts at {t} ms in a quiet period until {quietUntil}"
        | _ => pure ()
      return none }

def healedAtStop : FProp :=
  { name := "once faults stop, nothing of them lasts"
    source := "faults.zig:2 (\"on stop it undoes what it did\"); faults.zig:408 leftovers_check"
    check := fun s =>
      if s.slots.any (·.any (·.isSome)) then some "a node fault outlived the stop"
      else if !s.network.isEmpty then some "a network fault outlived the stop" else none }

def allFProps : List FProp :=
  [exclusionsHeld, exclusionsDrawnHeld, nodesDownLiteral, nodesDownRecovering, quietHeld, quietDrawnHeld, healedAtStop]

def judgeF (p : FProp) (setup : Setup) (injections : Nat) (source : Source) : Ended :=
  let (s, stop) := runInjector setup injections source
  let violation := match stop with
    | some .limit => none
    | _ => (p.check s).map fun d => (p.name, d)
  { taken := s.decisions.taken, violation }

def fstory (setup : Setup) (injections : Nat) (source : Source) : List String :=
  let (s, stop) := runInjector setup injections source
  let listed := (faults_collect setup).map (·.label)
  s!"faults listed: {listed}" ::
  (s.log.toList.map fun
    | .fault a t => s!"{t} ms: fault {a.kind.name} node={a.node} peer={a.peer} nodes={a.nodes} for {a.duration} ms{if a.injected then " (injected)" else ""}"
    | .skipped k n why t => s!"{t} ms: fault_skipped {k.name} {n} {why}"
    | .ended k n t => s!"{t} ms: {k.name} on {n} ends"
    | .quiet u t => s!"{t} ms: quiet until {u}"
    | .stopped t => s!"{t} ms: faults stop") ++ [s!"end: {reprStr stop}"]

structure FWorld where
  label : String
  setup : Setup
  injections : Nat := 3

/-- A node allowing only node faults: restarts, and power losses when `crash`. -/
def downNode (i : Nat) (crash : Bool) : NodeSpec :=
  { name := s!"n{i}", restart := true, crash, pause := false, isolate := false, partition := false,
    degrade := false, throttle := false, syncStall := false, runnerLinks := false }

def pausing (i : Nat) : NodeSpec :=
  { name := s!"n{i}", restart := true, isolate := false, partition := false, degrade := false,
    throttle := false, syncStall := false, runnerLinks := false }

def everything (i : Nat) : NodeSpec :=
  { name := s!"n{i}", restart := true, crash := true, stop := true, wipe := true }

def fworlds : List FWorld :=
  [ { label := "two nodes, the later one excluded, no swarm"
      setup := { nodes := [{ name := "a" }, { name := "b" }], excluded := ["b"], swarmOff := true }
      injections := 2 },
    { label := "two nodes, the earlier one excluded, no swarm"
      setup := { nodes := [{ name := "a" }, { name := "b" }], excluded := ["a"], swarmOff := true }
      injections := 2 },
    { label := "five nodes allowing restarts and power losses, nodes_down_max 2, no swarm"
      setup := { nodes := (List.range 5).map (downNode · true),
                 nodesDownMax := 2, recoveryMs := 100, swarmOff := true }
      injections := 3 },
    { label := "three nodes allowing restarts, nodes_down_max 1, no swarm"
      setup := { nodes := (List.range 3).map (downNode · false),
                 nodesDownMax := 1, recoveryMs := 100, swarmOff := true }
      injections := 3 },
    { label := "two nodes allowing restarts and pauses, quiet periods, no swarm"
      setup := { nodes := (List.range 2).map pausing, swarmOff := true }
      injections := 2 },
    { label := "three nodes, every kind modeled, pacing, swarm"
      setup := { nodes := (List.range 3).map everything,
                 nodesDownMax := 1, recoveryMs := 50, activeMsMax := 60, quietMsMax := 40, clockSkip := true,
                 excluded := ["n2"] }
      injections := 6 } ]

def searchAll (exhaustRuns worldRuns : Nat) : IO (List Found) := do
  let mut found : List Found := []
  for p in allFProps do
    say s!"== fault injector property: {p.name}"
    say s!"   source: {p.source}"
    let mut exhausted := false
    let mut explored := false
    for wd in fworlds do
      let run := judgeF p wd.setup wd.injections
      if !exhausted then
        if let some f ← exhaustSaid s!"{p.name} / {wd.label}" run exhaustRuns then
          printFound f (fstory wd.setup wd.injections)
          found := found ++ [f]
          exhausted := true
      if !explored && worldRuns > 0 then
        let run' := judgeF p wd.setup (wd.injections * 4)
        if let some f ← exploreSaid s!"{p.name} / {wd.label} ({wd.injections * 4} injections)" run' worldRuns then
          printFound f (fstory wd.setup (wd.injections * 4))
          found := found ++ [f]
          explored := true
  return found

end Replica.Faults

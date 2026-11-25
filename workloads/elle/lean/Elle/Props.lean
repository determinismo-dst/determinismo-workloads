import Elle.ListAppend
import Elle.RwRegister
import Elle.Spec
import Elle.Gen

/-!
# Properties

Each property names its source. A run generates a history from its decisions, computes Elle's
verdicts (the replica) and the specification's, and reports the first property it breaks.
-/

namespace Elle.Props

open Elle Elle.Spec Elle.Gen Determinismo

/-! ## EDN -/

def ednVal : Val → String
  | .nil => "nil"
  | .int i => toString i
  | .list l => "[" ++ " ".intercalate (l.map toString) ++ "]"
  | .kmap _ => "{}"
  | .unborn => ":elle/unborn"
  | .dead => ":elle/dead"

def ednF : F → String
  | .r => ":r" | .append => ":append" | .w => ":w" | .insert => ":insert" | .delete => ":delete" | .rp => ":rp"

def ednType : OpType → String
  | .invoke => ":invoke" | .ok => ":ok" | .fail => ":fail" | .info => ":info"

def ednOp (o : Op) : String :=
  let mops := o.value.map fun m => s!"[{ednF m.f} {m.k} {ednVal m.v}]"
  s!"\{:process {o.process}, :type {ednType o.type}, :f :txn, :value [{" ".intercalate mops}]}"

def ednHistory (h : History) : String :=
  "[" ++ "\n ".intercalate (h.toList.map ednOp) ++ "]"

/-! ## Configuration -/

structure Config where
  bounds : Bounds := {}
  /-- Property kinds not checked (a found disagreement masked to look for others). -/
  skip : List String := []
  /-- Models compared with the specification. -/
  models : List String := specModels
  /-- Model pairs checked for monotonicity. -/
  pairs : Bool := true
  /-- Only histories whose committed appends were all read (list append). -/
  observed : Bool := false
  /-- The alternative iteration order is a decision (explore); otherwise the reverse of the op
  indices (exhaust, where a decided permutation would multiply the space). -/
  rankDecided : Bool := true
  /-- Only histories where no transaction reads a key twice (rw-register's wr edges come from
  each transaction's first read of a key). -/
  singleReads : Bool := false
  deriving Inhabited

def isLA (c : Config) : Bool := c.bounds.workload == .listAppend

def analyzeWith (c : Config) (h : History) (e : Extra) (o : Order) : Except String Anomalies :=
  if isLA c then ListAppend.analyze h e o else RwRegister.analyze {} h e o

def interps (c : Config) (h : History) : List Interp :=
  if isLA c then interpsListAppend h else interpsRegister h

/-- The model's verdict from the anomalies of each extra graph. -/
def elleVerdict (an : Extra → Except String Anomalies) (models : List String) : Except String Valid := do
  let opts : Opts := { models := some models }
  let m ← an (additionalGraphs opts)
  return (resultMap opts m).valid

/-! ## Claims: what an Elle anomaly says about every interpretation -/

def variantOf (t : String) : String :=
  if t.endsWith "-process" then "-process" else if t.endsWith "-realtime" then "-realtime" else ""

def baseOf (t : String) : String :=
  let v := variantOf t
  String.ofList (t.toList.take (t.length - v.length))

/-- (phenomena any of which makes the claim true, claims over clean interpretations only).
A cycle claim also holds when a more severe cycle stands in its place (README, Soundness: "either
a corresponding anomaly exists, or something worse happened"): the specification's G1c includes
G0, its G-nonadjacent (Cerone's acyclicity) includes G1c, and a variant includes the plainer one. -/
def claimOf (t : String) : Option (List String × Bool) :=
  let v := variantOf t
  let b := baseOf t
  if b == "G0" then some (["G0" ++ v], true)
  else if b == "G1c" then some (["G1c" ++ v], true)
  else if b == "G-single" || b == "G-single-item" then some (["G-single" ++ v, "G1c" ++ v], true)
  else if b == "G-nonadjacent" || b == "G-nonadjacent-item" then some (["G-nonadjacent" ++ v], true)
  else if b == "G2" || b == "G2-item" then some (["G2" ++ v, "G1c" ++ v], true)
  else if t == "G1a" then some (["G1a", "dirty-update"], false)
  else if t == "G1b" then some (["G1b"], false)
  else if t == "dirty-update" then some (["dirty-update", "G1a"], false)
  else if t == "incompatible-order" then some (["G1a", "dirty-update"], false)
  else if t == "lost-update" then some (["lost-update"], true)
  else if t == "internal" then some (["internal"], false)
  else match t with
    | "PL-1-cycle-exists" => some (["G0"], true)
    | "PL-2-cycle-exists" => some (["G1c"], true)
    | "PL-SI-cycle-exists" => some (["G-nonadjacent"], true)
    | "PL-2.99-cycle-exists" => some (["G2", "G1c"], true)
    | "PL-3-cycle-exists" => some (["G2", "G1c"], true)
    | "strong-session-PL-1-cycle-exists" => some (["G0-process"], true)
    | "strong-session-PL-2-cycle-exists" => some (["G1c-process"], true)
    | "strong-session-snapshot-isolation-cycle-exists" => some (["G-nonadjacent-process"], true)
    | "strong-session-serializable-cycle-exists" => some (["G2-process", "G1c-process"], true)
    | "strong-PL-1-cycle-exists" => some (["G0-realtime"], true)
    | "strong-PL-2-cycle-exists" => some (["G1c-realtime"], true)
    | "strong-snapshot-isolation-cycle-exists" => some (["G-nonadjacent-realtime"], true)
    | "PL-SS-cycle-exists" => some (["G2-realtime", "G1c-realtime"], true)
    | _ => none

/-- The exact phenomenon an anomaly names, without severity: G-single(-item) needs a cycle with
exactly one anti-dependency; G1a an aborted read, not a dirty update. -/
def exactOf (t : String) : Option (List String × Bool) :=
  let v := variantOf t
  let b := baseOf t
  if b == "G-single" || b == "G-single-item" then some (["G-single" ++ v], true)
  else if t == "G1a" then some (["G1a"], false)
  else none

/-- Every append of a committed transaction appears in some acknowledged read (the paper's
traceability: Elle infers version orders from reads). -/
def allObserved (h : History) : Bool :=
  let reads := h.toList.filter Op.isOk |>.flatMap fun o => o.value.flatMap fun m =>
    if m.f == .r then (match m.v with | .list l => l.map (m.k, ·) | _ => []) else []
  h.toList.filter (fun o => o.isOk || o.isInfo) |>.all fun o => o.value.all fun m =>
    m.f != .append || (match m.v with | .int e => reads.contains (m.k, e) | _ => true)

/-- A step's relation, transitively, in an interpretation (Elle §4.3.2: inferred edges stand for
Adya's dependencies); `direct` asks for Adya's direct edge. -/
def stepHolds (h : History) (i : Interp) (a b : Nat) (s : Step) (direct : Bool) : Bool :=
  let ord (k : Nat) := (i.order.lookup k).getD []
  let pos (k : Nat) (x : Nat) := (ord k).findIdx? (· == x)
  match s.type, s.key with
  | "ww", some k =>
    match pos k a, pos k b with
    | some x, some y => if direct then y == x + 1 else x < y
    | _, _ => false
  | "wr", some k => i.reads.any fun (r, k', w) => r == b && k' == k && w == some a
  | "rw", some k =>
    match pos k b with
    | none => false
    | some y => i.reads.any fun (r, k', w) => r == a && k' == k &&
        (match w with
         | none => if direct then y == 0 else true
         | some w => match pos k w with
           | some x => if direct then y == x + 1 else x < y
           | none => false)
  | "process", _ =>
    match h[a]?, h[b]? with
    | some x, some y => x.process == y.process && x.index < y.index
    | _, _ => false
  | "realtime", _ =>
    let pairs := pairIndex h
    match (pairs.lookup b).bind (h[·]?) with
    | some inv => a < inv.index
    | none => false
  | _, _ => true

/-! ## The checks -/

/-- A disagreement: (property, detail). -/
abbrev Found := Option (String × String)

def firstSome {α : Type} (l : List α) (f : α → Found) : Found := l.findSome? f

/-- Every edge of `G` in `realtime-graph`'s transitive closure is a real-time precedence and
every precedence is in the closure (core.clj:371: a transitive reduction). -/
def realtimeOk (h : History) : Bool :=
  let g := (realtimeGraph h).graph
  let pairs := pairIndex h
  let comps := h.toList.filter fun o => !o.isInvoke
  comps.all fun a => comps.all fun b =>
    let inv := ((pairs.lookup b.index).bind (h[·]?)).map (·.index)
    let should := a.isOk && a.index != b.index && (match inv with | some i => a.index < i | none => false)
    let has := (reach g a.index).contains b.index
    should == has

def checkHistory (c : Config) (h : History) (rank : Nat → Nat) : Found := Id.run do
  let skip (k : String) := c.skip.contains k
  if c.observed && isLA c && !allObserved h then return none
  if c.singleReads && !(h.toList.all fun o => o.value.all fun m =>
      m.f != .r || (o.value.filter fun m' => m'.f == .r && m'.k == m.k).length ≤ 1) then return none
  let canon : Order := {}
  let perm : Order := Order.ofRank rank
  let cN := analyzeWith c h .none canon
  let cP := analyzeWith c h .process canon
  let cR := analyzeWith c h .realtime canon
  let an (o : Order) (e : Extra) : Except String Anomalies :=
    if o.iter [0, 1, 2, 3, 4, 5] == canon.iter [0, 1, 2, 3, 4, 5] && o.iter [7, 3, 9] == canon.iter [7, 3, 9] then
      match e with | .none => cN | .process => cP | .realtime => cR | _ => analyzeWith c h e o
    else analyzeWith c h e o
  -- Elle must not throw on a well-formed history (unique writes).
  if !skip "thrown" then
    if let .error e := an canon .realtime then
      return some ("thrown", s!"Elle throws: {e}")
  let is := interps c h
  -- 1-2. Model verdicts against the specification.
  for m in c.models do
    let ev := elleVerdict (an canon) [m]
    let sv := verdict is m
    match ev with
    | .ok .false_ =>
      if sv == .sat && !skip ("soundness:" ++ m) && !skip "soundness" then
        return some ("soundness:" ++ m, s!"Elle: {m} invalid; specification: {sv.str}")
    | .ok .true_ =>
      if sv == .unsat && !skip ("completeness:" ++ m) && !skip "completeness" then
        return some ("completeness:" ++ m, s!"Elle: {m} valid; specification: {sv.str}")
    | _ => pure ()
  -- 3. Claims: each anomaly Elle reports holds in every (clean) interpretation.
  if !skip "claim" then
    for e in [Extra.none, .process, .realtime] do
      if let .ok m := an canon e then
        for (t, _) in m do
          if skip ("claim:" ++ t) then continue
          match claimOf t with
          | none => pure ()
          | some (ps, cleanOnly) =>
            let scope := is.filter fun i => !cleanOnly || i.clean
            if let some bad := scope.find? (fun i => !(i.phen.any ps.contains)) then
              return some ("claim:" ++ t,
                s!"Elle reports {t}; an interpretation{if cleanOnly then " (clean)" else ""} without {ps}: {bad.phen}, order {bad.order}")
  -- 3b. Classification: the exact phenomenon named.
  if !skip "classification" then
    for e in [Extra.none, .process, .realtime] do
      if let .ok m := an canon e then
        for (t, _) in m do
          if skip ("classification:" ++ t) then continue
          match exactOf t with
          | none => pure ()
          | some (ps, cleanOnly) =>
            let scope := is.filter fun i => !cleanOnly || i.clean
            if let some bad := scope.find? (fun i => !(i.phen.any ps.contains)) then
              return some ("classification:" ++ t,
                s!"Elle reports {t}; an interpretation{if cleanOnly then " (clean)" else ""} without {ps}: {bad.phen}, order {bad.order}")
  -- 4. Explanations: each step of a reported cycle is an edge of its kind, in Elle's graph and
  -- (transitively) in every clean interpretation.
  if !skip "explanation" then
    for e in [Extra.none, .process, .realtime] do
      if let .ok m := an canon e then
        if let .ok a := (if isLA c then ListAppend.analysis h e else RwRegister.graphWith {} e h) then
          for (t, cs) in m do
            for cse in cs do
              if let .cycle ops steps := cse then
                for ((x, y), s) in (ops.zip (ops.drop 1)).zip steps do
                  let bit := (Rels.ALL.zip Rels.NAMES).find? (·.2 == s.type) |>.map (·.1) |>.getD 0
                  if Rels.inter (a.graph.edge x y) bit == 0 then
                    return some ("explanation:graph", s!"{t}: step {x}->{y} {s.type} is not an edge of that kind")
                  if !skip "explanation:transitive" then
                    if let some bad := is.find? (fun i => i.clean && !stepHolds h i x y s false) then
                      return some ("explanation:transitive",
                        s!"{t}: step {x}->{y} {s.type} {s.key} fails in a clean interpretation, order {bad.order}")
                  if !skip "explanation:direct" then
                    if let some bad := is.find? (fun i => i.clean && !stepHolds h i x y s true) then
                      return some ("explanation:direct",
                        s!"{t}: step {x}->{y} {s.type} {s.key} is no direct Adya edge in a clean interpretation, order {bad.order}")
  -- 5. Order independence: verdicts under another iteration order.
  if !skip "order" then
    let pN := analyzeWith c h .none perm
    let pP := analyzeWith c h .process perm
    let pR := analyzeWith c h .realtime perm
    let anP (e : Extra) : Except String Anomalies := match e with | .none => pN | .process => pP | .realtime => pR | _ => analyzeWith c h e perm
    for m in c.models do
      let a := elleVerdict (an canon) [m]
      let b := elleVerdict anP [m]
      match a, b with
      | .ok x, .ok y => if x != y then return some ("order:" ++ m, s!"{m}: {x.str} vs {y.str} under another order")
      | _, _ => pure ()
  -- 6. Monotonicity: models together fail when either fails alone.
  if c.pairs && !skip "monotone" then
    for m1 in c.models do
      for m2 in c.models do
        if m1 < m2 then
          match elleVerdict (an canon) [m1], elleVerdict (an canon) [m2], elleVerdict (an canon) [m1, m2] with
          | .ok a, .ok b, .ok ab =>
            let alone := a == .false_ || b == .false_
            if alone != (ab == .false_) then
              return some ("monotone", s!"[{m1}]: {a.str}, [{m2}]: {b.str}, [{m1} {m2}]: {ab.str}")
          | _, _, _ => pure ()
  -- 7. Tarjan's SCCs (Bifurcan's, as written) against mutual reachability, on Elle's graph.
  if !skip "scc" then
    if let .ok a := (if isLA c then ListAppend.analysis h .realtime else RwRegister.graphWith {} .realtime h) then
      if canonSccs (tarjan a.graph perm false) != canonSccs (sccSpec a.graph false) then
        return some ("scc", "Tarjan's components differ from mutual reachability")
      if canonSccs (tarjan a.graph perm true) != canonSccs (sccSpec a.graph true) then
        return some ("scc", "Tarjan's components (with singletons) differ from mutual reachability")
  -- 8. The real-time graph is a transitive reduction of real-time precedence.
  if !skip "realtime" && !realtimeOk h then
    return some ("realtime", "realtime-graph's closure differs from real-time precedence")
  return none

/-- One timeline: a history and an order from the source's decisions. -/
def runOnce (c : Config) (src : Source) : Ended × Option History :=
  let d : Decisions := { source := src, limit := 400 }
  let gen : W (History × (Nat → Nat)) := do
    let h ← genHistory c.bounds
    let r ← if c.rankDecided then genRank h.size else pure (fun v => h.size - v)
    pure (h, r)
  match gen.run d with
  | .ok (h, r) d' => ({ taken := d'.taken, violation := checkHistory c h r }, some h)
  | .error _ d' => ({ taken := d'.taken, violation := none }, none)

def run (c : Config) (src : Source) : Ended := (runOnce c src).1

end Elle.Props

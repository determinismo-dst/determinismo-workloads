import Elle.Service
import Elle.Props2

/-!
# The service's properties

- closing: Elle's verdict on the closed history equals its verdict with each open operation
  completed `:info` where it would have completed (the history the client meant to send), and
  the specification sees the same history either way (an open invocation is indeterminate);
- dedup: the answer's `not` is the boundary of what it reports (the lattice's
  `friendly-boundary`, consistency_model.clj:602), and deduplication hides no anomaly type Elle
  reports on the history without the duplicated reads;
- per key: the service's verdict against both readings of its definition, and never stricter
  than Elle's strict serializability.
-/

namespace Elle.ServiceProps

open Elle Elle.Spec Elle.SpecOpts Elle.Gen Elle.Props Elle.Service Determinismo

/-- The history with the completion of some processes' last ops dropped (left open), and the
same history with those completions turned `:info` in place. -/
def genOpen (h : History) : W (List Op × List Op) := do
  let ops := h.toList
  let procs := dedup (ops.map (·.process))
  let mut drop : List Nat := []
  for p in procs do
    match (ops.filter (·.process == p)).getLast? with
    | some o => if !o.isInvoke then if ← decideRare (σ := Decisions) "open.drop" 1 4 then drop := drop ++ [o.index]
    | none => pure ()
  let opened := ops.filter fun o => !drop.contains o.index
  let blank (o : Op) : List Mop := o.value.map fun m => if m.f == .r then { m with v := .nil } else m
  let infoed := ops.map fun o => if drop.contains o.index then { o with type := .info, value := blank o } else o
  return (opened, infoed)

/-- One `:ok` list read with an element repeated. -/
def genDup (ops : List Op) : W (List Op) := do
  let cands := ops.filter fun o => o.isOk && o.value.any fun m => m.f == .r && (match m.v with | .list l => !l.isEmpty | _ => false)
  if cands.isEmpty then return ops
  if !(← decideRare (σ := Decisions) "dup.inject" 1 2) then return ops
  let o ← dec "dup.op" cands.length
  let target := cands.getD o default
  let rs := (target.value.zip (List.range target.value.length)).filter fun (m, _) =>
    m.f == .r && (match m.v with | .list l => !l.isEmpty | _ => false)
  let (m, mi) := rs.getD (← dec "dup.mop" rs.length) (default, 0)
  let l := match m.v with | .list l => l | _ => []
  let e ← dec "dup.elem" l.length
  let at_ ← dec "dup.at" (l.length - e)
  let l' := l.take (e + 1 + at_) ++ [l.getD e 0] ++ l.drop (e + 1 + at_)
  return ops.map fun x => if x.index == target.index then
    { x with value := x.value.set mi { m with v := .list l' } } else x

def reindex (ops : List Op) : History :=
  (ops.zip (List.range ops.length)).toArray.map fun (o, i) => { o with index := i }

def answerOf (model : Model) (m : String) (lk : Bool) (ops : List Op) : Except String Answer :=
  Service.check model m lk ops

def modelOf (c : Props2.Config2) : Model := if c.bounds.workload == .listAppend then .listAppend else .register

def outcomeKey : Outcome → String
  | .result r => s!"{r.valid.str} {r.anomalyTypes}"
  | .thrown e => s!"throws {e}"

/-- All of Elle's anomaly names (reportable or not) for the boundary. -/
def allAnomalies (model : Model) (opts : Opts) (h : History) : List String :=
  match model with
  | .listAppend => ((ListAppend.analyze h (additionalGraphs opts)).toOption.getD []).map (·.1)
  | .register => ((RwRegister.analyze opts h (additionalGraphs opts)).toOption.getD []).map (·.1)
  | .closedPredicate => []

def check (c : Props2.Config2) (h : History) (opened infoed : List Op) (dupd : List Op) : Found := Id.run do
  let skip (k : String) := c.skip.contains k || c.skip.any fun s => k.startsWith (s ++ ":")
  let model := modelOf c
  -- closing
  if !skip "closing" && opened.length != infoed.length then
    let hc := reindex (Service.closed opened)
    let hi := reindex infoed
    for m in c.models do
      let o : Opts := { models := some [m] }
      let run (x : History) : Outcome :=
        if model == .listAppend then ListAppend.check o x else RwRegister.check o x
      let ra := run hc
      let rb := run hi
      let a := outcomeKey ra
      let b := outcomeKey rb
      if ra.valid != rb.valid && !skip ("closing:" ++ m) then
        return some ("closing:" ++ m, s!"closed at the end: {a}; :info in place: {b}")
      if a != b && !skip ("closing-types:" ++ m) then
        return some ("closing-types:" ++ m, s!"closed at the end: {a}; :info in place: {b}")
  -- dedup
  if model == .listAppend && !skip "dedup" then
    let dups := Service.duplicates dupd
    if !dups.isEmpty then
      for m in c.models do
        match answerOf model m false dupd with
        | .ok ans =>
          let hd := reindex (Service.deduplicated dupd)
          let all := allAnomalies model { models := some [m] } hd
          let want := (Model.friendlyBoundary (dedup (all ++ ["duplicate-elements"]))).1
          if ans.not_ != want && !skip "dedup:not" then
            return some ("dedup:not", s!"{m}: types {ans.types}, not {ans.not_}; the lattice's boundary of what Elle found and the duplicate: {want}")
          -- without the duplicated reads
          let dupOps := dups.map (·.1)
          let without := reindex (dupd.map fun o => if dupOps.contains o.index then
            { o with value := o.value.filter fun mo => !(mo.f == .r && dups.any fun (i, k, _) => i == o.index && k == mo.k) } else o)
          match ListAppend.check { models := some [m] } without with
          | .result r =>
            let classes := ans.types.flatMap fun t => match Props.claimOf t with
              | some (ps, _) => if t.endsWith "-cycle-exists" then ps else []
              | none => []
            -- what the reported types imply, or stand in for as more severe (the severity graph,
            -- consistency_model.clj:163, and the README's "something worse")
            let sev := Model.bfs (fun a => Model.dagOut (Model.impliedAnomalies ++ Model.severityGraph) a)
            let implied := sev (ans.types ++ classes ++
              (classes.filter (·.startsWith "G1c")).map fun c => "G0" ++ (c.drop 3).toString)
            -- a reported cycle stands in for T when its phenomenon is one T's claim accepts
            let phenOf (x : String) : String :=
              let b := Props.baseOf x
              let b := if b == "G-single-item" then "G-single" else if b == "G2-item" then "G2"
                       else if b == "G-nonadjacent-item" then "G-nonadjacent" else b
              b ++ Props.variantOf x
            let standsIn (t : String) : Bool := match Props.claimOf t with
              | some (ps, _) => implied.any fun x => ps.contains (phenOf x)
              | none => false
            let hidden := r.anomalyTypes.filter fun t =>
              !implied.contains t && !unknownAnomalyTypes.contains t && !standsIn t
            if !hidden.isEmpty && !skip "dedup:hides" then
              return some ("dedup:hides", s!"{m}: Elle reports {hidden} without the duplicated reads; the answer: {ans.types}")
          | _ => pure ()
        | .error _ => pure ()
  -- per key
  if c.perKey && !skip "perkey" then
    let ops := h.toList
    match answerOf model "strict-serializable-per-key" false ops, answerOf model "strict-serializable" false ops with
    | .ok pk, .ok ss =>
      let is := if model == .listAppend then interpsListAppend h else interpsRegister h
      let txs := txnViews h
      if ss.valid == .true_ && pk.valid == .false_ && !skip "perkey:weaker" then
        return some ("perkey:weaker", s!"strict-serializable valid, per key invalid {pk.types}")
      if pk.valid == .false_ && satB txs is && !skip "perkey:soundness-b" then
        return some ("perkey:soundness-b", s!"per key invalid {pk.types}; an interpretation has no proscribed cycle with per-key real time")
      if pk.valid == .false_ && satA txs is && !skip "perkey:soundness-a" then
        return some ("perkey:soundness-a", s!"per key invalid {pk.types}; an interpretation is serializable with every key linearizable")
      if pk.valid == .true_ && !is.isEmpty && !satB txs is && !satA txs is && !skip "perkey:completeness" then
        return some ("perkey:completeness", s!"per key valid; no interpretation satisfies either reading")
    | _, _ => pure ()
  return none

structure Gen3 where
  h : History
  opened : List Op
  infoed : List Op
  dupd : List Op

def gen3 (c : Props2.Config2) : W Gen3 := do
  let h ← genHistory c.bounds
  let (opened, infoed) ← genOpen h
  let dupd ← if c.bounds.workload == .listAppend then genDup h.toList else pure h.toList
  return { h, opened, infoed, dupd }

def runOnce3 (c : Props2.Config2) (src : Source) : Ended × Option Gen3 :=
  match (gen3 c).run { source := src, limit := 400 } with
  | .ok g d => ({ taken := d.taken, violation := check c g.h g.opened g.infoed g.dupd }, some g)
  | .error _ d => ({ taken := d.taken, violation := none }, none)

/-! ## JSON lines, as a client sends them -/

def jsonVal : Val → String
  | .nil | .dead | .unborn => "null"
  | .int i => toString i
  | .list l => "[" ++ ",".intercalate (l.map toString) ++ "]"
  | .kmap l => "[" ++ ",".intercalate (l.map fun (k, v) => s!"[{k},{match v with | .int i => toString i | _ => "null"}]") ++ "]"

def jsonPred : Pred → String
  | .tru => "\"true\""
  | .eq n => s!"[\"=\",{n}]"
  | .mod m t => s!"[\"mod\",{m},{t}]"

def jsonMop (o : Op) (m : Mop) : String :=
  if o.f == .init then s!"[\"init\",{m.k},{jsonVal m.v}]" else
  match m.f with
  | .r => s!"[\"r\",{m.k},{jsonVal m.v}]"
  | .append => s!"[\"append\",{m.k},{jsonVal m.v}]"
  | .w => s!"[\"w\",{m.k},{jsonVal m.v}]"
  | .insert => s!"[\"insert\",{m.k},{jsonVal m.v}]"
  | .delete => s!"[\"delete\",{m.k},null]"
  | .rp => s!"[\"rp\",{jsonPred m.pred},{jsonVal m.v}]"

def jsonOp (o : Op) : String :=
  let t := match o.type with | .invoke => "invoke" | .ok => "ok" | .fail => "fail" | .info => "info"
  let f := if o.f == .init then "init" else "txn"
  s!"\{\"process\":{o.process},\"type\":\"{t}\",\"f\":\"{f}\",\"value\":[{",".intercalate (o.value.map (jsonMop o))}],\"time\":{o.index * 1000}}"

def ednEscape (s : String) : String := (s.replace "\\" "\\\\").replace "\"" "\\\""

end Elle.ServiceProps

namespace Elle.ServiceProps
open Elle Elle.Spec Elle.Service

/-- The two readings of strict-serializable-per-key part: `a` finishes before `b` begins (both
read key 0, never written), `c` spans both; `b` writes 1, which `c` reads; `c` writes 2, which `a`
reads. Serial order b, c, a; each key linearizable; but a -rt-> b (key 0 in common) closes a
cycle with b -wr-> c -wr-> a. -/
def perKeyParts : List Op := [
  { index := 0, type := .invoke, process := 2, value := [{ f := .r, k := 1, v := .nil }, { f := .w, k := 2, v := .int 1 }] },
  { index := 1, type := .invoke, process := 0, value := [{ f := .r, k := 0, v := .nil }, { f := .r, k := 2, v := .nil }] },
  { index := 2, type := .ok, process := 0, value := [{ f := .r, k := 0, v := .nil }, { f := .r, k := 2, v := .int 1 }] },
  { index := 3, type := .invoke, process := 1, value := [{ f := .r, k := 0, v := .nil }, { f := .w, k := 1, v := .int 1 }] },
  { index := 4, type := .ok, process := 1, value := [{ f := .r, k := 0, v := .nil }, { f := .w, k := 1, v := .int 1 }] },
  { index := 5, type := .ok, process := 2, value := [{ f := .r, k := 1, v := .int 1 }, { f := .w, k := 2, v := .int 1 }] }]

def perKeyReport : String :=
  let h := perKeyParts.toArray
  let is := interpsRegister h
  let txs := txnViews h
  let ans := Service.check .register "strict-serializable-per-key" false perKeyParts
  let ser := Service.check .register "serializable" false perKeyParts
  let a := match ans with | .ok a => s!"{a.valid.str} {a.types}" | .error e => e
  let b := match ser with | .ok a => s!"{a.valid.str} {a.types}" | .error e => e
  s!"interpretations {is.length}; reading (a) serializable and each key linearizable: {satA txs is}; reading (b) no cycle with per-key real time: {satB txs is}; service per key: {a}; service serializable: {b}"

end Elle.ServiceProps

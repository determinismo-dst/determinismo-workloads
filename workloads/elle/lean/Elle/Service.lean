import Elle.ListAppend
import Elle.RwRegister
import Elle.ClosedPredicate
import Elle.SpecOpts

/-!
# The service (elle_service.clj, a public platform's checkers/elle at b8f9cc9)

What touches a verdict, function by function:

- `operation`/`mop` (69-87): a JSON line to an op. Parsing is checked end to end against the real
  service (`runner/service.clj`); here an op is already parsed.
- `closed` (100-108): invocations left open (by process, the last one) appended as `:info`.
- `duplicates`/`deduplicated` (139-157): list reads holding a value twice, each read deduplicated
  (first occurrences kept) before Elle judges; the verdict then forced invalid with
  `:duplicate-elements` added to the types (`:not` left as Elle computed it).
- `judged` (211-219): `:consistency-models [m]`, `:linearizable-keys? true` when asked; for
  `strict-serializable-per-key`, `:strict-serializable` with `elle/realtime-graph` redefined to
  `realtime-per-key-graph` (`Opts.perKey`).
- the answer (221-247): `valid`, `anomaly_types`, `not`.
-/

namespace Elle.Service

open Elle Elle.Spec Elle.SpecOpts

inductive Model where | listAppend | register | closedPredicate
  deriving Repr, BEq, Inhabited

/-- `closed` (elle_service.clj:100): the last open invocation of each process, in process order
(a sorted map), appended as `:info`; ops reindexed in order (`history/history`). -/
def closed (ops : List Op) : List Op :=
  let open_ : List (Nat × Op) := ops.foldl (fun m o =>
    if o.isInvoke then amPut (m.filter (·.1 != o.process)) o.process o
    else m.filter (·.1 != o.process)) []
  let added := (open_.mergeSort fun a b => decide (a.1 ≤ b.1)).map fun (_, o) => { o with type := .info }
  let all := ops ++ added
  (all.zip (List.range all.length)).map fun (o, i) => { o with index := i }

/-- `duplicates` (elle_service.clj:139): `:ok` ops' list reads holding a value twice. -/
def duplicates (ops : List Op) : List (Nat × Nat × List Int) :=
  ops.filter Op.isOk |>.flatMap fun o => o.value.filterMap fun m =>
    match m.f, m.v with
    | .r, .list l => if l.length != (dedup l).length then
        some (o.index, m.k, dedup (l.filter fun x => (l.filter (· == x)).length > 1)) else none
    | _, _ => none

/-- `deduplicated` (elle_service.clj:151): every list read with `distinct` values. -/
def deduplicated (ops : List Op) : List Op :=
  ops.map fun o => { o with value := o.value.map fun m =>
    match m.f, m.v with
    | .r, .list l => { m with v := .list (dedup l) }
    | _, _ => m }

/-- The deployed service's `deduplicated` (service-5fc908e/src/elle_service.clj:164-190, D17's
fix): each `:ok` read holding a value twice is dropped from its completion and from its
invocation (the process's open one, by position). -/
def deduplicatedFixed (ops : List Op) : List Op := Id.run do
  let dup (m : Mop) : Bool := m.f == .r && (match m.v with
    | .list l => l.length != (dedup l).length
    | _ => false)
  let mut openInv : List (Nat × Nat) := []
  let mut drops : List (Nat × List Nat) := []
  let mut i := 0
  for o in ops do
    if o.isInvoke then openInv := amPut openInv o.process i
    else
      let js := if o.isOk then ((o.value.zip (List.range o.value.length)).filter (dup ·.1)).map (·.2) else []
      if !js.isEmpty then
        drops := amPut drops i js
        if let some j := openInv.lookup o.process then drops := amPut drops j js
      openInv := openInv.filter (·.1 != o.process)
    i := i + 1
  return (ops.zip (List.range ops.length)).map fun (o, i) =>
    match drops.lookup i with
    | some js => { o with value := ((o.value.zip (List.range o.value.length)).filter (!js.contains ·.2)).map (·.1) }
    | none => o

/-- The deployed service's switches: Elle's patched namespaces (service-5fc908e/src/elle: D3, D9,
D10, D11, D13, D14) and the service's own changes (D16, D17, D19). -/
def deployedOpts : Opts := { fixD3 := true, fixD13 := true, cpFixed := true, perKeyFixed := true }

structure Answer where
  valid : Valid
  types : List String
  not_ : List String
  deriving Repr, Inhabited

/-- The checker a model names, with `result-map`'s boundary (txn.clj:1028: over every anomaly
found). -/
def judge (model : Model) (opts : Opts) (h : History) : Outcome :=
  let an := match model with
    | .listAppend => ListAppend.analyze h (additionalGraphs opts) {} false opts.cuts (ListAppend.fxOf opts)
    | .register => RwRegister.analyze opts h (additionalGraphs opts)
    | .closedPredicate => ClosedPredicate.analyzeOpts opts h (additionalGraphs opts)
  match an with
  | .error e => .thrown e
  | .ok m => .result (resultMap opts m true)

/-- `check` (elle_service.clj:221) on parsed operations. -/
def check (model : Model) (consistency : String) (linearizableKeys : Bool) (ops : List Op)
    (deployed : Bool := false) (base : Opts := {}) : Except String Answer := do
  let ops := closed ops
  let twice := if model == .listAppend then duplicates ops else []
  let h := (if twice.isEmpty then ops else if deployed then deduplicatedFixed ops else deduplicated ops).toArray
  let perKey := consistency == "strict-serializable-per-key"
  let base := if deployed then { base with fixD3 := true, fixD13 := true, cpFixed := true, perKeyFixed := true } else base
  let model1 := if perKey then "strict-serializable" else consistency
  let opts : Opts := { base with models := some [model1], linearizableKeys := linearizableKeys, perKey := perKey }
  match judge model opts h with
  | .thrown e => throw e
  | .result r =>
    if twice.isEmpty then return { valid := r.valid, types := r.anomalyTypes, not_ := r.boundary.1 }
    else
      let types := dedup (r.anomalyTypes ++ ["duplicate-elements"])
      -- the deployed service: `not` is the boundary of the answer's types (elle_service.clj:263-265)
      return { valid := .false_, types,
               not_ := if deployed then (Model.friendlyBoundary types).1 else r.boundary.1 }

/-! ## strict-serializable-per-key, as the service states it (elle_service.clj:17-20)

"Elle's strict serializability with real-time order only between operations touching a key in
common, i.e. serializable and each key linearizable":

- (b) the first half: no proscribed cycle in an interpretation's DSG with real-time edges only
  between transactions touching a common key;
- (a) the second half: the DSG serializable, and each key linearizable (`SpecOpts`). -/

/-- Transactions touching a common key. -/
def shareKey (a b : TxnV) : Bool := a.mops.any fun m => b.mops.any (·.k == m.k)

/-- An interpretation's DSG with real time only between transactions sharing a key. -/
def perKeyDsg (txs : List TxnV) (i : Interp) : Graph :=
  let g : Graph := { i.dsg with edges := i.dsg.edges.filterMap fun (a, b, r) =>
    let r' := Rels.diff r Rels.REALTIME
    if r' == 0 then none else some (a, b, r') }
  let committed := i.dsg.verts
  txs.foldl (fun g a =>
    if a.status != .ok then g else
    txs.foldl (fun g b =>
      if a.id == b.id || !committed.contains b.id || !(a.cmp < b.inv) || !shareKey a b then g
      else g.link a.id b.id Rels.REALTIME) g) g

def strictPhen : List String := (proscribed.lookup "strict-serializable").getD []
def serialPhen : List String := (proscribed.lookup "serializable").getD []

/-- Reading (b): some interpretation shows none of strict serializability's phenomena with
per-key real time. -/
def satB (txs : List TxnV) (is : List Interp) : Bool :=
  is.any fun i =>
    let other := i.phen.filter fun p => !(p.endsWith "-realtime" || p.endsWith "-process" ||
      p.startsWith "G0" || p.startsWith "G1c" || p.startsWith "G-single" || p.startsWith "G2" ||
      p.startsWith "G-nonadjacent")
    let phen := allCyclePhen (perKeyDsg txs i) ++ other
    !(phen.any strictPhen.contains)

/-- Reading (a): some interpretation is serializable with every key linearizable. -/
def satA (txs : List TxnV) (is : List Interp) : Bool :=
  is.any fun i => !(i.phen.any serialPhen.contains) && linearizableKeys txs i

end Elle.Service

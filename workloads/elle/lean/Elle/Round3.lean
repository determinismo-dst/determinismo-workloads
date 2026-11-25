import Elle.ServiceProps
import Elle.CPSpec
import Elle.Props3

/-!
# Round 3: the deployed service, and round 3's fixes, against the specification

Every property a history breaks is listed (no early return).

- **The deployed service** (service-5fc908e: Elle 0.2.8 with the patched namespaces of
  `src/elle/`, and `elle_service.clj`'s own changes), against Elle 0.2.8 as written and against
  the specification: a model the service rejects while Elle 0.2.8 doesn't must be violated in
  every interpretation (`deployed:new-false-positive` otherwise); no exception on a well-formed
  history; what it catches and still misses, counted.
- **Each round-3 fix**, against the deployed Elle (its base) and the specification: no new false
  positive, no regression, no exception; each anomaly type the fix newly reports holds in every
  (clean) interpretation; what it catches and what it drops, counted.
- **strict-serializable-per-key** (D18's reading (b), with D19's fix): the closure of the deployed
  per-key real-time graph equals the closure of real-time precedence between operations sharing a
  key (an init's keys are its map's keys; a predicate read shares every key).

List-append and rw-register histories are judged over every interpretation (`Spec`), closed
predicate under the checker's own reading (`CPSpec`), with a predicate read's rows as item reads
where D21's fix is judged.
-/

namespace Elle.Round3

open Elle Elle.Spec Elle.SpecOpts Elle.Gen Elle.Props Elle.Service Determinismo

def validOf : Outcome → Option Valid
  | .result r => some r.valid
  | .thrown _ => none

def typesOf : Outcome → List String
  | .result r => r.anomalyTypes
  | .thrown _ => []

/-- The specification's verdict. `rows`: a predicate read's rows are item reads (D21). -/
def specOf (model : Service.Model) (h : History) (is : List Interp) (m : String) (rows : Bool := false) :
    SpecVerdict :=
  match model with
  | .closedPredicate =>
    -- a predicate read that returned no row of a key every version of which matches is an
    -- observed anomaly (closed_predicate.clj:342), which PL-3 proscribes directly
    -- (consistency_model.clj:426-431); CPSpec's DSG doesn't model it
    let miss := !(ClosedPredicate.predReadMissCases (ClosedPredicate.allVersions h.toList) h.toList).isEmpty &&
      (Model.anomaliesProhibitedBy [m]).contains "predicate-read-miss"
    if miss || CPSpec.violates h m rows then .unsat else .sat
  | _ => Spec.verdict is m

/-- A base and a changed checker's verdicts on one model, against the specification. `pfx` names
the property family. -/
def compare (pfx m : String) (b f : Option Valid) (sv : SpecVerdict) : List (String × String) :=
  match b, f with
  | some _, none => [(pfx ++ ":throws", s!"{m}: the changed checker throws")]
  | none, none => []
  | none, some fv => [(pfx ++ ":no-longer-throws", s!"{m}: {fv.str}")]
  | some bv, some fv =>
    (if fv == .false_ && bv != .false_ && sv == .sat then
      [(pfx ++ ":new-false-positive", s!"{m}: was {bv.str}, now invalid; an interpretation satisfies {m}")] else []) ++
    (if bv == .false_ && fv != .false_ && sv == .unsat then
      [(pfx ++ ":regression", s!"{m}: was invalid, now {fv.str}; every interpretation violates {m}")] else []) ++
    (if bv != .false_ && fv == .false_ && sv == .unsat then
      [(pfx ++ ":caught", s!"{m}: was {bv.str}, now invalid; every interpretation violates {m}")] else []) ++
    (if bv != .false_ && fv == .false_ && sv == .none_ then
      [(pfx ++ ":caught-no-interpretation", s!"{m}: was {bv.str}, now invalid; no interpretation exists")] else []) ++
    (if bv == .false_ && fv != .false_ && sv == .sat then
      [(pfx ++ ":drops-false-positive", s!"{m}: was invalid, now {fv.str}; an interpretation satisfies {m}")] else []) ++
    (if fv == .false_ && sv == .sat then
      [(pfx ++ ":false-positive:" ++ m, s!"{m}: invalid; an interpretation satisfies {m}")] else []) ++
    (if fv == .true_ && sv == .unsat then
      [(pfx ++ ":misses:" ++ m, s!"{m}: valid; every interpretation violates {m}")] else [])

/-- What an anomaly type claims (round 1's `claimOf`), and round 3's new names: a fuzzy read is a
G-single in every clean interpretation; a future read and a garbage read have no interpretation. -/
def claim3 (t : String) : Option (List String × Bool) :=
  if t == "fuzzy-read" then some (["G-single", "G1c"], true)
  else if t == "future-read" || t == "garbage-read" then some ([], false)
  else claimOf t

/-- Each anomaly type in `ts` holds in every (clean) interpretation. -/
def claims (pfx : String) (is : List Interp) (ts : List String) : List (String × String) :=
  ts.filterMap fun t => match claim3 t with
    | none => none
    | some (ps, cleanOnly) =>
      let scope := is.filter fun i => !cleanOnly || i.clean
      match scope.find? (fun i => !(i.phen.any ps.contains)) with
      | some bad => some (pfx ++ ":false-claim:" ++ t,
          s!"reports {t}; an interpretation{if cleanOnly then " (clean)" else ""} without {ps}: {bad.phen}, order {bad.order}")
      | none => none

/-! ## The deployed service -/

/-- The deployed service against Elle 0.2.8 on a well-formed history (no open invocation, no
duplicated element), every model. -/
def deployedProps (model : Service.Model) (h : History) (models : List String) : List (String × String) :=
  let is := match model with
    | .listAppend => interpsListAppend h
    | .register => interpsRegister h
    | .closedPredicate => []
  models.flatMap fun m =>
    let e := Service.judge model { models := some [m] } h
    let d := Service.check model m false h.toList true
    let dv : Option Valid := match d with | .ok a => some a.valid | .error _ => none
    let sv := specOf model h is m
    let dtypes := match d with | .ok a => a.types | .error _ => []
    compare "deployed" m (validOf e) dv sv ++
    (if model == .closedPredicate then [] else
      claims "deployed" is (dtypes.filter fun t => !(typesOf e).contains t))

/-- The deployed service's closing (`closed`) and deduplication (`deduplicated`, `not`), as round 2's
`ServiceProps.check` checks them, the service deployed. -/
def deployedServiceProps (model : Service.Model) (h : History) (opened infoed dupd : List Op)
    (models : List String) : List (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  if opened.length != infoed.length then
    for m in models do
      let a := Service.check model m false opened true
      let b := Service.check model m false infoed true
      match a, b with
      | .ok x, .ok y =>
        if x.valid != y.valid then
          out := out.push ("closing:" ++ m, s!"closed at the end: {x.valid.str} {x.types}; :info in place: {y.valid.str} {y.types}")
      | .error e, _ => out := out.push ("closing:throws", s!"{m}: {e}")
      | _, _ => pure ()
  if model == .listAppend then
    let dups := Service.duplicates dupd
    if !dups.isEmpty then
      for m in models do
        match Service.check model m false dupd true with
        | .error e => out := out.push ("dedup:throws", s!"{m}: {e}")
        | .ok ans =>
          let want := (Model.friendlyBoundary ans.types).1
          if ans.not_ != want then
            out := out.push ("dedup:not", s!"{m}: types {ans.types}, not {ans.not_}; the boundary of those types: {want}")
          if ans.valid != .false_ then out := out.push ("dedup:valid", s!"{m}: {ans.valid.str}")
          -- without the duplicated reads: each read holding a value twice dropped from its
          -- completion (round 2 dropped every read of that key from it)
          let dupOps := dups.map (·.1)
          let twice (mo : Mop) : Bool := mo.f == .r && (match mo.v with
            | .list l => l.length != (dedup l).length
            | _ => false)
          let without := ServiceProps.reindex (dupd.map fun o => if dupOps.contains o.index then
            { o with value := o.value.filter fun mo => !twice mo } else o)
          match Service.judge model ({ Service.deployedOpts with models := some [m] }) without with
          | .result r =>
            let classes := ans.types.flatMap fun t => match Props.claimOf t with
              | some (ps, _) => if t.endsWith "-cycle-exists" then ps else []
              | none => []
            let sev := Model.bfs (fun a => Model.dagOut (Model.impliedAnomalies ++ Model.severityGraph) a)
            let implied := sev (ans.types ++ classes ++
              (classes.filter (·.startsWith "G1c")).map fun c => "G0" ++ (c.drop 3).toString)
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
            if !hidden.isEmpty then
              out := out.push ("dedup:hides", s!"{m}: Elle reports {hidden} without the duplicated reads; the answer: {ans.types}")
          | .thrown _ => pure ()
  return out.toList

/-! ## strict-serializable-per-key: reading (b), exactly -/

/-- The keys an operation touches as the stated definition has them: an init's map keys; a
predicate read every key (`none`). -/
def opKeys (o : Op) : Option (List Nat) :=
  if o.f == .init then some (o.value.map (·.k))
  else if o.value.any (·.f == .rp) then none
  else some (o.value.map (·.k))

/-- `a` (completed first) and `b` share a key, as the deployed service links them: a predicate
read precedes every later operation, an operation touching some key precedes every later
predicate read, and otherwise they need a key in common. (A predicate read is so also linked to a
later operation touching no key, an empty transaction; that operation is never linked onward and
has no data edge, so it changes no verdict.) -/
def sharesKey (a b : Op) : Bool :=
  match opKeys a, opKeys b with
  | none, _ => true
  | some x, none => !x.isEmpty
  | some x, some y => x.any y.contains

/-- Real-time precedence between operations sharing a key: an `:ok` completion before another
operation's invocation (to that operation's completion, as Elle links them). -/
def perKeyRelation (h : History) : List (Nat × Nat) :=
  let pairs := pairIndex h
  let comps := h.toList.filter fun o => !o.isInvoke
  comps.flatMap fun a => comps.filterMap fun b =>
    let inv := (pairs.lookup b.index).bind (h[·]?)
    match inv with
    | some i => if a.isOk && a.index != b.index && a.index < i.index && sharesKey a i then some (a.index, b.index) else none
    | none => none

/-- The closure of the deployed per-key graph equals the closure of that relation. -/
def perKeyExact (h : History) : Option String := Id.run do
  let g := (realtimePerKeyGraph h true).graph
  let rel := perKeyRelation h
  let r : Graph := rel.foldl (fun g (a, b) => g.link a b Rels.REALTIME) {}
  let comps := (h.toList.filter fun o => !o.isInvoke).map (·.index)
  for a in comps do
    let ga := reach g a
    let ra := reach r a
    for b in comps do
      if ga.contains b != ra.contains b then
        return some s!"{a} -> {b}: the per-key graph's closure {ga.contains b}, real time between operations sharing a key {ra.contains b}"
  return none

/-- The closed-predicate DSG with real time only between transactions sharing a key, under the
checker's reading (reading (b) for closed predicate). -/
def cpPerKeyViolates (h : History) : Bool :=
  let g := CPSpec.dsg h
  let g : Graph := { g with edges := g.edges.filterMap fun (a, b, r) =>
    let r' := Rels.diff r Rels.REALTIME
    if r' == 0 then none else some (a, b, r') }
  let rel := perKeyRelation h
  let committed := g.verts
  let g := rel.foldl (fun g (a, b) => if committed.contains a && committed.contains b then g.link a b Rels.REALTIME else g) g
  let dw := Rels.WW
  let dd := Rels.WW ||| Rels.WR ||| Rels.WRP
  let phen := CPSpec.cyclePhenP g dw dd "" ++
    CPSpec.cyclePhenP g (dw ||| Rels.PROCESS ||| Rels.REALTIME) (dd ||| Rels.PROCESS ||| Rels.REALTIME) "-realtime"
  phen.any (CPSpec.proscribedP "strict-serializable").contains

/-- Reading (b) as stated: real time, and so the process order within it, only between
transactions sharing a key (round 2's `Service.satB` kept every process edge). Some
interpretation shows none of strict serializability's phenomena. -/
def satBStated (h : History) (txs : List TxnV) (is : List Interp) : Bool :=
  let ops := h.toList
  let opOf (i : Nat) : Option Op := ops.find? (·.index == i)
  let share (a b : TxnV) : Bool := match opOf a.id, opOf b.id with
    | some x, some y => sharesKey x y
    | _, _ => false
  is.any fun i =>
    let g : Graph := { i.dsg with edges := i.dsg.edges.filterMap fun (a, b, r) =>
      let r' := Rels.diff (Rels.diff r Rels.REALTIME) Rels.PROCESS
      if r' == 0 then none else some (a, b, r') }
    let committed := i.dsg.verts
    let g := txs.foldl (fun g a =>
      if a.status != .ok then g else
      txs.foldl (fun g b =>
        if a.id == b.id || !committed.contains b.id || !(a.cmp < b.inv) || !share a b then g
        else g.link a.id b.id Rels.REALTIME) g) g
    let other := i.phen.filter fun p => !(p.endsWith "-realtime" || p.endsWith "-process" ||
      p.startsWith "G0" || p.startsWith "G1c" || p.startsWith "G-single" || p.startsWith "G2" ||
      p.startsWith "G-nonadjacent")
    !((allCyclePhen g ++ other).any strictPhen.contains)

/-- The deployed per-key model against reading (b): its graph exact; never invalid where (b)
holds; and where it passes a history every interpretation of which (b) rejects, counted. -/
def perKeyProps (model : Service.Model) (h : History) : List (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  if let some d := perKeyExact h then out := out.push ("perkey:graph", d)
  match Service.check model "strict-serializable-per-key" false h.toList true with
  | .error e => out := out.push ("perkey:throws", e)
  | .ok pk =>
    match model with
    | .closedPredicate =>
      let v := cpPerKeyViolates h
      if pk.valid == .false_ && !v then out := out.push ("perkey:soundness-b", s!"per key invalid {pk.types}; no proscribed cycle with per-key real time")
      if pk.valid == .true_ && v then out := out.push ("perkey:misses-b", s!"per key valid; a proscribed cycle with per-key real time")
    | _ =>
      let is := if model == .listAppend then interpsListAppend h else interpsRegister h
      let txs := txnViews h
      let b := satBStated h txs is
      if pk.valid == .false_ && b then out := out.push ("perkey:soundness-b", s!"per key invalid {pk.types}; an interpretation satisfies (b)")
      if pk.valid == .true_ && !is.isEmpty && !b then
        out := out.push ("perkey:misses-b", s!"per key valid; every interpretation has a proscribed cycle with per-key real time")
      if satB txs is != b then
        out := out.push ("perkey:round2-reading-b-differs", s!"round 2's (b), with every process edge: {satB txs is}; as stated: {b}")
      match Service.check model "strict-serializable" false h.toList true with
      | .ok ss => if ss.valid == .true_ && pk.valid == .false_ then out := out.push ("perkey:stricter-than-ss", s!"{pk.types}")
      | .error _ => pure ()
  return out.toList

/-! ## Round 3's fixes -/

/-- A fix's switches on top of the deployed Elle. -/
structure Fix where
  name : String
  opts : Opts → Opts

def fixes : List Fix := [
  ⟨"d1", fun o => { o with fixD1 := true }⟩, ⟨"d2", fun o => { o with fixD2 := true }⟩,
  ⟨"d4", fun o => { o with fixD4 := true }⟩, ⟨"d5", fun o => { o with fixD5 := true }⟩,
  ⟨"d6", fun o => { o with fixD6 := true }⟩, ⟨"d7", fun o => { o with fixD7 := true }⟩,
  ⟨"d8", fun o => { o with fixD8 := true }⟩, ⟨"d12", fun o => { o with fixD12 := true }⟩,
  ⟨"d20", fun o => { o with fixD20 := true }⟩, ⟨"d21", fun o => { o with fixD21 := true }⟩,
  ⟨"d22", fun o => { o with fixD22 := true }⟩,
  ⟨"all", fun o => { o with fixD1 := true, fixD2 := true, fixD4 := true, fixD5 := true, fixD6 := true,
                            fixD7 := true, fixD8 := true, fixD12 := true, fixD20 := true, fixD21 := true,
                            fixD22 := true }⟩]

def fixOf (names : List String) : Opts → Opts :=
  fun o => names.foldl (fun o n => match fixes.find? (·.name == n) with
    | some f => f.opts o
    | none => o) o

/-- A fix's properties on one history: each model set (a list of models, for D2's pairs) checked
by the deployed Elle and by the deployed Elle with the fix. -/
def fixProps (model : Service.Model) (fx : Opts → Opts) (h : History) (sets : List (List String))
    (rows : Bool := false) (baseOf : Opts := Service.deployedOpts) (fixedOf : Opts := Service.deployedOpts) :
    List (String × String) :=
  let is := match model with
    | .listAppend => interpsListAppend h
    | .register => interpsRegister h
    | .closedPredicate => []
  sets.flatMap fun ms =>
    let base : Opts := { baseOf with models := some ms }
    let b := Service.judge model base h
    let f := Service.judge model (fx { fixedOf with models := some ms }) h
    let name := " ".intercalate ms
    -- a model set's verdict against the specification: violated in every interpretation iff some
    -- interpretation-wise every one violates one of the models
    let sv : SpecVerdict := match model with
      | .closedPredicate => if ms.any (fun m => CPSpec.violates h m rows) then .unsat else .sat
      | _ =>
        if is.isEmpty then .none_
        else if is.any (fun i => ms.all fun m => !(i.phen.any ((proscribed.lookup m).getD []).contains)) then .sat
        else .unsat
    compare "fix" name (validOf b) (validOf f) sv ++
    (if model == .closedPredicate then [] else
      claims "fix" is ((typesOf f).filter fun t => !(typesOf b).contains t))

/-- The history with every list element `e` renamed `1000 - e` (a bijection on values). -/
def renamed (h : History) : History :=
  h.map fun o => { o with value := o.value.map fun m =>
    match m.v with
    | .int e => if m.f == .append then { m with v := .int (1000 - e) } else m
    | .list l => { m with v := .list (l.map (1000 - ·)) }
    | _ => m }

/-- D12's property: renaming values changes no verdict (order independence). -/
def renameProps (fx : Opts → Opts) (h : History) (models : List String) : List (String × String) :=
  let h' := renamed h
  models.flatMap fun m =>
    let base : Opts := { Service.deployedOpts with models := some [m] }
    let f1 := validOf (Service.judge .listAppend (fx base) h)
    let f2 := validOf (Service.judge .listAppend (fx base) h')
    let b1 := validOf (Service.judge .listAppend base h)
    let b2 := validOf (Service.judge .listAppend base h')
    (if f1 != f2 then [("rename:fixed:" ++ m, s!"{m}: {repr f1} renamed {repr f2}")] else []) ++
    (if b1 != b2 then [("rename:deployed:" ++ m, s!"{m}: {repr b1} renamed {repr b2}")] else [])

/-- Model sets: each model alone, and (for D2) each session model beside each real-time one. -/
def modelSets (models : List String) (pairs : Bool) : List (List String) :=
  models.map ([·]) ++ (if !pairs then [] else
    (models.filter (·.startsWith "strong-session")).flatMap fun a =>
      (models.filter fun m => m.startsWith "strong-read" || m == "strict-serializable" || m == "strong-snapshot-isolation").map
        fun b => [a, b])

end Elle.Round3

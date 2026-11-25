import Elle.Props
import Elle.SpecOpts

/-!
# Round 2's properties: rw-register's options, and the cycle search's time limit

A timeline decides a history (round 1's generator), and with `:transaction-order` the order
itself: a permutation of the `:ok` and `:info` completions, each `:info` one in the map or not.
-/

namespace Elle.Props2

open Elle Elle.Spec Elle.SpecOpts Elle.Gen Elle.Props Determinismo

structure Config2 where
  bounds : Bounds := { workload := .register }
  lin : Bool := false
  seq : Bool := false
  wfr : Bool := false
  order : Bool := false
  /-- The service's per-key real-time graph (strict-serializable-per-key). -/
  perKey : Bool := false
  models : List String := specModels
  skip : List String := []
  /-- Check every cut point of every SCC's cycle search. -/
  timeouts : Bool := false
  /-- Only histories whose transactions read each key at most once (D6 masked). -/
  singleReads : Bool := false
  /-- Only histories where no `:info` write is read (D13 masked). -/
  noInfoReads : Bool := false
  /-- `:info` completions never in the transaction order (D14 masked). -/
  orderNoInfo : Bool := false
  /-- The follow-ups' fixes. -/
  fixD3 : Bool := false
  fixD13 : Bool := false
  deriving Inhabited

def isLA (c : Config2) : Bool := c.bounds.workload == .listAppend

/-- The order map: completions of `:ok` and `:info` transactions, permuted; an `:info` one kept
or not. -/
def genOrder (h : History) (noInfo : Bool := false) : W (List (Nat × Int)) := do
  let cs := (h.toList.filter fun o => o.isOk || o.isInfo).map (·.index)
  let p ← genPerm "order.perm" cs.length
  let mut out : List (Nat × Int) := []
  let mut place : Int := 0
  for j in p do
    let i := cs.getD j 0
    let keep ← if (h[i]?.map Op.isInfo).getD false then
      (if noInfo then pure false else do pure ((← dec "order.info" 2) == 0)) else pure true
    if keep then out := out ++ [(i, place)]
    place := place + 1
  return out

def optsOf (c : Config2) (ord : Option (List (Nat × Int))) : Opts :=
  { wfrKeys := c.wfr, sequentialKeys := c.seq, linearizableKeys := c.lin, txnOrder := ord,
    perKey := c.perKey, fixD3 := c.fixD3, fixD13 := c.fixD13 }

def assumeOf (c : Config2) (ord : Option (List (Nat × Int))) : Assume :=
  { lin := c.lin || c.perKey, seq := c.seq, wfr := c.wfr, order := ord }

def analyze2 (c : Config2) (opts : Opts) (h : History) (e : Extra) (o : Order := {}) : Except String Anomalies :=
  if isLA c then ListAppend.analyze h e o false opts.cuts else RwRegister.analyze opts h e o

def analysis2 (c : Config2) (opts : Opts) (h : History) (e : Extra) : Except String Analysis :=
  if isLA c then ListAppend.analysis h e else RwRegister.graphWith opts e h

def verdictOf (opts : Opts) (anM : String → Except String Anomalies) (m : String) : Except String Valid := do
  let o : Opts := { opts with models := some [m] }
  let ms ← anM m
  return (resultMap o ms).valid

def specVerdict (is : List Interp) (m : String) : SpecVerdict := verdict is m

/-- Cut points of each SCC's search, for these options. -/
def cutSpace (an : Analysis) (o : Order := {}) : List Nat :=
  (sccs an.graph o).map fun scc => cutPoints (sccSearches (an.graph.select scc) o an)

def readsInfoWrite (h : History) : Bool :=
  let infoW := h.toList.filter Op.isInfo |>.flatMap fun o =>
    o.value.filterMap fun m => if m.f == .w || m.f == .append then some (m.k, m.v) else none
  h.toList.filter Op.isOk |>.any fun o => o.value.any fun m =>
    m.f == .r && infoW.any fun (k, v) => k == m.k &&
      (match m.v, v with
       | .int a, .int b => a == b
       | .list l, .int b => l.contains b
       | _, _ => false)

/-- Every two transactions touching a common key are ordered by `before` (their completions
known): the option's order alone fixes each key's version order. -/
def totalPerKey (h : History) (before : TxnV → TxnV → Bool) : Bool :=
  let txs := (txnViews h).filter fun t => t.status != .fail
  let keys := dedup (txs.flatMap fun t => t.mops.map (·.k))
  keys.all fun k =>
    let ts := txs.filter fun t => t.mops.any (·.k == k)
    ts.all fun a => ts.all fun b => a.id == b.id || before a b || before b a

def checkHistory2 (c : Config2) (h : History) (ord : Option (List (Nat × Int))) : Found := Id.run do
  let skip (k : String) := c.skip.contains k || c.skip.any fun s => k.startsWith (s ++ ":")
  if c.singleReads && !(h.toList.all fun o => o.value.all fun m =>
      m.f != .r || (o.value.filter fun m' => m'.f == .r && m'.k == m.k).length ≤ 1) then return none
  if c.noInfoReads && readsInfoWrite h then return none
  let opts := optsOf c ord
  let aN := analyze2 c opts h .none
  let aR := analyze2 c opts h .realtime
  let extras := dedup (c.models.map fun m => additionalGraphs { opts with models := some [m] })
  let memo : List (Extra × Except String Anomalies) := extras.map fun e => (e, analyze2 c opts h e)
  let an (e : Extra) : Except String Anomalies :=
    match memo.find? (·.1 == e) with | some (_, r) => r | none => analyze2 c opts h e
  -- with D13's fix, rw-register's graph depends on the models (whether they prohibit G1a)
  let anM (m : String) : Except String Anomalies :=
    let o : Opts := { opts with models := some [m] }
    if c.fixD13 && !isLA c then analyze2 c o h (additionalGraphs o) else an (additionalGraphs o)
  if !skip "thrown" then
    if let .error e := aR then return some ("thrown", s!"Elle throws: {e}")
  let is := if isLA c then interpsListAppend h else interpsRegister h
  let txs := txnViews h
  let asm := assumeOf c ord
  let isA := is.filter (asm.holds txs)
  -- 1. Each source's inferred version order holds wherever its assumption does.
  if !isLA c && !skip "inference" then
    for (src, vgs) in RwRegister.sources opts h do
      let a : Option Assume := match src with
        | "linearizable-keys" => some { lin := true }
        | "sequential-keys" => some { seq := true }
        | "transaction-order-keys" => some { order := ord }
        | "wfr-keys" => some { wfr := true }
        | "initial-state" => some {}
        | _ => none
      let some a := a | continue
      let scope := is.filter (a.holds txs)
      for (k, es) in vgs do
        for (v1, v2) in es do
          if let some bad := scope.find? (fun i => !edgeHolds txs i k v1 v2) then
            return some ("inference:" ++ src,
              s!"{src} infers {ednVal v1} < {ednVal v2} on key {k}; an interpretation where the assumption holds has the opposite: order {bad.order}, reads {bad.reads}")
  -- 2. Verdicts against the specification, under the options' assumption.
  for m in c.models do
    let ev := verdictOf opts anM m
    let svAll := specVerdict is m
    let svA := specVerdict isA m
    match ev with
    | .ok .false_ =>
      if svA == .sat && !skip ("soundness:" ++ m) then
        return some ("soundness:" ++ m, s!"Elle: {m} invalid; an interpretation satisfies {m} and the options' assumption")
    | .ok .true_ =>
      if svAll == .unsat && !skip ("completeness:" ++ m) then
        return some ("completeness:" ++ m, s!"Elle: {m} valid; specification: {svAll.str}")
      let total := (c.lin && totalPerKey h rtBefore) || (c.seq && totalPerKey h procBefore)
      if total && svA == .unsat && !skip ("completeness-total:" ++ m) then
        return some ("completeness-total:" ++ m,
          s!"Elle: {m} valid; the option's order fixes every key's versions, and every interpretation where its assumption holds violates {m}")
      if svAll != .unsat && svA == .unsat && !skip ("completeness-assumed:" ++ m) then
        return some ("completeness-assumed:" ++ m,
          s!"Elle: {m} valid; every interpretation where the options' assumption holds violates {m} (some do hold it)")
    | _ => pure ()
  -- 2b. A fix against Elle as written: no verdict turns invalid where an interpretation
  -- satisfies the model, none turns valid where every interpretation violates it.
  if c.fixD3 || c.fixD13 then
    let base := { opts with fixD3 := false, fixD13 := false }
    let baseAnM (m : String) : Except String Anomalies :=
      let o : Opts := { base with models := some [m] }
      analyze2 c o h (additionalGraphs o)
    for m in c.models do
      match verdictOf base baseAnM m, verdictOf opts anM m with
      | .ok b, .ok f =>
        let sv := specVerdict isA m
        if b != .false_ && f == .false_ && sv == .sat && !skip "fix:new-false-positive" then
          return some ("fix:new-false-positive", s!"{m}: Elle as written {b.str}, fixed invalid; an interpretation satisfies it")
        if b == .false_ && f != .false_ && sv == .unsat && !skip "fix:regression" then
          return some ("fix:regression", s!"{m}: Elle as written invalid, fixed {f.str}; specification {sv.str}")
        if b == .false_ && f != .false_ && sv == .sat && !skip "fix:drops-false-positive" then
          return some ("fix:drops-false-positive", s!"{m}: Elle as written invalid, fixed {f.str}; an interpretation satisfies it")
        if b != .false_ && f == .false_ && sv != .sat then
          if !skip "fix:caught" then pure ()
      | .ok _, .error e => if !skip "fix:throws" then return some ("fix:throws", s!"{m}: the fixed Elle throws {e}")
      | _, _ => pure ()
  -- 3. A cyclic version order claims the assumptions cannot all hold.
  if !skip "claim" then
    if let .ok m := aN then
      if (m.lookup "cyclic-versions").isSome then
        if let some bad := isA.head? then
          return some ("claim:cyclic-versions",
            s!"Elle reports cyclic-versions; an interpretation satisfies the options' assumption: order {bad.order}, reads {bad.reads}")
  -- 4. The cycle search's time limit, cut at every point of every SCC's search.
  if c.timeouts then
    for e in extras do
      let some a := (analysis2 c opts h e).toOption | continue
      let space := cutSpace a
      let full := an e
      let mut i := 0
      for pts in space do
        for cut in List.range (pts + 1) do
          let o2 := { opts with cuts := [(i, cut)] }
          let mc := analyze2 c o2 h e
          for m in c.models do
            let o3 : Opts := { o2 with models := some [m] }
            if additionalGraphs o3 != e then continue
            match mc, full with
            | .ok ms, .ok mf =>
              let v := (resultMap o3 ms).valid
              let vf := (resultMap o3 mf).valid
              if v == .true_ && !skip "timeout:valid" then
                return some ("timeout:valid", s!"{m}: :valid? true with the search of SCC {i} cut at {cut}")
              if v == .false_ && vf != .false_ && specVerdict isA m == .sat && !skip "timeout:soundness" then
                return some ("timeout:soundness",
                  s!"{m}: invalid only when SCC {i}'s search is cut at {cut} ({(resultMap o3 ms).anomalyTypes}); an interpretation satisfies it")
            | .ok _, .error err =>
              if !skip "timeout:masks-exception" then
                return some ("timeout:masks-exception", s!"{m}: Elle throws ({err}) unless SCC {i}'s search is cut at {cut}")
            | .error err, .ok _ =>
              if !skip "timeout:throws" then
                return some ("timeout:throws", s!"{m}: the fallback throws ({err}) when SCC {i}'s search is cut at {cut}")
            | _, _ => pure ()
        i := i + 1
  return none

def runOnce2 (c : Config2) (src : Source) : Ended × Option (History × Option (List (Nat × Int))) :=
  let d : Decisions := { source := src, limit := 400 }
  let gen : W (History × Option (List (Nat × Int))) := do
    let h ← genHistory c.bounds
    let ord ← if c.order then (do pure (some (← genOrder h c.orderNoInfo))) else pure none
    pure (h, ord)
  match gen.run d with
  | .ok (h, ord) d' => ({ taken := d'.taken, violation := checkHistory2 c h ord }, some (h, ord))
  | .error _ d' => ({ taken := d'.taken, violation := none }, none)

def run2 (c : Config2) (src : Source) : Ended := (runOnce2 c src).1

end Elle.Props2

namespace Elle.Props2
open Elle Elle.Spec Elle.Gen Determinismo

/-- For the report: over seeds, how many SCC searches, cut points, and the verdicts at those cuts
(false / unknown / true), and how many verdicts changed from the uncut one. -/
def timeoutStats (c : Config2) (seeds first : Nat) : List (String × Nat) := Id.run do
  let mut st : List (String × Nat) := []
  for i in List.range seeds do
    let d : Decisions := { source := Source.seeded (first + i), limit := 400 }
    match (genHistory c.bounds).run d with
    | .error _ _ => pure ()
    | .ok h _ =>
      let opts := optsOf c none
      for e in [Extra.none, .process, .realtime] do
        let some a := (analysis2 c opts h e).toOption | continue
        let space := cutSpace a
        st := amUpdate st "sccs" 0 (· + space.length)
        let full := analyze2 c opts h e
        let mut j := 0
        for pts in space do
          for cut in List.range (pts + 1) do
            st := amUpdate st "cuts" 0 (· + 1)
            let mc := analyze2 c { opts with cuts := [(j, cut)] } h e
            for m in c.models do
              let o3 : Opts := { opts with models := some [m] }
              if additionalGraphs o3 != e then continue
              match mc, full with
              | .ok ms, .ok mf =>
                let v := (resultMap o3 ms).valid
                let vf := (resultMap o3 mf).valid
                st := amUpdate st s!"verdict {v.str}" 0 (· + 1)
                if v != vf then st := amUpdate st s!"changed {vf.str} -> {v.str}" 0 (· + 1)
              | .ok _, .error _ => st := amUpdate st "exception masked" 0 (· + 1)
              | .error _, .ok _ => st := amUpdate st "exception added" 0 (· + 1)
              | _, _ => st := amUpdate st "exception both" 0 (· + 1)
          j := j + 1
  return st

end Elle.Props2

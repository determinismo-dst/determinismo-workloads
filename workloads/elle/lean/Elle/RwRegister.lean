import Elle.Txn

/-!
# elle.rw-register (rw_register.clj)

Reads `[:r k v]`, writes `[:w k v]` of unique values; `nil` is the initial state. Version graphs
per key are inferred from the initial state (always), a given transaction order
(`:transaction-order`), writes-follow-reads (`:wfr-keys?`), the process order
(`:sequential-keys?`) and the real-time order (`:linearizable-keys?`), in that order
(rw_register.clj:647-702).
-/

namespace Elle.RwRegister

open Elle

def isW (f : F) : Bool := f == .w

/-- `op-internal-case` (rw_register.clj:77). -/
def opInternalCase (o : Op) : Bool := Id.run do
  let mut st : List (Nat × Val) := []
  for m in o.value do
    match m.f with
    | .w => st := amPut st m.k m.v
    | .r =>
      match st.lookup m.k with
      | some s => if !(s == m.v) then return true
      | none => st := amPut st m.k m.v
    | _ => pure ()
  return false

/-- D6's fix: every read of a key not preceded in its transaction by a write of that key (the
first is `ext-reads`'s; the others are just as external). -/
def allExtReads (txn : List Mop) : List (Nat × Val) := Id.run do
  let mut written : List Nat := []
  let mut out : List (Nat × Val) := []
  for m in txn do
    match m.f with
    | .w => if !written.contains m.k then written := written ++ [m.k]
    | .r => if !written.contains m.k then out := out ++ [(m.k, m.v)]
    | _ => pure ()
  return out

/-- D6's fix: an `:ok` transaction's external reads of one key returning two values (a fuzzy,
non-repeatable read: Berenson et al.'s P2). In every clean interpretation one of the two values
precedes the other, so the transaction anti-depends on the version after the first value it
read, which precedes (or is) the second's writer: a G-single-item. -/
def fuzzyReadCases (h : List Op) : List Nat :=
  (oks h).filterMap fun o =>
    let rs := allExtReads o.value
    if rs.any (fun (k, v) => rs.any fun (k', v') => k == k' && !(v == v')) then some o.index else none

/-- D7's fix: an `:ok` transaction reading a value it writes later itself (values are unique, so
it read its own future write): `:future-read`, which Elle's lattice takes as a G1c
(consistency_model.clj:142-147), as list-append reports it. -/
def futureReadCases (h : List Op) : List Nat :=
  (oks h).filterMap fun o =>
    let ms := o.value.zip (List.range o.value.length)
    if ms.any (fun (m, i) => m.f == .r && m.v != .nil &&
        ms.any fun (m', j) => i < j && m'.f == .w && m'.k == m.k && m'.v == m.v)
    then some o.index else none

/-- `g1a-cases` (rw_register.clj:110). -/
def g1aCases (h : List Op) : List (Nat × Nat) :=
  let failed := failedWriteIndices isW h
  (oks h).flatMap fun o => o.value.filterMap fun m =>
    if m.f != .r then none else ((failed.lookup m.k).bind (·.lookup m.v)).map (o.index, ·)

/-- `g1b-cases` (rw_register.clj:136). -/
def g1bCases (h : List Op) : List (Nat × Nat) :=
  let im := intermediateWriteIndices isW h
  (oks h).flatMap fun o => o.value.filterMap fun m =>
    if m.f != .r then none else
    match (im.lookup m.k).bind (·.lookup m.v) with
    | some w => if w != o.index then some (o.index, w) else none
    | none => none

/-- `ext-index` (rw_register.clj:164): key -> value -> ok ops (only `:ok`; with D13's fix,
`:info` ops too, for external writes). -/
def extIndex (ext : List Mop → List (Nat × Val)) (h : List Op) (withInfo : Bool := false) : List (Nat × List (Val × List Nat)) :=
  (if withInfo then possible h else oks h).foldl (fun idx o => (ext o.value).foldl (fun idx (k, v) =>
    amUpdate idx k [] (amUpdate · v [] (· ++ [o.index]))) idx) []

abbrev VGraphs := List (Nat × List (Val × Val))

def vgLink (vgs : VGraphs) (k : Nat) (a b : Val) : VGraphs :=
  amUpdate vgs k [] fun es => if es.any (fun (x, y) => x == a && y == b) then es else es ++ [(a, b)]

/-- `initial-state-version-graphs` (rw_register.clj:184). -/
def initialStateVersionGraphs (h : List Op) (fixD6 : Bool := false) : VGraphs :=
  h.foldl (fun vgs o =>
    if o.isInvoke || o.isFail then vgs else
    -- D6's fix: every external read's value (nil precedes it, as each first read's)
    let kvs := extWrites o.value ++ (if o.isOk then (if fixD6 then allExtReads else extReads) o.value else [])
    kvs.foldl (fun vgs (k, v) => if v == .nil then vgs else vgLink vgs k .nil v) vgs) []

/-- `wfr-version-graphs` (rw_register.clj:255). -/
def wfrVersionGraphs (h : List Op) : VGraphs :=
  (oks h).foldl (fun vgs o =>
    let ws := extWrites o.value
    (extReads o.value).foldl (fun vgs (k, v) =>
      if v == .nil then vgs else
      match ws.lookup k with
      | some v' => vgLink vgs k v v'
      | none => vgs) vgs) []

/-- A key's version graph as a `Graph` over value ids, and the id table. -/
def vgToGraph (es : List (Val × Val)) : Graph × List Val :=
  let vs := es.foldl (fun acc (a, b) =>
    let acc := if acc.contains a then acc else acc ++ [a]
    if acc.contains b then acc else acc ++ [b]) ([] : List Val)
  let id (v : Val) := (vs.findIdx? (· == v)).getD 0
  (es.foldl (fun g (a, b) => g.link (id a) (id b) 0) {}, vs)

/-- `cyclic-version-cases` (rw_register.clj:624). -/
def cyclicVersionCases (vgs : VGraphs) : List Nat :=
  vgs.filterMap fun (k, es) => if (sccs (vgToGraph es).1).isEmpty then none else some k

def mergeVG (a b : VGraphs) : VGraphs :=
  b.foldl (fun acc (k, es) => es.foldl (fun acc (x, y) => vgLink acc k x y) acc) a

/-! ## Version orders from a transaction order (rw_register.clj:210-253) -/

/-- Clojure's `compare` on a `:version`: `nil` before every number. -/
def cmpVersion (a b : Option Int) : Bool :=
  match a, b with
  | none, _ => true
  | some _, none => false
  | some x, some y => x ≤ y

/-- `key-writes-version-sorted` (rw_register.clj:210): each key's external writes of `:ok` and
`:info` ops, `conj`ed onto a list (so newest first), then sorted stably by version. -/
def keyWritesVersionSorted (h : List Op) (order : List (Nat × Int)) : List (Nat × List Val) :=
  let m : List (Nat × List (Val × Option Int)) := h.foldl (fun m o =>
    if o.isInvoke || o.isFail then m else
    let version := order.lookup o.index
    (extWrites o.value).foldl (fun m (k, v) => amUpdate m k [] ((v, version) :: ·)) m) []
  m.map fun (k, vs) => (k, (vs.mergeSort fun a b => cmpVersion a.2 b.2).map (·.1))

/-- `transaction-order-graphs` (rw_register.clj:234): successive writes linked. -/
def transactionOrderGraphs (h : List Op) (order : List (Nat × Int)) : VGraphs :=
  (keyWritesVersionSorted h order).foldl (fun vgs (k, vs) =>
    (vs.zip (vs.drop 1)).foldl (fun vgs (a, b) => vgLink vgs k a b) (amUpdate vgs k [] id)) []

/-! ## Version orders from a transaction graph (rw_register.clj:278-622) -/

/-- `ext-keys` (rw_register.clj:278): keys of an `:ok` op's external reads and writes, of an
`:info` op's external writes. -/
def extKeys (o : Op) : List Nat :=
  if o.isOk || o.isInfo then
    dedup ((if o.isOk then (extReads o.value).map (·.1) else []) ++ (extWrites o.value).map (·.1))
  else []

/-- An external key graph: op -> key -> downstream ops. -/
abbrev KG := List (Nat × List (Nat × List Nat))

def setUnion (a b : List Nat) : List Nat := a ++ b.filter (!a.contains ·)
def setDiff (a b : List Nat) : List Nat := a.filter (!b.contains ·)

def inN (g : Graph) (v : Nat) : List Nat := (g.edges.filter (·.2.1 == v)).map (·.1)

/-- `ext-key-graph-search-op` (rw_register.clj:313): per key, the direct successors touching it,
and through the others their own downstream sets; then those shadowed (reachable through a
direct successor touching the key) removed. -/
def searchOp (g : Graph) (o : Order) (keysOf : Nat → List Nat) (kg : KG) (op : Nat) : KG := Id.run do
  let mut shadowed : List (Nat × List Nat) := []
  let mut reachable : List (Nat × List Nat) := []
  for op2 in g.out o op do
    let directKs := keysOf op2
    let indirect := (kg.lookup op2).getD []
    for k in directKs do
      shadowed := amUpdate shadowed k [] (setUnion · ((indirect.lookup k).getD []))
    let ours := directKs.foldl (fun m k => amPut m k [op2]) indirect
    for (k, st) in ours do
      reachable := amUpdate reachable k [] (setUnion · st)
  for (k, sh) in shadowed do
    if let some st := reachable.lookup k then reachable := amPut reachable k (setDiff st sh)
  return amPut kg op reachable

/-- `ext-key-graph-condense` (rw_register.clj:377): once every upstream op is known, an op keeps
only the keys it touched. -/
def condense (g : Graph) (keysOf : Nat → List Nat) (kg : KG) (op : Nat) : KG :=
  if (inN g op).all fun u => (kg.lookup u).isSome then
    match kg.lookup op with
    | some m => amPut kg op (m.filter fun (k, _) => (keysOf op).contains k)
    | none => kg
  else kg

/-- `ext-key-graph-search` (rw_register.clj:397): a stack of pending ops; an op is explored once
all its successors are. -/
def kgSearch (g : Graph) (o : Order) (keysOf : Nat → List Nat) (kg0 : KG) (pending0 : List Nat) : KG := Id.run do
  let mut kg := kg0
  let mut pending := pending0
  let mut fuel := 4 * (g.verts.length + 2) * (g.edges.length + g.verts.length + 2)
  while fuel > 0 do
    fuel := fuel - 1
    match pending.getLast? with
    | none => return kg
    | some op =>
      if (kg.lookup op).isSome then pending := pending.dropLast
      else
        let mut ready := true
        let mut pending' := pending
        for op2 in g.out o op do
          if (kg.lookup op2).isNone then
            pending' := pending' ++ [op2]
            ready := false
        if ready then
          kg := searchOp g o keysOf kg op
          kg := (g.out o op).foldl (condense g keysOf) kg
          pending := pending'.dropLast
        else pending := pending'
  return kg

/-- `ext-key-graph` (rw_register.clj:432): vertices in reverse index order. -/
def extKeyGraph (g : Graph) (o : Order) (keysOf : Nat → List Nat) : KG :=
  ((sortNat g.verts).reverse).foldl (fun kg op =>
    condense g keysOf (kgSearch g o keysOf kg [op]) op) []

/-- The reducer of `transaction-graph->version-graphs`'s fold (rw_register.clj:545-604) on one
entry of the external key graph: for op `a`, each key and downstream op `b`, `a`'s final value
of the key (an `:ok` op's external write, else its external read, `nil` when it has neither; an
`:info` op's external write) before `b`'s first (an `:ok` op's external read when not `nil`, else
its external write, else `nil`; an `:info` op's external write). -/
def vgOfEntry (h : History) (entry : Nat × List (Nat × List Nat)) : VGraphs := Id.run do
  let (a, downstream) := entry
  let some oa := h[a]? | return []
  let wa := extWrites oa.value
  let ra := extReads oa.value
  let mut vgs : VGraphs := []
  for (k, bs) in downstream do
    let v1 : Option Val :=
      if oa.isOk then some ((wa.lookup k).getD ((ra.lookup k).getD .nil))
      else if oa.isInfo then wa.lookup k
      else none
    let some v1 := v1 | continue
    for b in bs do
      let some ob := h[b]? | continue
      let v : Option Val :=
        if ob.isOk then
          let r := (extReads ob.value).lookup k
          some (match r with
            | some (.int i) => .int i
            | _ => ((extWrites ob.value).lookup k).getD .nil)
        else if ob.isInfo then (extWrites ob.value).lookup k
        else none
      match v with
      | some v => if !(v == v1) then vgs := vgLink vgs k v1 v
      | none => pure ()
  return vgs

/-- The external key graph of a transaction graph (`ext-key-graph`, rw_register.clj:432). -/
def kgOf (h : History) (g : Graph) (o : Order := {}) : KG :=
  extKeyGraph g o fun i => ((h[i]?).map extKeys).getD []

/-- `transaction-graph->version-graphs` (rw_register.clj:464): the fold's reducer on every entry
of the external key graph, combined by union (rw_register.clj:606-613). -/
def txnGraphToVersionGraphs (h : History) (g : Graph) (o : Order := {}) : VGraphs :=
  (kgOf h g o).foldl (fun vgs e => mergeVG vgs (vgOfEntry h e)) []

/-- The real-time graph Elle's `:linearizable-keys?` reads: `elle/realtime-graph`, or under the
service's `with-redefs`, its per-key graph. -/
def realtimeFor (opts : Opts) (h : History) : Graph :=
  if opts.perKey then (realtimePerKeyGraph h).graph else (realtimeGraph h).graph

/-- Each version-graph source of `version-graphs` (rw_register.clj:652-673), in order. -/
def sources (opts : Opts) (h : History) (o : Order := {}) : List (String × VGraphs) :=
  let hl := h.toList
  [("initial-state", initialStateVersionGraphs hl opts.fixD6)] ++
  (match opts.txnOrder with
   | some ord => [("transaction-order-keys", transactionOrderGraphs hl ord)]
   | none => []) ++
  (if opts.wfrKeys then [("wfr-keys", wfrVersionGraphs hl)] else []) ++
  (if opts.sequentialKeys then [("sequential-keys", txnGraphToVersionGraphs h (processGraph h).graph o)] else []) ++
  (if opts.linearizableKeys then [("linearizable-keys", txnGraphToVersionGraphs h (realtimeFor opts h) o)] else [])

/-- `version-graphs` (rw_register.clj:647): sources merged in order, one that makes a cycle
skipped and its cycles recorded (with the sources so far and its own). -/
def versionGraphsFull (opts : Opts) (h : History) (o : Order := {}) :
    VGraphs × List (Nat × List String) := Id.run do
  let mut graphs : VGraphs := []
  let mut used : List String := []
  let mut cyc : List (Nat × List String) := []
  for (name, a) in sources opts h o do
    let graphs' := mergeVG graphs a
    let cs := cyclicVersionCases graphs'
    if cs.isEmpty then
      graphs := graphs'
      used := used ++ [name]
    else cyc := cyc ++ cs.map (·, used ++ [name])
  return (graphs, cyc)

/-- `version-graphs` (rw_register.clj:647): the graphs, and whether a source made a cycle. -/
def versionGraphs (opts : Opts) (h : History) (o : Order := {}) : VGraphs × Bool :=
  let (g, c) := versionGraphsFull opts h o
  (g, !c.isEmpty)

def idxGet (idx : List (Nat × List (Val × List Nat))) (k : Nat) (v : Val) : List Nat :=
  ((idx.lookup k).bind (·.lookup v)).getD []

/-- The versions reachable from `v` in key `k`'s version graph, `v` included. -/
def vgReach (vgs : VGraphs) (k : Nat) (v : Val) : List Val := Id.run do
  let es := (vgs.lookup k).getD []
  let mut seen : List Val := [v]
  let mut queue : List Val := [v]
  let mut fuel := es.length + 2
  while !queue.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let next := queue.flatMap fun x => (es.filter (·.1 == x)).map (·.2)
    let fresh := dedup (next.filter fun y => !seen.contains y)
    seen := seen ++ fresh
    queue := fresh
  return seen

/-- D1's fix, the register form: (reader, writer, key) where an edge v1 -> v2 of key `k`'s version
graph gives the reader of v1 an rw edge to v2's writer, the reader also writes `k` (its final
write v3), and v2 and v3 are unordered in that graph: the reader's write came first (`ww`), or the
version after v1 came before it (a G-single through the reader). -/
def unreadPairsRR (h : List Op) (vgs : VGraphs) (fixD13 fixD6 : Bool) : List (Nat × Nat × Nat) :=
  let er := extIndex (if fixD6 then allExtReads else extReads) h
  let ew := extIndex extWrites h fixD13
  let writeOf (i : Nat) (k : Nat) : Option Val :=
    (h.find? (·.index == i)).bind fun o => (extWrites o.value).lookup k
  dedup <| vgs.flatMap fun (k, es) => es.flatMap fun (v1, v2) =>
    (idxGet er k v1).flatMap fun r => (idxGet ew k v2).filterMap fun w =>
      if r == w then none else
      match writeOf r k with
      | some v3 =>
        if v3 == v2 || (vgReach vgs k v3).contains v2 || (vgReach vgs k v2).contains v3 then none
        else some (r, w, k)
      | none => none

/-- `version-graphs->transaction-graph` (rw_register.clj:704). -/
def versionGraphsToTxnGraph (h : List Op) (vgs : VGraphs) (fixD13 : Bool := false) (g1a : Bool := false)
    (fixD6 : Bool := false) (unread : List (Nat × Nat × Nat) := []) : Graph := Id.run do
  let er := extIndex (if fixD6 then allExtReads else extReads) h
  let ew := extIndex extWrites h fixD13
  -- D13's fix: an :info writer whose write an :ok read saw committed in every clean
  -- interpretation; for models prohibiting G1a its ww edges hold wherever the model can.
  let readVals : List (Nat × Val) := (oks h).flatMap fun o => (o.value.filter (·.f == .r)).map fun m => (m.k, m.v)
  let observed (o : Op) : Bool := o.isInfo && (extWrites o.value).any fun (k, v) => readVals.any fun (k', v') => k == k' && v == v'
  let isOkOp (i : Nat) : Bool := h.any fun o => o.index == i && (o.isOk || (g1a && observed o))
  let mut g : Graph := {}
  for (k, es) in vgs do
    for (v1, v2) in es do
      let v1r := idxGet er k v1
      -- D13's fix: ww edges only out of acknowledged writers
      let v1w := (idxGet ew k v1).filter isOkOp
      let v2w := idxGet ew k v2
      g := g.linkAllToAll v1w v2w Rels.WW
      g := if unread.isEmpty then g.linkAllToAll v1r v2w Rels.RW
        else v1r.foldl (fun g r => v2w.foldl (fun g w =>
          if unread.contains (r, w, k) then g else g.link r w Rels.RW) g) g
      g := g.removeSelfEdges (dedup (v1r ++ v1w ++ v2w))
  return g

/-- `explain-op-deps` (rw_register.clj:737). -/
def explainOpDeps (vgs : VGraphs) (aKvs bKvs : List (Nat × Val)) : Option Nat :=
  aKvs.findSome? fun (k, av) =>
    match vgs.lookup k, bKvs.lookup k with
    | some es, some bv => if es.any (fun (x, y) => x == av && y == bv) then some k else none
    | _, _ => none

/-- D13's fix: a version written only by `:info` ops is stepped over: each predecessor also
precedes each successor (to a fixpoint). -/
def stepOverInfo (h : List Op) (vgs : VGraphs) : VGraphs := Id.run do
  let ew := extIndex extWrites h true
  let infoOnly (k : Nat) (v : Val) : Bool :=
    let ws := idxGet ew k v
    !ws.isEmpty && ws.all fun i => h.any fun o => o.index == i && o.isInfo
  let mut out := vgs
  for (k, _) in vgs do
    let mut changed := true
    let mut fuel := 50
    while changed && fuel > 0 do
      fuel := fuel - 1
      changed := false
      let es := (out.lookup k).getD []
      for (a, b) in es do
        if infoOnly k b then
          for (b', c) in es do
            if b' == b && !(c == a) && !es.any (fun (x, y) => x == a && y == c) then
              out := vgLink out k a c
              changed := true
  return out

/-- `wr-graph` (rw_register.clj:833); `none`: a value written by two ops (Elle throws). -/
def wrGraph (h : List Op) (fixD13 : Bool := false) (fixD6 : Bool := false) : Option Graph := do
  let ew := extIndex extWrites h fixD13
  let er := extIndex (if fixD6 then allExtReads else extReads) h
  let mut g : Graph := {}
  for (k, vr) in er do
    for (v, readers) in vr do
      let ws := idxGet ew k v
      match ws with
      | [] => pure ()
      | [w] => g := readers.foldl (fun g r => g.link w r Rels.WR) g
      | _ => none
  return g

/-- `graph` (rw_register.clj:879): wr, then ww+rw, then the extra order. -/
def graphWith (opts : Opts) (extra : Extra) (h : History) (unreadPass : Bool := false) :
    Except String Analysis := do
  let hl := h.toList
  let some gwr := wrGraph hl opts.fixD13 opts.fixD6 | throw "IllegalArgumentException: value written by more than one op"
  let (vgs, cyclic) := versionGraphs opts h
  let vgs := if opts.fixD13 then stepOverInfo hl vgs else vgs
  -- D1's second pass: each unread pair a `ww` step instead of `rw`
  let unread := if unreadPass then unreadPairsRR hl vgs opts.fixD13 opts.fixD6 else []
  let isUnread (a b k : Nat) : Bool := unread.contains (a, b, k)
  let tg := versionGraphsToTxnGraph hl vgs opts.fixD13 ((prohibitedAnomalyTypes opts).contains "G1a") opts.fixD6 unread
  let mops (b : Nat) := (h[b]?.map (·.value)).getD []
  let reads := if opts.fixD6 then allExtReads else extReads
  let explainWr : Nat → Nat → Option Step := fun a b =>
    let ws := extWrites (mops a)
    let rs := reads (mops b)
    ws.findSome? fun (k, v) => if rs.any (fun (k', v') => k == k' && v == v') then some { type := "wr", key := some k } else none
  let explainWwRw : Nat → Nat → Option Step := fun a b =>
    match explainOpDeps vgs (extWrites (mops a)) (extWrites (mops b)) with
    | some k => some { type := "ww", key := some k }
    | none =>
      let rs := reads (mops a)
      -- with D6's fix every external read is tried, each alone (a key may be read twice)
      (rs.findSome? fun r => match explainOpDeps vgs [r] (extWrites (mops b)) with
        | some k => if isUnread a b k then none else some k
        | none => none).map fun k =>
        ({ type := "rw", key := some k } : Step)
  let wr : Analysis := { graph := gwr, explain := explainWr }
  let wwrw : Analysis := { graph := tg, explain := explainWwRw,
                           anomalies := if cyclic then [("cyclic-versions", [])] else [] }
  if unread.isEmpty then return combine ([wr, wwrw] ++ extraAnalysesOf extra h)
  let gun : Graph := unread.foldl (fun g (r, w, _) => g.link r w Rels.WW) ({} : Graph)
  let explainUn : Nat → Nat → Option Step := fun a b =>
    (unread.find? fun (r, w, _) => r == a && w == b).map fun (_, _, k) =>
      ({ type := "ww", key := some k, unread := true } : Step)
  let un : Analysis := { graph := gun, explain := explainUn }
  return combine ([wr, wwrw, un] ++ extraAnalysesOf extra h)

def graph (opts : Opts) (h : History) : Except String Analysis := graphWith opts (additionalGraphs opts) h

/-- `elle.rw-register/check` (rw_register.clj:909) up to `result-map`. -/
def analyze (opts : Opts) (h : History) (extra : Extra) (o : Order := {}) : Except String Anomalies := do
  let hl := h.toList
  let g1a := g1aCases hl
  let g1b := g1bCases hl
  let internal := (oks hl).filter opInternalCase
  let lost := lostUpdateCases isW hl
  let an ← graphWith opts extra h
  let m ← cyclesE an o opts.cuts opts.fixD20
  -- D1's fix (register form): the G-singles through unread pairs, from a second search
  let m ← if !opts.fixD1 then pure m else do
    let vgs := (versionGraphs opts h).1
    let vgs := if opts.fixD13 then stepOverInfo hl vgs else vgs
    if (unreadPairsRR hl vgs opts.fixD13 opts.fixD6).isEmpty then pure m else
    let an2 ← graphWith opts extra h true
    let m2 ← cyclesE an2 o [] opts.fixD20
    let retyped : List (String × Case) := m2.flatMap fun (t, cs) => cs.filterMap fun c =>
      match c with
      | .cycle ops steps =>
        let v := if t.endsWith "-realtime" then "-realtime" else if t.endsWith "-process" then "-process" else ""
        let base := String.ofList (t.toList.take (t.length - v.length))
        let t' := if steps.any (·.unread) && (base == "G0" || base == "G1c") then "G-single-item" ++ v else t
        some (t', c)
      | _ => none
    pure (retyped.foldl (fun m (t, c) =>
      let have_ := (m.lookup t).getD []
      if have_.any (fun c' => match c, c' with | .cycle a _, .cycle b _ => a == b | _, _ => false) then m
      else addCases m t [c]) m)
  let m := addCases m "internal" (internal.map fun o => Case.other [o.index])
  let m := addCases m "G1a" (g1a.map fun (r, w) => Case.other [r, w])
  let m := addCases m "G1b" (g1b.map fun (r, w) => Case.other [r, w])
  let m := addCases m "lost-update" (lost.map fun (_, _, ts) => Case.other ts)
  let m := if opts.fixD6 then addCases m "fuzzy-read" ((fuzzyReadCases hl).map fun i => Case.other [i]) else m
  let m := if opts.fixD7 then addCases m "future-read" ((futureReadCases hl).map fun i => Case.other [i]) else m
  return m

/-- `elle.rw-register/check` (rw_register.clj:909). -/
def check (opts : Opts) (h : History) (o : Order := {}) : Outcome :=
  match analyze opts h (additionalGraphs opts) o with
  | .error e => .thrown e
  | .ok m => .result (resultMap opts m)

end Elle.RwRegister

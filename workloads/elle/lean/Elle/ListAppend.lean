import Elle.Txn

/-!
# elle.list-append (list_append.clj)

Reads `[:r k v]` return a vector (or `nil`); appends `[:append k e]` add a unique element.
-/

namespace Elle.ListAppend

open Elle

def isAppend (f : F) : Bool := f == .append

def Val.toList : Val → List Int
  | .list l => l
  | _ => []

/-- `(peek v)` of a read value: the last element, or `none` for `nil` and `[]`. -/
def peekV (v : Val) : Option Int := (Val.toList v).getLast?

/-- `verify-mop-types` (list_append.clj:40): only reads and appends. -/
def verifyMopTypes (h : List Op) : Option String :=
  if h.any (fun o => o.value.any fun m => m.f != .r && m.f != .append)
  then some ":unexpected-txn-micro-op-types" else none

/-- `verify-unique-appends` (list_append.clj:61): over invocations only. -/
def verifyUniqueAppends (h : List Op) : Option String := Id.run do
  let mut written : List (Nat × List Val) := []
  for o in h do
    if !o.isInvoke then continue
    for m in o.value do
      if m.f == .append then
        let ws := (written.lookup m.k).getD []
        if ws.contains m.v then return some ":duplicate-appends"
        written := amPut written m.k (ws ++ [m.v])
  return none

/-- `g1a-cases` (list_append.clj:83): an ok read containing an element a failed op appended. -/
def g1aCases (h : List Op) : List (Nat × Nat) :=
  let failed := failedWriteIndices isAppend h
  (oks h).flatMap fun o => o.value.flatMap fun m =>
    if m.f != .r then [] else
    match failed.lookup m.k with
    | none => []
    | some fk => (Val.toList m.v).filterMap fun e => (fk.lookup (.int e)).map fun w => (o.index, w)

/-- `g1b-cases` (list_append.clj:114): an ok read whose last element is another op's
intermediate append. -/
def g1bCases (h : List Op) : List (Nat × Nat) :=
  let im := intermediateWriteIndices isAppend h
  (oks h).flatMap fun o => o.value.filterMap fun m =>
    if m.f != .r then none else
    match peekV m.v with
    | none => none
    | some e =>
      match (im.lookup m.k).bind (·.lookup (.int e)) with
      | some w => if w != o.index then some (o.index, w) else none
      | none => none

/-- The expected state of a key inside a transaction (list_append.clj:150-185): a full list,
or a known suffix after an unknown prefix. `stored nil` is a read of `nil`. -/
inductive Expect where
  | full (l : List Int)
  | suffix (l : List Int)
  | readNil
  deriving Repr, BEq

/-- `op-int-case` (list_append.clj:158). -/
def opIntCase (o : Op) : Bool := Id.run do
  let mut st : List (Nat × Expect) := []
  for m in o.value do
    match m.f with
    | .append =>
      let e := match m.v with | .int i => i | _ => 0
      let s' := match st.lookup m.k with
        | some (.full l) => Expect.full (l ++ [e])
        | some (.suffix l) => Expect.suffix (l ++ [e])
        | some .readNil => Expect.full [e]
        | none => Expect.suffix [e]
      st := amPut st m.k s'
    | .r =>
      let bad := match st.lookup m.k with
        | none => false
        | some (.suffix l) =>
          let v := Val.toList m.v
          -- i = (inc (count v)) - (count s), s = ['... ++ l]
          if v.length + 1 < l.length + 1 then true
          else l != v.drop (v.length - l.length)
        | some (.full l) => match m.v with
          | .list v => l != v
          | _ => true
        | some .readNil => match m.v with
          | .nil => false
          | _ => true
      if bad then return true
      st := amPut st m.k (match m.v with | .list v => .full v | _ => .readNil)
    | _ => pure ()
  return false

/-- `op-future-read-case` (list_append.clj:187). -/
def opFutureReadCase (o : Op) : Bool := Id.run do
  let mut reads : List (Nat × List Int) := []
  for m in o.value do
    match m.f with
    | .append =>
      if let .int e := m.v then
        if ((reads.lookup m.k).getD []).contains e then return true
    | .r => reads := amUpdate reads m.k [] (· ++ Val.toList m.v)
    | _ => pure ()
  return false

/-- `values-from-single-appends` (list_append.clj:247). -/
def valuesFromSingleAppends (h : List Op) : List (Nat × List (List Int)) :=
  let m := h.foldl (fun (acc : List (Nat × Option Int)) o => o.value.foldl (fun acc mo =>
    if mo.f != .append then acc
    else if (acc.lookup mo.k).isSome then amPut acc mo.k none
    else amPut acc mo.k (match mo.v with | .int e => some e | _ => none)) acc) []
  m.filterMap fun (k, v) => v.map fun e => (k, [[e]])

/-- `sorted-values` (list_append.clj:271): per key, distinct non-empty read values by length.
Ties keep the order of Clojure's hash set of values (replicated), reversed when `flip`. -/
def sortedValues (h : List Op) (flip : Bool := false) : List (Nat × List (List Int)) :=
  let fromReads := h.foldl (fun (acc : List (Nat × List (List Int))) o => o.value.foldl (fun acc m =>
    match m.f, m.v with
    | .r, .list v => if v.isEmpty then acc else amUpdate acc m.k [] fun vs => if vs.contains v then vs else vs ++ [v]
    | _, _ => acc) acc) []
  let single := valuesFromSingleAppends h
  let merged := single.foldl (fun acc (k, v) => if (acc.lookup k).isSome then acc else acc ++ [(k, v)]) fromReads
  merged.map fun (k, vs) =>
    -- the read values' set, in Clojure's hash-set order (`datafy` of a Bifurcan set)
    let vs := Hash.vectorsOrder vs
    let vs := if flip then vs.reverse else vs
    (k, vs.mergeSort fun a b => decide (a.length ≤ b.length))

/-- `prefix?` (list_append.clj:237). -/
def isPrefix (a b : List Int) : Bool := a.length ≤ b.length && a == b.take a.length

/-- `incompatible-orders` (list_append.clj:318). -/
def incompatibleOrders (sv : List (Nat × List (List Int))) : List Nat :=
  sv.filterMap fun (k, vs) =>
    if (vs.zip (vs.drop 1)).any (fun (a, b) => !isPrefix a b) then some k else none

/-- `duplicates` (list_append.clj:370): a read with an element twice. -/
def duplicates (h : List Op) : List Nat :=
  h.filterMap fun o =>
    if o.value.any (fun m => m.f == .r && (let l := Val.toList m.v; l.length != (dedup l).length))
    then some o.index else none

/-- `append-index` (list_append.clj:392): the longest value's distinct elements. -/
def appendIndex (sv : List (Nat × List (List Int))) : List (Nat × List Int) :=
  sv.map fun (k, vs) => (k, dedup (vs.getLast?.getD []))

/-- `write-index` (list_append.clj:415): key -> element -> the (last) non-invoke op appending. -/
def writeIndex (h : List Op) : List (Nat × List (Int × Nat)) :=
  h.foldl (fun idx o => if o.isInvoke then idx else
    o.value.foldl (fun idx m => match m.f, m.v with
      | .append, .int e => amUpdate idx m.k [] (amPut · e o.index)
      | _, _ => idx) idx) []

def wiGet (wi : List (Nat × List (Int × Nat))) (k : Nat) (e : Int) : Option Nat :=
  (wi.lookup k).bind (·.lookup e)

/-- `dirty-update-cases` (list_append.clj:434). `none`: the `(assert t2 ..)` fails, which Elle
throws. -/
def dirtyUpdateCases (ai : List (Nat × List Int)) (h : History) : Option (List Nat) := do
  let wi := writeIndex h.toList
  let mut cases : List Nat := []
  for (k, vs) in ai do
    let mut t1 : OpType := .ok
    for v in vs do
      let t2i ← wiGet wi k v
      let t2 := (h[t2i]?.map (·.type)).getD .ok
      match t1, t2 with
      | .fail, .ok => cases := cases ++ [k]; t1 := t2
      | _, .ok => t1 := t2
      | _, .info => pure ()
      | .fail, .fail => pure ()
      | _, .fail => t1 := t2
      | _, _ => pure ()
  return cases

/-- `read-index` (list_append.clj:486): key -> last element (`none` = `::init`) -> readers. -/
def readIndex (h : List Op) : List (Nat × List (Option Int × List Nat)) :=
  h.foldl (fun idx o => o.value.foldl (fun idx m =>
    if m.f == .r && !(o.isInfo && m.v == .nil) then
      amUpdate idx m.k [] (amUpdate · (peekV m.v) [] (· ++ [o.index]))
    else idx) idx) []

structure Pre where
  hist : History
  possible : List Op
  ai : List (Nat × List Int)
  wi : List (Nat × List (Int × Nat))
  ri : List (Nat × List (Option Int × List Nat))

/-- `previously-appended-element` (list_append.clj:517): `none` is `::init`. -/
def prevElem (p : Pre) (k : Nat) (e : Int) : Option Int :=
  let vs := (p.ai.lookup k).getD []
  match vs.findIdx? (· == e) with
  | some i => if 0 < i then vs[i - 1]? else none
  | none => vs.getLast?

/-- `ww-mop-dep` (list_append.clj:537). -/
def wwMopDep (p : Pre) (op : Nat) (k : Nat) (e : Int) : Option Nat :=
  match prevElem p k e with
  | none => none
  | some pe => match wiGet p.wi k pe with
    | some w => if w != op then some w else none
    | none => none

/-- `rw-mop-deps` (list_append.clj:550). -/
def rwMopDeps (p : Pre) (op : Nat) (k : Nat) (e : Int) : List Nat :=
  let pe := prevElem p k e
  (dedup (((p.ri.lookup k).bind (·.lookup pe)).getD [])).filter (· != op)

/-- `wr-mop-dep` (list_append.clj:506). -/
def wrMopDep (p : Pre) (op : Nat) (k : Nat) (v : Val) : Option Nat :=
  match peekV v with
  | none => none
  | some e => match wiGet p.wi k e with
    | some w => if w != op then some w else none
    | none => none

/-- `preprocess` (list_append.clj:582). -/
def preprocess (h : History) (flip : Bool) : Except String Pre := do
  if let some e := verifyMopTypes h.toList then throw e
  if let some e := verifyUniqueAppends h.toList then throw e
  let ps := possible h.toList
  let sv := sortedValues ps flip
  return { hist := h, possible := ps, ai := appendIndex sv, wi := writeIndex ps, ri := readIndex ps }

/-- `ww-graph`, `wr-graph`, `rw-graph` and their explainers (list_append.clj:618-759), combined
(list_append.clj:761). -/
def graph (p : Pre) : Analysis := Id.run do
  let mut gww : Graph := {}
  let mut gwr : Graph := {}
  let mut grw : Graph := {}
  for o in p.possible do
    for m in o.value do
      match m.f, m.v with
      | .append, .int e =>
        if let some d := wwMopDep p o.index m.k e then gww := gww.link d o.index Rels.WW
      | .r, v =>
        if let some d := wrMopDep p o.index m.k v then gwr := gwr.link d o.index Rels.WR
      | _, _ => pure ()
  for o in p.possible do
    for m in o.value do
      match m.f, m.v with
      | .append, .int e =>
        grw := (rwMopDeps p o.index m.k e).foldl (fun g d => g.link d o.index Rels.RW) grw
      | _, _ => pure ()
  let mops (b : Nat) := (p.hist[b]?.map (·.value)).getD []
  let ww : Analysis := { graph := gww, explain := fun a b => (mops b).findSome? fun m =>
      match m.f, m.v with
      | .append, .int e => if wwMopDep p b m.k e == some a then some { type := "ww", key := some m.k } else none
      | _, _ => none }
  let wr : Analysis := { graph := gwr, explain := fun a b => (mops b).findSome? fun m =>
      if m.f == .r && wrMopDep p b m.k m.v == some a then some { type := "wr", key := some m.k } else none }
  let rw : Analysis := { graph := grw, explain := fun a b => (mops b).findSome? fun m =>
      match m.f, m.v with
      | .append, .int e => if (rwMopDeps p b m.k e).contains a then some { type := "rw", key := some m.k } else none
      | _, _ => none }
  return combine [ww, wr, rw]

/-- `elle.list-append/check` (list_append.clj:920) up to `result-map`: every anomaly, with the
extra graph `extra` (what `additional-graphs` picks for the options). -/
def analyze (h : History) (extra : Extra) (o : Order := {}) (flip : Bool := false)
    (cuts : List (Nat × Nat) := []) : Except String Anomalies := do
  let hl := h.toList
  let g1a := g1aCases hl
  let g1b := g1bCases hl
  let okOps := oks hl
  let internal := okOps.filter opIntCase
  let future := okOps.filter opFutureReadCase
  let dirty := dirtyUpdateCases (appendIndex (sortedValues hl flip)) h
  let hp := possible hl
  let dups := duplicates hp
  let incmp := incompatibleOrders (sortedValues hp flip)
  let lost := lostUpdateCases isAppend hp
  let p ← preprocess h flip
  let an := combine ([graph p] ++ extraAnalysesOf extra h)
  let cyc ← cyclesE an o cuts
  let some dirty := dirty | throw "AssertionError: No transaction wrote k = v (dirty-update-cases)"
  let mut m := cyc
  m := addCases m "duplicate-elements" (dups.map fun i => Case.other [i])
  m := addCases m "incompatible-order" (incmp.map fun _ => Case.other [])
  m := addCases m "internal" (internal.map fun o => Case.other [o.index])
  m := addCases m "future-read" (future.map fun o => Case.other [o.index])
  m := addCases m "dirty-update" (dirty.map fun _ => Case.other [])
  m := addCases m "G1a" (g1a.map fun (r, w) => Case.other [r, w])
  m := addCases m "G1b" (g1b.map fun (r, w) => Case.other [r, w])
  m := addCases m "lost-update" (lost.map fun (_, _, ts) => Case.other ts)
  return m

/-- The analysis Elle runs for these options. -/
def analysis (h : History) (extra : Extra) (flip : Bool := false) : Except String Analysis := do
  let p ← preprocess h flip
  return combine ([graph p] ++ extraAnalysesOf extra h)

/-- `elle.list-append/check` (list_append.clj:920). -/
def check (opts : Opts) (h : History) (o : Order := {}) (flip : Bool := false) : Outcome :=
  match analyze h (additionalGraphs opts) o flip opts.cuts with
  | .error e => .thrown e
  | .ok m => .result (resultMap opts m)

end Elle.ListAppend

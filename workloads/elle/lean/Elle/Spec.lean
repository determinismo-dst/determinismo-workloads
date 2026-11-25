import Elle.Graph

/-!
# An independent specification: every Adya interpretation of an observation

Written from the definitions, not from Elle's code:

- Adya, Liskov, O'Neil, "Generalized Isolation Level Definitions" (ICDE 2000), and Adya's thesis
  "Weak Consistency" (1999): histories with a version order `<<` over installed versions, the
  DSG's ww, wr and rw edges, G0, G1a, G1b, G1c, G-single, G2-item, and PL-1, PL-2, PL-2+, PL-2.99,
  PL-3.
- Kingsbury and Alvaro, "Elle" (VLDB 2020), §4: observations, interpretations (an indeterminate
  transaction commits or aborts), list versions as traces (the version order consistent with the
  version graph: installed versions form a prefix chain), dirty updates (§4.1.5), and Theorem 1
  (non-cycle anomalies in every interpretation, cycle anomalies in every clean one).
- Cerone and Gotsman, "Analysing Snapshot Isolation" (PODC 2016), Theorem 10: SI is acyclicity of
  `(WR ∪ WW) ; RW?` (with session order for strong session SI); Cerone, Bernardi, Gotsman (CONCUR
  2015): the INT axiom.
- Daudjee and Salem (ICDE 2004, VLDB 2006): session and strong variants order a process's
  transactions, or all transactions in real time.

An interpretation chooses which indeterminate (`:info`) transactions committed, a total order of
installed versions per key, and the versions that committed indeterminate transactions read
(their results are unknown). In each, the DSG over committed transactions gets ww (successive
installed versions), wr (a read of an installed version) and rw (a read of a version, and the
installer of the next) edges, plus session (SO) and real-time (RT) edges from an acknowledged
transaction to a committed one invoked after it completed.
-/

namespace Elle.Spec

open Elle

/-- A transaction as observed: its completion's index (the vertex), status, process, and the
indices of its invocation and completion. -/
structure TxnV where
  id : Nat
  status : OpType
  process : Nat
  inv : Nat
  cmp : Nat
  mops : List Mop
  deriving Repr, Inhabited

def txnViews (h : History) : List TxnV :=
  let pairs := pairIndex h
  h.toList.filterMap fun o =>
    if o.isInvoke then none else
    some { id := o.index, status := o.type, process := o.process,
           inv := (pairs.lookup o.index).getD o.index, cmp := o.index, mops := o.value }

def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap fun p => (List.range (p.length + 1)).map fun i => p.take i ++ [x] ++ p.drop i

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (subsets xs).flatMap fun s => [s, x :: s]

/-- The phenomena of one interpretation. -/
structure Interp where
  phen : List String
  /-- No aborted read, intermediate read or dirty update (Elle §4.3.2). -/
  clean : Bool
  /-- The DSG with SO and RT edges, over committed transactions. -/
  dsg : Graph
  /-- Per key, the installed versions' writers in version order. -/
  order : List (Nat × List Nat)
  /-- External reads of installed versions: (reader, key, writer; `none` = initial version). -/
  reads : List (Nat × Nat × Option Nat)
  deriving Inhabited

/-! ## Phenomena from a DSG -/

def DW : Rels := Rels.WW
def DD : Rels := Rels.WW ||| Rels.WR

/-- The cycle phenomena with edges `d` (data dependencies plus SO/RT for variants) and `w` (write
dependencies plus SO/RT) and the anti-dependencies. -/
def cyclePhen (g : Graph) (w d : Rels) (suffix : String) : List String :=
  let gd := g.project d
  let rwEdges := (g.edges.filter fun (_, _, r) => Rels.inter r Rels.RW != 0).map fun (a, b, _) => (a, b)
  let gall := g.project (d ||| Rels.RW)
  let g0 := hasCycle (g.project w)
  let g1c := hasCycle gd
  let gsingle := rwEdges.any fun (a, b) => (reach gd b).contains a
  let g2 := rwEdges.any fun (a, b) => (reach gall b).contains a
  let gnonadj := hasCycle (Graph.seqExtension gd (g.project Rels.RW))
  (if g0 then ["G0" ++ suffix] else []) ++ (if g1c then ["G1c" ++ suffix] else []) ++
  (if gsingle then ["G-single" ++ suffix] else []) ++ (if g2 then ["G2" ++ suffix] else []) ++
  (if gnonadj then ["G-nonadjacent" ++ suffix] else [])

def allCyclePhen (g : Graph) : List String :=
  cyclePhen g DW DD "" ++
  cyclePhen g (DW ||| Rels.PROCESS) (DD ||| Rels.PROCESS) "-process" ++
  cyclePhen g (DW ||| Rels.PROCESS ||| Rels.REALTIME) (DD ||| Rels.PROCESS ||| Rels.REALTIME) "-realtime"

/-- SO and RT edges: an acknowledged transaction to a committed one invoked after it completed. -/
def orderEdges (g : Graph) (txs : List TxnV) (committed : List Nat) : Graph :=
  txs.foldl (fun g a =>
    if a.status != .ok then g else
    txs.foldl (fun g b =>
      if a.id == b.id || !committed.contains b.id || !(a.cmp < b.inv) then g
      else
        let g := g.link a.id b.id Rels.REALTIME
        if a.process == b.process then g.link a.id b.id Rels.PROCESS else g) g) g

/-- INT (Cerone et al. 2015): a read preceded by an operation on its key in the same
transaction returns that operation's outcome; for lists, a read after appends ends with them and
after a read and appends is that read plus them. -/
def intViolated (t : TxnV) : Bool := Id.run do
  -- per key: known full value, or known suffix
  let mut st : List (Nat × (Bool × Val)) := []
  for m in t.mops do
    match m.f with
    | .r =>
      match st.lookup m.k with
      | some (true, v) => if !(v == m.v) then return true
      | some (false, .list suf) =>
        match m.v with
        | .list l => if !(l.length ≥ suf.length && l.drop (l.length - suf.length) == suf) then return true
        | _ => return true
      | _ => pure ()
      st := amPut st m.k (true, m.v)
    | .append =>
      let e := match m.v with | .int i => i | _ => 0
      st := match st.lookup m.k with
        | some (true, .list l) => amPut st m.k (true, .list (l ++ [e]))
        | some (true, .nil) => amPut st m.k (true, .list [e])
        | some (false, .list s) => amPut st m.k (false, .list (s ++ [e]))
        | _ => amPut st m.k (false, .list [e])
    | .w => st := amPut st m.k (true, m.v)
    | _ => pure ()
  return false

/-! ## List append -/

/-- The appends of `t` to `k`, in order. -/
def apps (t : TxnV) (k : Nat) : List Int :=
  t.mops.filterMap fun m => if m.f == .append && m.k == k then (match m.v with | .int e => some e | _ => none) else none

/-- A read decomposed into its trace's writes: (writer, number of its appends), in order. `none`:
no write produced it (an unknown element, a write's elements out of order, a writer twice). -/
def decompose (owner : Int → Option (Nat × Nat)) (appsOf : Nat → List Int) (l : List Int) :
    Option (List (Nat × Nat)) := do
  let mut segs : List (Nat × Nat) := []
  for e in l do
    let (w, pos) ← owner e
    match segs.getLast? with
    | some (w', n) =>
      if w' == w then
        if pos != n then none
        segs := segs.dropLast ++ [(w, n + 1)]
      else
        if pos != 0 || segs.any (·.1 == w) then none
        segs := segs ++ [(w, 1)]
    | none =>
      if pos != 0 then none
      segs := [(w, 1)]
  -- every segment is a prefix of its writer's appends
  if segs.all (fun (w, n) => n ≤ (appsOf w).length) then return segs else none

/-- Concatenated appends of the first segments. -/
def segsValue (appsOf : Nat → List Int) (segs : List (Nat × Nat)) : List Int :=
  segs.flatMap fun (w, n) => (appsOf w).take n

/-- Every interpretation of a list-append observation (`[]`: none exists). `limit` bounds how
many are built. -/
def interpsListAppend (h : History) (limit : Nat := 200000) : List Interp := Id.run do
  let txs := txnViews h
  let keys := dedup (txs.flatMap fun t => t.mops.map (·.k))
  let txOf (i : Nat) : Option TxnV := txs.find? (·.id == i)
  -- unique elements per key
  for k in keys do
    let es := txs.flatMap fun t => apps t k
    if es.length != (dedup es).length then return []
  let ownerK (k : Nat) (e : Int) : Option (Nat × Nat) :=
    txs.findSome? fun t => ((apps t k).findIdx? (· == e)).map (t.id, ·)
  let appsK (k : Nat) (w : Nat) : List Int := ((txOf w).map (apps · k)).getD []
  -- Observed reads (acknowledged transactions): decompositions and the bases they pin.
  let mut pins : List ((Nat × Nat) × List Int) := []   -- (key, writer) -> base
  let mut decs : List ((Nat × Nat × Nat) × List (Nat × Nat)) := []  -- (txn, mop pos, key) -> segs
  for t in txs do
    if t.status != .ok then continue
    let mut pos := 0
    for m in t.mops do
      if m.f == .r then
        let l := match m.v with | .list l => l | _ => []
        let some segs := decompose (ownerK m.k) (appsK m.k) l | return []
        decs := decs ++ [((t.id, pos, m.k), segs)]
        let mut pre : List (Nat × Nat) := []
        for s in segs do
          let base := segsValue (appsK m.k) pre
          match pins.lookup (m.k, s.1) with
          | some b => if b != base then return []
          | none => pins := pins ++ [((m.k, s.1), base)]
          pre := pre ++ [s]
      pos := pos + 1
  let infos := (txs.filter (·.status == .info)).map (·.id)
  let mut out : List Interp := []
  for chosen in subsets infos do
    let committed := (txs.filter fun t => t.status == .ok || chosen.contains t.id).map (·.id)
    let isCommitted (w : Nat) := committed.contains w
    -- version orders, key by key
    let orderChoices : List (List (Nat × List Nat)) :=
      keys.foldl (fun acc k =>
        let ws := committed.filter fun w => !(appsK k w).isEmpty
        acc.flatMap fun a => (perms ws).map fun p => a ++ [(k, p)]) [[]]
    for ord in orderChoices do
      if out.length ≥ limit then return out
      -- installed values and the chain check
      let mut inst : List ((Nat × Nat) × List Int) := []
      let mut dirty := false
      let mut ok := true
      for (k, p) in ord do
        let mut prev : List Int := []
        for w in p do
          let base := (pins.lookup (k, w)).getD prev
          -- prev must be a prefix of base, the rest written by aborted transactions
          if !(prev.length ≤ base.length && base.take prev.length == prev) then ok := false
          else
            let rest := base.drop prev.length
            match decompose (ownerK k) (appsK k) rest with
            | none =>
              -- the rest may continue a segment begun in prev only if decomposable from scratch
              ok := false
            | some segs =>
              if segs.any (fun s => isCommitted s.1) then ok := false
              if !segs.isEmpty then dirty := true
          let v := base ++ appsK k w
          inst := inst ++ [((k, w), v)]
          prev := v
      if !ok then continue
      -- reads of acknowledged transactions
      let mut g : Graph := committed.foldl Graph.addVertex {}
      let mut g1a := false
      let mut g1b := false
      let mut nonAdya := false
      let mut readsOf : List (Nat × Nat × Option Nat) := []
      let mut firstRead : List ((Nat × Nat) × Option Nat) := []   -- (txn, key) -> version read first, before own append
      for t in txs do
        if !isCommitted t.id then continue
        let mut pos := 0
        let mut ownCount : List (Nat × Nat) := []
        for m in t.mops do
          match m.f with
          | .append => ownCount := amUpdate ownCount m.k 0 (· + 1)
          | .r =>
            let k := m.k
            let p := (ord.lookup k).getD []
            let own := (ownCount.lookup k).getD 0
            if t.status == .ok then
              let segs := ((decs.lookup (t.id, pos, k)).getD [])
              if 0 < own then
                -- a read after the transaction's own appends reads its own version
                match segs.getLast? with
                | some (w, n) => if w != t.id || n != own then nonAdya := true
                | none => nonAdya := true
              else
                if segs.any (·.1 == t.id) then nonAdya := true
                else
                  match segs.getLast? with
                  | none =>
                    readsOf := readsOf ++ [(t.id, k, none)]
                    if (firstRead.lookup (t.id, k)).isNone then firstRead := firstRead ++ [((t.id, k), none)]
                    match p.head? with
                    | some w1 => if w1 != t.id then g := g.link t.id w1 Rels.RW
                    | none => pure ()
                  | some (w, n) =>
                    -- Adya's G1b does not ask the writer to commit: an aborted transaction's
                    -- intermediate version read is G1a and G1b.
                    if n < (appsK k w).length then g1b := true
                    if !isCommitted w then g1a := true
                    else if n < (appsK k w).length then pure ()
                    else
                      readsOf := readsOf ++ [(t.id, k, some w)]
                      if (firstRead.lookup (t.id, k)).isNone then firstRead := firstRead ++ [((t.id, k), some w)]
                      g := g.link w t.id Rels.WR
                      match p.findIdx? (· == w) with
                      | some i => match p[i + 1]? with
                        | some nx => if nx != t.id then g := g.link t.id nx Rels.RW
                        | none => pure ()
                      | none => pure ()
          | _ => pure ()
          pos := pos + 1
      if nonAdya then continue
      -- committed indeterminate transactions: each external read reads some installed version
      let infoReads : List (Nat × Nat) := (txs.filter fun t => t.status == .info && isCommitted t.id).flatMap fun t =>
        Id.run do
          let mut own : List Nat := []
          let mut rs : List (Nat × Nat) := []
          for m in t.mops do
            if m.f == .append then own := if own.contains m.k then own else own ++ [m.k]
            if m.f == .r && !own.contains m.k then rs := rs ++ [(t.id, m.k)]
          return rs
      let choices : List (List (Nat × Nat × Option Nat)) :=
        infoReads.foldl (fun acc (r, k) =>
          let p := (ord.lookup k).getD []
          let before := match p.findIdx? (· == r) with | some i => p.take i | none => p
          let opts : List (Option Nat) := none :: before.map some
          acc.flatMap fun a => opts.map fun o => a ++ [(r, k, o)]) [[]]
      for ch in choices do
        let mut g' := g
        let mut fr := firstRead
        for (r, k, o) in ch do
          let p := (ord.lookup k).getD []
          if (fr.lookup (r, k)).isNone then fr := fr ++ [((r, k), o)]
          match o with
          | none => match p.head? with
            | some w1 => if w1 != r then g' := g'.link r w1 Rels.RW
            | none => pure ()
          | some w =>
            g' := g'.link w r Rels.WR
            match p.findIdx? (· == w) with
            | some i => match p[i + 1]? with
              | some nx => if nx != r then g' := g'.link r nx Rels.RW
              | none => pure ()
            | none => pure ()
        -- write dependencies
        for (_, p) in ord do
          for (a, b) in p.zip (p.drop 1) do g' := g'.link a b Rels.WW
        g' := orderEdges g' txs committed
        -- lost update: two committed transactions read the same version of a key, then append to it
        let lost := keys.any fun k =>
          let rs := (committed.filterMap fun t =>
            match txOf t with
            | none => none
            | some tv => if (apps tv k).isEmpty then none else (fr.lookup (t, k)).map (t, ·))
          rs.any fun (a, va) => rs.any fun (b, vb) => a != b && va == vb
        let intV := committed.any fun t => match txOf t with
          | some tv => tv.status == .ok && intViolated tv
          | none => false
        let phen := allCyclePhen g' ++ (if g1a then ["G1a"] else []) ++ (if g1b then ["G1b"] else []) ++
          (if dirty then ["dirty-update"] else []) ++ (if lost then ["lost-update"] else []) ++
          (if intV then ["internal"] else [])
        out := out ++ [{ phen, clean := !(g1a || g1b || dirty), dsg := g', order := ord,
                         reads := readsOf ++ ch }]
  return out

/-! ## Read-write registers -/

/-- The final write of `t` to `k`, and its earlier writes. -/
def finalWrite (t : TxnV) (k : Nat) : Option Val :=
  (t.mops.filter fun m => m.f == .w && m.k == k).getLast?.map (·.v)
def interWrites (t : TxnV) (k : Nat) : List Val :=
  (t.mops.filter fun m => m.f == .w && m.k == k).dropLast.map (·.v)

/-- Every interpretation of a register observation: values are unique, `nil` the initial one;
writes are blind, so any order of installed versions is possible. -/
def interpsRegister (h : History) (limit : Nat := 200000) : List Interp := Id.run do
  let txs := txnViews h
  let keys := dedup (txs.flatMap fun t => t.mops.map (·.k))
  let txOf (i : Nat) : Option TxnV := txs.find? (·.id == i)
  for k in keys do
    let vs := txs.flatMap fun t => (t.mops.filter fun m => m.f == .w && m.k == k).map (·.v)
    if vs.length != (dedup vs).length || vs.contains .nil then return []
  let writerOf (k : Nat) (v : Val) : Option Nat :=
    (txs.find? fun t => t.mops.any fun m => m.f == .w && m.k == k && m.v == v).map (·.id)
  let infos := (txs.filter (·.status == .info)).map (·.id)
  let mut out : List Interp := []
  for chosen in subsets infos do
    let committed := (txs.filter fun t => t.status == .ok || chosen.contains t.id).map (·.id)
    let isCommitted (w : Nat) := committed.contains w
    let orderChoices : List (List (Nat × List Nat)) :=
      keys.foldl (fun acc k =>
        let ws := committed.filter fun w => ((txOf w).bind (finalWrite · k)).isSome
        acc.flatMap fun a => (perms ws).map fun p => a ++ [(k, p)]) [[]]
    for ord in orderChoices do
      if out.length ≥ limit then return out
      let mut g : Graph := committed.foldl Graph.addVertex {}
      let mut g1a := false
      let mut g1b := false
      let mut nonAdya := false
      let mut readsOf : List (Nat × Nat × Option Nat) := []
      let mut firstRead : List ((Nat × Nat) × Option Nat) := []
      for t in txs do
        if !isCommitted t.id || t.status != .ok then continue
        let mut wrote : List (Nat × Val) := []
        for m in t.mops do
          match m.f with
          | .w => wrote := amPut wrote m.k m.v
          | .r =>
            let k := m.k
            let p := (ord.lookup k).getD []
            match wrote.lookup k with
            | some v => if !(v == m.v) then nonAdya := true
            | none =>
              let read (o : Option Nat) (g : Graph) : Graph :=
                match o with
                | none => match p.head? with
                  | some w1 => if w1 != t.id then g.link t.id w1 Rels.RW else g
                  | none => g
                | some w =>
                  let g := g.link w t.id Rels.WR
                  match p.findIdx? (· == w) with
                  | some i => match p[i + 1]? with
                    | some nx => if nx != t.id then g.link t.id nx Rels.RW else g
                    | none => g
                  | none => g
              if m.v == .nil then
                readsOf := readsOf ++ [(t.id, k, none)]
                if (firstRead.lookup (t.id, k)).isNone then firstRead := firstRead ++ [((t.id, k), none)]
                g := read none g
              else
                match writerOf k m.v with
                | none => nonAdya := true
                | some w =>
                  let final := (((txOf w).bind (finalWrite · k)).map (· == m.v)).getD false
                  if w == t.id then nonAdya := true
                  else if !isCommitted w then
                    g1a := true
                    if !final then g1b := true
                  else if (((txOf w).bind (finalWrite · k)).map (· == m.v)).getD false then
                    readsOf := readsOf ++ [(t.id, k, some w)]
                    if (firstRead.lookup (t.id, k)).isNone then firstRead := firstRead ++ [((t.id, k), some w)]
                    g := read (some w) g
                  else g1b := true
          | _ => pure ()
      if nonAdya then continue
      let infoReads : List (Nat × Nat) := (txs.filter fun t => t.status == .info && isCommitted t.id).flatMap fun t =>
        Id.run do
          let mut own : List Nat := []
          let mut rs : List (Nat × Nat) := []
          for m in t.mops do
            if m.f == .w then own := if own.contains m.k then own else own ++ [m.k]
            if m.f == .r && !own.contains m.k then rs := rs ++ [(t.id, m.k)]
          return rs
      let choices : List (List (Nat × Nat × Option Nat)) :=
        infoReads.foldl (fun acc (r, k) =>
          let p := (ord.lookup k).getD []
          let opts : List (Option Nat) := none :: (p.filter (· != r)).map some
          acc.flatMap fun a => opts.map fun o => a ++ [(r, k, o)]) [[]]
      for ch in choices do
        let mut g' := g
        let mut fr := firstRead
        for (r, k, o) in ch do
          let p := (ord.lookup k).getD []
          if (fr.lookup (r, k)).isNone then fr := fr ++ [((r, k), o)]
          match o with
          | none => match p.head? with
            | some w1 => if w1 != r then g' := g'.link r w1 Rels.RW
            | none => pure ()
          | some w =>
            g' := g'.link w r Rels.WR
            match p.findIdx? (· == w) with
            | some i => match p[i + 1]? with
              | some nx => if nx != r then g' := g'.link r nx Rels.RW
              | none => pure ()
            | none => pure ()
        for (_, p) in ord do
          for (a, b) in p.zip (p.drop 1) do g' := g'.link a b Rels.WW
        g' := orderEdges g' txs committed
        let lost := keys.any fun k =>
          let rs := committed.filterMap fun t =>
            match txOf t with
            | none => none
            | some tv => if (finalWrite tv k).isNone then none else (fr.lookup (t, k)).map (t, ·)
          rs.any fun (a, va) => rs.any fun (b, vb) => a != b && va == vb
        let intV := committed.any fun t => match txOf t with
          | some tv => tv.status == .ok && intViolated tv
          | none => false
        let phen := allCyclePhen g' ++ (if g1a then ["G1a"] else []) ++ (if g1b then ["G1b"] else []) ++
          (if lost then ["lost-update"] else []) ++ (if intV then ["internal"] else [])
        out := out ++ [{ phen, clean := !(g1a || g1b), dsg := g', order := ord, reads := readsOf ++ ch }]
  return out

/-! ## Models, from their definitions -/

def rc : List String := ["G0", "G1a", "G1b", "G1c", "dirty-update"]

/-- The phenomena each model proscribes (sources in the module docstring). -/
def proscribed : List (String × List String) := [
  ("read-uncommitted", ["G0"]),
  ("read-committed", rc),
  ("repeatable-read", rc ++ ["G2"]),
  ("consistent-view", rc ++ ["G-single"]),
  ("snapshot-isolation", rc ++ ["G-nonadjacent", "internal"]),
  ("serializable", rc ++ ["G2", "internal"]),
  ("strict-serializable", rc ++ ["G2", "internal", "G1c-realtime", "G2-realtime"]),
  ("strong-session-read-uncommitted", ["G0", "G0-process"]),
  ("strong-session-read-committed", rc ++ ["G1c-process"]),
  ("strong-read-uncommitted", ["G0", "G0-process", "G0-realtime"]),
  ("strong-read-committed", rc ++ ["G1c-process", "G1c-realtime"]),
  ("strong-session-snapshot-isolation", rc ++ ["G-nonadjacent", "internal", "G1c-process", "G-nonadjacent-process"]),
  ("strong-snapshot-isolation", rc ++ ["G-nonadjacent", "internal", "G1c-process", "G-nonadjacent-process",
                                       "G1c-realtime", "G-nonadjacent-realtime"]),
  ("strong-session-serializable", rc ++ ["G2", "internal", "G1c-process", "G2-process"])]

def specModels : List String := proscribed.map (·.1)

inductive SpecVerdict where
  /-- Some interpretation shows none of the model's phenomena. -/
  | sat
  /-- Interpretations exist; every one shows some. -/
  | unsat
  /-- No interpretation exists (an observation no Adya history explains). -/
  | none_
  deriving Repr, DecidableEq, Inhabited

def SpecVerdict.str : SpecVerdict → String
  | .sat => "satisfiable" | .unsat => "violated in every interpretation" | .none_ => "no interpretation"

def verdict (is : List Interp) (model : String) : SpecVerdict :=
  if is.isEmpty then .none_ else
  let bad := (proscribed.lookup model).getD []
  if is.any (fun i => !(i.phen.any bad.contains)) then .sat else .unsat

end Elle.Spec

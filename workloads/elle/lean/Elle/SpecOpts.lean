import Elle.Spec

/-!
# The options' assumptions, on every interpretation

rw-register's options each assume something of the execution (rw_register.clj:925-951):

- `:linearizable-keys?`: "each key is independently linearizable" (Herlihy and Wing 1990, as a
  register per key): a total order of the transactions touching the key, consistent with real time
  (one completed before the other was invoked), in which each read returns the latest write.
- `:sequential-keys?`: "each key is independently sequentially consistent" (Lamport 1979): the
  same, with each process's order in place of real time.
- `:transaction-order`: "each key written in a transaction is assigned the version of its owning
  transaction" (rw_register.clj:234-238), from "a numeric, total transaction order"
  (rw_register.clj:925-932): every committed transaction has a place, and each key's versions
  follow their writers' places.
- `:wfr-keys?`: "within each transaction, writes follow reads" (rw_register.clj:950-951): a
  transaction's external read of a key precedes its external write of it.

With an interpretation's version order fixed, a key's linearization exists exactly when the graph
of its constraints (versions in order; a read after the version it read and before the next; the
order relation between transactions touching the key) is acyclic. A read of an aborted or
intermediate version (an unclean interpretation) is no register state, so it breaks both.
-/

namespace Elle.SpecOpts

open Elle Elle.Spec

/-- Committed transactions of an interpretation (the DSG's vertices). -/
def committedOf (i : Interp) : List Nat := i.dsg.verts

def touches (t : TxnV) (k : Nat) : Bool := t.mops.any (·.k == k)

def keysOf (txs : List TxnV) : List Nat := dedup (txs.flatMap fun t => t.mops.map (·.k))

/-- The version after writer `w` (none: the initial version) in `p`, if any. -/
def nextAfter (p : List Nat) (w : Option Nat) : Option Nat :=
  match w with
  | none => p.head?
  | some w => match p.findIdx? (· == w) with
    | some j => p[j + 1]?
    | none => none

/-- Key `k`'s constraint graph, with `before` relating transactions touching the key. -/
def keyGraph (txs : List TxnV) (i : Interp) (k : Nat) (before : TxnV → TxnV → Bool) : Graph :=
  let committed := committedOf i
  let nodes := txs.filter fun t => committed.contains t.id && touches t k
  let p := (i.order.lookup k).getD []
  let g : Graph := nodes.foldl (fun g t => g.addVertex t.id) {}
  let g := (p.zip (p.drop 1)).foldl (fun g (a, b) => g.link a b Rels.WW) g
  let g := i.reads.foldl (fun g (r, k', w) =>
    if k' != k then g else
    let g := match w with | some w => g.link w r Rels.WR | none => g
    match nextAfter p w with
    | some n => if n != r then g.link r n Rels.RW else g
    | none => g) g
  nodes.foldl (fun g a => nodes.foldl (fun g b =>
    if a.id != b.id && before a b then g.link a.id b.id Rels.REALTIME else g) g) g

def perKeyOk (txs : List TxnV) (i : Interp) (before : TxnV → TxnV → Bool) : Bool :=
  i.clean && (keysOf txs).all fun k => !hasCycle (keyGraph txs i k before)

/-- Real time: `a` acknowledged before `b` was invoked. -/
def rtBefore (a b : TxnV) : Bool := a.status == .ok && a.cmp < b.inv
/-- Process order: the same, on one process. -/
def procBefore (a b : TxnV) : Bool := a.status == .ok && a.process == b.process && a.cmp < b.inv

/-- `:linearizable-keys?`'s assumption. -/
def linearizableKeys (txs : List TxnV) (i : Interp) : Bool := perKeyOk txs i rtBefore
/-- `:sequential-keys?`'s assumption. -/
def sequentialKeys (txs : List TxnV) (i : Interp) : Bool := perKeyOk txs i procBefore

/-- `:transaction-order`'s assumption. -/
def txnOrderOk (ord : List (Nat × Int)) (i : Interp) : Bool :=
  (committedOf i).all (fun t => (ord.lookup t).isSome) &&
  i.order.all fun (_, p) => (p.zip (p.drop 1)).all fun (a, b) =>
    match ord.lookup a, ord.lookup b with
    | some x, some y => x < y
    | _, _ => false

/-- The place of value `v` of key `k` in the interpretation's version order: -1 for `nil` (the
initial version), none when no committed transaction installed it. -/
def posOf (txs : List TxnV) (i : Interp) (k : Nat) (v : Val) : Option Int :=
  if v == .nil then some (-1) else
  let p := (i.order.lookup k).getD []
  match txs.find? (fun t => p.contains t.id && (finalWrite t k).map (· == v) == some true) with
  | some t => (p.findIdx? (· == t.id)).map Int.ofNat
  | none => none

/-- `:wfr-keys?`'s assumption: an acknowledged transaction's first read of a key, when the
transaction also writes it, reads a version before its own. -/
def wfrOk (txs : List TxnV) (i : Interp) : Bool :=
  txs.all fun t =>
    if t.status != .ok || !(committedOf i).contains t.id then true else
    (keysOf [t]).all fun k =>
      match t.mops.find? (·.k == k), finalWrite t k with
      | some m, some v =>
        if m.f != .r then true else
        match posOf txs i k m.v, posOf txs i k v with
        | some a, some b => a < b
        | _, _ => true
      | _, _ => true

/-- A version-graph edge `v1 -> v2` of key `k` holds in an interpretation: both versions
installed and in that order, or one of them not installed there. -/
def edgeHolds (txs : List TxnV) (i : Interp) (k : Nat) (v1 v2 : Val) : Bool :=
  match posOf txs i k v1, posOf txs i k v2 with
  | some a, some b => a < b
  | _, _ => true

/-- An option set's assumption, as a predicate on interpretations. -/
structure Assume where
  lin : Bool := false
  seq : Bool := false
  wfr : Bool := false
  order : Option (List (Nat × Int)) := none

def Assume.holds (a : Assume) (txs : List TxnV) (i : Interp) : Bool :=
  (!a.lin || linearizableKeys txs i) && (!a.seq || sequentialKeys txs i) &&
  (!a.wfr || wfrOk txs i) &&
  (match a.order with | some o => txnOrderOk o i | none => true)

end Elle.SpecOpts

import Elle.RwRegister
import Elle.ListAppend
import Elle.Spec
import Elle.Gen

/-!
# Folds, as jepsen.history and tesser run them

jepsen.history 0.1.9 runs a fold over a history's chunks (16,384 ops each by default,
fold.clj:10-13): each chunk reduced from `reducer-identity`, the results combined left to right
from `combiner-identity` (fold.clj:596-631: each combine task waits for the previous one;
`:associative?` "does nothing; we haven't implemented associative combine", fold.clj:144-147),
then `post-combiner`. tesser.core's own executor (`t/tesser`, core.clj:275-315), which
`transaction-graph->version-graphs` uses over chunks of a Bifurcan map split `4 × processors`
ways, combines chunk results in the order workers finish them.

Each fold Elle uses is written here as its reducer over one chunk, its combiner, and its final
step; `onChunks` runs it over a chunking. The property: the result is the same for every
chunking (contiguous, in order) and, for tesser.core's executor, every combine order.
-/

namespace Elle.Folds

open Elle

/-- A fold: chunk results of type `R`, a combiner accumulator `C`, a final result `O`. -/
structure Fold (R C O : Type) where
  reduce : List Op → R
  cid : C
  combine : C → R → C
  final : C → O

def Fold.onChunks {R C O : Type} (f : Fold R C O) (chunks : List (List Op)) : O :=
  f.final (chunks.foldl (fun c ch => f.combine c (f.reduce ch)) f.cid)

/-- Every way to cut `l` into contiguous nonempty chunks (2^(n-1) of them). -/
def chunkings {α : Type} : List α → List (List (List α))
  | [] => [[]]
  | [x] => [[[x]]]
  | x :: xs => (chunkings xs).flatMap fun cs =>
      match cs with
      | c :: rest => [[x] :: c :: rest, (x :: c) :: rest]
      | [] => [[[x]]]

/-! ## Canonical forms (maps and sets compared as Clojure compares them) -/

def canonNat (l : List Nat) : List Nat := sortNat (dedup l)

def canonMap {β : Type} (m : List (Nat × β)) (f : β → String) : List String :=
  (m.map fun (k, v) => s!"{k}={f v}").mergeSort fun a b => decide (a ≤ b)

/-! ## jepsen.history's `pair-index-fold` (history.clj:421-505) -/

/-- A chunk's partial index: pairs, completions whose invocation came before the chunk (head),
invocations still open at its end (tail). -/
structure PairChunk where
  pairs : List (Nat × Int) := []
  head : List (Nat × Nat) := []   -- process -> completion
  tail : List (Nat × Nat) := []   -- process -> invocation
  deriving Inhabited

def pairReduce (ops : List Op) : Except String PairChunk :=
  ops.foldlM (fun (c : PairChunk) o =>
    let p := o.process
    if o.isInvoke then
      if (c.tail.lookup p).isSome then .error ":jepsen.history/double-invoke"
      else .ok { c with tail := amPut c.tail p o.index }
    else
      match c.tail.lookup p with
      | some i => .ok { c with pairs := c.pairs ++ [(i, Int.ofNat o.index), (o.index, Int.ofNat i)],
                               tail := c.tail.filter (·.1 != p) }
      | none =>
        if (c.head.lookup p).isSome then .error ":jepsen.history/double-complete"
        else .ok { c with head := amPut c.head p o.index }) {}

/-- The combiner: pairs merged, the chunk's head completes running invocations, its tail starts
new ones (`MERGE_LAST_WRITE_WINS`). -/
def pairCombine (acc : Except String (List (Nat × Int) × List (Nat × Nat))) (r : Except String PairChunk) :
    Except String (List (Nat × Int) × List (Nat × Nat)) := do
  let (pairs, running) ← acc
  let c ← r
  let mut pairs := c.pairs.foldl (fun m (k, v) => amPut m k v) pairs
  let mut running := running
  for (p, i1) in c.head do
    match running.lookup p with
    | some i0 =>
      pairs := amPut (amPut pairs i0 (Int.ofNat i1)) i1 (Int.ofNat i0)
      running := running.filter (·.1 != p)
    | none => throw ":jepsen.history/not-running"
  running := c.tail.foldl (fun m (p, i) => amPut m p i) running
  return (pairs, running)

def pairIndexFold : Fold (Except String PairChunk) (Except String (List (Nat × Int) × List (Nat × Nat))) (Except String (List String)) where
  reduce := pairReduce
  cid := .ok ([], [])
  combine := pairCombine
  final := fun acc => do
    let (pairs, running) ← acc
    let pairs := running.foldl (fun m (_, i) => amPut m i (-1)) pairs
    return canonMap pairs toString

/-! ## elle.txn's `failed-write-indices` and `intermediate-write-indices` (txn.clj:111-189) -/

abbrev KVI := List (Nat × List (Val × Nat))

/-- `(merge-with merge a b)`: b's values win. -/
def mergeKVI (a b : KVI) : KVI :=
  b.foldl (fun m (k, vs) => amUpdate m k [] fun old => vs.foldl (fun o (v, i) => amPut o v i) old) a

def showKVI (m : KVI) : List String :=
  canonMap m fun vs => toString ((vs.map fun (v, i) => s!"{repr v}:{i}").mergeSort fun a b => decide (a ≤ b))

def failedFold (write? : F → Bool) : Fold KVI KVI (List String) where
  reduce := fun ops => failedWriteIndices write? ops
  cid := []
  combine := mergeKVI
  final := showKVI

def intermediateFold (write? : F → Bool) : Fold KVI KVI (List String) where
  reduce := fun ops => intermediateWriteIndices write? ops
  cid := []
  combine := mergeKVI
  final := showKVI

/-! ## elle.core's `process-graph` (core.clj:286-344) -/

structure ProcChunk where
  edges : List (Nat × Nat) := []
  first : List (Nat × Nat) := []
  last : List (Nat × Nat) := []
  deriving Inhabited

def procReduce (ops : List Op) : ProcChunk :=
  ops.foldl (fun c o =>
    if !o.isOk then c else
    match c.last.lookup o.process with
    | none => { c with first := amPut c.first o.process o.index, last := amPut c.last o.process o.index }
    | some l => { c with edges := c.edges ++ [(l, o.index)], last := amPut c.last o.process o.index }) {}

/-- The combiner: graphs unioned; an unresolved last op linked to the chunk's first op of its
process (and dropped); then the chunk's last ops override. -/
def procCombine (acc : List (Nat × Nat) × List (Nat × Nat)) (c : ProcChunk) : List (Nat × Nat) × List (Nat × Nat) :=
  let (edges, last) := acc
  let (edges, last) := c.first.foldl (fun (es, la) (p, f) =>
    match la.lookup p with
    | some l => (es ++ [(l, f)], la.filter (·.1 != p))
    | none => (es, la)) (edges ++ c.edges, last)
  (edges, c.last.foldl (fun m (p, i) => amPut m p i) last)

def processFold : Fold ProcChunk (List (Nat × Nat) × List (Nat × Nat)) (List String) where
  reduce := procReduce
  cid := ([], [])
  combine := procCombine
  final := fun (es, _) => (dedup (es.map fun (a, b) => s!"{a}->{b}")).mergeSort fun a b => decide (a ≤ b)

/-! ## elle.list-append's `sorted-values` (list_append.clj:271-316): sets of reads, unioned -/

abbrev KSets := List (Nat × List (List Int))

def sortedReduce (ops : List Op) : KSets :=
  ops.foldl (fun st o => o.value.foldl (fun st m =>
    match m.f, m.v with
    | .r, .list l => if l.isEmpty then st else amUpdate st m.k [] fun vs => if vs.contains l then vs else vs ++ [l]
    | _, _ => st) st) []

def unionKSets (a b : KSets) : KSets :=
  b.foldl (fun m (k, vs) => amUpdate m k [] fun old => old ++ vs.filter (!old.contains ·)) a

def sortedFold : Fold KSets KSets (List String) where
  reduce := sortedReduce
  cid := []
  combine := unionKSets
  final := fun m => canonMap m fun vs => toString ((vs.map toString).mergeSort fun a b => decide (a ≤ b))

/-! ## tesser's ordered `into []` (ok-keep, keep-op-mops, g1a/g1b/internal/duplicates) -/

def intoFold (keep : Op → List String) : Fold (List String) (List String) (List String) where
  reduce := fun ops => ops.flatMap keep
  cid := []
  combine := (· ++ ·)
  final := id

/-! ## rw-register's `transaction-graph->version-graphs` fold (rw_register.clj:543-622), over
chunks of the external key graph's entries (`.split`, 4 × processors), combined by
tesser.core's executor in the order its workers finish -/

def showVG (vgs : RwRegister.VGraphs) : List String :=
  (dedup (vgs.flatMap fun (k, es) => es.map fun (a, b) => s!"{k}:{repr a}->{repr b}")).mergeSort
    fun a b => decide (a ≤ b)

/-- The version graphs from chunks of entries, chunk results combined in `order`. -/
def vgChunks (h : History) (chunks : List (List (Nat × List (Nat × List Nat)))) (order : List Nat) : List String :=
  let results := chunks.map fun ch => ch.foldl (fun vgs e => RwRegister.mergeVG vgs (RwRegister.vgOfEntry h e)) []
  showVG ((order.filterMap (results[·]?)).foldl RwRegister.mergeVG [])

end Elle.Folds

namespace Elle.Folds
open Elle Determinismo Elle.Gen

/-- A history made malformed for the pair index: an invocation repeated (a process invoking
twice), a completion dropped, or a completion repeated. -/
def malform (h : History) : W History := do
  let k ← dec "malform.kind" 4
  if k == 0 then return h
  let n := h.size
  if n == 0 then return h
  let i ← dec "malform.at" n
  let ops := h.toList
  let ops := match k with
    | 1 => ops.take (i + 1) ++ (ops.drop i).take 1 ++ ops.drop (i + 1)
    | 2 => if (ops.getD i default).isInvoke then ops else ops.eraseIdx i
    | _ => ops.take (i + 1) ++ (ops.drop i).take 1 ++ ops.drop (i + 1)
  return (ops.zip (List.range ops.length)).toArray.map fun (o, j) => { o with index := j }

/-- Every chunking (and for the version-graph fold, every combine order) against one chunk.
Returns the first fold whose result differs, with the chunking. -/
def check (h : History) (maxChunkings : Nat := 512) : Option (String × String) := Id.run do
  let ops := h.toList
  let cs := (chunkings ops).take maxChunkings
  let one := [ops]
  let showC (chs : List (List Op)) : String := toString (chs.map fun ch => ch.map (·.index))
  let p1 := pairIndexFold.onChunks one
  let f1 := (failedFold ListAppend.isAppend).onChunks one
  let fw := (failedFold RwRegister.isW).onChunks one
  let i1 := (intermediateFold ListAppend.isAppend).onChunks one
  let pr := processFold.onChunks one
  let sv := sortedFold.onChunks [possible ops]
  for ch in cs do
    let pc := pairIndexFold.onChunks ch
    let same := match p1, pc with
      | .ok a, .ok b => a == b
      | .error a, .error b => a == b
      | _, _ => false
    if !same then
      return some ("pair-index-fold", s!"one chunk: {repr p1}; chunks {showC ch}: {repr pc}")
    if (failedFold ListAppend.isAppend).onChunks ch != f1 then return some ("failed-write-indices", showC ch)
    if (failedFold RwRegister.isW).onChunks ch != fw then return some ("failed-write-indices", showC ch)
    if (intermediateFold ListAppend.isAppend).onChunks ch != i1 then return some ("intermediate-write-indices", showC ch)
    if processFold.onChunks ch != pr then return some ("process-graph", showC ch)
  for ch in (chunkings (possible ops)).take maxChunkings do
    if sortedFold.onChunks ch != sv then return some ("sorted-values", showC ch)
  -- the version-graph fold over the real-time graph's external key graph
  let kg := RwRegister.kgOf h (realtimeGraph h).graph
  let vg1 := vgChunks h [kg] [0]
  for ch in (chunkings kg).take 64 do
    for order in (Spec.perms (List.range ch.length)).take 24 do
      if vgChunks h ch order != vg1 then
        return some ("transaction-graph->version-graphs", s!"{ch.length} chunks in order {order}")
  -- algebra of the combiners on chunk results
  let rs := (cs.headD one).map fun c => failedWriteIndices ListAppend.isAppend c
  match rs with
  | a :: b :: c :: _ =>
    if showKVI (mergeKVI (mergeKVI a b) c) != showKVI (mergeKVI a (mergeKVI b c)) then
      return some ("merge-with merge: not associative", "")
  | _ => pure ()
  return none

end Elle.Folds

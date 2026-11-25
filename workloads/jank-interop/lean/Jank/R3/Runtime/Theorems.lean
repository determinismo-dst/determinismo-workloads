import Jank.R3.Runtime.Folly
import Jank.R3.Runtime.Gc
import Jank.R3.Runtime.Containers

/-!
# Round 3, Runtime: theorems (no `sorry`, no `native_decide`, no axioms beyond Lean's)

- The coarse SharedMutex (`Folly.CSM`, validated against the replica by the refinement table)
  has the blocking facts jank's deadlocks rest on, for every lock state: a thread holding a mutex
  shared never completes its own exclusive acquisition; a writer that set kHasE keeps every new
  reader out (also the reader that already holds it); a held upgrade lock keeps writers out; an
  exclusive holder blocks its own second exclusive acquisition. These are for-every-input forms of
  round 1's bounded D16 search.
- The fine replica's control flow at the same points.
- bdwgc: `GC_make_descriptor` of jank's persistent_string bitmap scans exactly the word holding
  `store.large.data`, and for every 6-word bitmap the descriptor scans exactly its set words.
- fbvector's growth policy.
-/

namespace Jank.R3.Runtime.Theorems

open Jank.R3.Runtime

/-! ## The coarse SharedMutex: why the deadlocks happen, for every state -/

/-- A thread holding the mutex shared can set kHasE (if no solo bit), but never drains: `lock()`
while holding `rlock()` waits for itself (validator: `set-validator!` inside a validator; watches:
`add-watch`/`remove-watch` inside a watch). -/
theorem exclusive_after_shared_never_drains (c c' : Folly.CSM) (t : Nat)
    (h : t ∈ c.s) (hs : c.lockSet t = some c') : c'.lockDrain t = none := by
  unfold Folly.CSM.lockSet at hs
  split at hs
  · cases hs
  · cases hs
    unfold Folly.CSM.lockDrain
    have : c.s.isEmpty = false := by
      cases hc : c.s with
      | nil => simp [hc] at h
      | cons _ _ => rfl
    simp [this]

/-- A writer that has set kHasE (draining or holding) keeps every reader out, including one
that already holds the mutex shared and asks again (watch/validator re-entry beside a writer). -/
theorem pending_writer_blocks_readers (c : Folly.CSM) (t w : Nat) (h : c.pend = some w) :
    c.lockShared t = none := by
  simp [Folly.CSM.lockShared, h]

/-- ... and the writer cannot drain while that reader holds it: neither moves. -/
theorem writer_waits_for_reader (c : Folly.CSM) (t w : Nat) (h : t ∈ c.s) :
    c.lockDrain w = none := by
  unfold Folly.CSM.lockDrain
  have : c.s.isEmpty = false := by
    cases hc : c.s with
    | nil => simp [hc] at h
    | cons _ _ => rfl
  simp [this]

/-- The exclusive holder's second `lock()` never sets kHasE (alter-var-root re-entering the same
var's `write_mutex`; a var's meta expression reading the same var's meta). -/
theorem exclusive_reentry_blocked (c : Folly.CSM) (t : Nat) (h : c.e = some t) :
    c.lockSet t = none := by
  simp [Folly.CSM.lockSet, h]

/-- An upgrade holder keeps writers from setting kHasE (`future-cancelled?` holds the future's
state `ulock()` while it waits for the thread lock; the future's own completion needs `wlock()`). -/
theorem upgrade_blocks_writer (c : Folly.CSM) (u w : Nat) (h : c.u = some u) :
    c.lockSet w = none := by
  simp [Folly.CSM.lockSet, h]

/-- A shared holder keeps a writer from completing (`future-cancel` holds the future's state
`rlock()` while it waits for the thread lock). -/
theorem reader_blocks_writer_drain (c : Folly.CSM) (r w : Nat) (h : r ∈ c.s) :
    c.lockDrain w = none := writer_waits_for_reader c r w h

/-! ## The fine replica at the same points -/

open Folly in
theorem shared_waits_while_kHasE (st : St) (h : st &&& kHasE ≠ 0) :
    lsLoop st = .fwLoad kHasE kWaitingS .lsSlow2 := by
  simp [lsLoop, h]

open Folly in
theorem lock_waits_while_solo (st : St) (h : st &&& kHasSolo ≠ 0) :
    leLoop kHasSolo st = .fwLoad kHasSolo kWaitingE (.leSlow2 kHasSolo) := by
  simp [leLoop, h]

open Folly in
theorem drain_waits_for_readers (st : St) (h : st &&& kHasS ≠ 0) :
    leDrain st = .next (.fwLoad kHasS kWaitingNotS .doneE) := by
  simp [leDrain, h]

open Folly in
/-- The state bits are disjoint: the reader count never overlaps the solo or waiter bits. -/
theorem state_bits_disjoint :
    kHasS &&& kHasSolo = 0 ∧ kHasS &&& kMayDefer = 0 ∧ kHasS &&& kPrevDefer = 0 ∧
    kHasS &&& (kWaitingNotS ||| kWaitingE ||| kWaitingU ||| kWaitingS) = 0 ∧
    kHasE &&& kHasU = 0 ∧ kIncrHasS &&& kHasS = kIncrHasS := by
  decide

/-! ## bdwgc: the persistent_string descriptor -/

/-- jank's bitmap (only word 2 set, 6 words) gives the bitmap descriptor with bit 61 set. -/
theorem ps_descriptor_value : Gc.psDescriptor = 0x2000000000000001 := by decide

/-- The collector scans exactly word 2 of a persistent_string: `store.large.data`. -/
theorem ps_descriptor_scans_data : Gc.scannedWords Gc.psDescriptor Gc.psWords = [Gc.psDataWord] := by
  decide

/-- The bitmap of a 6-bit number, word i = bit i. -/
def bits6 (n : Nat) : List Bool := (List.range 6).map fun i => n.testBit i

/-- For every 6-word bitmap, `GC_make_descriptor` followed by the mark procedure's decoding scans
exactly the set words (length and bitmap descriptors alike). -/
theorem make_descriptor_exact :
    ∀ n : Fin 64, Gc.scannedWords (Gc.makeDescriptor (bits6 n)) 6 =
      (List.range 6).filter fun i => (bits6 n).getD i false := by
  decide

/-- An atomic (pointer-free) object is never scanned: `var_unbound_root`'s `var` word. -/
theorem atomic_scans_nothing (o : Gc.Obj) (h : o.kind = .atomic) :
    (match o.kind with
     | .normal | .uncollectable => List.range o.words.size
     | .atomic => []
     | .typed d => Gc.scannedWords d o.words.size) = [] := by
  simp [h]

/-! ## fbvector's growth policy (sizeof(T) = 8) -/

theorem first_capacity : Containers.computePushBackCapacity 0 = 8 := by decide

theorem doubles_below_512 (c : Nat) (h0 : 0 < c) (h : c < 512) :
    Containers.computePushBackCapacity c = 2 * c := by
  unfold Containers.computePushBackCapacity Containers.sizeofT
  have h1 : (c == 0) = false := by simp; omega
  have h2 : c < 4096 / 8 := by omega
  simp [h1, h2]; omega

theorem grows_by_half_between (c : Nat) (h0 : 512 ≤ c) (h : c ≤ 16384) :
    Containers.computePushBackCapacity c = (c * 3 + 1) / 2 := by
  unfold Containers.computePushBackCapacity Containers.sizeofT
  have h1 : (c == 0) = false := by simp; omega
  have h2 : ¬ c < 4096 / 8 := by omega
  have h3 : ¬ c > 4096 * 32 / 8 := by omega
  simp [h1, h2, h3]

/-! ## fbvector::emplace and insert with an argument aliasing an element -/

/-- `[1 2]`, then `emplace(begin(), v[1])`: make_window shifts the elements before the argument
is read, so fbvector inserts 1 where std::vector (LWG 2164) inserts 2. -/
theorem emplace_alias_inserts_shifted :
    (do let v ← Containers.pushBack {} (.fresh 1)
        let v ← Containers.pushBack v (.fresh 2)
        let v ← Containers.insertOne v 0 (.ref 1) false
        pure v.elems) = (Except.ok [1, 1, 2] : Except String (List Nat)) := by
  rfl

/-- `insert(begin(), v[1])` copies the argument first (`dataIsInternal`): std::vector's result. -/
theorem insert_alias_copies_first :
    (do let v ← Containers.pushBack {} (.fresh 1)
        let v ← Containers.pushBack v (.fresh 2)
        let v ← Containers.insertOne v 0 (.ref 1) true
        pure v.elems) = (Except.ok [2, 1, 2] : Except String (List Nat)) := by
  rfl

/-! ## immutable_string: `s = s.c_str()` -/

def selfCStrFails : Bool :=
  match (do Containers.sstep (.lit 0 30); Containers.sstep (.assignCStr 0 0)).run
      ({ vars := Array.replicate 2 {} } : Containers.SW) with
  | .error _ _ => true
  | .ok _ _ => false

/-- A large owned string assigned its own `c_str()`: `operator=(const_pointer_type)` frees the
buffer (`destroy()`) before it reads the characters. -/
theorem self_cstr_assign_reads_freed : selfCStrFails = true := by rfl

end Jank.R3.Runtime.Theorems

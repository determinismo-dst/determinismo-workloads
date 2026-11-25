import Elle.R4.Lift
import Elle.R4.LAIndex

/-!
# Round 4: list-append histories and their clean interpretations, declaratively

**Well-formed** (`WF`): a list-append history as the service hands it to Elle: operations at their
index; only reads and appends; reads of operations that didn't end `:ok` hold `nil` (unknown);
an `:ok` read holds no element twice (the service drops such reads, D17); each element of a key
appended by one completion only, once; each process one operation at a time, an `:info`
completion ending it (Elle's rule, and the service's `closed`).

**A clean interpretation** (Adya's histories with list traces, Elle §4: Theorem 1's "clean": no
aborted read, intermediate read or dirty update): which transactions committed (every `:ok`, no
`:fail`, any `:info`), and per key the version order: the committed transactions that append to
it. Its version `i` is the concatenation of the first `i` writers' appends. A read before any own
append of the key returns some version not holding the reader's own writes; a read after own
appends returns the version just before the reader's own, then its own appends so far.

The DSG: `ww` between successive writers; `wr` from the writer of the version an external read
returned to the reader; `rw` from that reader to the writer of the next version; `so` and `rt`
from an `:ok` transaction to a committed one invoked after it completed (`so`: the same process),
as round 1's specification draws them (`Spec.orderEdges`, invocation by the pair index).
-/

namespace Elle.R4.LA

open Elle Elle.R4 Elle.ListAppend

/-- The appends of `o` to `k`, in order. -/
def appsOf (o : Op) (k : Nat) : List Int :=
  o.value.filterMap fun m => if m.f == .append && m.k == k then (match m.v with | .int e => some e | _ => none) else none

/-- The appends of the op at index `w` to `k`. -/
def apps (h : History) (w k : Nat) : List Int := ((h[w]?).map (appsOf · k)).getD []

/-- The appends of `o` to `k` before its `j`-th mop. -/
def appsBefore (o : Op) (j k : Nat) : List Int := appsOf { o with value := o.value.take j } k

/-- A read value as a list (`nil` is the empty list). -/
def toL (v : Val) : List Int := ListAppend.Val.toList v

/-- The invocation index of completion `b`, as round 1's specification takes it. -/
def invIdx (h : History) (b : Nat) : Nat := ((pairIndex h).lookup b).getD b

structure WF (h : History) : Prop where
  index : ∀ i (hi : i < h.size), h[i].index = i
  mops : ∀ o ∈ h.toList, ∀ m ∈ o.value, m.f = .r ∨ (m.f = .append ∧ ∃ e, m.v = .int e)
  nilReads : ∀ o ∈ h.toList, o.type ≠ .ok → ∀ m ∈ o.value, m.f = .r → m.v = .nil
  okReads : ∀ o ∈ h.toList, o.type = .ok → ∀ m ∈ o.value, m.f = .r →
    m.v = .nil ∨ ∃ l, m.v = .list l ∧ l.Nodup
  uniq : ∀ o ∈ h.toList, ∀ o' ∈ h.toList, o.type ≠ .invoke → o'.type ≠ .invoke →
    ∀ k e, e ∈ appsOf o k → e ∈ appsOf o' k → o.index = o'.index
  uniqIn : ∀ o ∈ h.toList, ∀ k, (appsOf o k).Nodup

/-- An interpretation: who committed, and each key's version order (its writers). -/
structure Interp where
  com : Nat → Prop
  ord : Nat → List Nat

namespace Interp
variable {h : History}

/-- Version `i` of `k`: the first `i` writers' appends. -/
def chainUpTo (h : History) (I : Interp) (k i : Nat) : List Int :=
  ((I.ord k).take i).flatMap fun w => apps h w k

/-- The last version of `k`. -/
def chainAll (h : History) (I : Interp) (k : Nat) : List Int := chainUpTo h I k (I.ord k).length

structure Clean (h : History) (I : Interp) : Prop where
  okCom : ∀ i o, h[i]? = some o → o.type = .ok → I.com i
  comPoss : ∀ i, I.com i → ∃ o, h[i]? = some o ∧ (o.type = .ok ∨ o.type = .info)
  ordNodup : ∀ k, (I.ord k).Nodup
  ordMem : ∀ k w, w ∈ I.ord k ↔ I.com w ∧ apps h w k ≠ []
  extRead : ∀ t o, h[t]? = some o → o.type = .ok → ∀ j m, o.value[j]? = some m → m.f = .r →
    appsBefore o j m.k = [] → ∃ i ≤ (I.ord m.k).length, toL m.v = chainUpTo h I m.k i ∧ t ∉ (I.ord m.k).take i
  intRead : ∀ t o, h[t]? = some o → o.type = .ok → ∀ j m, o.value[j]? = some m → m.f = .r →
    appsBefore o j m.k ≠ [] → ∃ i, (I.ord m.k)[i]? = some t ∧ toL m.v = chainUpTo h I m.k i ++ appsBefore o j m.k

/-- An external read of `k` by `t` returned version `i`. -/
def ExtRead (h : History) (I : Interp) (t k i : Nat) : Prop :=
  ∃ o j m, h[t]? = some o ∧ o.type = .ok ∧ o.value[j]? = some m ∧ m.f = .r ∧ m.k = k ∧
    appsBefore o j k = [] ∧ toL m.v = chainUpTo h I k i

/-- The interpretation's DSG. -/
def dsg (h : History) (I : Interp) : DSG where
  ww a b := ∃ k i, (I.ord k)[i]? = some a ∧ (I.ord k)[i + 1]? = some b
  wr a b := ∃ k i, ExtRead h I b k (i + 1) ∧ (I.ord k)[i]? = some a ∧ a ≠ b
  rw a b := ∃ k i, ExtRead h I a k i ∧ (I.ord k)[i]? = some b ∧ a ≠ b
  so a b := a ≠ b ∧ (∃ oa ob, h[a]? = some oa ∧ oa.type = .ok ∧ h[b]? = some ob ∧ oa.process = ob.process) ∧
    I.com b ∧ a < invIdx h b
  rt a b := a ≠ b ∧ (∃ oa, h[a]? = some oa ∧ oa.type = .ok) ∧ I.com b ∧ a < invIdx h b

theorem dsg_rw_irrefl (I : Interp) : ∀ a, ¬ (dsg h I).rw a a := by
  intro a ⟨_, _, _, _, hne⟩; exact hne rfl

end Interp

end Elle.R4.LA

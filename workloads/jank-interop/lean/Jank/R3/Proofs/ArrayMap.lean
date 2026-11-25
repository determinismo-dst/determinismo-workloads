import Jank.ArrayMap

/-!
# Array-map transients after the clone fix: the source never changes (round 3, proofs)

Round 1 (D14) found that a transient array map wrote into its persistent source; at 7135b7708
`to_transient` clones (transient_array_map.cpp:24-27), and `exhaust` over 3 operations from
`{}` and `{:a 0 :b 1}` was complete over 33,849 timelines with nothing found. Here the heap
lemmas of the replica (`Jank.ArrayMap`: `native_array_map` as arrays in a heap,
`insert_or_assign`, `erase`'s in-place shift, `make_next_array`, `clone`) and the step's
invariant, for any number of operations.

The heap: reads after an allocation or a write.
-/

namespace Jank.R3.Proofs.ArrayMap

open Jank.ArrayMap

/-- The slots of the array at `a` (none: no such array). -/
def slots (h : Heap) (a : Nat) : Array (Option Nat) := (h.arrays.getD a { slots := #[] }).slots

theorem read_eq (h : Heap) (a i : Nat) : h.read a i = (slots h a).getD i none := rfl

theorem slots_alloc (h : Heap) (s : Array (Option Nat)) (a : Nat) :
    slots (h.alloc s).1 a = if a = h.arrays.size then s else slots h a := by
  simp only [slots, Heap.alloc, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split
  · simp
  · rfl

theorem alloc_addr (h : Heap) (s : Array (Option Nat)) : (h.alloc s).2 = h.arrays.size := rfl

theorem alloc_size (h : Heap) (s : Array (Option Nat)) : (h.alloc s).1.arrays.size = h.arrays.size + 1 := by
  simp [Heap.alloc]

theorem slots_write (h : Heap) (a i v b : Nat) :
    slots (h.write a i v) b = if b = a then (slots h a).set! i (some v) else slots h b := by
  simp only [slots, Heap.write, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases hb : b = a
  · subst hb; simp only [↓reduceIte]
    cases h.arrays[b]? <;> simp
  · simp only [hb, ↓reduceIte]
    rw [if_neg (Ne.symm hb)]

theorem write_size (h : Heap) (a i v : Nat) : (h.write a i v).arrays.size = h.arrays.size := by
  simp [Heap.write]

theorem read_write (h : Heap) (a i v b j : Nat) :
    (h.write a i v).read b j = if b = a ∧ j = i ∧ i < (slots h a).size then some v else h.read b j := by
  rw [read_eq, read_eq, slots_write]
  by_cases hb : b = a
  · subst hb
    simp only [↓reduceIte, true_and]
    simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
    by_cases hj : j = i
    · subst hj
      by_cases hi : j < (slots h b).size
      · simp [hi]
      · simp [hi]
    · simp [hj, Ne.symm hj]
  · simp [hb]

theorem read_alloc (h : Heap) (s : Array (Option Nat)) (b j : Nat) :
    (h.alloc s).1.read b j = if b = h.arrays.size then s.getD j none else h.read b j := by
  rw [read_eq, read_eq, slots_alloc]
  split <;> rfl

theorem read_write_ne (h : Heap) (a i v b j : Nat) (hb : b ≠ a) : (h.write a i v).read b j = h.read b j := by
  rw [read_write]; simp [hb]

theorem read_alloc_lt (h : Heap) (s : Array (Option Nat)) (b j : Nat) (hb : b < h.arrays.size) :
    (h.alloc s).1.read b j = h.read b j := by
  rw [read_alloc]; simp [Nat.ne_of_lt hb]

/-- The heap only grows. -/
theorem write_size' (h : Heap) (a i v : Nat) : h.arrays.size ≤ (h.write a i v).arrays.size :=
  Nat.le_of_eq (write_size h a i v).symm

theorem fold_frame (b j : Nat) (g : Heap → Nat → Heap) (hg : ∀ h x, (g h x).read b j = h.read b j) :
    ∀ (js : List Nat) (h : Heap), (js.foldl g h).read b j = h.read b j
  | [], _ => rfl
  | x :: xs, h => by rw [List.foldl_cons, fold_frame b j g hg xs, hg]

theorem fold_size (g : Heap → Nat → Heap) (hg : ∀ h x, (g h x).arrays.size = h.arrays.size) :
    ∀ (js : List Nat) (h : Heap), (js.foldl g h).arrays.size = h.arrays.size
  | [], _ => rfl
  | x :: xs, h => by rw [List.foldl_cons, fold_size g hg xs, hg]

/-! ## What the transient operations touch -/

/-- `make_next_array`: writes only the map's own array, or allocates a new one. -/
theorem makeNextArray_frame (h : Heap) (prev cap length key value : Nat) (b j : Nat) (hb : b ≠ prev)
    (hbs : b < h.arrays.size) :
    (makeNextArray h prev cap length key value).1.read b j = h.read b j ∧
    h.arrays.size ≤ (makeNextArray h prev cap length key value).1.arrays.size ∧
    ((makeNextArray h prev cap length key value).2 = prev ∨
     (makeNextArray h prev cap length key value).2 = h.arrays.size) := by
  unfold makeNextArray
  split
  · refine ⟨?_, ?_, Or.inl rfl⟩
    · rw [read_write_ne _ _ _ _ _ _ hb, read_write_ne _ _ _ _ _ _ hb]
    · simp [write_size]
  · refine ⟨read_alloc_lt _ _ _ _ hbs, by simp [alloc_size], Or.inr rfl⟩

theorem insertOrAssign_frame (h : Heap) (m : NativeMap) (k v : Nat) (b j : Nat) (hb : b ≠ m.data)
    (hbs : b < h.arrays.size) :
    (insertOrAssign h m k v).1.read b j = h.read b j ∧
    h.arrays.size ≤ (insertOrAssign h m k v).1.arrays.size ∧
    ((insertOrAssign h m k v).2.data = m.data ∨ (insertOrAssign h m k v).2.data = h.arrays.size) := by
  unfold insertOrAssign
  split
  · exact ⟨read_write_ne _ _ _ _ _ _ hb, write_size' _ _ _ _, by simp⟩
  · unfold insertUnique
    exact makeNextArray_frame h m.data m.cap m.length k v b j hb hbs

/-- `erase`'s in-place shift writes only the map's own array. -/
theorem erase_frame (h : Heap) (m : NativeMap) (k : Nat) (b j : Nat) (hb : b ≠ m.data) :
    (erase h m k).1.read b j = h.read b j ∧ (erase h m k).1.arrays.size = h.arrays.size ∧
    (erase h m k).2.data = m.data := by
  unfold erase
  split
  · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨fold_frame b j _ ?_ _ _, fold_size _ ?_ _ _, rfl⟩
    · intro h0 x
      simp only
      split <;> split <;> simp only [read_write_ne _ _ _ _ _ _ hb]
    · intro h0 x
      simp only
      split <;> split <;> simp only [write_size]

/-- `assoc!` and `dissoc!` on the transient, one after another (`true`: `assoc!` with a value). -/
def applyOps (h : Heap) (t : Transient) : List (Bool × Key × Val) → Heap × Transient
  | [] => (h, t)
  | (isAssoc, k, v) :: rest =>
    let r := if isAssoc then jAssocBang h t k v else jDissocBang h t k
    match r with
    | .ok (h', t') => applyOps h' t' rest
    | .error _ => applyOps h t rest

theorem assocBang_res (h : Heap) (t : Transient) (k v : Nat) (h' : Heap) (t' : Transient)
    (hr : jAssocBang h t k v = .ok (h', t')) :
    (h' = h ∧ t'.data = t.data) ∨
    (h' = (insertOrAssign h t.data k v).1 ∧ t'.data = (insertOrAssign h t.data k v).2) := by
  unfold jAssocBang at hr
  split at hr
  · cases hr
  · split at hr
    · injection hr with hr; injection hr with h1 h2; subst h1; subst h2; exact Or.inl ⟨rfl, rfl⟩
    · split at hr
      · injection hr with hr; injection hr with h1 h2; subst h1; subst h2; exact Or.inl ⟨rfl, rfl⟩
      · generalize hio : insertOrAssign h t.data k v = r at hr
        obtain ⟨h1, d1⟩ := r
        injection hr with hr; injection hr with e1 e2; subst e1; subst e2
        exact Or.inr ⟨rfl, rfl⟩

theorem dissocBang_res (h : Heap) (t : Transient) (k : Nat) (h' : Heap) (t' : Transient)
    (hr : jDissocBang h t k = .ok (h', t')) :
    (h' = h ∧ t'.data = t.data) ∨ (h' = (erase h t.data k).1 ∧ t'.data = (erase h t.data k).2) := by
  unfold jDissocBang at hr
  split at hr
  · cases hr
  · split at hr
    · injection hr with hr; injection hr with h1 h2; subst h1; subst h2; exact Or.inl ⟨rfl, rfl⟩
    · generalize hio : erase h t.data k = r at hr
      obtain ⟨h1, d1⟩ := r
      injection hr with hr; injection hr with e1 e2; subst e1; subst e2
      exact Or.inr ⟨rfl, rfl⟩

/-- The transient's array is at or past `lo`, and the heap only grows: what every operation keeps;
so every operation leaves the arrays below `lo` alone. -/
theorem applyOps_frame (lo : Nat) :
    ∀ (ops : List (Bool × Key × Val)) (h : Heap) (t : Transient), lo ≤ t.data.data → lo ≤ h.arrays.size →
      ∀ b j, b < lo → (applyOps h t ops).1.read b j = h.read b j
  | [], h, t, _, _, b, j, _ => rfl
  | (isAssoc, k, v) :: rest, h, t, ht, hh, b, j, hb => by
    have hne : b ≠ t.data.data := by omega
    -- one operation: the result keeps the frame
    have one : ∀ h' t', (if isAssoc then jAssocBang h t k v else jDissocBang h t k) = .ok (h', t') →
        h'.read b j = h.read b j ∧ lo ≤ t'.data.data ∧ lo ≤ h'.arrays.size := by
      intro h' t' hr
      cases isAssoc with
      | true =>
        simp only [↓reduceIte] at hr
        rcases assocBang_res h t k v h' t' hr with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · subst e1; exact ⟨rfl, by rw [e2]; exact ht, hh⟩
        · obtain ⟨hr1, hs1, hd1⟩ := insertOrAssign_frame h t.data k v b j hne (by omega)
          subst e1
          refine ⟨hr1, ?_, by omega⟩
          rw [e2]; rcases hd1 with hd1 | hd1 <;> rw [hd1] <;> omega
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hr
        rcases dissocBang_res h t k h' t' hr with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · subst e1; exact ⟨rfl, by rw [e2]; exact ht, hh⟩
        · obtain ⟨hr1, hs1, hd1⟩ := erase_frame h t.data k b j hne
          subst e1
          exact ⟨hr1, by rw [e2, hd1]; exact ht, by rw [hs1]; exact hh⟩
    simp only [applyOps]
    cases hr : (if isAssoc then jAssocBang h t k v else jDissocBang h t k) with
    | ok p =>
      obtain ⟨h', t'⟩ := p
      obtain ⟨e1, e2, e3⟩ := one h' t' hr
      simp only
      rw [applyOps_frame lo rest h' t' e2 e3 b j hb, e1]
    | error e =>
      simp only
      exact applyOps_frame lo rest h t ht hh b j hb

/-- D14 fixed, for every array map and every sequence of `assoc!`/`dissoc!` on its transient: the
map shows the same entries afterwards (`(transient m)` clones: transient_array_map.cpp:24-27). -/
theorem transient_keeps_source (h : Heap) (nm : NativeMap) (hnm : nm.length = 0 ∨ nm.data < h.arrays.size)
    (ops : List (Bool × Key × Val)) :
    nm.entries (applyOps (jTransient (.array nm) h).1 (jTransient (.array nm) h).2 ops).1 = nm.entries h := by
  rcases hnm with h0 | hlt
  · simp [NativeMap.entries, h0]
  · unfold NativeMap.entries
    congr 1
    funext i
    have key : ∀ j, (applyOps (jTransient (.array nm) h).1 (jTransient (.array nm) h).2 ops).1.read nm.data j =
        h.read nm.data j := by
      intro j
      rw [applyOps_frame h.arrays.size ops _ _ (by simp [jTransient, clone, alloc_addr, Heap.alloc])
        (by simp [jTransient, clone, Heap.alloc]) nm.data j hlt]
      simp only [jTransient, clone]
      exact read_alloc_lt _ _ _ _ hlt
    rw [key, key]

end Jank.R3.Proofs.ArrayMap

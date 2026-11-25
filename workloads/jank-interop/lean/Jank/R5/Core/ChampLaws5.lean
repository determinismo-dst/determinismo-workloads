import Jank.R3.Immer.ChampLaws

/-!
# Round 5, core: CHAMP laws beyond get-after-add, for every input

Round 3's `get_add` (`Jank/R3/Immer/ChampLaws.lean`) is `get` after `add`. Here, over the same
replica of immer's `champ.hpp` (`Jank/R3/Immer/Champ.lean`) and for every champ satisfying round 3's
`wfNode` (bitmaps below 2^32 and disjoint, buffers holding their popcounts, collision nodes of at
least two values at the last level):

- ★ `added_doAdd` / `size_add`: `add`'s `added` flag is exactly "`get` found nothing", so
  `count` after `assoc`/`conj` grows by one iff the key was absent, for any hash and equality
  (the walk `do_add` takes is `get`'s). With the replaced pair kept (IM1): `(count (assoc m k x))`.
- ★ `added_doAddMut` / `size_addMut`: the transient path (`add_mut`, `assoc!`/`conj!`) sets the same
  flag, whether it mutates in place or copies: the transient count agrees with the persistent one.
- ★ `doSub_absent` / `sub_absent`: removing an absent key returns the same champ and leaves the
  allocator untouched (`dissoc`/`disj` of an absent key is the identity); ★ `doSubMut_absent` /
  `subMut_absent` for `dissoc!`/`disj!`.
- ★ `doSub_found` / `size_sub`: removing a present key gives a tree (never the root-level
  "singleton", which immer marks unreachable), so `count` drops by one.

What these need of the hash and equality: only that the query `k` and the value `v` agree
(`hashK k = hashT v`, `eqTK x k = eqTT x v` for every stored `x`), which holds for jank's maps and
sets by construction (`mapCfg`, `setCfg`). They do not need `=` to agree with the hash: the laws
are about `get` (the walk on `k`'s hash path), so with jank's equality (D12, R55) they hold as
stated; what breaks is the link between `get` and `=`-membership, shown by the searches.
-/

namespace Jank.R3.Immer.Champ

variable {α κ : Type}

/-! ## Lists -/

theorem find_findIdx_isNone {β : Type} (p : β → Bool) :
    ∀ xs : List β, (xs.find? p).isNone = (xs.findIdx? p).isNone
  | [] => rfl
  | x :: xs => by
    rw [List.find?_cons, List.findIdx?_cons]
    cases p x
    · simp [find_findIdx_isNone p xs]
    · rfl

theorem getElem?_of_lt {β : Type} [Inhabited β] (l : List β) (i : Nat) (h : i < l.length) :
    l[i]? = some (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-! ## The walk, one level -/

/-- The level's bit, in `get`'s form and in `do_add`'s. -/
theorem bit_forms (h r : Nat) :
    1 <<< ((h >>> (65 - 5 * (r + 1))) &&& 31) = bitAt h (maxShift - 5 * (r + 1)) := by
  rw [hidx]; rfl

theorem testBit_of_bne (x d : Nat) (hx : (x &&& 1 <<< d != 0) = true) : x.testBit d = true := by
  rw [one_shl, and_pow_bne] at hx; exact hx

/-- In a well-formed node, the data slot a set data bit names exists. -/
theorem data_slot_lt (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (D : Nat) (hD : D < 32)
    (hB : (N.datamap &&& 1 <<< D != 0) = true) :
    N.dataCountBit (1 <<< D) < N.values.length := by
  obtain ⟨_, hvals, _⟩ := wf_facts r N hw
  have := popcount_lt N.datamap D hD (testBit_of_bne _ _ hB)
  unfold Node.dataCountBit
  rw [one_shl]
  omega

/-- In a well-formed node, the child a set node bit names is well formed. -/
theorem child_wf (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (D : Nat) (hD : D < 32)
    (hA : (N.nodemap &&& 1 <<< D != 0) = true) :
    wfNode r (N.child (N.childrenCountBit (1 <<< D))) = true := by
  obtain ⟨hcs, _, hch⟩ := wf_facts r N hw
  have hlt := popcount_lt N.nodemap D hD (testBit_of_bne _ _ hA)
  apply hch
  unfold Node.child Node.childrenCountBit
  rw [one_shl]
  exact getD_mem_take _ _ _ _ hlt (by omega)

/-! ## `count` after `add` -/

/-- ★ `do_add`'s `added` is exactly "`get` along the same hash found nothing". -/
theorem added_doAdd [Inhabited α] (cfg : Cfg α κ) (k : κ) (v : α) (h : Nat)
    (he : ∀ x, cfg.eqTK x k = cfg.eqTT x v) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      ((doAdd cfg r N v h).run s).1.2 = (getLoop cfg k r N (h >>> (65 - 5 * r))).isNone := by
  intro r
  induction r with
  | zero =>
    intro _ N s _
    have hfe : (fun x => cfg.eqTK x k) = (fun x => cfg.eqTT x v) := funext he
    rw [getLoop.eq_1, hfe, find_findIdx_isNone]
    rw [doAdd.eq_1]
    unfold findIdx?
    cases N.collisions.findIdx? (fun x => cfg.eqTT x v) <;> rfl
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 1 <<< D := by unfold bitAt; rw [hDdef]
    rw [getLoop.eq_2]
    dsimp only
    rw [bit_forms, hbit]
    by_cases hA : (N.nodemap &&& 1 <<< D != 0) = true
    · have e : ((doAdd cfg (r + 1) N v h).run s).1.2 =
          ((doAdd cfg r (N.child (N.childrenCountBit (1 <<< D))) v h).run s).1.2 := by
        rw [doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA]; rfl
      rw [e, if_pos hA, shr_step h r hr]
      exact ih (by omega) _ s (child_wf r N hw D hD hA)
    · by_cases hB : (N.datamap &&& 1 <<< D != 0) = true
      · have hlt := data_slot_lt r N hw D hD hB
        have e : ((doAdd cfg (r + 1) N v h).run s).1.2 =
            !cfg.eqTT (N.values.getD (N.dataCountBit (1 <<< D)) default) v := by
          rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA, if_pos hB]
          split <;> simp_all <;> rfl
        rw [e, if_neg hA, if_pos hB, getElem?_of_lt _ _ hlt]
        dsimp only
        rw [he]
        split <;> simp_all
      · have e : ((doAdd cfg (r + 1) N v h).run s).1.2 = true := by
          rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA, if_neg hB]; rfl
        rw [e, if_neg hA, if_neg hB]
        rfl

/-- ★ **`count` after `add`**: grows by one exactly when `get` of the key found nothing. -/
theorem size_add [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (v : α) (k : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hk : cfg.hashK k = cfg.hashT v)
    (he : ∀ x, cfg.eqTK x k = cfg.eqTT x v) :
    ((c.add cfg v).run s).1.size = c.size + (if Champ.get cfg c k = none then 1 else 0) := by
  have e : ((c.add cfg v).run s).1.size =
      c.size + (if ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.2 then 1 else 0) := rfl
  have := added_doAdd cfg k v (cfg.hashT v) he 13 (Nat.le_refl _) c.root s hw
  rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero] at this
  rw [e, this]
  unfold Champ.get
  rw [hk]
  cases getLoop cfg k 13 c.root (cfg.hashT v) <;> rfl

/-! ## The transient `add_mut` agrees -/

/-- ★ `do_add_mut`'s `added` is the persistent one's: "`get` found nothing", on every branch
(mutating in place, or copying through `do_add` when the node is not owned). -/
theorem added_doAddMut [Inhabited α] (cfg : Cfg α κ) (e : Nat) (k : κ) (v : α) (h : Nat)
    (he : ∀ x, cfg.eqTK x k = cfg.eqTT x v) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      ((doAddMut cfg e r N v h).run s).1.2.1 = (getLoop cfg k r N (h >>> (65 - 5 * r))).isNone := by
  intro r
  induction r with
  | zero =>
    intro _ N s _
    have hfe : (fun x => cfg.eqTK x k) = (fun x => cfg.eqTT x v) := funext he
    rw [getLoop.eq_1, hfe, find_findIdx_isNone]
    rw [doAddMut.eq_1]
    unfold findIdx?
    cases N.collisions.findIdx? (fun x => cfg.eqTT x v) with
    | none => simp only [Option.isNone_none]; split <;> rfl
    | some pos =>
      simp only [Option.isNone_some]
      split
      · cases N <;> rfl
      · rfl
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 1 <<< D := by unfold bitAt; rw [hDdef]
    rw [getLoop.eq_2]
    dsimp only
    rw [bit_forms, hbit]
    by_cases hA : (N.nodemap &&& 1 <<< D != 0) = true
    · rw [if_pos hA, shr_step h r hr]
      have hcw := child_wf r N hw D hD hA
      by_cases hm : N.canMutate e = true
      · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1.2.1 =
            ((doAddMut cfg e r (N.child (N.childrenCountBit (1 <<< D))) v h).run s).1.2.1 := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_pos hA, if_pos hm]
          cases N <;> rfl
        rw [e1]
        exact ih (by omega) _ s hcw
      · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1.2.1 =
            ((doAdd cfg r (N.child (N.childrenCountBit (1 <<< D))) v h).run s).1.2 := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_pos hA, if_neg hm]; rfl
        rw [e1]
        exact added_doAdd cfg k v h he r (by omega) _ s hcw
    · by_cases hB : (N.datamap &&& 1 <<< D != 0) = true
      · have hlt := data_slot_lt r N hw D hD hB
        have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1.2.1 =
            !cfg.eqTT (N.values.getD (N.dataCountBit (1 <<< D)) default) v := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA, if_pos hB]
          split
          · next hE => simp only [hE, Bool.not_true]; split <;> rfl
          · next hE => simp only [Bool.not_eq_true] at hE; simp only [hE, Bool.not_false]; split <;> rfl
        rw [e1, if_neg hA, if_pos hB, getElem?_of_lt _ _ hlt]
        dsimp only
        rw [he]
        split <;> simp_all
      · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1.2.1 = true := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA, if_neg hB]; split <;> rfl
        rw [e1, if_neg hA, if_neg hB]
        rfl

/-- ★ **`count` after `assoc!`/`conj!`** equals `count` after `assoc`/`conj`. -/
theorem size_addMut [Inhabited α] (cfg : Cfg α κ) (e : Nat) (c : Champ α) (v : α) (k : κ) (s s' : Al)
    (hw : wfNode 13 c.root = true) (hk : cfg.hashK k = cfg.hashT v)
    (he : ∀ x, cfg.eqTK x k = cfg.eqTT x v) :
    ((c.addMut cfg e v).run s).1.size = ((c.add cfg v).run s').1.size := by
  have e1 : ((c.addMut cfg e v).run s).1.size =
      c.size + (if ((doAddMut cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1 then 1 else 0) := rfl
  have := added_doAddMut cfg e k v (cfg.hashT v) he 13 (Nat.le_refl _) c.root s hw
  rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero] at this
  rw [e1, this, size_add cfg c v k s' hw hk he]
  unfold Champ.get
  rw [hk]
  cases getLoop cfg k 13 c.root (cfg.hashT v) <;> rfl

/-! ## Removing an absent key -/

/-- ★ `do_sub` of a key `get` does not find: nothing, and no allocation. -/
theorem doSub_absent [Inhabited α] (cfg : Cfg α κ) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      getLoop cfg k r N (h >>> (65 - 5 * r)) = none → (doSub cfg k r N h).run s = (.nothing, s) := by
  intro r
  induction r with
  | zero =>
    intro _ N s _ hg
    rw [getLoop.eq_1] at hg
    have h2 : (N.collisions.findIdx? fun x => cfg.eqTK x k) = none := by
      have := find_findIdx_isNone (fun x => cfg.eqTK x k) N.collisions
      rw [hg] at this
      exact Option.isNone_iff_eq_none.mp this.symm
    rw [doSub.eq_1]
    unfold findIdx?
    simp only [h2]
    rfl
  | succ r ih =>
    intro hr N s hw hg
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 1 <<< D := by unfold bitAt; rw [hDdef]
    rw [getLoop.eq_2] at hg
    dsimp only at hg
    rw [bit_forms, hbit] at hg
    rw [doSub.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : (N.nodemap &&& 1 <<< D != 0) = true
    · rw [if_pos hA, shr_step h r hr] at hg
      rw [if_pos hA]
      have := ih (by omega) _ s (child_wf r N hw D hD hA) hg
      simp only [StateT.run_bind, this]
      rfl
    · by_cases hB : (N.datamap &&& 1 <<< D != 0) = true
      · have hlt := data_slot_lt r N hw D hD hB
        rw [if_neg hA, if_pos hB, getElem?_of_lt _ _ hlt] at hg
        dsimp only at hg
        have hE : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k = false := by
          cases hc : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k
          · rfl
          · rw [hc] at hg; simp at hg
        rw [if_neg hA, if_pos hB]
        rw [if_neg (show ¬ (cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k = true) by rw [hE]; simp)]
        rfl
      · rw [if_neg hA, if_neg hB]
        rfl

/-- ★ **`dissoc`/`disj` of an absent key** returns the champ itself and allocates nothing. -/
theorem sub_absent [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (k : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hg : Champ.get cfg c k = none) :
    (c.sub cfg k).run s = (c, s) := by
  have := doSub_absent cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    (by rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero]; exact hg)
  unfold Champ.sub
  simp only [StateT.run_bind, this]
  rfl

/-- ★ `do_sub_mut` of a key `get` does not find: nothing, and no allocation, on the mutating and
the copying branch alike. -/
theorem doSubMut_absent [Inhabited α] (cfg : Cfg α κ) (e : Nat) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      getLoop cfg k r N (h >>> (65 - 5 * r)) = none →
      (doSubMut cfg e k r N h).run s = ({ r := .nothing }, s) := by
  intro r
  induction r with
  | zero =>
    intro _ N s _ hg
    rw [getLoop.eq_1] at hg
    have h2 : (N.collisions.findIdx? fun x => cfg.eqTK x k) = none := by
      have := find_findIdx_isNone (fun x => cfg.eqTK x k) N.collisions
      rw [hg] at this
      exact Option.isNone_iff_eq_none.mp this.symm
    rw [doSubMut.eq_1]
    unfold findIdx?
    simp only [h2]
    rfl
  | succ r ih =>
    intro hr N s hw hg
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 1 <<< D := by unfold bitAt; rw [hDdef]
    rw [getLoop.eq_2] at hg
    dsimp only at hg
    rw [bit_forms, hbit] at hg
    rw [doSubMut.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : (N.nodemap &&& 1 <<< D != 0) = true
    · rw [if_pos hA, shr_step h r hr] at hg
      rw [if_pos hA]
      have hcw := child_wf r N hw D hD hA
      by_cases hm : N.canMutate e = true
      · have := ih (by omega) _ s hcw hg
        simp only [hm, if_true, StateT.run_bind, this]
        rfl
      · have := doSub_absent cfg k h r (by omega) _ s hcw hg
        simp only [hm, Bool.false_eq_true, if_false, StateT.run_bind, this]
        rfl
    · by_cases hB : (N.datamap &&& 1 <<< D != 0) = true
      · have hlt := data_slot_lt r N hw D hD hB
        rw [if_neg hA, if_pos hB, getElem?_of_lt _ _ hlt] at hg
        dsimp only at hg
        have hE : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k = false := by
          cases hc : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k
          · rfl
          · rw [hc] at hg; simp at hg
        rw [if_neg hA, if_pos hB]
        rw [if_neg (show ¬ (cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k = true) by rw [hE]; simp)]
        rfl
      · rw [if_neg hA, if_neg hB]
        rfl

/-- ★ **`dissoc!`/`disj!` of an absent key** leaves the transient's champ and the allocator. -/
theorem subMut_absent [Inhabited α] (cfg : Cfg α κ) (e : Nat) (c : Champ α) (k : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hg : Champ.get cfg c k = none) :
    (c.subMut cfg e k).run s = (c, s) := by
  have := doSubMut_absent cfg e k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    (by rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero]; exact hg)
  unfold Champ.subMut
  simp only [StateT.run_bind, this]
  rfl

/-! ## Removing a present key -/

def Sub.isNothing : Sub α → Bool
  | .nothing => true
  | _ => false

def Sub.isTree : Sub α → Bool
  | .tree _ => true
  | _ => false

/-- ★ `do_sub` of a key `get` finds is never "nothing"; at the root (shift 0) it is a tree. -/
theorem doSub_found [Inhabited α] (cfg : Cfg α κ) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      getLoop cfg k r N (h >>> (65 - 5 * r)) ≠ none →
      ((doSub cfg k r N h).run s).1.isNothing = false ∧
      (r = 13 → ((doSub cfg k r N h).run s).1.isTree = true) := by
  intro r
  induction r with
  | zero =>
    intro _ N s _ hg
    rw [getLoop.eq_1] at hg
    have h2 : (N.collisions.findIdx? fun x => cfg.eqTK x k).isNone = false := by
      rw [← find_findIdx_isNone]
      cases hf : N.collisions.find? (fun x => cfg.eqTK x k)
      · exact absurd hf hg
      · rfl
    refine ⟨?_, fun h0 => absurd h0 (by omega)⟩
    rw [doSub.eq_1]
    unfold findIdx?
    cases hx : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => rw [hx] at h2; cases h2
    | some cur => dsimp only; split <;> rfl
  | succ r ih =>
    intro hr N s hw hg
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 1 <<< D := by unfold bitAt; rw [hDdef]
    rw [getLoop.eq_2] at hg
    dsimp only at hg
    rw [bit_forms, hbit] at hg
    rw [doSub.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : (N.nodemap &&& 1 <<< D != 0) = true
    · rw [if_pos hA, shr_step h r hr] at hg
      rw [if_pos hA]
      have ⟨hn, _⟩ := ih (by omega) _ s (child_wf r N hw D hD hA) hg
      simp only [StateT.run_bind]
      generalize ((doSub cfg k r (N.child (N.childrenCountBit (1 <<< D))) h).run s) = q at hn
      obtain ⟨sub, s1⟩ := q
      cases sub with
      | nothing => cases hn
      | singleton x =>
        constructor
        · split <;> rfl
        · intro h13
          have h0 : maxShift - 5 * (r + 1) = 0 := by unfold maxShift; omega
          split
          · next hc => simp [h0] at hc
          · rfl
      | tree t => exact ⟨rfl, fun _ => rfl⟩
    · by_cases hB : (N.datamap &&& 1 <<< D != 0) = true
      · have hlt := data_slot_lt r N hw D hD hB
        rw [if_neg hA, if_pos hB, getElem?_of_lt _ _ hlt] at hg
        dsimp only at hg
        have hE : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k = true := by
          cases hc : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k
          · rw [hc] at hg; simp at hg
          · rfl
        rw [if_neg hA, if_pos hB]
        rw [if_pos hE]
        constructor
        · split
          · rfl
          · split
            · split <;> rfl
            · rfl
        · intro h13
          have h0 : maxShift - 5 * (r + 1) = 0 := by unfold maxShift; omega
          split
          · rfl
          · split
            · split
              · next hc => omega
              · rfl
            · rfl
      · rw [if_neg hA, if_neg hB] at hg
        exact absurd rfl hg

/-- ★ **`count` after `dissoc`/`disj` of a present key** drops by one. -/
theorem size_sub [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (k : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hg : Champ.get cfg c k ≠ none) :
    ((c.sub cfg k).run s).1.size = c.size - 1 := by
  have ⟨_, ht⟩ := doSub_found cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    (by rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero]; exact hg)
  have ht := ht rfl
  unfold Champ.sub
  simp only [StateT.run_bind]
  generalize ((doSub cfg k 13 c.root (cfg.hashK k)).run s) = q at ht
  obtain ⟨sub, s1⟩ := q
  cases sub with
  | tree t => rfl
  | _ => cases ht

end Jank.R3.Immer.Champ

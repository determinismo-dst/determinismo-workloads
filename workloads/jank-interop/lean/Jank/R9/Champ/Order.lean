import Jank.R9.Champ.SeqF

/-!
# Round 9, CHAMP: with H8-1's fix, `assoc`/`conj` of a present key keeps every position

- ★ `addF_inPlace`: the fixed `do_add` (`assoc`/`conj`) of a value `v` that a stored value accepts
  (`added = false`) leaves the champ's iteration (`seq`, `keys`, `vals`, printing) EXACTLY as it was,
  except that the stored value at one position `j` is now `v` (`(iterNode N).set j v`), the stored
  value there being one `Equal` accepts. For every well-formed node, every hash, every equality.
- ★ `addMutF_inPlace`: the same for the fixed `do_add_mut` (`assoc!`/`conj!`), any owner token.
- ★ `addRootF_inPlace`, ★ `addMutRootF_inPlace`: at the root (`Champ.toList`).
- ★ `keys_kept`: for a map (pairs) whose step stores the STORED key with the new value (H8-1.diff's
  jank side: `set_keeping_key`), the key sequence is unchanged.

Round 3's (stock) `do_add` writes `v` first in a collision node (`v :: eraseAt xs pos`), which is
round 8's H8-1; round 8's `inPlace_eq_iff` showed the two differ exactly when `pos ≠ 0`.
-/

namespace Jank.R9.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ Jank.R8.Champ

variable {α κ : Type} [Inhabited α]

/-! ## Lists -/

/-- Setting one element of a list of lists' source sets one element of the flattened list. -/
theorem flatMap_set {β γ : Type} (f : β → List γ) (v : γ) :
    ∀ (L : List β) (i : Nat) (c c' : β) (j : Nat), L[i]? = some c → f c' = (f c).set j v → j < (f c).length →
      (L.set i c').flatMap f = (L.flatMap f).set (((L.take i).flatMap f).length + j) v ∧
        (L.flatMap f)[((L.take i).flatMap f).length + j]? = (f c)[j]?
  | [], _, _, _, _, hL, _, _ => by simp at hL
  | a :: t, 0, c, c', j, hL, hf, hj => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
    subst hL
    simp only [List.set_cons_zero, List.flatMap_cons, List.take_zero, List.flatMap_nil, List.length_nil,
      Nat.zero_add]
    refine ⟨?_, List.getElem?_append_left hj⟩
    rw [hf, List.set_append_left _ _ hj]
  | a :: t, i + 1, c, c', j, hL, hf, hj => by
    simp only [List.getElem?_cons_succ] at hL
    obtain ⟨h1, h2⟩ := flatMap_set f v t i c c' j hL hf hj
    simp only [List.set_cons_succ, List.flatMap_cons, List.take_succ_cons, List.length_append]
    refine ⟨?_, ?_⟩
    · rw [h1, List.set_append_right _ _ (by omega)]
      congr 2
      omega
    · rw [List.getElem?_append_right (by omega), ← h2]
      congr 1
      omega

theorem mkInner_parts (nm dm : Nat) (xs : List α) (cs : List (Node α)) (s : Al) :
    ((mkInner nm dm xs cs).run s).1.datamap = dm ∧ ((mkInner nm dm xs cs).run s).1.nodemap = nm ∧
      ((mkInner nm dm xs cs).run s).1.cs = cs ∧ ((mkInner nm dm xs cs).run s).1.values = xs := by
  cases xs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The fixed `do_add` -/

/-- ★ **With the fix, `assoc`/`conj` of a present key keeps every position**: when the fixed `do_add`
finds a stored value `x` that `Equal` accepts (`added = false`), the iteration of the result is the
old one with `v` at `x`'s position. For every well-formed node, every hash, every equality. -/
theorem addF_inPlace (cfg : Cfg α κ) (v : α) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true → ((doAddF cfg r N v h).run s).1.2 = false →
      ∃ j x, (iterNode r N)[j]? = some x ∧ cfg.eqTT x v = true ∧
        iterNode r ((doAddF cfg r N v h).run s).1.1 = (iterNode r N).set j v := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw hadd
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      rw [doAddF.eq_1] at hadd ⊢
      unfold findIdx? at hadd ⊢
      simp only [Node.collisions] at hadd ⊢
      cases hf : xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        rw [hf] at hadd
        exact absurd hadd (by simp)
      | some pos =>
        obtain ⟨hpos, hpx, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        refine ⟨pos, xs[pos], List.getElem?_eq_getElem hpos, hpx, ?_⟩
        rw [iterNode.eq_1, iterNode.eq_1]
        rfl
  | succ r ih =>
    intro hr N s hw hadd
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    obtain ⟨hcs, hvals, _⟩ := wf_facts r N hw
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have eP : ((doAddF cfg (r + 1) N v h).run s).1 =
          (((copyInnerReplace N (pos N.nodemap D) ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAddF.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      rw [eP] at hadd ⊢
      dsimp only at hadd ⊢
      generalize hc : N.cs.getD (pos N.nodemap D) Node.dummy = c at hcw hadd
      obtain ⟨j, x, hx, hxv, hit⟩ := ih (by omega) c s hcw hadd
      generalize hq : (doAddF cfg r c v h).run s = q at hit
      obtain ⟨⟨c', _⟩, s1⟩ := q
      dsimp only at hit
      have hi : pos N.nodemap D < (N.cs.take N.childrenCount).length := by
        rw [List.length_take]
        have := pos_lt_popcount N.nodemap D hD hA
        exact Nat.lt_min.mpr ⟨this, Nat.lt_of_lt_of_le this hcs⟩
      have hLi : (N.cs.take N.childrenCount)[pos N.nodemap D]? = some c := by
        rw [List.getElem?_eq_getElem hi, List.getElem_take, ← hc, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [List.length_take] at hi; omega)]
        rfl
      have hj : j < (iterNode r c).length := by
        rcases (List.getElem?_eq_some_iff.mp hx) with ⟨hj, _⟩; exact hj
      obtain ⟨fs1, fs2⟩ := flatMap_set (iterNode r) v (N.cs.take N.childrenCount) (pos N.nodemap D) c c' j hLi hit hj
      refine ⟨(N.values.take N.dataCount).length +
        (((N.cs.take N.childrenCount).take (pos N.nodemap D)).flatMap (iterNode r)).length + j, x, ?_, hxv, ?_⟩
      · rw [iterNode.eq_2, List.getElem?_append_right (by omega), Nat.add_assoc, Nat.add_sub_cancel_left, fs2, hx]
      · dsimp only
        have eN : ((copyInnerReplace N (pos N.nodemap D) c').run s1).1 =
            Node.inner s1.next 0 N.nodemap N.datamap N.vals (setL (N.cs.take N.childrenCount) (pos N.nodemap D) c') := rfl
        rw [eN]
        have hXv := values_vals N s1.next 0 N.nodemap N.datamap (setL (N.cs.take N.childrenCount) (pos N.nodemap D) c')
        have hXd : (Node.inner s1.next 0 N.nodemap N.datamap N.vals
            (setL (N.cs.take N.childrenCount) (pos N.nodemap D) c')).dataCount = N.dataCount := rfl
        have hXc : (Node.inner s1.next 0 N.nodemap N.datamap N.vals
            (setL (N.cs.take N.childrenCount) (pos N.nodemap D) c')).childrenCount = N.childrenCount := rfl
        have hXcs : (Node.inner s1.next 0 N.nodemap N.datamap N.vals
            (setL (N.cs.take N.childrenCount) (pos N.nodemap D) c')).cs =
              setL (N.cs.take N.childrenCount) (pos N.nodemap D) c' := rfl
        generalize Node.inner s1.next 0 N.nodemap N.datamap N.vals
            (setL (N.cs.take N.childrenCount) (pos N.nodemap D) c') = X at hXv hXd hXc hXcs
        rw [iterNode.eq_2, iterNode.eq_2, hXv, hXd, hXc, hXcs]
        try simp only [setL]
        rw [List.take_of_length_le (l := (N.cs.take N.childrenCount).set (pos N.nodemap D) c') (i := N.childrenCount)
          (by rw [List.length_set, List.length_take]; omega)]
        rw [fs1, List.set_append_right _ _ (by omega), Nat.add_assoc, Nat.add_sub_cancel_left]
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · have eP : ((doAddF cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceValue N (pos N.datamap D) v).run s).1, false) := by
            rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]; rfl
          rw [eP]
          dsimp only
          have hoff : pos N.datamap D < (N.values.take N.dataCount).length := by
            rw [List.length_take]
            have := pos_lt_popcount N.datamap D hD hB
            exact Nat.lt_min.mpr ⟨this, Nat.lt_of_lt_of_le this hvals⟩
          refine ⟨pos N.datamap D, N.values.getD (pos N.datamap D) default, ?_, hE, ?_⟩
          · rw [iterNode.eq_2, List.getElem?_append_left hoff, List.getElem?_eq_getElem hoff, List.getElem_take,
              List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_take] at hoff; omega)]
            rfl
          · have eN : ((copyInnerReplaceValue N (pos N.datamap D) v).run s).1 =
                ((mkInner N.nodemap N.datamap (setL (N.values.take N.dataCount) (pos N.datamap D) v)
                  (N.cs.take N.childrenCount)).run s).1 := rfl
            rw [eN]
            obtain ⟨hd1, hn1, hc1, hv1⟩ := mkInner_parts N.nodemap N.datamap
              (setL (N.values.take N.dataCount) (pos N.datamap D) v) (N.cs.take N.childrenCount) s
            generalize ((mkInner N.nodemap N.datamap (setL (N.values.take N.dataCount) (pos N.datamap D) v)
                  (N.cs.take N.childrenCount)).run s).1 = X at hd1 hn1 hc1 hv1
            have hXd : X.dataCount = N.dataCount := by simp only [Node.dataCount, hd1]
            have hXc : X.childrenCount = N.childrenCount := by simp only [Node.childrenCount, hn1]
            rw [iterNode.eq_2, iterNode.eq_2, hXd, hXc, hv1, hc1]
            rw [List.take_of_length_le (by unfold setL; rw [List.length_set, List.length_take]; omega)]
            rw [List.take_take, Nat.min_self]
            unfold setL
            rw [List.set_append_left _ _ hoff]
        · generalize hval : N.values.getD (pos N.datamap D) default = val at hE
          have eP : ((doAddF cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged none r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged none r v h val (cfg.hashT val)).run s).2).1, true) := by
            rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            rfl
          rw [eP] at hadd
          exact absurd hadd (by simp)
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have eP : ((doAddF cfg (r + 1) N v h).run s).1 = (((copyInnerInsertValue N (2 ^ D) v).run s).1, true) := by
          rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']; rfl
        rw [eP] at hadd
        exact absurd hadd (by simp)

/-- ★ The same for the fixed `do_add_mut` (`assoc!`/`conj!`), any owner token: through `addMutF_agree`
(exact agreement with the fixed `do_add`) and `agreeEq_iter`. -/
theorem addMutF_inPlace (cfg : Cfg α κ) (e : Nat) (v : α) (h : Nat) (r : Nat) (hr : r ≤ 13) (N : Node α) (s : Al)
    (hw : wfNode r N = true) (hadd : ((doAddMutF cfg e r N v h).run s).1.2.1 = false) :
    ∃ j x, (iterNode r N)[j]? = some x ∧ cfg.eqTT x v = true ∧
      iterNode r ((doAddMutF cfg e r N v h).run s).1.1 = (iterNode r N).set j v := by
  obtain ⟨hag, hflag⟩ := addMutF_agree cfg e v h r hr N s hw
  rw [hflag] at hadd
  obtain ⟨j, x, hx, hxv, hit⟩ := addF_inPlace cfg v h r hr N s hw hadd
  refine ⟨j, x, hx, hxv, ?_⟩
  rw [agreeEq_iter r _ _ (wf_doAddMutF cfg e v h r hr N s hw) (wf_doAddF cfg v h r hr N s hw) hag, hit]

/-- ★ At the root: `assoc`/`conj` of a present key (the size unchanged) keeps the seq order. -/
theorem addRootF_inPlace (cfg : Cfg α κ) (c : Champ α) (v : α) (s : Al) (hw : wfNode 13 c.root = true)
    (hsz : ((addRootF cfg c v).run s).1.size = c.size) :
    ∃ j x, c.toList[j]? = some x ∧ cfg.eqTT x v = true ∧ ((addRootF cfg c v).run s).1.toList = c.toList.set j v := by
  have hadd : ((doAddF cfg 13 c.root v (cfg.hashT v)).run s).1.2 = false := by
    have : c.size + (if ((doAddF cfg 13 c.root v (cfg.hashT v)).run s).1.2 then 1 else 0) = c.size := hsz
    cases hb : ((doAddF cfg 13 c.root v (cfg.hashT v)).run s).1.2
    · rfl
    · rw [hb] at this; simp at this
  exact addF_inPlace cfg v (cfg.hashT v) 13 (Nat.le_refl _) c.root s hw hadd

/-- ★ At the root: `assoc!`/`conj!` of a present key (the size unchanged) keeps the seq order. -/
theorem addMutRootF_inPlace (cfg : Cfg α κ) (e : Nat) (c : Champ α) (v : α) (s : Al) (hw : wfNode 13 c.root = true)
    (hsz : ((addMutRootF cfg e c v).run s).1.size = c.size) :
    ∃ j x, c.toList[j]? = some x ∧ cfg.eqTT x v = true ∧ ((addMutRootF cfg e c v).run s).1.toList = c.toList.set j v := by
  have hadd : ((doAddMutF cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1 = false := by
    have : c.size + (if ((doAddMutF cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1 then 1 else 0) = c.size := hsz
    cases hb : ((doAddMutF cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1
    · rfl
    · rw [hb] at this; simp at this
  exact addMutF_inPlace cfg e v (cfg.hashT v) 13 (Nat.le_refl _) c.root s hw hadd

/-- ★ For a map: when the stored entry at `j` has the key `k` and the step stores `(k, val)` (H8-1.diff's
jank side keeps the stored key), the key sequence is unchanged. -/
theorem keys_kept {β : Type} (l : List (α × β)) (j : Nat) (k : α) (b val : β) (hj : l[j]? = some (k, b)) :
    (l.set j (k, val)).map Prod.fst = l.map Prod.fst := by
  rw [List.map_set]
  have hj' : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have : (l.map Prod.fst)[j]? = some k := by rw [List.getElem?_map, hj]; rfl
  rw [show k = (l.map Prod.fst)[j]'(by simpa using hj') by
    rw [List.getElem?_eq_getElem (by simpa using hj')] at this; exact (Option.some.inj this).symm]
  exact List.set_getElem_self _

end Jank.R9.Champ

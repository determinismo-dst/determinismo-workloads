import Jank.R6.Champ.Laws
import Jank.R6.Champ.Mut

/-!
# Round 7, CHAMP: law 1 (`get` of another key) without round 6's invariant

Round 6 proved law 1 (`get_add_other`, `get_sub_other`: `get` of a key not `Equal` to the one added
or removed is unchanged) for champs meeting `Inv` (well formed, the hash-path invariant `HP`, no two
stored values `Equal`, `size` = the iteration's length). Here the premises are taken apart, over the
same replica of immer's `champ.hpp` (round 3, `Jank/R3/Immer/Champ.lean`):

- ★ `add_walk`, ★ `get_add_other_wf`: **law 1 for `add` holds for every well-formed champ** (no `HP`,
  no uniqueness, no size premise). What it uses of the equality is only: `v` is not `Equal` to the
  query, a stored value `Equal` to `v` is not `Equal` to the query, and a stored value `Equal` to the
  query hashes as the query (each a consequence of round 6's `Lawful`).
- ★ `sub_walk`, ★ `get_sub_other_hp`: **law 1 for `sub` holds for every well-formed champ meeting `HP`**
  (uniqueness and the size premise dropped).
- `law1_sub_fails_without_HP` (`decide +kernel`): `HP` cannot be dropped for `sub`. A well-formed
  champ over `Nat` with the lawful equality `==` and the identity hash, holding 225 and 289 in one
  level-1 node where 225 sits at bit 3 though its hash names bit 7: `get 225` is `none`, and after
  `sub 289` the collapse passes 225 up and inlines it at the root, where `get 225` finds it.
  `badChamp_not_HP`: that champ breaks `HP` (by `get_complete`).

Whether a jank program can build such a champ: no. `HP` is kept by `do_add`, `do_sub`, `do_add_mut`
and `do_sub_mut` for EVERY hash function and equality (round 6: `add_step`, `sub_step`,
`addMut_step`, `subMut_step`), and holds of `champ::empty()`; so a champ off its hash paths needs a
stored object whose `to_hash` changed while stored. Every jank `to_hash` is a function of a value that
does not change (immutable values, collections caching their hash, lazy seqs realized once), or
`object::to_hash`, the object's address (object.cpp 69-72) with identity `equal` (47-50), for the
mutable objects (atoms, volatiles, transients, arrays: none overrides either); Boehm's collector does
not move objects. So the `sub` counterexample is outside what jank builds, and law 1 holds for every
champ jank builds under a lawful equality (round 6), and for `add` under any well-formed one.
-/

namespace Jank.R7.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ

variable {α κ : Type}

/-! ## Lists -/

theorem find?_cons_false {β : Type} (p : β → Bool) (a : β) (l : List β) (h : p a = false) :
    (a :: l).find? p = l.find? p := by
  simp [h]

theorem find?_eraseAt_false {β : Type} (p : β → Bool) :
    ∀ (l : List β) (i : Nat), (∀ (hi : i < l.length), p l[i] = false) → (eraseAt l i).find? p = l.find? p
  | [], i, _ => by simp [eraseAt]
  | a :: l, 0, h => by
    have := h (by simp)
    simp only [eraseAt, List.take_zero, List.nil_append, List.drop_succ_cons, List.drop_zero]
    rw [find?_cons_false p a l (by simpa using this)]
  | a :: l, i + 1, h => by
    have ih := find?_eraseAt_false p l i (fun hi => by have := h (by simp; omega); simpa using this)
    unfold eraseAt at ih ⊢
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, List.find?_cons]
    rw [ih]

theorem find?_unique {β : Type} (p : β → Bool) (l : List β) (b : β) (hb : b ∈ l) (hpb : p b = true)
    (hu : ∀ x ∈ l, p x = true → x = b) : l.find? p = some b := by
  cases hf : l.find? p with
  | none => rw [List.find?_eq_none] at hf; exact absurd hpb (hf b hb)
  | some y => rw [hu y (List.mem_of_find?_eq_some hf) (List.find?_some hf)]

/-! ## The walk after an edit of one slot -/

variable [Inhabited α]

/-- The list `get`'s walk reaches through one slot. -/
def slotW (r : Nat) : Slot α → Nat → List α
  | .child c, h => walk r c h
  | .data x, _ => [x]
  | .empty, _ => []

theorem walk_succ_slotW (r : Nat) (N : Node α) (H : Nat) :
    walk (r + 1) N H = slotW r (slot N (H &&& 31)) (H >>> 5) := by
  rw [walk.eq_2]; cases slot N (H &&& 31) <;> rfl

theorem walk_edit (r : Nat) (N N' : Node α) (D : Nat) (X : Slot α) (he : Edit r N N' D X) (H : Nat) :
    walk (r + 1) N' H = if H &&& 31 = D then slotW r X (H >>> 5) else walk (r + 1) N H := by
  rw [walk_succ_slotW, he.2 _ (and31_lt H)]
  by_cases hd : H &&& 31 = D
  · rw [if_pos hd, if_pos hd]
  · rw [if_neg hd, if_neg hd, walk_succ_slotW]

/-- `get` of a query with hash `H` after an edit of slot `D`: only slot `D`'s walk can change. -/
theorem find_edit (p : α → Bool) (r : Nat) (hr : r + 1 ≤ 13) (N N' : Node α) (D : Nat) (X : Slot α)
    (he : Edit r N N' D X) (H : Nat)
    (hX : chunk r H = D →
      (slotW r X (H >>> (65 - 5 * r))).find? p = (slotW r (slot N D) (H >>> (65 - 5 * r))).find? p) :
    (walk (r + 1) N' (H >>> (65 - 5 * (r + 1)))).find? p = (walk (r + 1) N (H >>> (65 - 5 * (r + 1)))).find? p := by
  rw [walk_edit r N N' D X he, walk_succ_slotW r N, hidx, shr_step H r hr]
  by_cases hc : idxAt H (maxShift - 5 * (r + 1)) = D
  · rw [if_pos hc, hc]; exact hX hc
  · rw [if_neg hc]

/-! ## Law 1 for `add`, for every well-formed champ -/

/-- ★ `do_add` of `v` leaves `get` of a query (predicate `p`, hash `H`) unchanged, at every level, for
every well-formed node: no hash-path invariant, no uniqueness. -/
theorem add_walk (cfg : Cfg α κ) (v : α) (h : Nat) (hv : cfg.hashT v = h) (p : α → Bool) (H : Nat)
    (hpv : p v = false) (hpe : ∀ x, cfg.eqTT x v = true → p x = false)
    (hph : ∀ x, p x = true → cfg.hashT x = H) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      (walk r ((doAdd cfg r N v h).run s).1.1 (H >>> (65 - 5 * r))).find? p =
        (walk r N (H >>> (65 - 5 * r))).find? p := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      rw [doAdd.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases hf : xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        show (v :: xs).find? p = xs.find? p
        exact find?_cons_false p v xs hpv
      | some pos =>
        obtain ⟨hpos, hpx, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        show (v :: eraseAt xs pos).find? p = xs.find? p
        rw [find?_cons_false p v _ hpv]
        exact find?_eraseAt_false p xs pos (fun hi => hpe _ hpx)
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have e : ((doAdd cfg (r + 1) N v h).run s).1 =
          (((copyInnerReplace N (pos N.nodemap D) ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      rw [e]
      have o := add_step cfg v h hv r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
      have ihc := ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
      generalize (doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s = q at o ihc ⊢
      obtain ⟨⟨c1, a1⟩, s1⟩ := q
      dsimp only at o ihc ⊢
      have hE := edit_replace r N c1 D s1 hw hD hA o.wf
      apply find_edit p r hr N _ D _ hE H
      intro _
      rw [hs]; exact ihc
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have hs : slot N D = .data (N.values.getD (pos N.datamap D) default) := by
          unfold slot; rw [if_neg hA, if_pos hB]
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · -- `copy_inner_replace_value`
          have e : ((doAdd cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceValue N (pos N.datamap D) v).run s).1, false) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]; rfl
          rw [e]
          dsimp only
          have hE' := edit_replaceValue r N v D s hw hD hA0 hB
          apply find_edit p r hr N _ D _ hE' H
          intro _
          rw [hs]
          show [v].find? p = [N.values.getD (pos N.datamap D) default].find? p
          rw [find?_cons_false p v [] hpv, find?_cons_false p _ [] (hpe _ hE)]
        · -- `make_merged` below, `copy_inner_replace_merged`
          have e : ((doAdd cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged none r v h (N.values.getD (pos N.datamap D) default)
                  (cfg.hashT (N.values.getD (pos N.datamap D) default))).run s).1).run
                ((makeMerged none r v h (N.values.getD (pos N.datamap D) default)
                  (cfg.hashT (N.values.getD (pos N.datamap D) default))).run s).2).1, true) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]
            rfl
          rw [e]
          generalize hval : N.values.getD (pos N.datamap D) default = val at hs hE ⊢
          generalize hq : (makeMerged none r v h val (cfg.hashT val)).run s = q
          obtain ⟨m, s1⟩ := q
          dsimp only
          have hmw : wfNode r m = true := by
            have := wf_makeMerged none v val h (cfg.hashT val) r s; rw [hq] at this; exact this
          have hmi : (iterNode r m).Perm [v, val] := by
            have := iter_makeMerged none v val h (cfg.hashT val) r s; rw [hq] at this; exact this
          have hmh : HP cfg r m := by
            have := HP_makeMerged cfg none v val h (cfg.hashT val) hv rfl r s; rw [hq] at this; exact this
          have hE' := edit_replaceMerged r N m D s1 hw hD hA0 hB hmw
          apply find_edit p r hr N _ D _ hE' H
          intro _
          rw [hs]
          show (walk r m (H >>> (65 - 5 * r))).find? p = [val].find? p
          have hsub : ∀ x ∈ walk r m (H >>> (65 - 5 * r)), x = v ∨ x = val := by
            intro x hx
            have := hmi.subset (walk_sub r m _ hmw x hx)
            simpa using this
          cases hpval : p val
          · rw [find?_cons_false p val [] hpval, List.find?_nil, List.find?_eq_none]
            intro x hx
            rcases hsub x hx with h1 | h1 <;> rw [h1] <;> simp [hpv, hpval]
          · rw [show [val].find? p = some val by simp [List.find?_cons, hpval]]
            apply find?_unique p _ val
            · have hc := walk_complete cfg r (by omega) m hmw hmh val (hmi.symm.subset (by simp))
              rw [hph val hpval] at hc; exact hc
            · exact hpval
            · intro x hx hpx
              rcases hsub x hx with h1 | h1
              · rw [h1, hpv] at hpx; cases hpx
              · exact h1
      · -- an empty slot: `copy_inner_insert_value`
        have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have hs : slot N D = .empty := by unfold slot; rw [if_neg hA, if_neg hB]
        have e : ((doAdd cfg (r + 1) N v h).run s).1 = (((copyInnerInsertValue N (2 ^ D) v).run s).1, true) := by
          rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']; rfl
        rw [e]
        dsimp only
        have hE' := edit_insertValue r N v D s hw hD hA0 hB0
        apply find_edit p r hr N _ D _ hE' H
        intro _
        rw [hs]
        show [v].find? p = ([] : List α).find? p
        rw [find?_cons_false p v [] hpv]

/-- ★ **Law 1 for `add` (`assoc`/`conj`), for every well-formed champ**: under a lawful equality,
`get` of a key not `Equal` to the value added is unchanged. Round 6's `get_add_other` assumed `Inv`
(the hash-path invariant and uniqueness); neither is needed. -/
theorem get_add_other_wf {cfg : Cfg α κ} (L : Lawful cfg) (c : Champ α) (v : α) (k' : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hne : L.eqK (L.key v) k' = false) :
    Champ.get cfg ((c.add cfg v).run s).1 k' = Champ.get cfg c k' := by
  have o := add_step cfg v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw
  have hpv : cfg.eqTK v k' = false := by rw [L.eqTK_key]; exact hne
  have hpe : ∀ x, cfg.eqTT x v = true → cfg.eqTK x k' = false := by
    intro x hx
    cases hk : cfg.eqTK x k'
    · rfl
    · rw [L.eqTT_key] at hx; rw [L.eqTK_key] at hk
      rw [L.trans _ _ _ (L.symm _ _ hx) hk] at hne; cases hne
  have hph : ∀ x, cfg.eqTK x k' = true → cfg.hashT x = cfg.hashK k' :=
    fun x hx => (L.hash_of_eqTK x k' hx).symm
  have := add_walk cfg v (cfg.hashT v) rfl (fun x => cfg.eqTK x k') (cfg.hashK k') hpv hpe hph 13
    (Nat.le_refl _) c.root s hw
  rw [shr13] at this
  unfold Champ.get
  show getLoop cfg k' 13 ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.1 (cfg.hashK k') = _
  rw [getLoop_walk cfg k' 13 _ _ o.wf, getLoop_walk cfg k' 13 _ _ hw]
  exact this

/-! ## Law 1 for `sub`, for every well-formed champ meeting the hash-path invariant -/

/-- What `get` of a query (predicate `p`, hash `H`) sees in `do_sub`'s tree, against the node. -/
def SubWalk (r : Nat) (N : Node α) (p : α → Bool) (H : Nat) : Jank.R3.Immer.Champ.Sub α → Prop
  | .tree t => (walk r t (H >>> (65 - 5 * r))).find? p = (walk r N (H >>> (65 - 5 * r))).find? p
  | _ => True

/-- ★ `do_sub` of `k` leaves `get` of a query not `Equal` to `k`'s values unchanged, at every level,
for every well-formed node meeting `HP` (no uniqueness). -/
theorem sub_walk (cfg : Cfg α κ) (k : κ) (h : Nat) (p : α → Bool) (H : Nat)
    (hpk : ∀ y, cfg.eqTK y k = true → p y = false)
    (hph : ∀ x, p x = true → cfg.hashT x = H) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true → HP cfg r N →
      SubWalk r N p H ((doSub cfg k r N h).run s).1 := by
  intro r
  induction r with
  | zero =>
    intro _ N s _ _
    rw [doSub.eq_1]
    unfold findIdx?
    cases hf : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => trivial
    | some cur =>
      obtain ⟨hcur, hpc, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      dsimp only
      split
      · show (eraseAt N.collisions cur).find? p = N.collisions.find? p
        exact find?_eraseAt_false p _ cur (fun _ => hpk _ hpc)
      · trivial
  | succ r ih =>
    intro hr N s hw hpN
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    rw [doSub.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_pos hA']
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have hok := hpN D hD
      rw [hs] at hok
      obtain ⟨_, hk2⟩ := hok
      have o : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
          ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
        sub_step cfg k h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
      have iw : SubWalk r (N.cs.getD (pos N.nodemap D) Node.dummy) p H
          ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
        ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw hk2
      simp only [StateT.run_bind]
      generalize hq : (doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q at o iw
      obtain ⟨sub, s1⟩ := q
      cases sub with
      | nothing => trivial
      | singleton x =>
        obtain ⟨y, hy, hp⟩ := o
        split
        · trivial
        · show SubWalk (r + 1) N p H (.tree ((copyInnerReplaceInline N (2 ^ D) (pos N.nodemap D) x).run s1).1)
          have hE := edit_replaceInline r N x D s1 hw hD hA
          apply find_edit p r hr N _ D _ hE H
          intro _
          rw [hs]
          show [x].find? p = (walk r (N.cs.getD (pos N.nodemap D) Node.dummy) (H >>> (65 - 5 * r))).find? p
          generalize N.cs.getD (pos N.nodemap D) Node.dummy = c at hp hcw hk2
          have hsub : ∀ z ∈ walk r c (H >>> (65 - 5 * r)), z = y ∨ z = x := by
            intro z hz; have := hp.subset (walk_sub r c _ hcw z hz); simpa using this
          have hpy := hpk y hy
          cases hpx : p x
          · rw [find?_cons_false p x [] hpx, List.find?_nil]
            symm
            rw [List.find?_eq_none]
            intro z hz
            rcases hsub z hz with h1 | h1 <;> rw [h1] <;> simp [hpy, hpx]
          · rw [show [x].find? p = some x by simp [List.find?_cons, hpx]]
            symm
            apply find?_unique p _ x
            · have hcm := walk_complete cfg r (by omega) c hcw hk2 x (hp.symm.subset (by simp))
              rw [hph x hpx] at hcm; exact hcm
            · exact hpx
            · intro z hz hpz
              rcases hsub z hz with h1 | h1
              · rw [h1, hpy] at hpz; cases hpz
              · exact h1
      | tree t =>
        obtain ⟨htw, _, _⟩ := o
        show SubWalk (r + 1) N p H (.tree ((copyInnerReplace N (pos N.nodemap D) t).run s1).1)
        have hE := edit_replace r N t D s1 hw hD hA htw
        apply find_edit p r hr N _ D _ hE H
        intro _
        rw [hs]
        exact iw
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_neg hA']
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_pos hB']
        have hs : slot N D = .data (N.values.getD (pos N.datamap D) default) := by
          unfold slot; rw [if_neg hA, if_pos hB]
        by_cases hE : cfg.eqTK (N.values.getD (pos N.datamap D) default) k = true
        · rw [if_pos (show cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)]
          have hpv0 := hpk _ hE
          have hgone : ([] : List α).find? p = (slotW r (slot N D) (H >>> (65 - 5 * r))).find? p := by
            rw [hs]
            show ([] : List α).find? p = [N.values.getD (pos N.datamap D) default].find? p
            rw [find?_cons_false p _ [] hpv0]
          by_cases c1 : (N.nodemap != 0 || decide (N.dataCount > 2)) = true
          · rw [if_pos c1]
            show SubWalk (r + 1) N p H (.tree ((copyInnerRemoveValue N (2 ^ D) (pos N.datamap D)).run s).1)
            rw [copyInnerRemoveValue_eq]
            have hE' := edit_removeValue r N D s hw hD hA0 hB
            exact find_edit p r hr N _ D _ hE' H (fun _ => hgone)
          · rw [if_neg c1]
            have hn0 : N.nodemap = 0 := by simp at c1; exact c1.1
            by_cases c2 : (N.dataCount == 2) = true
            · rw [if_pos c2]
              have hdc : popcount N.datamap = 2 := (by simpa using c2 : N.dataCount = 2)
              split
              · trivial
              · show SubWalk (r + 1) N p H (.tree ((mkInner 0 (clearBit N.datamap (2 ^ D))
                  [N.values.getD (if (pos N.datamap D == 0) = true then 1 else 0) default] ([] : List (Node α))).run s).1)
                have hE' := edit_rootCollapse r N D s hw hD hB hn0 hdc
                exact find_edit p r hr N _ D _ hE' H (fun _ => hgone)
            · rw [if_neg c2]
              have hle : popcount N.datamap ≤ 2 := by simp at c1; exact c1.2
              have hdc : popcount N.datamap = 1 := by
                have h1 : popcount N.datamap ≠ 2 := (by simpa using c2 : ¬ N.dataCount = 2)
                have h2 := pos_lt_popcount N.datamap D hD hB
                omega
              show SubWalk (r + 1) N p H (.tree (Champ.empty (α := α)).root)
              have hE' := edit_empty r N D hw hD hB hn0 hdc
              exact find_edit p r hr N _ D _ hE' H (fun _ => hgone)
        · rw [if_neg (show ¬ cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)]
          trivial
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_neg hB']
        trivial

/-- ★ **Law 1 for `sub` (`dissoc`/`disj`), for every well-formed champ meeting `HP`**: under a lawful
equality, `get` of a key not `Equal` to the one removed is unchanged. Uniqueness and the size premise
of round 6's `get_sub_other` are dropped; `HP` cannot be (`law1_sub_fails_without_HP`). -/
theorem get_sub_other_hp {cfg : Cfg α κ} (L : Lawful cfg) (c : Champ α) (k k' : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hp : HP cfg 13 c.root) (hne : L.eqK k k' = false) :
    Champ.get cfg ((c.sub cfg k).run s).1 k' = Champ.get cfg c k' := by
  have hpk : ∀ y, cfg.eqTK y k = true → cfg.eqTK y k' = false := by
    intro y hy
    cases hk : cfg.eqTK y k'
    · rfl
    · rw [L.eqTK_key] at hy hk
      rw [L.trans _ _ _ (L.symm _ _ hy) hk] at hne; cases hne
  have hph : ∀ x, cfg.eqTK x k' = true → cfg.hashT x = cfg.hashK k' :=
    fun x hx => (L.hash_of_eqTK x k' hx).symm
  have iw := sub_walk cfg k (cfg.hashK k) (fun x => cfg.eqTK x k') (cfg.hashK k') hpk hph 13
    (Nat.le_refl _) c.root s hw hp
  have o := sub_step cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
  unfold Champ.sub
  simp only [StateT.run_bind]
  generalize (doSub cfg k 13 c.root (cfg.hashK k)).run s = q at iw o
  obtain ⟨sub, s1⟩ := q
  cases sub with
  | nothing => rfl
  | singleton x => rfl
  | tree t =>
    obtain ⟨htw, _, _⟩ := o
    show Champ.get cfg { root := t, size := c.size - 1 } k' = Champ.get cfg c k'
    unfold Champ.get
    rw [getLoop_walk cfg k' 13 t _ htw, getLoop_walk cfg k' 13 c.root _ hw]
    have h' : (walk 13 t (cfg.hashK k' >>> (65 - 5 * 13))).find? (fun x => cfg.eqTK x k') =
        (walk 13 c.root (cfg.hashK k' >>> (65 - 5 * 13))).find? (fun x => cfg.eqTK x k') := iw
    rw [shr13] at h'
    exact h'

/-! ## `HP` cannot be dropped for `sub` -/

/-- `Nat` keys, identity hash, `==`: a lawful equality. -/
def natCfg : Cfg Nat Nat where
  hashT := id
  hashK := id
  eqTT a b := a == b
  eqTK a b := a == b

def natLawful : Lawful natCfg where
  key := id
  eqK a b := a == b
  hashT_key _ := rfl
  eqTT_key _ _ := rfl
  eqTK_key _ _ := rfl
  refl k := by simp
  symm a b h := by simp at h ⊢; omega
  trans a b c h1 h2 := by simp at h1 h2 ⊢; omega
  compat a b h := by simp at h; simp [natCfg, h]

/-- A well-formed champ: the root's child at bit 1 holds 225 (bit 3) and 289 (bit 9). 225's hash
names bit 7 at that level (225 = 7·32 + 1), so it sits off its hash path; 289 = 9·32 + 1 is on its. -/
def badChamp : Champ Nat :=
  { root := .inner 1 0 2 0 none
      [.inner 2 0 0 (2 ^ 3 ||| 2 ^ 9) (some { id := 3, tok := 0, xs := [225, 289] }) []],
    size := 2 }

theorem badChamp_wf : wfNode 13 badChamp.root = true := by decide +kernel

theorem badChamp_get_before : Champ.get natCfg badChamp 225 = none := by decide +kernel

theorem badChamp_get_after : Champ.get natCfg ((badChamp.sub natCfg 289).run {}).1 225 = some 225 := by
  decide +kernel

/-- The champ breaks the hash-path invariant: otherwise `get 225` would find the stored 225. -/
theorem badChamp_not_HP : ¬ HP natCfg 13 badChamp.root := fun hp =>
  get_complete natCfg badChamp 225 225 badChamp_wf hp (by decide +kernel) rfl (by decide) badChamp_get_before

/-- **`HP` cannot be dropped from law 1 for `sub`**: a well-formed champ under a lawful equality where
removing 289 (not `Equal` to 225) changes `get 225` from nothing to 225. -/
theorem law1_sub_fails_without_HP :
    wfNode 13 badChamp.root = true ∧ ¬ HP natCfg 13 badChamp.root ∧ natLawful.eqK 289 225 = false ∧
      Champ.get natCfg ((badChamp.sub natCfg 289).run {}).1 225 ≠ Champ.get natCfg badChamp 225 := by
  refine ⟨badChamp_wf, badChamp_not_HP, by decide, ?_⟩
  rw [badChamp_get_after, badChamp_get_before]
  simp

end Jank.R7.Champ

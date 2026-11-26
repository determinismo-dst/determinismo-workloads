import Jank.R6.Champ.Ops

/-!
# Round 6, CHAMP: the transients (`add_mut`, `sub_mut`) keep the invariant

`assoc!`/`conj!` (`champ::add_mut`, replica `doAddMut`) and `dissoc!`/`disj!` (`champ::sub_mut`,
replica `doSubMut`) mutate the nodes the transient owns in place and copy the others (through
`do_add`/`do_sub` below an unowned node). For every hash and every equality:

- ★ `addMut_step`: what `do_add_mut` returns meets `AddOut` (well formed, the iteration with the
  value added or one `Equal` value replaced, the hash-path invariant kept) on every branch: the
  in-place child write, the in-place value write (`ensure_mutable_values`), the in-place collision
  write (which keeps the collision node's order where `do_add` moves the value to the front), the
  moves, and the copies.
- ★ `subMut_step`: what `do_sub_mut` returns meets `SubOut` on every branch.
-/

namespace Jank.R6.Champ

open Jank.R3.Immer.Champ

variable {α κ : Type}

/-! ## Owners, moves -/

theorem AddOut.owned' [Inhabited α] {cfg : Cfg α κ} {r : Nat} {N : Node α} {v : α} {n : Node α} {a : Bool}
    (o : AddOut cfg r N v n a) (e : Nat) : AddOut cfg r N v (owned n e) a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [wf_owned]; exact o.wf
  · intro ha; rw [iter_owned]; exact o.grew ha
  · intro ha; rw [iter_owned]; exact o.replaced ha
  · intro hp; rw [HP_owned]; exact o.hp hp

theorem AddOut.ownedValues' [Inhabited α] {cfg : Cfg α κ} {r : Nat} {N : Node α} {v : α} {n : Node α} {a : Bool}
    (o : AddOut cfg r N v n a) (e : Nat) : AddOut cfg r N v (ownedValues n e) a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [wf_ownedValues]; exact o.wf
  · intro ha; rw [iter_ownedValues]; exact o.grew ha
  · intro ha; rw [iter_ownedValues]; exact o.replaced ha
  · intro hp; rw [HP_ownedValues]; exact o.hp hp

theorem subTree_owned [Inhabited α] {cfg : Cfg α κ} {k : κ} {r : Nat} {N t : Node α}
    (o : SubOut cfg k r N (.tree t)) (e : Nat) : SubOut cfg k r N (.tree (owned t e)) := by
  obtain ⟨hw, ⟨y, hy, hp⟩, hh⟩ := o
  refine ⟨by rw [wf_owned]; exact hw, ⟨y, hy, by rw [iter_owned]; exact hp⟩, fun h => by rw [HP_owned]; exact hh h⟩

theorem subTree_ownedValues [Inhabited α] {cfg : Cfg α κ} {k : κ} {r : Nat} {N t : Node α}
    (o : SubOut cfg k r N (.tree t)) (e : Nat) : SubOut cfg k r N (.tree (ownedValues t e)) := by
  obtain ⟨hw, ⟨y, hy, hp⟩, hh⟩ := o
  refine ⟨by rw [wf_ownedValues]; exact hw, ⟨y, hy, by rw [iter_ownedValues]; exact hp⟩,
    fun h => by rw [HP_ownedValues]; exact h |> hh⟩

/-! ## In-place writes -/

/-- `node->children()[offset] = result` on an owned node. -/
theorem edit_setChild [Inhabited α] (r : Nat) (N c' : Node α) (D : Nat) (hw : wfNode (r + 1) N = true)
    (hD : D < 32) (hA : N.nodemap.testBit D = true) (hc : wfNode r c' = true) :
    Edit r N (.inner N.id N.tok N.nodemap N.datamap N.vals (setL N.cs (pos N.nodemap D) c')) D (.child c') := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hlt := pos_lt_popcount _ D hD hA
  constructor
  · apply wf_inner_intro r _ _ _ _ _ _ h1 h2 h3 (by rw [length_setL]; exact h4) h5'
    intro c hcm
    unfold setL at hcm
    rw [List.take_set] at hcm
    rcases List.mem_or_eq_of_mem_set hcm with hcm | hcm
    · exact h6 c hcm
    · rw [hcm]; exact hc
  · intro d hd
    rw [slot_inner, values_vals]
    by_cases hdD : d = D
    · subst hdD
      rw [if_pos hA, if_pos rfl, getD_setL_self _ _ _ _ (by omega)]
    · rw [if_neg hdD]
      unfold slot
      by_cases hm : N.nodemap.testBit d = true
      · rw [if_pos hm, if_pos hm, getD_setL_ne _ _ _ _ _ (pos_ne _ D d hD hd (Ne.symm hdD) hA hm)]
      · rw [if_neg hm, if_neg hm]

/-- `*val = std::move(v)` after `ensure_mutable_values`: a value buffer `L` agreeing with the node's
on the slots in use, written at `D`. -/
theorem edit_writeValue [Inhabited α] (r : Nat) (N : Node α) (v : α) (D : Nat) (hw : wfNode (r + 1) N = true)
    (hD : D < 32) (hA : N.nodemap.testBit D = false) (hB : N.datamap.testBit D = true)
    (vid tk : Nat) (L : List α) (hL : popcount N.datamap ≤ L.length)
    (hLe : ∀ j, j < popcount N.datamap → L.getD j default = N.values.getD j default) :
    Edit r N (.inner N.id N.tok N.nodemap N.datamap (some { id := vid, tok := tk, xs := setL L (pos N.datamap D) v })
      N.cs) D (.data v) := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hlt := pos_lt_popcount _ D hD hB
  constructor
  · apply wf_inner_intro r _ _ _ _ _ _ h1 h2 h3 h4
    · show popcount N.datamap ≤ (setL L (pos N.datamap D) v).length
      rw [length_setL]; exact hL
    · exact h6
  · intro d hd
    rw [slot_inner]
    show (if N.nodemap.testBit d = true then _ else if N.datamap.testBit d = true then
      Slot.data ((setL L (pos N.datamap D) v).getD (pos N.datamap d) default) else _) = _
    by_cases hdD : d = D
    · subst hdD
      rw [if_neg (by simp [hA]), if_pos hB, if_pos rfl, getD_setL_self _ _ _ _ (by omega)]
    · rw [if_neg hdD]
      unfold slot
      by_cases hm : N.nodemap.testBit d = true
      · rw [if_pos hm, if_pos hm]
      · rw [if_neg hm, if_neg hm]
        by_cases hb : N.datamap.testBit d = true
        · rw [if_pos hb, if_pos hb, getD_setL_ne _ _ _ _ _ (pos_ne _ D d hD hd (Ne.symm hdD) hB hb),
            hLe _ (pos_lt_popcount _ d hd hb)]
        · rw [if_neg hb, if_neg hb]


/-! ## `AddOut` from one edit (the four kinds of slot change) -/

theorem addOut_child [Inhabited α] (cfg : Cfg α κ) (r : Nat) (N : Node α) (v : α) (D : Nat)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hvD : chunk r (cfg.hashT v) = D)
    (c0 c1 : Node α) (hs : slot N D = .child c0) (a : Bool) (o : AddOut cfg r c0 v c1 a) (N' : Node α)
    (hE : Edit r N N' D (.child c1)) : AddOut cfg (r + 1) N v N' a := by
  obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE
  rw [hs] at p0
  simp only [slotL] at p0 p1
  refine ⟨hE.1, ?_, ?_, ?_⟩
  · intro ha
    exact p1.trans (((o.grew ha).append_right _).trans (p0.symm.cons v))
  · intro ha
    obtain ⟨x, hx, hxe, hp⟩ := o.replaced ha
    exact ⟨x, p0.symm.subset (List.mem_append_left _ hx), hxe,
      (p0.cons v).trans ((hp.append_right _).trans (p1.symm.cons x))⟩
  · intro hpN
    have hok := hpN D hD
    rw [hs] at hok
    obtain ⟨hk1, hk2⟩ := hok
    apply HP_edit cfg r N _ D _ hE hpN
    refine ⟨?_, o.hp hk2⟩
    intro x hx
    rcases o.mem x hx with hx | hx
    · rw [hx]; exact hvD
    · exact hk1 x hx

theorem addOut_replace [Inhabited α] (cfg : Cfg α κ) (r : Nat) (N : Node α) (v : α) (D : Nat)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hvD : chunk r (cfg.hashT v) = D)
    (val : α) (hs : slot N D = .data val) (hE : cfg.eqTT val v = true) (N' : Node α)
    (hE' : Edit r N N' D (.data v)) : AddOut cfg (r + 1) N v N' false := by
  have hvalm := mem_iter_of_slot r N hw D hD val (by rw [hs]; simp [slotL])
  obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
  rw [hs] at p0
  simp only [slotL] at p0 p1
  refine ⟨hE'.1, (fun hc => by cases hc), ?_, ?_⟩
  · intro _
    exact ⟨_, hvalm, hE, (p0.cons v).trans ((List.Perm.swap _ _ _).trans (p1.symm.cons _))⟩
  · intro hpN
    exact HP_edit cfg r N _ D _ hE' hpN hvD

theorem addOut_insert [Inhabited α] (cfg : Cfg α κ) (r : Nat) (N : Node α) (v : α) (D : Nat)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hvD : chunk r (cfg.hashT v) = D)
    (hs : slot N D = .empty) (N' : Node α) (hE' : Edit r N N' D (.data v)) : AddOut cfg (r + 1) N v N' true := by
  obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
  rw [hs] at p0
  simp only [slotL, List.nil_append] at p0 p1
  refine ⟨hE'.1, ?_, (fun hc => by cases hc), ?_⟩
  · intro _; exact p1.trans (p0.symm.cons v)
  · intro hpN; exact HP_edit cfg r N _ D _ hE' hpN hvD

theorem addOut_merge [Inhabited α] (cfg : Cfg α κ) (r : Nat) (N : Node α) (v : α) (D : Nat)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hvD : chunk r (cfg.hashT v) = D)
    (val : α) (hs : slot N D = .data val) (m : Node α) (hmi : (iterNode r m).Perm [v, val]) (hmh : HP cfg r m)
    (N' : Node α) (hE' : Edit r N N' D (.child m)) : AddOut cfg (r + 1) N v N' true := by
  obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
  rw [hs] at p0
  simp only [slotL] at p0 p1
  refine ⟨hE'.1, ?_, (fun hc => by cases hc), ?_⟩
  · intro _; exact p1.trans ((hmi.append_right _).trans (p0.symm.cons v))
  · intro hpN
    have hok := hpN D hD
    rw [hs] at hok
    have hvalD : chunk r (cfg.hashT val) = D := hok
    apply HP_edit cfg r N _ D _ hE' hpN
    refine ⟨?_, hmh⟩
    intro x hx
    have := hmi.subset hx
    simp at this
    rcases this with hx | hx <;> rw [hx]
    · exact hvD
    · exact hvalD

/-! ## `do_add_mut` -/

theorem addOut_coll_ins [Inhabited α] (cfg : Cfg α κ) (nid tok i t : Nat) (xs : List α) (v : α) (hl : xs.length ≥ 2) :
    AddOut cfg 0 (.collision nid tok xs) v (.collision i t (v :: xs)) true := by
  refine ⟨?_, fun _ => List.Perm.refl _, (fun hc => by cases hc), fun _ => trivial⟩
  show decide ((v :: xs).length ≥ 2) = true
  simp; omega

theorem addOut_coll_rep [Inhabited α] (cfg : Cfg α κ) (nid tok i t : Nat) (xs : List α) (v : α) (pos : Nat)
    (hl : xs.length ≥ 2) (hpos : pos < xs.length) (hpx : cfg.eqTT (xs.getD pos default) v = true)
    (L : List α) (hL : L.Perm (v :: eraseAt xs pos)) :
    AddOut cfg 0 (.collision nid tok xs) v (.collision i t L) false := by
  refine ⟨?_, (fun hc => by cases hc), ?_, fun _ => trivial⟩
  · show decide (L.length ≥ 2) = true
    have := hL.length_eq
    have := length_eraseAt xs pos hpos
    simp at *; omega
  · intro _
    refine ⟨xs.getD pos default, getD_mem' xs pos default hpos, hpx, ?_⟩
    show (v :: xs).Perm (xs.getD pos default :: L)
    exact ((perm_eraseAt xs pos default hpos).cons v).trans ((List.Perm.swap _ _ _).trans (hL.symm.cons _))

/-- ★ `do_add_mut` (`assoc!`/`conj!`), one level at a time, for every hash and every equality. -/
theorem addMut_step [Inhabited α] (cfg : Cfg α κ) (e : Nat) (v : α) (h : Nat) (hv : cfg.hashT v = h) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      AddOut cfg r N v ((doAddMut cfg e r N v h).run s).1.1 ((doAddMut cfg e r N v h).run s).1.2.1 := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      have hl : xs.length ≥ 2 := by simpa [wfNode, Node.collisions] using hw
      rw [doAddMut.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases hf : xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        dsimp only
        split
        · exact (addOut_coll_ins cfg nid tok s.next 0 xs v hl).owned' e
        · exact (addOut_coll_ins cfg nid tok s.next 0 xs v hl).owned' e
      | some pos =>
        obtain ⟨hpos, hpx, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        have hpx' : cfg.eqTT (xs.getD pos default) v = true := by rw [getD_eq_getElem' xs pos default hpos]; exact hpx
        dsimp only
        split
        · exact addOut_coll_rep cfg nid tok nid tok xs v pos hl hpos hpx' _ (perm_setL xs pos v default hpos)
        · exact (addOut_coll_rep cfg nid tok s.next 0 xs v pos hl hpos hpx' _ (List.Perm.refl _)).owned' e
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    have hvD : chunk r (cfg.hashT v) = D := by rw [hv]; exact hDdef
    have hP := add_step cfg v h hv (r + 1) hr N s hw
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      by_cases hm : N.canMutate e = true
      · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (.inner N.id N.tok N.nodemap N.datamap N.vals (setL N.cs (pos N.nodemap D)
              ((doAddMut cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1),
             ((doAddMut cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2.1, true) := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_pos hA', if_pos hm]
          cases N with
          | inner => rfl
          | collision => simp [wfNode] at hw
        rw [e1]
        have o := ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        exact addOut_child cfg r N v D hw hD hvD _ _ hs _ o _ (edit_setChild r N _ D hw hD hA o.wf)
      · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (owned ((doAdd cfg (r + 1) N v h).run s).1.1 e, ((doAdd cfg (r + 1) N v h).run s).1.2, false) := by
          rw [doAddMut.eq_2, doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA', if_neg hm, if_pos hA']; rfl
        rw [e1]
        exact hP.owned' e
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have hs : slot N D = .data (N.values.getD (pos N.datamap D) default) := by
          unfold slot; rw [if_neg hA, if_pos hB]
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · by_cases hm : N.canMutate e = true
          · -- `ensure_mutable_values` and a write in place
            obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
            have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
                (writeValue ((ensureMutableValues N e).run s).1 (pos N.datamap D) v, false, true) := by
              rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_pos hm]
              rfl
            rw [e1]
            apply addOut_replace cfg r N v D hw hD hvD _ hs hE
            cases N with
            | collision => simp [wfNode] at hw
            | inner nid tok nm dm vals cs =>
              cases vals with
              | none =>
                have : dm = 0 := h5'
                subst this
                exact absurd hB (by simp [Node.datamap, Nat.zero_testBit])
              | some vs =>
                by_cases hvt : (vs.tok == e) = true
                · have em : ((ensureMutableValues (Node.inner nid tok nm dm (some vs) cs) e).run s).1 =
                      Node.inner nid tok nm dm (some vs) cs := by
                    unfold ensureMutableValues
                    rw [if_pos (show (Node.inner nid tok nm dm (some vs) cs).canMutateValues e = true from hvt)]
                    rfl
                  rw [em]
                  exact edit_writeValue r _ v D hw hD hA0 hB vs.id vs.tok vs.xs h5 (fun _ _ => rfl)
                · have em : ((ensureMutableValues (Node.inner nid tok nm dm (some vs) cs) e).run s).1 =
                      Node.inner nid tok nm dm (some ⟨s.next, e, (Node.inner nid tok nm dm (some vs) cs).values.take (popcount dm)⟩) cs := by
                    unfold ensureMutableValues
                    rw [if_neg (show ¬ (Node.inner nid tok nm dm (some vs) cs).canMutateValues e = true from hvt)]
                    rfl
                  rw [em]
                  exact edit_writeValue r _ v D hw hD hA0 hB s.next e _
                    (by rw [List.length_take]; exact Nat.le_min.mpr ⟨Nat.le_refl _, h5⟩)
                    (fun j hj => getD_take _ _ _ _ hj)
          · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
                (ownedValues ((doAdd cfg (r + 1) N v h).run s).1.1 e, ((doAdd cfg (r + 1) N v h).run s).1.2, false) := by
              rw [doAddMut.eq_2, doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB', if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_neg hm,
                if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]
              rfl
            rw [e1]
            exact hP.ownedValues' e
        · -- `make_merged_e` below, moved or copied
          generalize hval : N.values.getD (pos N.datamap D) default = val at hs hE
          have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
              (ownedValues ((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).2).1 e, true, N.canMutate e) := by
            rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            split <;> rfl
          rw [e1]
          dsimp only
          apply AddOut.ownedValues'
          generalize hq : (makeMerged (some e) r v h val (cfg.hashT val)).run s = q
          obtain ⟨m, s1⟩ := q
          have hmw : wfNode r m = true := by
            have := wf_makeMerged (some e) v val h (cfg.hashT val) r s; rw [hq] at this; exact this
          have hmi : (iterNode r m).Perm [v, val] := by
            have := iter_makeMerged (some e) v val h (cfg.hashT val) r s; rw [hq] at this; exact this
          have hmh : HP cfg r m := by
            have := HP_makeMerged cfg (some e) v val h (cfg.hashT val) hv rfl r s; rw [hq] at this; exact this
          exact addOut_merge cfg r N v D hw hD hvD val hs m hmi hmh _ (edit_replaceMerged r N m D s1 hw hD hA0 hB hmw)
      · have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have hs : slot N D = .empty := by unfold slot; rw [if_neg hA, if_neg hB]
        have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (ownedValues ((copyInnerInsertValue N (2 ^ D) v).run s).1 e, true, N.canMutate e) := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']
          split <;> rfl
        rw [e1]
        exact (addOut_insert cfg r N v D hw hD hvD hs _ (edit_insertValue r N v D s hw hD hA0 hB0)).ownedValues' e


/-! ## `SubOut` from one edit -/

theorem subOut_inline [Inhabited α] (cfg : Cfg α κ) (k : κ) (r : Nat) (N : Node α) (D : Nat)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (c0 : Node α) (hs : slot N D = .child c0) (x : α)
    (o : SubOut cfg k r c0 (.singleton x)) (N' : Node α) (hE : Edit r N N' D (.data x)) :
    SubOut cfg k (r + 1) N (.tree N') := by
  obtain ⟨y, hy, hp⟩ := o
  obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE
  rw [hs] at p0
  simp only [slotL] at p0 p1
  refine ⟨hE.1, ⟨y, hy, p0.trans ((hp.append_right _).trans (p1.symm.cons y))⟩, ?_⟩
  intro hpN
  have hok := hpN D hD
  rw [hs] at hok
  obtain ⟨hk1, _⟩ := hok
  exact HP_edit cfg r N _ D _ hE hpN (hk1 x (hp.symm.subset (by simp)))

theorem subOut_tree [Inhabited α] (cfg : Cfg α κ) (k : κ) (r : Nat) (N : Node α) (D : Nat)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (c0 : Node α) (hs : slot N D = .child c0) (t : Node α)
    (o : SubOut cfg k r c0 (.tree t)) (N' : Node α) (hE : Edit r N N' D (.child t)) :
    SubOut cfg k (r + 1) N (.tree N') := by
  obtain ⟨_, ⟨y, hy, hp⟩, hhp⟩ := o
  obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE
  rw [hs] at p0
  simp only [slotL] at p0 p1
  refine ⟨hE.1, ⟨y, hy, p0.trans ((hp.append_right _).trans (p1.symm.cons y))⟩, ?_⟩
  intro hpN
  have hok := hpN D hD
  rw [hs] at hok
  obtain ⟨hk1, hk2⟩ := hok
  apply HP_edit cfg r N _ D _ hE hpN
  exact ⟨fun z hz => hk1 z (hp.symm.subset (List.mem_cons_of_mem _ hz)), hhp hk2⟩

theorem subOut_remove [Inhabited α] (cfg : Cfg α κ) (k : κ) (r : Nat) (N : Node α) (D : Nat)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (y : α) (hs : slot N D = .data y) (hy : cfg.eqTK y k = true)
    (N' : Node α) (hE : Edit r N N' D .empty) : SubOut cfg k (r + 1) N (.tree N') := by
  obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE
  rw [hs] at p0
  simp only [slotL, List.nil_append] at p0 p1
  exact ⟨hE.1, ⟨_, hy, p0.trans (p1.symm.cons _)⟩, fun hpN => HP_edit cfg r N _ D _ hE hpN trivial⟩

/-! ## `do_sub_mut` -/

/-- ★ `do_sub_mut` (`dissoc!`/`disj!`), one level at a time, for every hash and every equality. -/
theorem subMut_step [Inhabited α] (cfg : Cfg α κ) (e : Nat) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      SubOut cfg k r N ((doSubMut cfg e k r N h).run s).1.r := by
  intro r
  induction r with
  | zero =>
    intro hr N s hw
    have hP := sub_step cfg k h 0 hr N s hw
    rw [doSub.eq_1] at hP
    rw [doSubMut.eq_1]
    unfold findIdx? at hP ⊢
    cases hf : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => trivial
    | some cur =>
      rw [hf] at hP
      dsimp only at hP ⊢
      by_cases hl : N.collisions.length ≤ 2
      · rw [if_neg (by omega)] at hP
        rw [if_pos hl]
        split <;> exact hP
      · rw [if_pos (by omega)] at hP
        rw [if_neg hl]
        split
        · exact subTree_owned hP e
        · exact subTree_owned hP e
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    have hP := sub_step cfg k h (r + 1) hr N s hw
    rw [doSub.eq_2] at hP
    dsimp only at hP
    rw [hbit] at hP
    rw [doSubMut.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_pos hA']
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      by_cases hm : N.canMutate e = true
      · rw [if_pos hm]
        simp only [hm, ↓reduceIte]
        have o : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
            ((doSubMut cfg e k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1.r :=
          ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        simp only [StateT.run_bind]
        generalize (doSubMut cfg e k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q at o
        obtain ⟨⟨res, ow, mu⟩, s1⟩ := q
        dsimp only at o ⊢
        cases res with
        | nothing => trivial
        | singleton x =>
          try dsimp only
          split
          · next hc =>
            obtain ⟨y, hy, hp⟩ := o
            have hdm : N.datamap = 0 := by simp at hc; exact hc.1.1
            have hcc : popcount N.nodemap = 1 := by simp at hc; exact hc.1.2
            exact ⟨y, hy, (iter_only r N hw D hD hA hdm hcc).trans hp⟩
          · exact subTree_ownedValues (subOut_inline cfg k r N D hw hD _ hs x o _
              (edit_replaceInline r N x D s1 hw hD hA)) e
        | tree t =>
          try dsimp only
          try rw [if_pos hm]
          cases N with
          | collision => simp [wfNode] at hw
          | inner nid tok nm dm vs cs =>
            exact subOut_tree cfg k r _ D hw hD _ hs t o _ (edit_setChild r _ t D hw hD hA o.1)
      · rw [if_neg hm]
        simp only [hm, ↓reduceIte, Bool.false_eq_true]
        have o : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
            ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
          sub_step cfg k h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        simp only [StateT.run_bind]
        generalize (doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q at o
        obtain ⟨res, s1⟩ := q
        dsimp only at o ⊢
        cases res with
        | nothing => trivial
        | singleton x =>
          try dsimp only
          split
          · next hc =>
            obtain ⟨y, hy, hp⟩ := o
            have hdm : N.datamap = 0 := by simp at hc; exact hc.1.1
            have hcc : popcount N.nodemap = 1 := by simp at hc; exact hc.1.2
            exact ⟨y, hy, (iter_only r N hw D hD hA hdm hcc).trans hp⟩
          · exact subTree_ownedValues (subOut_inline cfg k r N D hw hD _ hs x o _
              (edit_replaceInline r N x D s1 hw hD hA)) e
        | tree t =>
          try dsimp only
          try rw [if_neg hm]
          exact subTree_owned (subOut_tree cfg k r N D hw hD _ hs t o _ (edit_replace r N t D s1 hw hD hA o.1)) e
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_neg hA'] at hP ⊢
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_pos hB'] at hP ⊢
        have hs : slot N D = .data (N.values.getD (pos N.datamap D) default) := by
          unfold slot; rw [if_neg hA, if_pos hB]
        by_cases hE : cfg.eqTK (N.values.getD (pos N.datamap D) default) k = true
        · rw [if_pos (show cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)] at hP ⊢
          by_cases c1 : (N.nodemap != 0 || decide (N.dataCount > 2)) = true
          · rw [if_pos c1] at hP ⊢
            split <;> exact subTree_ownedValues hP e
          · rw [if_neg c1] at hP ⊢
            by_cases c2 : (N.dataCount == 2) = true
            · rw [if_pos c2] at hP ⊢
              split
              · next hsh =>
                rw [if_pos hsh] at hP
                split <;> exact hP
              · next hsh =>
                rw [if_neg hsh] at hP
                by_cases hm : N.canMutate e = true
                · simp only [hm, ↓reduceIte]; exact subTree_ownedValues hP e
                · simp only [hm, ↓reduceIte, Bool.false_eq_true]; exact subTree_ownedValues hP e
            · rw [if_neg c2] at hP ⊢
              split <;> exact hP
        · rw [if_neg (show ¬ cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)]
          trivial
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_neg hB']
        trivial

end Jank.R6.Champ

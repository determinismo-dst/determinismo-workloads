import Jank.R9.Champ.SeqF

/-!
# Round 9, CHAMP: stock jank's sequence theorem under a weaker hypothesis (a partial equivalence)

Round 8's `buildT_agree_empty` (a transient chain and its persistent twin agree up to the order inside
collision nodes) assumed a lawful equality (round 6's `Lawful`: reflexive, symmetric, transitive,
agreeing with the hash). jank's `=` is none of these on every value. Here the hypothesis is weakened to
`PER`: `Equal` is symmetric and transitive on stored values, and two stored values that accept one key
are `Equal`. Reflexivity and agreement with the hash are dropped, so NaN (V85: equal to nothing, itself
included) and the `=`/hash mismatches (D12: 0.0 and -0.0, 1 and 1N, a map seq and its vector) are
covered. Non-transitive `=` (D8's BigDecimals) and asymmetric `=` (R55's string seq against a vector)
are not, and there the conclusion fails (H9-1, `Programs.lean`; `jank9-champ seqs`).

The invariant is per collision node (`CU`: its values pairwise not `Equal`), not round 6's `Uniq` of
the whole iteration (which D12's mismatches break: two `=` values can sit in different nodes).

- ★ `cu_makeMerged`, ★ `cu_add`, ★ `cu_sub`, ★ `cu_step`, ★ `cu_reach`: every stock step (`do_add`, `do_sub`,
  `do_add_mut`, `do_sub_mut`) keeps `CU` under `PER`, so every champ jank builds from `champ::empty()`
  meets it.
- ★ `add_congrP`, ★ `sub_congrP`: round 8's congruences with `PER` and `CU` in place of `Lawful` and
  `Uniq` (the proofs are round 8's, the two uses of lawfulness replaced: one stored value per
  collision node accepts a query, and the invariant passes to a child).
- ★ `buildT_agreeP`, ★ `buildT_agreeP_empty`: **under `PER`, every sequence of persistent and transient
  stock steps and its all-persistent twin agree node by node up to collision order, with the same size
  (so the same contents)**.
-/

namespace Jank.R9.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ Jank.R8.Champ

variable {α κ : Type} [Inhabited α]

/-- `Equal` is a partial equivalence on stored values, and keys reach it (no reflexivity, no hash). -/
structure PER (cfg : Cfg α κ) : Prop where
  symm : ∀ a b, cfg.eqTT a b = true → cfg.eqTT b a = true
  trans : ∀ a b c, cfg.eqTT a b = true → cfg.eqTT b c = true → cfg.eqTT a c = true
  viaK : ∀ x y k, cfg.eqTK x k = true → cfg.eqTK y k = true → cfg.eqTT x y = true

theorem ne_symm {cfg : Cfg α κ} (P : PER cfg) (a b : α) (h : cfg.eqTT a b = false) : cfg.eqTT b a = false := by
  cases hb : cfg.eqTT b a
  · rfl
  · rw [P.symm b a hb] at h; cases h

theorem eqTT_viaP {cfg : Cfg α κ} (P : PER cfg) (v : α) :
    ∀ x y, cfg.eqTT x v = true → cfg.eqTT y v = true → cfg.eqTT x y = true :=
  fun x y hx hy => P.trans x v y hx (P.symm y v hy)

/-- A slot's child meets `Q`. -/
def SlotCU (Q : Node α → Prop) : Slot α → Prop
  | .child c => Q c
  | _ => True

/-- Every collision node below holds pairwise non-`Equal` values. -/
def CU (cfg : Cfg α κ) : Nat → Node α → Prop
  | 0, N => N.collisions.Pairwise (fun a b => cfg.eqTT a b = false)
  | r + 1, N => ∀ d, d < 32 → SlotCU (CU cfg r) (slot N d)

theorem cu_zero_iff {cfg : Cfg α κ} {N : Node α} :
    CU cfg 0 N ↔ N.collisions.Pairwise (fun a b => cfg.eqTT a b = false) := Iff.rfl

/-- In a list of pairwise non-`Equal` values, two values a predicate accepts are the same, when the
values it accepts are pairwise `Equal`. -/
theorem one_of_cu {cfg : Cfg α κ} :
    ∀ (xs : List α), xs.Pairwise (fun a b => cfg.eqTT a b = false) → ∀ (q : α → Bool),
      (∀ x y, q x = true → q y = true → cfg.eqTT x y = true) →
      ∀ x ∈ xs, ∀ y ∈ xs, q x = true → q y = true → x = y
  | [], _, _, _, x, hx, _, _, _, _ => by simp at hx
  | a :: t, hp, q, hq, x, hx, y, hy, hqx, hqy => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · have := hp.1 y hy'; rw [hq x y hqx hqy] at this; cases this
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have := hp.1 x hx'; rw [hq y x hqy hqx] at this; cases this
      · exact one_of_cu t hp.2 q hq x hx' y hy' hqx hqy

theorem cu_edit (cfg : Cfg α κ) (r : Nat) (N N' : Node α) (D : Nat) (X : Slot α) (hE : Edit r N N' D X)
    (hN : CU cfg (r + 1) N) (hX : SlotCU (CU cfg r) X) : CU cfg (r + 1) N' := by
  intro d hd
  rw [hE.2 d hd]
  split
  · exact hX
  · exact hN d hd

theorem cu_owned (cfg : Cfg α κ) (n : Node α) (e : Nat) : ∀ r, CU cfg r (owned n e) ↔ CU cfg r n
  | 0 => by simp only [CU, collisions_owned]
  | r + 1 => by simp only [CU, slot_owned]

theorem cu_ownedValues (cfg : Cfg α κ) (n : Node α) (e : Nat) : ∀ r, CU cfg r (ownedValues n e) ↔ CU cfg r n
  | 0 => by simp only [CU, collisions_ownedValues]
  | r + 1 => by simp only [CU, slot_ownedValues]

/-- `CU` passes along an agreement whose collision relation keeps pairwise non-equality. -/
theorem cu_agree (cfg : Cfg α κ) (C : List α → List α → Prop)
    (hC : ∀ a b, C a b → b.Pairwise (fun x y => cfg.eqTT x y = false) → a.Pairwise (fun x y => cfg.eqTT x y = false)) :
    ∀ r (X Y : Node α), Agree C r X Y → CU cfg r Y → CU cfg r X
  | 0, X, Y, hag, hY => hC _ _ hag hY
  | r + 1, X, Y, hag, hY => by
    intro d hd
    have hs := hag d hd
    have hy := hY d hd
    generalize slot X d = sx at hs
    generalize slot Y d = sy at hs hy
    cases sx <;> cases sy <;> simp only [SlotRel] at hs <;> simp only [SlotCU] at hy ⊢
    exact cu_agree cfg C hC r _ _ hs hy

theorem cu_empty (cfg : Cfg α κ) : ∀ r, CU cfg (r + 1) (Champ.empty (α := α)).root := by
  intro r d _
  show SlotCU (CU cfg r) (if (0 : Nat).testBit d = true then _ else if (0 : Nat).testBit d = true then _ else _)
  simp [Nat.zero_testBit, SlotCU]

theorem cu_makeMerged (cfg : Cfg α κ) (own : Option Nat) (v1 v2 : α) (h1 h2 : Nat) (hne : cfg.eqTT v1 v2 = false) :
    ∀ r (s : Al), CU cfg r ((makeMerged own r v1 h1 v2 h2).run s).1 := by
  intro r
  induction r with
  | zero =>
    intro s
    show List.Pairwise _ ((makeMerged own 0 v1 h1 v2 h2).run s).1.collisions
    rw [makeMerged_zero, List.pairwise_pair]
    exact hne
  | succ r ih =>
    intro s
    have hA := idxAt_lt h1 (maxShift - 5 * (r + 1))
    by_cases hc : idxAt h1 (maxShift - 5 * (r + 1)) = idxAt h2 (maxShift - 5 * (r + 1))
    · obtain ⟨nid, tok, e⟩ := makeMerged_same own r v1 v2 h1 h2 s hc
      rw [e]
      intro d hd
      rw [slot_pow_one _ _ _ _ _ hA]
      split
      · exact ih s
      · trivial
    · obtain ⟨nid, tok, vv, e, ex⟩ := makeMerged_diff own r v1 v2 h1 h2 s hc
      have hB := idxAt_lt h2 (maxShift - 5 * (r + 1))
      rw [e]
      intro d hd
      rw [slot_two nid tok _ _ d vv v1 v2 hA hB hc ex]
      split
      · trivial
      · split <;> trivial

/-! ## The stock persistent steps keep `CU` -/

/-- ★ `do_add` keeps `CU` under `PER`. -/
theorem cu_add (cfg : Cfg α κ) (P : PER cfg) (v : α) (h : Nat) (hv : cfg.hashT v = h) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true → CU cfg r N →
      CU cfg r ((doAdd cfg r N v h).run s).1.1 := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw hcu
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      have hx : xs.Pairwise (fun a b => cfg.eqTT a b = false) := hcu
      rw [doAdd.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases hf : xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        show List.Pairwise _ (v :: xs)
        rw [List.pairwise_cons]
        refine ⟨fun x hxm => ?_, hx⟩
        rw [List.findIdx?_eq_none_iff] at hf
        exact ne_symm P x v (by simpa using hf x hxm)
      | some pos =>
        obtain ⟨hpos, hpx, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        show List.Pairwise _ (v :: eraseAt xs pos)
        have hperm := perm_eraseAt xs pos default hpos
        have hx' := (hperm.pairwise_iff (fun {a b} h => ne_symm P a b h)).mp hx
        rw [List.pairwise_cons] at hx' ⊢
        refine ⟨fun x hxm => ?_, hx'.2⟩
        cases hvx : cfg.eqTT v x
        · rfl
        · have h1 : cfg.eqTT (xs.getD pos default) v = true := by rw [getD_eq_getElem' xs pos default hpos]; exact hpx
          have := hx'.1 x hxm
          rw [P.trans _ v x h1 hvx] at this; cases this
  | succ r ih =>
    intro hr N s hw hcu
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have hcc : CU cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) := by
        have := hcu D hD; rw [hs] at this; exact this
      have eP : ((doAdd cfg (r + 1) N v h).run s).1 =
          (((copyInnerReplace N (pos N.nodemap D) ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      rw [eP]
      have o := add_step cfg v h hv r (by omega) _ s hcw
      exact cu_edit cfg r N _ D _ (edit_replace r N _ D _ hw hD hA o.wf) hcu (ih (by omega) _ s hcw hcc)
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · have eP : ((doAdd cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceValue N (pos N.datamap D) v).run s).1, false) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]; rfl
          rw [eP]
          exact cu_edit cfg r N _ D _ (edit_replaceValue r N v D s hw hD hA0 hB) hcu trivial
        · generalize hval : N.values.getD (pos N.datamap D) default = val at hE
          have eP : ((doAdd cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged none r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged none r v h val (cfg.hashT val)).run s).2).1, true) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            rfl
          rw [eP]
          have hne : cfg.eqTT v val = false := ne_symm P val v (by simpa using hE)
          have hcm := cu_makeMerged cfg none v val h (cfg.hashT val) hne r s
          have hw1 := wf_makeMerged none v val h (cfg.hashT val) r s
          generalize (makeMerged none r v h val (cfg.hashT val)).run s = q at hw1 hcm
          obtain ⟨m, s1⟩ := q
          exact cu_edit cfg r N _ D _ (edit_replaceMerged r N m D s1 hw hD hA0 hB hw1) hcu hcm
      · have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have eP : ((doAdd cfg (r + 1) N v h).run s).1 = (((copyInnerInsertValue N (2 ^ D) v).run s).1, true) := by
          rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']; rfl
        rw [eP]
        exact cu_edit cfg r N _ D _ (edit_insertValue r N v D s hw hD hA0 hB0) hcu trivial

/-- A `sub_result` meets `CU` when it is a tree that does. -/
def SubCU (cfg : Cfg α κ) (r : Nat) : Jank.R3.Immer.Champ.Sub α → Prop
  | .tree t => CU cfg r t
  | _ => True

/-- ★ `do_sub` keeps `CU` under `PER` (it only removes; `PER` is used for the symmetry of `CU`'s
relation when a collision list is permuted). -/
theorem cu_sub (cfg : Cfg α κ) (P : PER cfg) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true → CU cfg r N →
      SubCU cfg r ((doSub cfg k r N h).run s).1 := by
  intro r
  induction r with
  | zero =>
    intro _ N s _ hcu
    have hx : N.collisions.Pairwise (fun a b => cfg.eqTT a b = false) := hcu
    rw [doSub.eq_1]
    unfold findIdx?
    cases hf : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => trivial
    | some cur =>
      obtain ⟨hcur, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      dsimp only
      split
      · show List.Pairwise _ (eraseAt N.collisions cur)
        have hperm := perm_eraseAt N.collisions cur default hcur
        have hx' := (hperm.pairwise_iff (fun {a b} h => ne_symm P a b h)).mp hx
        exact (List.pairwise_cons.mp hx').2
      · trivial
  | succ r ih =>
    intro hr N s hw hcu
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
      have hcc : CU cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) := by
        have := hcu D hD; rw [hs] at this; exact this
      have o : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
          ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
        sub_step cfg k h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
      have oc : SubCU cfg r ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
        ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw hcc
      simp only [StateT.run_bind]
      generalize hq : (doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q at o oc
      obtain ⟨sub, s1⟩ := q
      cases sub with
      | nothing => trivial
      | singleton x =>
        split
        · trivial
        · exact cu_edit cfg r N _ D _ (edit_replaceInline r N x D s1 hw hD hA) hcu trivial
      | tree t =>
        exact cu_edit cfg r N _ D _ (edit_replace r N t D s1 hw hD hA o.1) hcu oc
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_neg hA']
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_pos hB']
        by_cases hE : cfg.eqTK (N.values.getD (pos N.datamap D) default) k = true
        · rw [if_pos (show cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)]
          by_cases c1 : (N.nodemap != 0 || decide (N.dataCount > 2)) = true
          · rw [if_pos c1]
            show CU cfg (r + 1) ((copyInnerRemoveValue N (2 ^ D) (pos N.datamap D)).run s).1
            rw [copyInnerRemoveValue_eq]
            exact cu_edit cfg r N _ D _ (edit_removeValue r N D s hw hD hA0 hB) hcu trivial
          · rw [if_neg c1]
            have hn0 : N.nodemap = 0 := by simp at c1; exact c1.1
            by_cases c2 : (N.dataCount == 2) = true
            · rw [if_pos c2]
              have hdc : popcount N.datamap = 2 := (by simpa using c2 : N.dataCount = 2)
              split
              · trivial
              · exact cu_edit cfg r N _ D _ (edit_rootCollapse r N D s hw hD hB hn0 hdc) hcu trivial
            · rw [if_neg c2]
              exact cu_empty cfg r
        · rw [if_neg (show ¬ cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)]
          trivial
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_neg hB']
        trivial

/-! ## Every stock step keeps `CU` -/

/-- `wfNode` for every stock step (round 6's step lemmas; no `HP`). -/
theorem stepS_wf (cfg : Cfg α κ) (c : Champ α) (s : Al) (hw : wfNode 13 c.root = true) (op : TOp α κ) :
    wfNode 13 ((applyT cfg c op).run s).1.root = true := by
  cases op with
  | add v => exact (add_step cfg v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw).wf
  | addMut e v => exact (addMut_step cfg e v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw).wf
  | sub k =>
    have o := sub_step cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    show wfNode 13 ((c.sub cfg k).run s).1.root = true
    unfold Champ.sub
    simp only [StateT.run_bind]
    generalize (doSub cfg k 13 c.root (cfg.hashK k)).run s = q at o
    obtain ⟨sub, s1⟩ := q
    cases sub with
    | nothing => exact hw
    | singleton x => exact hw
    | tree t => exact o.1
  | subMut e k =>
    have o := subMut_step cfg e k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    show wfNode 13 ((c.subMut cfg e k).run s).1.root = true
    unfold Champ.subMut
    simp only [StateT.run_bind]
    generalize (doSubMut cfg e k 13 c.root (cfg.hashK k)).run s = q at o
    obtain ⟨res, s1⟩ := q
    obtain ⟨rr, ow, mu⟩ := res
    cases rr with
    | nothing => exact hw
    | singleton x => exact hw
    | tree t => exact o.1

theorem cu_sub_root (cfg : Cfg α κ) (P : PER cfg) (c : Champ α) (k : κ) (s : Al) (hw : wfNode 13 c.root = true)
    (hcu : CU cfg 13 c.root) : CU cfg 13 ((c.sub cfg k).run s).1.root := by
  have o := cu_sub cfg P k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw hcu
  unfold Champ.sub
  simp only [StateT.run_bind]
  generalize (doSub cfg k 13 c.root (cfg.hashK k)).run s = q at o
  obtain ⟨sub, s1⟩ := q
  cases sub with
  | nothing => exact hcu
  | singleton x => exact hcu
  | tree t => exact o

/-- ★ Every stock step keeps `CU` under `PER` (the transient steps through round 8's agreement with
the persistent ones: the in-place collision write is a permutation of the persistent list). -/
theorem cu_step (cfg : Cfg α κ) (P : PER cfg) (c : Champ α) (s : Al) (hw : wfNode 13 c.root = true)
    (hcu : CU cfg 13 c.root) (op : TOp α κ) : CU cfg 13 ((applyT cfg c op).run s).1.root := by
  have hperm : ∀ a b : List α, InPlace a b → b.Pairwise (fun x y => cfg.eqTT x y = false) →
      a.Pairwise (fun x y => cfg.eqTT x y = false) :=
    fun a b hab hb => ((inPlace_perm a b hab).pairwise_iff (fun {x y} h => ne_symm P x y h)).mpr hb
  cases op with
  | add v => exact cu_add cfg P v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw hcu
  | sub k => exact cu_sub_root cfg P c k s hw hcu
  | addMut e v =>
    have hag := (addMut_root_agree cfg c e v s hw).1
    exact cu_agree cfg InPlace hperm 13 _ _ hag (cu_add cfg P v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw hcu)
  | subMut e k =>
    have hag := (subMut_root_agree cfg c e k s hw).1
    exact cu_agree cfg Eq (fun a b hab hb => hab ▸ hb) 13 _ _ hag (cu_sub_root cfg P c k s hw hcu)

/-- ★ Every champ a jank program builds from `champ::empty()` meets `CU` under `PER`. -/
theorem cu_reach (cfg : Cfg α κ) (P : PER cfg) :
    ∀ (ops : List (TOp α κ)) (c : Champ α) (s : Al), wfNode 13 c.root = true → CU cfg 13 c.root →
      CU cfg 13 ((buildT cfg c ops).run s).1.root
  | [], _, _, _, hcu => hcu
  | op :: ops, c, s, hw, hcu => by
    have e : ((buildT cfg c (op :: ops)).run s).1 =
        ((buildT cfg ((applyT cfg c op).run s).1 ops).run ((applyT cfg c op).run s).2).1 := rfl
    rw [e]
    exact cu_reach cfg P ops _ _ (stepS_wf cfg c s hw op) (cu_step cfg P c s hw hcu op)


/-- Every sequence of stock steps keeps `wfNode` (every hash, every equality, no `HP`). -/
theorem buildT_wf_any (cfg : Cfg α κ) :
    ∀ (ops : List (TOp α κ)) (c : Champ α) (s : Al), wfNode 13 c.root = true →
      wfNode 13 ((buildT cfg c ops).run s).1.root = true
  | [], _, _, hw => hw
  | op :: ops, c, s, hw => by
    have e : ((buildT cfg c (op :: ops)).run s).1 =
        ((buildT cfg ((applyT cfg c op).run s).1 ops).run ((applyT cfg c op).run s).2).1 := rfl
    rw [e]
    exact buildT_wf_any cfg ops _ _ (stepS_wf cfg c s hw op)

/-! ## Round 8's congruences under `PER` and `CU` -/

variable {cfg : Cfg α κ}

theorem add_congrP (P : PER cfg) (v : α) (h : Nat) (hv : cfg.hashT v = h) :
    ∀ r, r ≤ 13 → ∀ (A B : Node α) (s s' : Al), wfNode r A = true → wfNode r B = true →
      CU cfg r A → AgreeP r A B →
      AgreeP r ((doAdd cfg r A v h).run s).1.1 ((doAdd cfg r B v h).run s').1.1 ∧
        ((doAdd cfg r A v h).run s).1.2 = ((doAdd cfg r B v h).run s').1.2 := by
  intro r
  induction r with
  | zero =>
    intro _ A B s s' hwA hwB huA hag
    cases A with
    | inner => simp [wfNode] at hwA
    | collision ia ta xs =>
      cases B with
      | inner => simp [wfNode] at hwB
      | collision ib tb ys =>
        have hp : xs.Perm ys := hag
        have hone := one_of_cu xs huA (fun x => cfg.eqTT x v) (eqTT_viaP P v)
        rw [doAdd.eq_1, doAdd.eq_1]
        unfold findIdx?
        simp only [Node.collisions]
        rcases perm_found (fun x => cfg.eqTT x v) xs ys hp hone with ⟨h1, h2⟩ | ⟨i, j, h1, h2, _, _, _, hpe⟩
        · rw [h1, h2]
          show (v :: xs).Perm (v :: ys) ∧ true = true
          exact ⟨hp.cons v, rfl⟩
        · rw [h1, h2]
          show (v :: eraseAt xs i).Perm (v :: eraseAt ys j) ∧ false = false
          exact ⟨hpe.cons v, rfl⟩
  | succ r ih =>
    intro hr A B s s' hwA hwB huA hag
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    obtain ⟨hnm, hdm⟩ := agree_maps PermL r A B hwA hwB hag
    have hsl := hag D hD
    by_cases hA : A.nodemap.testBit D = true
    · have hB : B.nodemap.testBit D = true := by rw [← hnm]; exact hA
      have hA' : (A.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hB' : (B.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
      have hsA : slot A D = .child (A.cs.getD (pos A.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hsB : slot B D = .child (B.cs.getD (pos B.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hB]
      rw [hsA, hsB] at hsl
      have hab : AgreeP r (A.cs.getD (pos A.nodemap D) Node.dummy) (B.cs.getD (pos B.nodemap D) Node.dummy) := hsl
      have hwa := slot_child_wf r A hwA D hD _ hsA
      have hwb := slot_child_wf r B hwB D hD _ hsB
      have hua : CU cfg r (A.cs.getD (pos A.nodemap D) Node.dummy) := by
        have := huA D hD; rw [hsA] at this; exact this
      have eA : ((doAdd cfg (r + 1) A v h).run s).1 =
          (((copyInnerReplace A (pos A.nodemap D) ((doAdd cfg r (A.cs.getD (pos A.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAdd cfg r (A.cs.getD (pos A.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAdd cfg r (A.cs.getD (pos A.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      have eB : ((doAdd cfg (r + 1) B v h).run s').1 =
          (((copyInnerReplace B (pos B.nodemap D) ((doAdd cfg r (B.cs.getD (pos B.nodemap D) Node.dummy) v h).run s').1.1).run
            ((doAdd cfg r (B.cs.getD (pos B.nodemap D) Node.dummy) v h).run s').2).1,
           ((doAdd cfg r (B.cs.getD (pos B.nodemap D) Node.dummy) v h).run s').1.2) := by
        rw [doAdd.eq_2]; dsimp only; rw [hbit, if_pos hB']; rfl
      rw [eA, eB]
      dsimp only
      have oA := add_step cfg v h hv r (by omega) _ s hwa
      have oB := add_step cfg v h hv r (by omega) _ s' hwb
      have ihc := ih (by omega) _ _ s s' hwa hwb hua hab
      exact ⟨agree_edits2 PermL r A B _ _ D _ _ (edit_replace r A _ D _ hwA hD hA oA.wf)
        (edit_replace r B _ D _ hwB hD hB oB.wf) hag ihc.1, ihc.2⟩
    · have hA0 : A.nodemap.testBit D = false := by simpa using hA
      have hB0 : B.nodemap.testBit D = false := by rw [← hnm]; exact hA0
      have hA' : ¬ (A.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hB' : ¬ (B.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne, hB0]; simp
      by_cases hBd : A.datamap.testBit D = true
      · have hBdB : B.datamap.testBit D = true := by rw [← hdm]; exact hBd
        have hBd' : (A.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hBd
        have hBdB' : (B.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hBdB
        have hsA : slot A D = .data (A.values.getD (pos A.datamap D) default) := by
          unfold slot; rw [if_neg hA, if_pos hBd]
        have hsB : slot B D = .data (B.values.getD (pos B.datamap D) default) := by
          unfold slot; rw [if_neg (by rw [hB0]; simp), if_pos hBdB]
        rw [hsA, hsB] at hsl
        have hyv : A.values.getD (pos A.datamap D) default = B.values.getD (pos B.datamap D) default := hsl
        generalize hvalA : A.values.getD (pos A.datamap D) default = val at hyv
        have hvalB : B.values.getD (pos B.datamap D) default = val := hyv.symm
        by_cases hE : cfg.eqTT val v = true
        · have eA : ((doAdd cfg (r + 1) A v h).run s).1 =
              (((copyInnerReplaceValue A (pos A.datamap D) v).run s).1, false) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hBd']
            rw [if_pos (show cfg.eqTT (A.values.getD (A.dataCountBit (2 ^ D)) default) v = true by
              rw [show A.dataCountBit (2 ^ D) = pos A.datamap D from rfl, hvalA]; exact hE)]; rfl
          have eB : ((doAdd cfg (r + 1) B v h).run s').1 =
              (((copyInnerReplaceValue B (pos B.datamap D) v).run s').1, false) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hB', if_pos hBdB']
            rw [if_pos (show cfg.eqTT (B.values.getD (B.dataCountBit (2 ^ D)) default) v = true by
              rw [show B.dataCountBit (2 ^ D) = pos B.datamap D from rfl, hvalB]; exact hE)]; rfl
          rw [eA, eB]
          dsimp only
          exact ⟨agree_edits2 PermL r A B _ _ D _ _ (edit_replaceValue r A v D s hwA hD hA0 hBd)
            (edit_replaceValue r B v D s' hwB hD hB0 hBdB) hag rfl, rfl⟩
        · have eA : ((doAdd cfg (r + 1) A v h).run s).1 =
              (((copyInnerReplaceMerged A (2 ^ D) (pos A.datamap D)
                ((makeMerged none r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged none r v h val (cfg.hashT val)).run s).2).1, true) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hBd']
            rw [if_neg (show ¬ cfg.eqTT (A.values.getD (A.dataCountBit (2 ^ D)) default) v = true by
              rw [show A.dataCountBit (2 ^ D) = pos A.datamap D from rfl, hvalA]; exact hE)]
            rw [show A.dataCountBit (2 ^ D) = pos A.datamap D from rfl, hvalA]
            rfl
          have eB : ((doAdd cfg (r + 1) B v h).run s').1 =
              (((copyInnerReplaceMerged B (2 ^ D) (pos B.datamap D)
                ((makeMerged none r v h val (cfg.hashT val)).run s').1).run
                ((makeMerged none r v h val (cfg.hashT val)).run s').2).1, true) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hB', if_pos hBdB']
            rw [if_neg (show ¬ cfg.eqTT (B.values.getD (B.dataCountBit (2 ^ D)) default) v = true by
              rw [show B.dataCountBit (2 ^ D) = pos B.datamap D from rfl, hvalB]; exact hE)]
            rw [show B.dataCountBit (2 ^ D) = pos B.datamap D from rfl, hvalB]
            rfl
          rw [eA, eB]
          dsimp only
          have hag2 := agree_makeMerged PermL (fun l => List.Perm.refl l) none none v val h (cfg.hashT val) r s s'
          have hw1 := wf_makeMerged none v val h (cfg.hashT val) r s
          have hw2 := wf_makeMerged none v val h (cfg.hashT val) r s'
          generalize (makeMerged none r v h val (cfg.hashT val)).run s = q1 at hag2 hw1
          generalize (makeMerged none r v h val (cfg.hashT val)).run s' = q2 at hag2 hw2
          obtain ⟨m1, s1⟩ := q1
          obtain ⟨m2, s2⟩ := q2
          dsimp only at hag2 hw1 hw2 ⊢
          exact ⟨agree_edits2 PermL r A B _ _ D _ _ (edit_replaceMerged r A m1 D s1 hwA hD hA0 hBd hw1)
            (edit_replaceMerged r B m2 D s2 hwB hD hB0 hBdB hw2) hag hag2, rfl⟩
      · have hBd0 : A.datamap.testBit D = false := by simpa using hBd
        have hBdB0 : B.datamap.testBit D = false := by rw [← hdm]; exact hBd0
        have hBd' : ¬ (A.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hBd
        have hBdB' : ¬ (B.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne, hBdB0]; simp
        have eA : ((doAdd cfg (r + 1) A v h).run s).1 = (((copyInnerInsertValue A (2 ^ D) v).run s).1, true) := by
          rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hBd']; rfl
        have eB : ((doAdd cfg (r + 1) B v h).run s').1 = (((copyInnerInsertValue B (2 ^ D) v).run s').1, true) := by
          rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hB', if_neg hBdB']; rfl
        rw [eA, eB]
        dsimp only
        exact ⟨agree_edits2 PermL r A B _ _ D _ _ (edit_insertValue r A v D s hwA hD hA0 hBd0)
          (edit_insertValue r B v D s' hwB hD hB0 hBdB0) hag rfl, rfl⟩


theorem sub_congrP (P : PER cfg) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (A B : Node α) (s s' : Al), wfNode r A = true → wfNode r B = true →
      CU cfg r A → AgreeP r A B →
      SubAgree (AgreeP r) ((doSub cfg k r A h).run s).1 ((doSub cfg k r B h).run s').1 := by
  intro r
  induction r with
  | zero =>
    intro _ A B s s' hwA hwB huA hag
    have hp : A.collisions.Perm B.collisions := hag
    have hlA : A.collisions.length ≥ 2 := by
      cases A with
      | inner => simp [wfNode] at hwA
      | collision _ _ xs => simpa [wfNode, Node.collisions] using hwA
    have hlen : A.collisions.length = B.collisions.length := hp.length_eq
    have hone := one_of_cu A.collisions (cu_zero_iff.mp huA) (fun x => cfg.eqTK x k) (P.viaK · · k)
    rw [doSub.eq_1, doSub.eq_1]
    unfold findIdx?
    rcases perm_found (fun x => cfg.eqTK x k) A.collisions B.collisions hp hone with
      ⟨h1, h2⟩ | ⟨i, j, h1, h2, hi, hj, _, hpe⟩
    · rw [h1, h2]; trivial
    · rw [h1, h2]
      dsimp only
      by_cases hl : A.collisions.length > 2
      · rw [if_pos hl, if_pos (show B.collisions.length > 2 by omega)]
        show (eraseAt A.collisions i).Perm (eraseAt B.collisions j)
        exact hpe
      · rw [if_neg hl, if_neg (show ¬ B.collisions.length > 2 by omega)]
        have h2x : A.collisions.length = 2 := by omega
        have h2y : B.collisions.length = 2 := by omega
        rw [eraseAt_two _ i h2x (by omega), eraseAt_two _ j h2y (by omega)] at hpe
        show A.collisions.getD (if i == 0 then 1 else 0) default = B.collisions.getD (if j == 0 then 1 else 0) default
        have := List.perm_singleton.mp hpe
        simpa using this
  | succ r ih =>
    intro hr A B s s' hwA hwB huA hag
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    obtain ⟨hnm, hdm⟩ := agree_maps PermL r A B hwA hwB hag
    have hsl := hag D hD
    rw [doSub.eq_2, doSub.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : A.nodemap.testBit D = true
    · have hB : B.nodemap.testBit D = true := by rw [← hnm]; exact hA
      have hA' : (A.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hB' : (B.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
      rw [if_pos hA', if_pos hB']
      have hsA : slot A D = .child (A.cs.getD (pos A.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hsB : slot B D = .child (B.cs.getD (pos B.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hB]
      rw [hsA, hsB] at hsl
      have hab : AgreeP r (A.child (A.childrenCountBit (2 ^ D))) (B.child (B.childrenCountBit (2 ^ D))) := hsl
      have hwa := slot_child_wf r A hwA D hD _ hsA
      have hwb := slot_child_wf r B hwB D hD _ hsB
      have hua : CU cfg r (A.child (A.childrenCountBit (2 ^ D))) := by
        have := huA D hD; rw [hsA] at this; exact this
      have iw : SubAgree (AgreeP r) ((doSub cfg k r (A.child (A.childrenCountBit (2 ^ D))) h).run s).1
          ((doSub cfg k r (B.child (B.childrenCountBit (2 ^ D))) h).run s').1 :=
        ih (by omega) _ _ s s' hwa hwb hua hab
      have oA : SubOut cfg k r (A.cs.getD (pos A.nodemap D) Node.dummy)
          ((doSub cfg k r (A.child (A.childrenCountBit (2 ^ D))) h).run s).1 :=
        sub_step cfg k h r (by omega) _ s hwa
      have oB : SubOut cfg k r (B.cs.getD (pos B.nodemap D) Node.dummy)
          ((doSub cfg k r (B.child (B.childrenCountBit (2 ^ D))) h).run s').1 :=
        sub_step cfg k h r (by omega) _ s' hwb
      have hcm : B.childrenCount = A.childrenCount := by
        show popcount B.nodemap = popcount A.nodemap; rw [hnm]
      simp only [StateT.run_bind]
      generalize (doSub cfg k r (A.child (A.childrenCountBit (2 ^ D))) h).run s = q1 at iw oA
      generalize (doSub cfg k r (B.child (B.childrenCountBit (2 ^ D))) h).run s' = q2 at iw oB
      obtain ⟨res1, s1⟩ := q1
      obtain ⟨res2, s2⟩ := q2
      dsimp only at iw oA oB ⊢
      cases res1 with
      | nothing =>
        cases res2 with
        | nothing => trivial
        | singleton _ => exact (iw : False).elim
        | tree _ => exact (iw : False).elim
      | singleton x =>
        cases res2 with
        | nothing => exact (iw : False).elim
        | tree _ => exact (iw : False).elim
        | singleton y =>
          have hxy : x = y := iw
          subst hxy
          try dsimp only
          rw [show B.datamap = A.datamap from hdm.symm, hcm]
          split
          · next c1 => (try rw [if_pos c1]); rfl
          · next c1 =>
            try rw [if_neg c1]
            exact agree_edits2 PermL r A B _ _ D _ _ (edit_replaceInline r A x D s1 hwA hD hA)
              (edit_replaceInline r B x D s2 hwB hD hB) hag rfl
      | tree t1 =>
        cases res2 with
        | nothing => exact (iw : False).elim
        | singleton _ => exact (iw : False).elim
        | tree t2 =>
          have ht : AgreeP r t1 t2 := iw
          exact agree_edits2 PermL r A B _ _ D _ _ (edit_replace r A t1 D s1 hwA hD hA oA.1)
            (edit_replace r B t2 D s2 hwB hD hB oB.1) hag ht
    · have hA0 : A.nodemap.testBit D = false := by simpa using hA
      have hB0 : B.nodemap.testBit D = false := by rw [← hnm]; exact hA0
      have hA' : ¬ (A.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hB' : ¬ (B.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne, hB0]; simp
      rw [if_neg hA', if_neg hB']
      by_cases hBd : A.datamap.testBit D = true
      · have hBdB : B.datamap.testBit D = true := by rw [← hdm]; exact hBd
        have hBd' : (A.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hBd
        have hBdB' : (B.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hBdB
        rw [if_pos hBd', if_pos hBdB']
        have hsA : slot A D = .data (A.values.getD (pos A.datamap D) default) := by
          unfold slot; rw [if_neg hA, if_pos hBd]
        have hsB : slot B D = .data (B.values.getD (pos B.datamap D) default) := by
          unfold slot; rw [if_neg (by rw [hB0]; simp), if_pos hBdB]
        rw [hsA, hsB] at hsl
        have hyv : A.values.getD (pos A.datamap D) default = B.values.getD (pos B.datamap D) default := hsl
        have hdc : B.dataCount = A.dataCount := by show popcount B.datamap = popcount A.datamap; rw [hdm]
        by_cases hE : cfg.eqTK (A.values.getD (pos A.datamap D) default) k = true
        · have hEA : cfg.eqTK (A.values.getD (A.dataCountBit (2 ^ D)) default) k = true := hE
          have hEB : cfg.eqTK (B.values.getD (B.dataCountBit (2 ^ D)) default) k = true := by
            show cfg.eqTK (B.values.getD (pos B.datamap D) default) k = true; rw [← hyv]; exact hE
          rw [if_pos hEA, if_pos hEB]
          by_cases c1 : (A.nodemap != 0 || decide (A.dataCount > 2)) = true
          · have c1B : (B.nodemap != 0 || decide (B.dataCount > 2)) = true := by
              rw [show B.nodemap = A.nodemap from hnm.symm, hdc]; exact c1
            rw [if_pos c1, if_pos c1B]
            exact agree_edits2 PermL r A B _ _ D _ _ (edit_removeValue r A D s hwA hD hA0 hBd)
              (edit_removeValue r B D s' hwB hD hB0 hBdB) hag trivial
          · have c1B : ¬ (B.nodemap != 0 || decide (B.dataCount > 2)) = true := by
              rw [show B.nodemap = A.nodemap from hnm.symm, hdc]; exact c1
            rw [if_neg c1, if_neg c1B]
            have hn0 : A.nodemap = 0 := by simp at c1; exact c1.1
            by_cases c2 : (A.dataCount == 2) = true
            · have c2B : (B.dataCount == 2) = true := by rw [hdc]; exact c2
              rw [if_pos c2, if_pos c2B]
              have hdc2 : popcount A.datamap = 2 := (by simpa using c2 : A.dataCount = 2)
              split
              · next hsh =>
                try rw [if_pos hsh]
                have pA := iter_two r A hwA D hD hBd hn0 hdc2
                have pB := iter_two r B hwB D hD hBdB (by rw [← hnm]; exact hn0) (by rw [← hdm]; exact hdc2)
                have pAB := agree_iter (r + 1) A B hwA hwB hag
                rw [hyv] at pA
                have hoo := List.perm_singleton.mp ((pA.symm.trans (pAB.trans pB)).cons_inv)
                show A.values.getD (if (pos A.datamap D == 0) = true then 1 else 0) default =
                  B.values.getD (if (pos B.datamap D == 0) = true then 1 else 0) default
                simpa using hoo
              · next hsh =>
                try rw [if_neg hsh]
                exact agree_edits2 PermL r A B _ _ D _ _ (edit_rootCollapse r A D s hwA hD hBd hn0 hdc2)
                  (edit_rootCollapse r B D s' hwB hD hBdB (by rw [← hnm]; exact hn0) (by rw [← hdm]; exact hdc2))
                  hag trivial
            · have c2B : ¬ (B.dataCount == 2) = true := by rw [hdc]; exact c2
              rw [if_neg c2, if_neg c2B]
              exact agree_refl PermL (fun l => List.Perm.refl l) (r + 1) _
        · have hEA : ¬ cfg.eqTK (A.values.getD (A.dataCountBit (2 ^ D)) default) k = true := hE
          have hEB : ¬ cfg.eqTK (B.values.getD (B.dataCountBit (2 ^ D)) default) k = true := by
            show ¬ cfg.eqTK (B.values.getD (pos B.datamap D) default) k = true; rw [← hyv]; exact hE
          rw [if_neg hEA, if_neg hEB]
          trivial
      · have hBd0 : A.datamap.testBit D = false := by simpa using hBd
        have hBdB0 : B.datamap.testBit D = false := by rw [← hdm]; exact hBd0
        have hBd' : ¬ (A.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hBd
        have hBdB' : ¬ (B.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne, hBdB0]; simp
        rw [if_neg hBd', if_neg hBdB']
        trivial


theorem add_root_congrP (P : PER cfg) (A B : Champ α) (v : α) (s s' : Al) (hwA : wfNode 13 A.root = true)
    (hwB : wfNode 13 B.root = true) (hcu : CU cfg 13 A.root) (hag : AgreeP 13 A.root B.root) (hsz : A.size = B.size) :
    AgreeP 13 ((A.add cfg v).run s).1.root ((B.add cfg v).run s').1.root ∧
      ((A.add cfg v).run s).1.size = ((B.add cfg v).run s').1.size := by
  obtain ⟨h1, h2⟩ := add_congrP P v (cfg.hashT v) rfl 13 (Nat.le_refl _) A.root B.root s s' hwA hwB hcu hag
  refine ⟨h1, ?_⟩
  show A.size + (if ((doAdd cfg 13 A.root v (cfg.hashT v)).run s).1.2 then 1 else 0) =
    B.size + (if ((doAdd cfg 13 B.root v (cfg.hashT v)).run s').1.2 then 1 else 0)
  rw [hsz, h2]

theorem sub_root_congrP (P : PER cfg) (A B : Champ α) (k : κ) (s s' : Al) (hwA : wfNode 13 A.root = true)
    (hwB : wfNode 13 B.root = true) (hcu : CU cfg 13 A.root) (hag : AgreeP 13 A.root B.root) (hsz : A.size = B.size) :
    AgreeP 13 ((A.sub cfg k).run s).1.root ((B.sub cfg k).run s').1.root ∧
      ((A.sub cfg k).run s).1.size = ((B.sub cfg k).run s').1.size := by
  have ag := sub_congrP P k (cfg.hashK k) 13 (Nat.le_refl _) A.root B.root s s' hwA hwB hcu hag
  unfold Champ.sub
  simp only [StateT.run_bind]
  generalize (doSub cfg k 13 A.root (cfg.hashK k)).run s = q1 at ag
  generalize (doSub cfg k 13 B.root (cfg.hashK k)).run s' = q2 at ag
  obtain ⟨res1, s1⟩ := q1
  obtain ⟨res2, s2⟩ := q2
  dsimp only at ag ⊢
  cases res1 <;> cases res2 <;> first
    | exact (ag : False).elim
    | exact ⟨hag, hsz⟩
    | exact ⟨ag, show A.size - 1 = B.size - 1 by rw [hsz]⟩

theorem congr_stepP (P : PER cfg) (A B : Champ α) (op : TOp α κ) (s s' : Al) (hwA : wfNode 13 A.root = true)
    (hwB : wfNode 13 B.root = true) (hcu : CU cfg 13 A.root) (hag : AgreeP 13 A.root B.root) (hsz : A.size = B.size) :
    AgreeP 13 ((applyT cfg A op.persist).run s).1.root ((applyT cfg B op.persist).run s').1.root ∧
      ((applyT cfg A op.persist).run s).1.size = ((applyT cfg B op.persist).run s').1.size := by
  cases op with
  | add v => exact add_root_congrP P A B v s s' hwA hwB hcu hag hsz
  | addMut e v => exact add_root_congrP P A B v s s' hwA hwB hcu hag hsz
  | sub k => exact sub_root_congrP P A B k s s' hwA hwB hcu hag hsz
  | subMut e k => exact sub_root_congrP P A B k s s' hwA hwB hcu hag hsz

/-- ★ **Stock jank, `PER` equality**: a sequence of persistent and transient steps and the same sequence
with every transient step made persistent agree node by node up to collision order, with the same
size, from two well-formed champs that agree so (the first meeting `CU`). -/
theorem buildT_agreeP (P : PER cfg) :
    ∀ (ops : List (TOp α κ)) (A B : Champ α) (s s' : Al), wfNode 13 A.root = true → wfNode 13 B.root = true →
      CU cfg 13 A.root → AgreeP 13 A.root B.root → A.size = B.size →
      AgreeP 13 ((buildT cfg A ops).run s).1.root ((buildT cfg B (ops.map TOp.persist)).run s').1.root ∧
        ((buildT cfg A ops).run s).1.size = ((buildT cfg B (ops.map TOp.persist)).run s').1.size
  | [], _, _, _, _, _, _, _, hag, hsz => ⟨hag, hsz⟩
  | op :: ops, A, B, s, s', hwA, hwB, hcu, hag, hsz => by
    have eA : ((buildT cfg A (op :: ops)).run s).1 =
        ((buildT cfg ((applyT cfg A op).run s).1 ops).run ((applyT cfg A op).run s).2).1 := rfl
    have eB : ((buildT cfg B ((op :: ops).map TOp.persist)).run s').1 =
        ((buildT cfg ((applyT cfg B op.persist).run s').1 (ops.map TOp.persist)).run
          ((applyT cfg B op.persist).run s').2).1 := rfl
    rw [eA, eB]
    have h1 := persist_step (cfg := cfg) A op s hwA
    have h2 := congr_stepP P A B op s s' hwA hwB hcu hag hsz
    exact buildT_agreeP P ops _ _ _ _ (stepS_wf cfg A s hwA op) (stepS_wf cfg B s' hwB op.persist)
      (cu_step cfg P A s hwA hcu op)
      (agree_trans PermL (fun a b c h1 h2 => h1.trans h2) 13 _ _ _ h1.1 h2.1) (h1.2.trans h2.2)

/-- ★ **From `champ::empty()`, stock jank, `PER` equality**: a jank program's chain of `conj`/`assoc`/
`disj`/`dissoc` and `transient`/`conj!`/`assoc!`/`disj!`/`dissoc!`/`persistent!` and the same chain with
no transient give champs with the same size that agree node by node up to the order inside collision
nodes, and so iterate as permutations of each other (the same contents). NaN's irreflexive `=` and
D12's `=`/hash mismatches are inside the hypothesis; D8's non-transitive `=` is not (H9-1). -/
theorem buildT_agreeP_empty (P : PER cfg) (ops : List (TOp α κ)) (s s' : Al) :
    AgreeP 13 ((buildT cfg Champ.empty ops).run s).1.root ((buildT cfg Champ.empty (ops.map TOp.persist)).run s').1.root ∧
      ((buildT cfg Champ.empty ops).run s).1.size = ((buildT cfg Champ.empty (ops.map TOp.persist)).run s').1.size ∧
      ((buildT cfg Champ.empty ops).run s).1.toList.Perm ((buildT cfg Champ.empty (ops.map TOp.persist)).run s').1.toList := by
  obtain ⟨h1, h2⟩ := buildT_agreeP P ops Champ.empty Champ.empty s s' rfl rfl (cu_empty cfg 12)
    (agree_refl PermL (fun l => List.Perm.refl l) 13 _) rfl
  refine ⟨h1, h2, ?_⟩
  exact agree_iter 13 _ _ (buildT_wf_any cfg ops _ s rfl) (buildT_wf_any cfg _ _ s' rfl) h1

end Jank.R9.Champ

import Jank.R9.Champ.Fix

/-!
# Round 9, CHAMP: with H8-1's fix, a transient chain and its persistent twin agree EXACTLY, for every
equality

Round 8 (`Jank.R8.Champ.buildT_agree_empty`) compared a sequence of persistent and transient steps with
the same sequence made all persistent, under a lawful equality (round 6's `Lawful`: an equivalence
agreeing with the hash), and found agreement only up to the order inside collision nodes. With the fix
(`fixes/H8-1-immer.diff`; `Fix.lean`) the comparison is exact and needs nothing of the equality:

- ★ `add_congrF`, ★ `sub_congrE`: the (fixed) `do_add` and `do_sub` of one value or key on two
  well-formed nodes that agree EXACTLY (`Agree Eq`) give results that agree exactly, with the same
  `added` flag / result kind and passed-up value. For every hash and EVERY equality (no `Lawful`, no
  uniqueness): both nodes hold the same values in the same order, so every `Equal` call is the same.
  Round 8's `add_congr`/`sub_congr` (up to collision order) needed a lawful equality because two
  orders of one collision list can find different values.
- ★ `stepF_wf`, ★ `buildTF_wf`: every fixed step keeps `wfNode` (every hash, every equality).
- ★ `buildTF_agree`, ★ `buildTF_agree_empty`: **with the fix, every sequence of `assoc`/`conj`,
  `dissoc`/`disj`, `assoc!`/`conj!`, `dissoc!`/`disj!` (any owner tokens) and the same sequence with
  every transient step made persistent give champs that agree node by node EXACTLY, with the same size,
  for every hash function and every equality** (jank's non-transitive BigDecimal `=` (D8), NaN's
  irreflexive `=` (V85) and the `=`/hash mismatches (D12) included).
- ★ `agreeEq_iter`: such champs iterate identically (seq, keys, vals, printing, reduce see one order).
-/

namespace Jank.R9.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ Jank.R8.Champ

variable {α κ : Type} [Inhabited α]

/-! ## Exact congruence of the persistent steps (every equality) -/

/-- ★ The fixed `do_add` of one value on two well-formed nodes that agree exactly gives results that
agree exactly and the same `added` flag, for every hash and every equality. -/
theorem add_congrF (cfg : Cfg α κ) (v : α) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (A B : Node α) (s s' : Al), wfNode r A = true → wfNode r B = true →
      Agree Eq r A B →
      Agree Eq r ((doAddF cfg r A v h).run s).1.1 ((doAddF cfg r B v h).run s').1.1 ∧
        ((doAddF cfg r A v h).run s).1.2 = ((doAddF cfg r B v h).run s').1.2 := by
  intro r
  induction r with
  | zero =>
    intro _ A B s s' hwA hwB hag
    cases A with
    | inner => simp [wfNode] at hwA
    | collision ia ta xs =>
      cases B with
      | inner => simp [wfNode] at hwB
      | collision ib tb ys =>
        have hp : xs = ys := hag
        subst hp
        rw [doAddF.eq_1, doAddF.eq_1]
        unfold findIdx?
        simp only [Node.collisions]
        cases xs.findIdx? (fun x => cfg.eqTT x v) with
        | none =>
          show (v :: xs) = (v :: xs) ∧ true = true
          exact ⟨rfl, rfl⟩
        | some pos =>
          show xs.set pos v = xs.set pos v ∧ false = false
          exact ⟨rfl, rfl⟩
  | succ r ih =>
    intro hr A B s s' hwA hwB hag
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    obtain ⟨hnm, hdm⟩ := agree_maps Eq r A B hwA hwB hag
    have hsl := hag D hD
    by_cases hA : A.nodemap.testBit D = true
    · have hB : B.nodemap.testBit D = true := by rw [← hnm]; exact hA
      have hA' : (A.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hB' : (B.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
      have hsA : slot A D = .child (A.cs.getD (pos A.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hsB : slot B D = .child (B.cs.getD (pos B.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hB]
      rw [hsA, hsB] at hsl
      have hab : Agree Eq r (A.cs.getD (pos A.nodemap D) Node.dummy) (B.cs.getD (pos B.nodemap D) Node.dummy) := hsl
      have hwa := slot_child_wf r A hwA D hD _ hsA
      have hwb := slot_child_wf r B hwB D hD _ hsB
      have eA : ((doAddF cfg (r + 1) A v h).run s).1 =
          (((copyInnerReplace A (pos A.nodemap D) ((doAddF cfg r (A.cs.getD (pos A.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAddF cfg r (A.cs.getD (pos A.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAddF cfg r (A.cs.getD (pos A.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAddF.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      have eB : ((doAddF cfg (r + 1) B v h).run s').1 =
          (((copyInnerReplace B (pos B.nodemap D) ((doAddF cfg r (B.cs.getD (pos B.nodemap D) Node.dummy) v h).run s').1.1).run
            ((doAddF cfg r (B.cs.getD (pos B.nodemap D) Node.dummy) v h).run s').2).1,
           ((doAddF cfg r (B.cs.getD (pos B.nodemap D) Node.dummy) v h).run s').1.2) := by
        rw [doAddF.eq_2]; dsimp only; rw [hbit, if_pos hB']; rfl
      rw [eA, eB]
      dsimp only
      have oA := wf_doAddF cfg v h r (by omega) _ s hwa
      have oB := wf_doAddF cfg v h r (by omega) _ s' hwb
      have ihc := ih (by omega) _ _ s s' hwa hwb hab
      exact ⟨agree_edits2 Eq r A B _ _ D _ _ (edit_replace r A _ D _ hwA hD hA oA)
        (edit_replace r B _ D _ hwB hD hB oB) hag ihc.1, ihc.2⟩
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
        · have eA : ((doAddF cfg (r + 1) A v h).run s).1 =
              (((copyInnerReplaceValue A (pos A.datamap D) v).run s).1, false) := by
            rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hBd']
            rw [if_pos (show cfg.eqTT (A.values.getD (A.dataCountBit (2 ^ D)) default) v = true by
              rw [show A.dataCountBit (2 ^ D) = pos A.datamap D from rfl, hvalA]; exact hE)]; rfl
          have eB : ((doAddF cfg (r + 1) B v h).run s').1 =
              (((copyInnerReplaceValue B (pos B.datamap D) v).run s').1, false) := by
            rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hB', if_pos hBdB']
            rw [if_pos (show cfg.eqTT (B.values.getD (B.dataCountBit (2 ^ D)) default) v = true by
              rw [show B.dataCountBit (2 ^ D) = pos B.datamap D from rfl, hvalB]; exact hE)]; rfl
          rw [eA, eB]
          dsimp only
          exact ⟨agree_edits2 Eq r A B _ _ D _ _ (edit_replaceValue r A v D s hwA hD hA0 hBd)
            (edit_replaceValue r B v D s' hwB hD hB0 hBdB) hag rfl, rfl⟩
        · have eA : ((doAddF cfg (r + 1) A v h).run s).1 =
              (((copyInnerReplaceMerged A (2 ^ D) (pos A.datamap D)
                ((makeMerged none r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged none r v h val (cfg.hashT val)).run s).2).1, true) := by
            rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hBd']
            rw [if_neg (show ¬ cfg.eqTT (A.values.getD (A.dataCountBit (2 ^ D)) default) v = true by
              rw [show A.dataCountBit (2 ^ D) = pos A.datamap D from rfl, hvalA]; exact hE)]
            rw [show A.dataCountBit (2 ^ D) = pos A.datamap D from rfl, hvalA]
            rfl
          have eB : ((doAddF cfg (r + 1) B v h).run s').1 =
              (((copyInnerReplaceMerged B (2 ^ D) (pos B.datamap D)
                ((makeMerged none r v h val (cfg.hashT val)).run s').1).run
                ((makeMerged none r v h val (cfg.hashT val)).run s').2).1, true) := by
            rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hB', if_pos hBdB']
            rw [if_neg (show ¬ cfg.eqTT (B.values.getD (B.dataCountBit (2 ^ D)) default) v = true by
              rw [show B.dataCountBit (2 ^ D) = pos B.datamap D from rfl, hvalB]; exact hE)]
            rw [show B.dataCountBit (2 ^ D) = pos B.datamap D from rfl, hvalB]
            rfl
          rw [eA, eB]
          dsimp only
          have hag2 := agree_makeMerged Eq (fun _ => rfl) none none v val h (cfg.hashT val) r s s'
          have hw1 := wf_makeMerged none v val h (cfg.hashT val) r s
          have hw2 := wf_makeMerged none v val h (cfg.hashT val) r s'
          generalize (makeMerged none r v h val (cfg.hashT val)).run s = q1 at hag2 hw1
          generalize (makeMerged none r v h val (cfg.hashT val)).run s' = q2 at hag2 hw2
          obtain ⟨m1, s1⟩ := q1
          obtain ⟨m2, s2⟩ := q2
          dsimp only at hag2 hw1 hw2 ⊢
          exact ⟨agree_edits2 Eq r A B _ _ D _ _ (edit_replaceMerged r A m1 D s1 hwA hD hA0 hBd hw1)
            (edit_replaceMerged r B m2 D s2 hwB hD hB0 hBdB hw2) hag hag2, rfl⟩
      · have hBd0 : A.datamap.testBit D = false := by simpa using hBd
        have hBdB0 : B.datamap.testBit D = false := by rw [← hdm]; exact hBd0
        have hBd' : ¬ (A.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hBd
        have hBdB' : ¬ (B.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne, hBdB0]; simp
        have eA : ((doAddF cfg (r + 1) A v h).run s).1 = (((copyInnerInsertValue A (2 ^ D) v).run s).1, true) := by
          rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hBd']; rfl
        have eB : ((doAddF cfg (r + 1) B v h).run s').1 = (((copyInnerInsertValue B (2 ^ D) v).run s').1, true) := by
          rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hB', if_neg hBdB']; rfl
        rw [eA, eB]
        dsimp only
        exact ⟨agree_edits2 Eq r A B _ _ D _ _ (edit_insertValue r A v D s hwA hD hA0 hBd0)
          (edit_insertValue r B v D s' hwB hD hB0 hBdB0) hag rfl, rfl⟩


/-! ## Exact congruence of `do_sub` (every equality) -/

/-- ★ `do_sub` (`dissoc`/`disj`, unchanged by the fix) of one key on two well-formed nodes that agree
exactly gives the same result kind, the same passed-up value and trees that agree exactly, for every
hash and every equality. -/
theorem sub_congrE (cfg : Cfg α κ) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (A B : Node α) (s s' : Al), wfNode r A = true → wfNode r B = true →
      Agree Eq r A B →
      SubAgree (Agree Eq r) ((doSub cfg k r A h).run s).1 ((doSub cfg k r B h).run s').1 := by
  intro r
  induction r with
  | zero =>
    intro _ A B s s' _ _ hag
    have hp : A.collisions = B.collisions := hag
    rw [doSub.eq_1, doSub.eq_1]
    unfold findIdx?
    rw [← hp]
    cases A.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => trivial
    | some cur =>
      dsimp only
      by_cases hl : A.collisions.length > 2
      · rw [if_pos hl, if_pos hl]
        show eraseAt A.collisions cur = eraseAt B.collisions cur
        rw [hp]
      · rw [if_neg hl, if_neg hl]
        rfl
  | succ r ih =>
    intro hr A B s s' hwA hwB hag
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    obtain ⟨hnm, hdm⟩ := agree_maps Eq r A B hwA hwB hag
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
      have hab : Agree Eq r (A.child (A.childrenCountBit (2 ^ D))) (B.child (B.childrenCountBit (2 ^ D))) := hsl
      have hwa := slot_child_wf r A hwA D hD _ hsA
      have hwb := slot_child_wf r B hwB D hD _ hsB
      have iw : SubAgree (Agree Eq r) ((doSub cfg k r (A.child (A.childrenCountBit (2 ^ D))) h).run s).1
          ((doSub cfg k r (B.child (B.childrenCountBit (2 ^ D))) h).run s').1 :=
        ih (by omega) _ _ s s' hwa hwb hab
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
            exact agree_edits2 Eq r A B _ _ D _ _ (edit_replaceInline r A x D s1 hwA hD hA)
              (edit_replaceInline r B x D s2 hwB hD hB) hag rfl
      | tree t1 =>
        cases res2 with
        | nothing => exact (iw : False).elim
        | singleton _ => exact (iw : False).elim
        | tree t2 =>
          have ht : Agree Eq r t1 t2 := iw
          exact agree_edits2 Eq r A B _ _ D _ _ (edit_replace r A t1 D s1 hwA hD hA oA.1)
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
            exact agree_edits2 Eq r A B _ _ D _ _ (edit_removeValue r A D s hwA hD hA0 hBd)
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
                have pAB := agree_iter (r + 1) A B hwA hwB (agree_mono Eq PermL (fun a b hab => hab ▸ List.Perm.refl a) (r + 1) A B hag)
                rw [hyv] at pA
                have hoo := List.perm_singleton.mp ((pA.symm.trans (pAB.trans pB)).cons_inv)
                show A.values.getD (if (pos A.datamap D == 0) = true then 1 else 0) default =
                  B.values.getD (if (pos B.datamap D == 0) = true then 1 else 0) default
                simpa using hoo
              · next hsh =>
                try rw [if_neg hsh]
                exact agree_edits2 Eq r A B _ _ D _ _ (edit_rootCollapse r A D s hwA hD hBd hn0 hdc2)
                  (edit_rootCollapse r B D s' hwB hD hBdB (by rw [← hnm]; exact hn0) (by rw [← hdm]; exact hdc2))
                  hag trivial
            · have c2B : ¬ (B.dataCount == 2) = true := by rw [hdc]; exact c2
              rw [if_neg c2, if_neg c2B]
              exact agree_refl Eq (fun _ => rfl) (r + 1) _
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


/-! ## Iteration -/

theorem flatMap_map_congr {β γ δ : Type} (k : γ → List δ) (f g : β → γ) :
    ∀ l : List β, (∀ x ∈ l, k (f x) = k (g x)) → (l.map f).flatMap k = (l.map g).flatMap k
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, List.map_cons, List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_map_congr k f g l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- ★ Nodes that agree exactly iterate identically (seq, keys, vals, printing see one order). -/
theorem agreeEq_iter : ∀ r (A B : Node α), wfNode r A = true → wfNode r B = true → Agree Eq r A B →
    iterNode r A = iterNode r B
  | 0, A, B, _, _, hag => by rw [iterNode.eq_1, iterNode.eq_1]; exact hag
  | r + 1, A, B, hwA, hwB, hag => by
    obtain ⟨hnm, hdm⟩ := agree_maps Eq r A B hwA hwB hag
    obtain ⟨hcsA, hvalsA, _⟩ := wf_facts r A hwA
    obtain ⟨hcsB, hvalsB, _⟩ := wf_facts r B hwB
    obtain ⟨h1A, _⟩ := wf_parts r A hwA
    have evA := map_getD_filter A.datamap A.values default 32 (Nat.le_refl _) hvalsA
    have ecA := map_getD_filter A.nodemap A.cs Node.dummy 32 (Nat.le_refl _) hcsA
    have evB := map_getD_filter B.datamap B.values default 32 (Nat.le_refl _) hvalsB
    have ecB := map_getD_filter B.nodemap B.cs Node.dummy 32 (Nat.le_refl _) hcsB
    rw [iterNode.eq_2, iterNode.eq_2]
    show A.values.take ((List.range 32).countP A.datamap.testBit) ++
        (A.cs.take ((List.range 32).countP A.nodemap.testBit)).flatMap (iterNode r) =
      B.values.take ((List.range 32).countP B.datamap.testBit) ++
        (B.cs.take ((List.range 32).countP B.nodemap.testBit)).flatMap (iterNode r)
    rw [← evA, ← ecA, ← evB, ← ecB, ← hnm, ← hdm]
    congr 1
    · apply List.map_congr_left
      intro d hd
      rw [List.mem_filter, List.mem_range] at hd
      have hn : A.nodemap.testBit d = false := by
        cases hh : A.nodemap.testBit d
        · rfl
        · exact absurd ⟨hh, hd.2⟩ (disjoint_bits _ _ h1A d)
      have hs := hag d hd.1
      have hsA : slot A d = .data (A.values.getD (pos A.datamap d) default) := by
        unfold slot; rw [hn, hd.2]; rfl
      have hsB : slot B d = .data (B.values.getD (pos A.datamap d) default) := by
        unfold slot; rw [← hnm, ← hdm, hn, hd.2]; rfl
      rw [hsA, hsB] at hs
      exact hs
    · apply flatMap_map_congr
      intro d hd
      rw [List.mem_filter, List.mem_range] at hd
      have hs := hag d hd.1
      have hsA : slot A d = .child (A.cs.getD (pos A.nodemap d) Node.dummy) := by
        unfold slot; rw [if_pos hd.2]
      have hsB : slot B d = .child (B.cs.getD (pos A.nodemap d) Node.dummy) := by
        unfold slot; rw [← hnm, if_pos hd.2]
      have hwa := slot_child_wf r A hwA d hd.1 _ hsA
      have hwb := slot_child_wf r B hwB d hd.1 _ hsB
      rw [hsA, hsB] at hs
      exact agreeEq_iter r _ _ hwa hwb hs

/-! ## The sequence theorem -/

/-- One step of a sequence, with the fix: `assoc`/`conj` is `addRootF`, `assoc!`/`conj!` is
`addMutRootF`; `dissoc`/`disj` and their transient forms are round 3's (the fix does not touch them). -/
def applyTF (cfg : Cfg α κ) (c : Champ α) : TOp α κ → M (Champ α)
  | .add v => addRootF cfg c v
  | .sub k => c.sub cfg k
  | .addMut e v => addMutRootF cfg e c v
  | .subMut e k => c.subMut cfg e k

def buildTF (cfg : Cfg α κ) (c : Champ α) : List (TOp α κ) → M (Champ α)
  | [] => pure c
  | op :: ops => do buildTF cfg (← applyTF cfg c op) ops

/-- ★ Every fixed step keeps `wfNode`, for every hash and every equality. -/
theorem stepF_wf (cfg : Cfg α κ) (c : Champ α) (s : Al) (hw : wfNode 13 c.root = true) (op : TOp α κ) :
    wfNode 13 ((applyTF cfg c op).run s).1.root = true := by
  cases op with
  | add v => exact wf_doAddF cfg v (cfg.hashT v) 13 (Nat.le_refl _) c.root s hw
  | addMut e v => exact wf_doAddMutF cfg e v (cfg.hashT v) 13 (Nat.le_refl _) c.root s hw
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

/-- ★ Every sequence of fixed steps keeps `wfNode`, for every hash and every equality. -/
theorem buildTF_wf (cfg : Cfg α κ) :
    ∀ (ops : List (TOp α κ)) (c : Champ α) (s : Al), wfNode 13 c.root = true →
      wfNode 13 ((buildTF cfg c ops).run s).1.root = true
  | [], _, _, hw => hw
  | op :: ops, c, s, hw => by
    have e : ((buildTF cfg c (op :: ops)).run s).1 =
        ((buildTF cfg ((applyTF cfg c op).run s).1 ops).run ((applyTF cfg c op).run s).2).1 := rfl
    rw [e]
    exact buildTF_wf cfg ops _ _ (stepF_wf cfg c s hw op)

theorem addF_root_congr (cfg : Cfg α κ) (A B : Champ α) (v : α) (s s' : Al) (hwA : wfNode 13 A.root = true)
    (hwB : wfNode 13 B.root = true) (hag : Agree Eq 13 A.root B.root) (hsz : A.size = B.size) :
    Agree Eq 13 ((addRootF cfg A v).run s).1.root ((addRootF cfg B v).run s').1.root ∧
      ((addRootF cfg A v).run s).1.size = ((addRootF cfg B v).run s').1.size := by
  obtain ⟨h1, h2⟩ := add_congrF cfg v (cfg.hashT v) 13 (Nat.le_refl _) A.root B.root s s' hwA hwB hag
  refine ⟨h1, ?_⟩
  show A.size + (if ((doAddF cfg 13 A.root v (cfg.hashT v)).run s).1.2 then 1 else 0) =
    B.size + (if ((doAddF cfg 13 B.root v (cfg.hashT v)).run s').1.2 then 1 else 0)
  rw [hsz, h2]

theorem subE_root_congr (cfg : Cfg α κ) (A B : Champ α) (k : κ) (s s' : Al) (hwA : wfNode 13 A.root = true)
    (hwB : wfNode 13 B.root = true) (hag : Agree Eq 13 A.root B.root) (hsz : A.size = B.size) :
    Agree Eq 13 ((A.sub cfg k).run s).1.root ((B.sub cfg k).run s').1.root ∧
      ((A.sub cfg k).run s).1.size = ((B.sub cfg k).run s').1.size := by
  have ag := sub_congrE cfg k (cfg.hashK k) 13 (Nat.le_refl _) A.root B.root s s' hwA hwB hag
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

/-- One transient step against the same step made persistent, from the same champ: exact. -/
theorem persistF_step (cfg : Cfg α κ) (c : Champ α) (op : TOp α κ) (s : Al) (hw : wfNode 13 c.root = true) :
    Agree Eq 13 ((applyTF cfg c op).run s).1.root ((applyTF cfg c op.persist).run s).1.root ∧
      ((applyTF cfg c op).run s).1.size = ((applyTF cfg c op.persist).run s).1.size := by
  cases op with
  | add v => exact ⟨agree_refl Eq (fun _ => rfl) 13 _, rfl⟩
  | sub k => exact ⟨agree_refl Eq (fun _ => rfl) 13 _, rfl⟩
  | addMut e v => exact addMutF_root_agree cfg c e v s hw
  | subMut e k => exact subMut_root_agree cfg c e k s hw

/-- The persistent fixed step on two exactly agreeing champs. -/
theorem congrF_step (cfg : Cfg α κ) (A B : Champ α) (op : TOp α κ) (s s' : Al) (hwA : wfNode 13 A.root = true)
    (hwB : wfNode 13 B.root = true) (hag : Agree Eq 13 A.root B.root) (hsz : A.size = B.size) :
    Agree Eq 13 ((applyTF cfg A op.persist).run s).1.root ((applyTF cfg B op.persist).run s').1.root ∧
      ((applyTF cfg A op.persist).run s).1.size = ((applyTF cfg B op.persist).run s').1.size := by
  cases op with
  | add v => exact addF_root_congr cfg A B v s s' hwA hwB hag hsz
  | addMut e v => exact addF_root_congr cfg A B v s s' hwA hwB hag hsz
  | sub k => exact subE_root_congr cfg A B k s s' hwA hwB hag hsz
  | subMut e k => exact subE_root_congr cfg A B k s s' hwA hwB hag hsz

theorem agreeEq_trans (r : Nat) (A B C : Node α) (h1 : Agree Eq r A B) (h2 : Agree Eq r B C) : Agree Eq r A C :=
  agree_trans Eq (fun a b c h1 h2 => h1.trans h2) r A B C h1 h2

/-- ★ **With the fix, a sequence of persistent and transient steps and the same sequence with every
transient step made persistent agree EXACTLY**: from two well-formed champs that agree exactly with
the same size, the results agree node by node with every collision list equal and have the same size,
for every sequence, every owner token, every hash function and EVERY equality. -/
theorem buildTF_agree (cfg : Cfg α κ) :
    ∀ (ops : List (TOp α κ)) (A B : Champ α) (s s' : Al), wfNode 13 A.root = true → wfNode 13 B.root = true →
      Agree Eq 13 A.root B.root → A.size = B.size →
      Agree Eq 13 ((buildTF cfg A ops).run s).1.root ((buildTF cfg B (ops.map TOp.persist)).run s').1.root ∧
        ((buildTF cfg A ops).run s).1.size = ((buildTF cfg B (ops.map TOp.persist)).run s').1.size
  | [], _, _, _, _, _, _, hag, hsz => ⟨hag, hsz⟩
  | op :: ops, A, B, s, s', hwA, hwB, hag, hsz => by
    have eA : ((buildTF cfg A (op :: ops)).run s).1 =
        ((buildTF cfg ((applyTF cfg A op).run s).1 ops).run ((applyTF cfg A op).run s).2).1 := rfl
    have eB : ((buildTF cfg B ((op :: ops).map TOp.persist)).run s').1 =
        ((buildTF cfg ((applyTF cfg B op.persist).run s').1 (ops.map TOp.persist)).run
          ((applyTF cfg B op.persist).run s').2).1 := rfl
    rw [eA, eB]
    have h1 := persistF_step cfg A op s hwA
    have h2 := congrF_step cfg A B op s s' hwA hwB hag hsz
    exact buildTF_agree cfg ops _ _ _ _ (stepF_wf cfg A s hwA op) (stepF_wf cfg B s' hwB op.persist)
      (agreeEq_trans 13 _ _ _ h1.1 h2.1) (h1.2.trans h2.2)

/-- ★ **From `champ::empty()`, with the fix**: a jank program's chain of `conj`/`assoc`/`disj`/`dissoc`
and `transient`/`conj!`/`assoc!`/`disj!`/`dissoc!`/`persistent!` and the same chain with no transient
give champs that agree node by node EXACTLY, with the same size and the same iteration order, for
every hash and every equality. -/
theorem buildTF_agree_empty (cfg : Cfg α κ) (ops : List (TOp α κ)) (s s' : Al) :
    Agree Eq 13 ((buildTF cfg Champ.empty ops).run s).1.root ((buildTF cfg Champ.empty (ops.map TOp.persist)).run s').1.root ∧
      ((buildTF cfg Champ.empty ops).run s).1.size = ((buildTF cfg Champ.empty (ops.map TOp.persist)).run s').1.size ∧
      ((buildTF cfg Champ.empty ops).run s).1.toList = ((buildTF cfg Champ.empty (ops.map TOp.persist)).run s').1.toList := by
  obtain ⟨h1, h2⟩ := buildTF_agree cfg ops Champ.empty Champ.empty s s' rfl rfl (agree_refl Eq (fun _ => rfl) 13 _) rfl
  exact ⟨h1, h2, agreeEq_iter 13 _ _ (buildTF_wf cfg ops _ s rfl) (buildTF_wf cfg _ _ s' rfl) h1⟩

end Jank.R9.Champ

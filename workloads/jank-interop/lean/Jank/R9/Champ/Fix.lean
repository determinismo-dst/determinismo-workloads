import Jank.R8.Champ.Seq

/-!
# Round 9, CHAMP: H8-1's fix on the replica (immer's `copy_collision_replace` keeps the position)

`fixes/H8-1-immer.diff` changes one immer function, node.hpp `copy_collision_replace` (495-523): the
new value is written where the replaced one was (`xs.set pos v`), not first (`v :: eraseAt xs pos`).
Every caller (champ.hpp `do_add` 575-581, `do_add_mut`'s copying branch 657-659, `do_update`,
`do_update_if_exists`, `do_update_mut`, `do_update_if_exists_mut`) then gives what its in-place
branch (`*fst = ...`) gives.

This file extends round 3's replica (`Jank.R3.Immer.Champ.doAdd`, `doAddMut`) with the fixed steps
`doAddF` and `doAddMutF`: the same code, with `copyCollisionReplaceF` for `copyCollisionReplace`
(and `doAddF` below a node the transient does not own). Round 3's functions are right for jank at
94d32623; these are jank with the fix.

- ★ `wf_doAddF`, ★ `wf_doAddMutF`: the fixed steps keep `wfNode` (every hash, every equality, every
  owner token).
- ★ `addMutF_agree`, ★ `addMutF_root_agree`: with the fix, `do_add_mut` (`assoc!`/`conj!`) and `do_add`
  (`assoc`/`conj`) from the same node agree node by node EXACTLY (every collision list equal) and
  give the same `added` flag, for every well-formed node, every hash, every equality, every owner.
  Round 8's `addMut_agree` had one collision list differing (`InPlace`); the fix closes it.
-/

namespace Jank.R9.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ Jank.R8.Champ

variable {α κ : Type} [Inhabited α]

/-! ## The fixed steps -/

/-- `copy_collision_replace(src, pos, v)` with H8-1-immer.diff: the old values in order, `v` at `pos`. -/
def copyCollisionReplaceF (src : Node α) (pos : Nat) (v : α) : M (Node α) :=
  mkCollision (src.collisions.set pos v)

/-- `champ::do_add` with the fix (round 3's `doAdd` otherwise). -/
def doAddF (cfg : Cfg α κ) : (rem : Nat) → Node α → α → Nat → M (Node α × Bool)
  | 0, node, v, _ => do
    match findIdx? node.collisions (fun x => cfg.eqTT x v) with
    | some pos => pure (← copyCollisionReplaceF node pos v, false)
    | none => pure (← copyCollisionInsert node v, true)
  | r + 1, node, v, hash => do
    let shift := maxShift - 5 * (r + 1)
    let bit := bitAt hash shift
    if node.nodemap &&& bit != 0 then
      let offset := node.childrenCountBit bit
      let (child, added) ← doAddF cfg r (node.child offset) v hash
      pure (← copyInnerReplace node offset child, added)
    else if node.datamap &&& bit != 0 then
      let offset := node.dataCountBit bit
      let val := node.values.getD offset default
      if cfg.eqTT val v then
        pure (← copyInnerReplaceValue node offset v, false)
      else
        let child ← makeMerged none r v hash val (cfg.hashT val)
        pure (← copyInnerReplaceMerged node bit offset child, true)
    else
      pure (← copyInnerInsertValue node bit v, true)

/-- `champ::do_add_mut` with the fix (round 3's `doAddMut` otherwise). -/
def doAddMutF (cfg : Cfg α κ) (e : Nat) : (rem : Nat) → Node α → α → Nat → M (Node α × Bool × Bool)
  | 0, node, v, _ => do
    match findIdx? node.collisions (fun x => cfg.eqTT x v) with
    | some pos =>
      if node.canMutate e then
        match node with
        | .collision id t xs => pure (.collision id t (setL xs pos v), false, true)
        | other => pure (other, false, true)
      else
        let r ← copyCollisionReplaceF node pos v
        pure (owned r e, false, false)
    | none =>
      let mutate := node.canMutate e
      let r ← if mutate then moveCollisionInsert node v else copyCollisionInsert node v
      pure (owned r e, true, mutate)
  | r + 1, node, v, hash => do
    let shift := maxShift - 5 * (r + 1)
    let bit := bitAt hash shift
    if node.nodemap &&& bit != 0 then
      let offset := node.childrenCountBit bit
      let child := node.child offset
      if node.canMutate e then
        let (rn, added, _) ← doAddMutF cfg e r child v hash
        match node with
        | .inner id t nm dm vs cs => pure (.inner id t nm dm vs (setL cs offset rn), added, true)
        | other => pure (other, added, true)
      else
        let (rn, added) ← doAddF cfg r child v hash
        let n ← copyInnerReplace node offset rn
        pure (owned n e, added, false)
    else if node.datamap &&& bit != 0 then
      let offset := node.dataCountBit bit
      let val := node.values.getD offset default
      if cfg.eqTT val v then
        if node.canMutate e then
          let n ← ensureMutableValues node e
          pure (writeValue n offset v, false, true)
        else
          let n ← copyInnerReplaceValue node offset v
          pure (ownedValues n e, false, false)
      else
        let mutate := node.canMutate e
        let hash2 := cfg.hashT val
        let child ← makeMerged (some e) r v hash val hash2
        let n ← if mutate then moveInnerReplaceMerged node bit offset child
                 else copyInnerReplaceMerged node bit offset child
        pure (ownedValuesSafe n e, true, mutate)
    else
      let mutate := node.canMutate e
      let n ← if mutate then moveInnerInsertValue node bit v else copyInnerInsertValue node bit v
      pure (ownedValues n e, true, mutate)

/-- `champ::add(v) const` with the fix. -/
def addRootF (cfg : Cfg α κ) (c : Champ α) (v : α) : M (Champ α) := do
  let (root, added) ← doAddF cfg 13 c.root v (cfg.hashT v)
  pure { root, size := c.size + (if added then 1 else 0) }

/-- `champ::add_mut(e, v)` with the fix. -/
def addMutRootF (cfg : Cfg α κ) (e : Nat) (c : Champ α) (v : α) : M (Champ α) := do
  let (root, added, _) ← doAddMutF cfg e 13 c.root v (cfg.hashT v)
  pure { root, size := c.size + (if added then 1 else 0) }

/-! ## Well-formedness -/

/-- ★ The fixed `do_add` keeps `wfNode`, for every hash and every equality. -/
theorem wf_doAddF (cfg : Cfg α κ) (v : α) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      wfNode r ((doAddF cfg r N v h).run s).1.1 = true := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      have hl : xs.length ≥ 2 := by simpa [wfNode, Node.collisions] using hw
      rw [doAddF.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        show decide ((v :: xs).length ≥ 2) = true
        simp; omega
      | some pos =>
        show decide ((xs.set pos v).length ≥ 2) = true
        simp; omega
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have eP : ((doAddF cfg (r + 1) N v h).run s).1 =
          (((copyInnerReplace N (pos N.nodemap D) ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAddF.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      rw [eP]
      exact (edit_replace r N _ D _ hw hD hA (ih (by omega) _ s hcw)).1
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
          exact (edit_replaceValue r N v D s hw hD hA0 hB).1
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
          rw [eP]
          have hw1 := wf_makeMerged none v val h (cfg.hashT val) r s
          generalize (makeMerged none r v h val (cfg.hashT val)).run s = q at hw1
          obtain ⟨m, s1⟩ := q
          exact (edit_replaceMerged r N m D s1 hw hD hA0 hB hw1).1
      · have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have eP : ((doAddF cfg (r + 1) N v h).run s).1 = (((copyInnerInsertValue N (2 ^ D) v).run s).1, true) := by
          rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']; rfl
        rw [eP]
        exact (edit_insertValue r N v D s hw hD hA0 hB0).1

/-- ★ The fixed `do_add_mut` keeps `wfNode`, for every hash, every equality, every owner token. -/
theorem wf_doAddMutF (cfg : Cfg α κ) (e : Nat) (v : α) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      wfNode r ((doAddMutF cfg e r N v h).run s).1.1 = true := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      have hl : xs.length ≥ 2 := by simpa [wfNode, Node.collisions] using hw
      rw [doAddMutF.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        dsimp only
        split
        · show decide ((v :: xs).length ≥ 2) = true
          simp; omega
        · show decide ((v :: xs).length ≥ 2) = true
          simp; omega
      | some pos =>
        dsimp only
        split
        · show decide ((setL xs pos v).length ≥ 2) = true
          simp [setL]; omega
        · show decide ((xs.set pos v).length ≥ 2) = true
          simp; omega
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      by_cases hm : N.canMutate e = true
      · have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
            (.inner N.id N.tok N.nodemap N.datamap N.vals (setL N.cs (pos N.nodemap D)
              ((doAddMutF cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1),
             ((doAddMutF cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2.1, true) := by
          rw [doAddMutF.eq_2]; dsimp only; rw [hbit, if_pos hA', if_pos hm]
          cases N with
          | inner => rfl
          | collision => simp [wfNode] at hw
        rw [e1]
        exact (edit_setChild r N _ D hw hD hA (ih (by omega) _ s hcw)).1
      · have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
            (owned ((doAddF cfg (r + 1) N v h).run s).1.1 e, ((doAddF cfg (r + 1) N v h).run s).1.2, false) := by
          rw [doAddMutF.eq_2, doAddF.eq_2]; dsimp only; rw [hbit, if_pos hA', if_neg hm, if_pos hA']; rfl
        rw [e1]
        dsimp only
        rw [wf_owned]
        exact wf_doAddF cfg v h (r + 1) hr N s hw
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · by_cases hm : N.canMutate e = true
          · have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
                (writeValue ((ensureMutableValues N e).run s).1 (pos N.datamap D) v, false, true) := by
              rw [doAddMutF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_pos hm]
              rfl
            rw [e1]
            exact (edit_ensureWrite r N v D e s hw hD hA0 hB).1
          · have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
                (ownedValues ((doAddF cfg (r + 1) N v h).run s).1.1 e, ((doAddF cfg (r + 1) N v h).run s).1.2, false) := by
              rw [doAddMutF.eq_2, doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB', if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_neg hm,
                if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]
              rfl
            rw [e1]
            dsimp only
            rw [wf_ownedValues]
            exact wf_doAddF cfg v h (r + 1) hr N s hw
        · generalize hval : N.values.getD (pos N.datamap D) default = val at hE
          have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
              (ownedValues ((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).2).1 e, true, N.canMutate e) := by
            rw [doAddMutF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            split <;> rfl
          rw [e1]
          dsimp only
          rw [wf_ownedValues]
          have hw1 := wf_makeMerged (some e) v val h (cfg.hashT val) r s
          generalize (makeMerged (some e) r v h val (cfg.hashT val)).run s = q at hw1
          obtain ⟨m, s1⟩ := q
          exact (edit_replaceMerged r N m D s1 hw hD hA0 hB hw1).1
      · have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
            (ownedValues ((copyInnerInsertValue N (2 ^ D) v).run s).1 e, true, N.canMutate e) := by
          rw [doAddMutF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']
          split <;> rfl
        rw [e1]
        dsimp only
        rw [wf_ownedValues]
        exact (edit_insertValue r N v D s hw hD hA0 hB0).1

/-! ## One transient step against the persistent step, exactly -/

/-- ★ **With the fix, `do_add_mut` (`assoc!`/`conj!`) and `do_add` (`assoc`/`conj`) from the same node
agree EXACTLY**: trees equal slot by slot with every collision list equal, and the same `added` flag.
For every well-formed node, every hash, every equality, every owner token. -/
theorem addMutF_agree (cfg : Cfg α κ) (e : Nat) (v : α) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      Agree Eq r ((doAddMutF cfg e r N v h).run s).1.1 ((doAddF cfg r N v h).run s).1.1 ∧
        ((doAddMutF cfg e r N v h).run s).1.2.1 = ((doAddF cfg r N v h).run s).1.2 := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      rw [doAddMutF.eq_1, doAddF.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        dsimp only
        split
        · show (v :: xs) = (v :: xs) ∧ true = true
          exact ⟨rfl, rfl⟩
        · show (v :: xs) = (v :: xs) ∧ true = true
          exact ⟨rfl, rfl⟩
      | some pos =>
        dsimp only
        split
        · show setL xs pos v = xs.set pos v ∧ false = false
          exact ⟨rfl, rfl⟩
        · show xs.set pos v = xs.set pos v ∧ false = false
          exact ⟨rfl, rfl⟩
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have eP : ((doAddF cfg (r + 1) N v h).run s).1 =
          (((copyInnerReplace N (pos N.nodemap D) ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAddF cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAddF.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      by_cases hm : N.canMutate e = true
      · have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
            (.inner N.id N.tok N.nodemap N.datamap N.vals (setL N.cs (pos N.nodemap D)
              ((doAddMutF cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1),
             ((doAddMutF cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2.1, true) := by
          rw [doAddMutF.eq_2]; dsimp only; rw [hbit, if_pos hA', if_pos hm]
          cases N with
          | inner => rfl
          | collision => simp [wfNode] at hw
        rw [e1, eP]
        dsimp only
        have wM := wf_doAddMutF cfg e v h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        have wP := wf_doAddF cfg v h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        have ihc := ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        exact ⟨agree_edits Eq (fun _ => rfl) r N _ _ D _ _ (edit_setChild r N _ D hw hD hA wM)
          (edit_replace r N _ D _ hw hD hA wP) ihc.1, ihc.2⟩
      · have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
            (owned ((doAddF cfg (r + 1) N v h).run s).1.1 e, ((doAddF cfg (r + 1) N v h).run s).1.2, false) := by
          rw [doAddMutF.eq_2, doAddF.eq_2]; dsimp only; rw [hbit, if_pos hA', if_neg hm, if_pos hA']; rfl
        rw [e1]
        dsimp only
        exact ⟨(agree_owned_left Eq _ _ e (r + 1)).mpr (agree_refl Eq (fun _ => rfl) _ _), rfl⟩
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · have eP : ((doAddF cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceValue N (pos N.datamap D) v).run s).1, false) := by
            rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]; rfl
          by_cases hm : N.canMutate e = true
          · have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
                (writeValue ((ensureMutableValues N e).run s).1 (pos N.datamap D) v, false, true) := by
              rw [doAddMutF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_pos hm]
              rfl
            rw [e1, eP]
            dsimp only
            exact ⟨agree_edits Eq (fun _ => rfl) r N _ _ D _ _ (edit_ensureWrite r N v D e s hw hD hA0 hB)
              (edit_replaceValue r N v D s hw hD hA0 hB) rfl, rfl⟩
          · have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
                (ownedValues ((doAddF cfg (r + 1) N v h).run s).1.1 e, ((doAddF cfg (r + 1) N v h).run s).1.2, false) := by
              rw [doAddMutF.eq_2, doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB', if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_neg hm,
                if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]
              rfl
            rw [e1]
            dsimp only
            exact ⟨(agree_ownedValues_left Eq _ _ e (r + 1)).mpr (agree_refl Eq (fun _ => rfl) _ _), rfl⟩
        · generalize hval : N.values.getD (pos N.datamap D) default = val at hE
          have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
              (ownedValues ((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).2).1 e, true, N.canMutate e) := by
            rw [doAddMutF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            split <;> rfl
          have eP : ((doAddF cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged none r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged none r v h val (cfg.hashT val)).run s).2).1, true) := by
            rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            rfl
          rw [e1, eP]
          dsimp only
          rw [agree_ownedValues_left]
          have hag := agree_makeMerged Eq (fun _ => rfl) (some e) none v val h (cfg.hashT val) r s s
          have hw1 := wf_makeMerged (some e) v val h (cfg.hashT val) r s
          have hw2 := wf_makeMerged none v val h (cfg.hashT val) r s
          generalize (makeMerged (some e) r v h val (cfg.hashT val)).run s = q1 at hag hw1
          generalize (makeMerged none r v h val (cfg.hashT val)).run s = q2 at hag hw2
          obtain ⟨m1, s1⟩ := q1
          obtain ⟨m2, s2⟩ := q2
          dsimp only at hag hw1 hw2 ⊢
          exact ⟨agree_edits Eq (fun _ => rfl) r N _ _ D _ _ (edit_replaceMerged r N m1 D s1 hw hD hA0 hB hw1)
            (edit_replaceMerged r N m2 D s2 hw hD hA0 hB hw2) hag, rfl⟩
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have e1 : ((doAddMutF cfg e (r + 1) N v h).run s).1 =
            (ownedValues ((copyInnerInsertValue N (2 ^ D) v).run s).1 e, true, N.canMutate e) := by
          rw [doAddMutF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']
          split <;> rfl
        have eP : ((doAddF cfg (r + 1) N v h).run s).1 = (((copyInnerInsertValue N (2 ^ D) v).run s).1, true) := by
          rw [doAddF.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']; rfl
        rw [e1, eP]
        dsimp only
        exact ⟨(agree_ownedValues_left Eq _ _ e (r + 1)).mpr (agree_refl Eq (fun _ => rfl) _ _), rfl⟩

/-- ★ At the root: with the fix, `add_mut` and `add` from the same champ agree node by node exactly,
with the same size. -/
theorem addMutF_root_agree (cfg : Cfg α κ) (c : Champ α) (e : Nat) (v : α) (s : Al) (hw : wfNode 13 c.root = true) :
    Agree Eq 13 ((addMutRootF cfg e c v).run s).1.root ((addRootF cfg c v).run s).1.root ∧
      ((addMutRootF cfg e c v).run s).1.size = ((addRootF cfg c v).run s).1.size := by
  obtain ⟨h1, h2⟩ := addMutF_agree cfg e v (cfg.hashT v) 13 (Nat.le_refl _) c.root s hw
  refine ⟨h1, ?_⟩
  show c.size + (if ((doAddMutF cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1 then 1 else 0) =
    c.size + (if ((doAddF cfg 13 c.root v (cfg.hashT v)).run s).1.2 then 1 else 0)
  rw [h2]

end Jank.R9.Champ

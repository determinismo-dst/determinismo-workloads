import Jank.R4.Immer.TransientGet

/-!
# `nth` after `pop!`: `take_mut` and `slice_right_mut_visitor` (round 4)

jank's `pop!` is `data.take(data.size() - 1)` on the transient (transient_vector.cpp
`pop_in_place`), immer's `vector_transient::take` → `rbtree::take_mut` →
`slice_right_mut_visitor<Collapse, Mutating>`. This file mirrors round 3's `get_take` proof
(slice_right_visitor) for the mutating visitor: a node owned by the transient is cut in place
(`destroy_n` on a leaf, `inner()[idx] = next` or the node itself on an inner node), others are
copied (`copy_leaf_e`, `copy_inner_e`). Reads below the new size are unchanged either way.
-/

namespace Jank.R3.Immer.Rbts

variable {α : Type}

/-! ## The leaf -/

theorem sliceMutLeaf_none [Inhabited α] (p : LPos) (m : Bool) (e : Nat) (node : Node α) (last n : Nat) :
    (sliceMutLeaf p m e node last n).1.2.1 = none := by
  unfold sliceMutLeaf; dsimp only
  repeat' split
  all_goals rfl

theorem sliceMutLeaf_tail [Inhabited α] (p : LPos) (m : Bool) (e : Nat) (node : Node α) (last n j : Nat)
    (hleaf : node.isLeaf = true) (hl : lIndex last + 1 ≤ node.xs.length) (hj : lIndex j ≤ lIndex last) :
    (sliceMutLeaf p m e node last n).1.2.2.2.isLeaf = true ∧
    (sliceMutLeaf p m e node last n).1.2.2.2.xs[lIndex j]? = node.xs[lIndex j]? := by
  unfold sliceMutLeaf; dsimp only
  split
  · exact ⟨hleaf, rfl⟩
  · split
    · refine ⟨rfl, ?_⟩
      simp only [Node.xs]
      rw [List.getElem?_take, if_pos (by omega)]
    · refine ⟨rfl, ?_⟩
      simp only [Node.xs]
      exact leafCopy_getElem? node _ _ (by omega) (by omega)

/-! ## Equations of `slice_right_mut_visitor::visit_regular` at level 0 and above -/

theorem sliceMutInner_zero [Inhabited α] (c m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat) :
    sliceMutInner 0 c m e p node last n =
      if c && iIndex 5 last == 0 then
        sliceMutLeaf (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e (node.child (iIndex 5 last)) last n
      else
        match sliceMutLeaf (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e
            (node.child (iIndex 5 last)) last n with
        | ((_, next, ts, tail), n) =>
          match next with
          | some nx =>
            if m && node.canMutate e then ((5, some (node.writeChild (iIndex 5 last) nx), ts, tail), n)
            else ((5, some (.inner n e (setAt Node.dummy (childCopy node (iIndex 5 last)) (iIndex 5 last) nx)),
              ts, tail), n + 1)
          | none =>
            if iIndex 5 last == 0 then ((5, none, ts, tail), n)
            else if c && iIndex 5 last == 1 && 5 > 5 then ((5 - 5, some (node.child 0), ts, tail), n)
            else if m && node.canMutate e then ((5, some node, ts, tail), n)
            else ((5, some (.inner n e (childCopy node (iIndex 5 last))), ts, tail), n + 1) := rfl

theorem sliceMutInner_succ [Inhabited α] (k : Nat) (c m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat) :
    sliceMutInner (k + 1) c m e p node last n =
      if c && iIndex (5 * (k + 2)) last == 0 then
        sliceMutInner k c (m && node.canMutate e) e (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last))
          (node.child (iIndex (5 * (k + 2)) last)) last n
      else
        match sliceMutInner k false (m && node.canMutate e) e (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last))
            (node.child (iIndex (5 * (k + 2)) last)) last n with
        | ((_, next, ts, tail), n) =>
          match next with
          | some nx =>
            if m && node.canMutate e then
              ((5 * (k + 2), some (node.writeChild (iIndex (5 * (k + 2)) last) nx), ts, tail), n)
            else ((5 * (k + 2), some (.inner n e (setAt Node.dummy (childCopy node (iIndex (5 * (k + 2)) last))
              (iIndex (5 * (k + 2)) last) nx)), ts, tail), n + 1)
          | none =>
            if iIndex (5 * (k + 2)) last == 0 then ((5 * (k + 2), none, ts, tail), n)
            else if c && iIndex (5 * (k + 2)) last == 1 && 5 * (k + 2) > 5 then
              ((5 * (k + 2) - 5, some (node.child 0), ts, tail), n)
            else if m && node.canMutate e then ((5 * (k + 2), some node, ts, tail), n)
            else ((5 * (k + 2), some (.inner n e (childCopy node (iIndex (5 * (k + 2)) last))), ts, tail), n + 1) := rfl

/-! ## The tail a slice ends with -/

theorem sliceMutInner_tail_zero [Inhabited α] (c m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat) :
    (sliceMutInner 0 c m e p node last n).1.2.2.2 =
      (sliceMutLeaf (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e (node.child (iIndex 5 last)) last n).1.2.2.2 := by
  rw [sliceMutInner_zero]
  generalize (m && node.canMutate e) = mt
  repeat' split
  all_goals simp_all

theorem sliceMutInner_tail_succ [Inhabited α] (k : Nat) (c m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat) :
    (sliceMutInner (k + 1) c m e p node last n).1.2.2.2 =
      (sliceMutInner k (c && iIndex (5 * (k + 2)) last == 0) (m && node.canMutate e) e
        (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last)) (node.child (iIndex (5 * (k + 2)) last)) last n).1.2.2.2 := by
  rw [sliceMutInner_succ]
  split
  · rename_i h
    rw [h]
    have hc : c = true := by revert h; cases c <;> simp
    subst hc; rfl
  · rename_i h
    have hf : (c && iIndex (5 * (k + 2)) last == 0) = false := by simpa using h
    rw [hf]
    generalize (m && node.canMutate e) = mt
    repeat' split
    all_goals simp_all

/-- **The tail after a mutating slice**: the leaf holding `last`, its slots up to `last` unchanged. -/
theorem sliceMutInner_tail_read [Inhabited α] : ∀ (k : Nat) (c m : Bool) (e : Nat) (p : IPos) (node : Node α)
    (last n j : Nat),
    wfP k p node → validI k p last → j >>> 5 = last >>> 5 → lIndex j ≤ lIndex last →
    (sliceMutInner k c m e p node last n).1.2.2.2.isLeaf = true ∧
    (sliceMutInner k c m e p node last n).1.2.2.2.xs[lIndex j]? = readAt k node j := by
  intro k
  induction k with
  | zero =>
    intro c m e p node last n j hw hv hjb hjl
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨lid, ltok, lxs, hcs, hlen⟩ := hch _ hv1
    rw [sliceMutInner_tail_zero, child_of_getElem? _ _ _ hcs]
    have hd : iIndex 5 j = iIndex 5 last := by
      simp only [iIndex_eq]; rw [hjb]
    obtain ⟨h1, h2⟩ := sliceMutLeaf_tail (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e
      (.leaf lid ltok lxs) last n j rfl (by simp [Node.xs]; omega) hjl
    refine ⟨h1, ?_⟩
    rw [h2, readAt_zero_cs, hd, hcs]
    simp [leafOpt, Node.xs]
  | succ k ih =>
    intro c m e p node last n j hw hv hjb hjl
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
    rw [sliceMutInner_tail_succ, child_of_getElem? _ _ _ hcs]
    have hd : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) last := by
      have e : 5 * (k + 2) = 5 + (5 * (k + 2) - 5) := by omega
      simp only [iIndex_eq]; rw [e, Nat.shiftRight_add, Nat.shiftRight_add, hjb]
    obtain ⟨h1, h2⟩ := ih (c && iIndex (5 * (k + 2)) last == 0) (m && node.canMutate e) e _ ch last n j hwc hv2 hjb hjl
    refine ⟨h1, ?_⟩
    rw [h2, readAt_succ_cs, hd, hcs]
    rfl

/-! ## The root a slice keeps -/

/-- **Mutating slice without collapse**: no root iff `last` sits in the first leaf of its block;
else a root at the same shift reading as the node below `last`'s leaf. -/
theorem sliceMutInner_root_nc [Inhabited α] : ∀ (k : Nat) (m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat),
    wfP k p node → validI k p last →
    ((sliceMutInner k false m e p node last n).1.2.1 = none → last % 2 ^ (5 * (k + 2)) < 32) ∧
    (∀ x, (sliceMutInner k false m e p node last n).1.2.1 = some x →
      (sliceMutInner k false m e p node last n).1.1 = 5 * (k + 1) ∧
      ∀ j, j >>> (5 * (k + 2)) = last >>> (5 * (k + 2)) → j < last - lIndex last →
        readAt k x j = readAt k node j) := by
  intro k
  induction k with
  | zero =>
    intro m e p node last n hw hv
    rw [sliceMutInner_zero]
    rw [if_neg (by simp)]
    have hnone := sliceMutLeaf_none (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e
      (node.child (iIndex 5 last)) last n
    rcases hR : sliceMutLeaf (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e
      (node.child (iIndex 5 last)) last n with ⟨⟨a, b, c, d⟩, e'⟩
    rw [hR] at hnone
    simp only at hnone
    subst hnone
    dsimp only
    by_cases h0 : iIndex 5 last = 0
    · rw [if_pos (by simp [h0])]
      refine ⟨fun _ => ?_, fun x hx => by simp at hx⟩
      simp only [iIndex_eq, shr_eq] at h0; simp at h0 ⊢; omega
    · rw [if_neg (by simp [h0]), if_neg (by simp)]
      have hd' : ∀ j, j >>> 10 = last >>> 10 → j < last - lIndex last → iIndex 5 j < iIndex 5 last :=
        fun j hjb hj => digit5_lt j last hjb hj
      split
      · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
        simp only [Option.some.injEq] at hx
        subst hx
        exact ⟨rfl, fun j _ _ => rfl⟩
      · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
        simp only [Option.some.injEq] at hx
        subst hx
        refine ⟨rfl, fun j hjb hj => ?_⟩
        have hd := hd' j (by simpa using hjb) hj
        rw [readAt_zero_cs, readAt_zero_cs, cs_inner]
        unfold childCopy
        exact copyN_bind _ _ _ _ _ (by simp [leafOpt, Node.dummy]) hd
  | succ k ih =>
    intro m e p node last n hw hv
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
    have IH := ih (m && node.canMutate e) e _ ch last n hwc hv2
    rw [sliceMutInner_succ]
    rw [if_neg (by simp)]
    rw [child_of_getElem? _ _ _ hcs]
    rcases hR : sliceMutInner k false (m && node.canMutate e) e
      (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last)) ch last n with ⟨⟨a, b, c, d⟩, e'⟩
    rw [hR] at IH
    simp only at IH
    obtain ⟨IHn, IHs⟩ := IH
    have e3 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e3]
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    cases b with
    | some nx =>
      dsimp only
      obtain ⟨_, IHr⟩ := IHs nx rfl
      -- in place (`inner()[idx] = next`) or a copy (`copy_inner_e`): the same reads up to idx
      have key : ∀ (ys : List (Node α)), (ys = node.cs ∨ ys = childCopy node (iIndex (5 * (k + 2)) last)) →
          ∀ j, j >>> (5 * (k + 2) + 5) = last >>> (5 * (k + 2) + 5) → j < last - lIndex last →
          ((setAt Node.dummy ys (iIndex (5 * (k + 2)) last) nx)[iIndex (5 * (k + 2)) j]?).bind
            (fun c => readAt k c j) = readAt (k + 1) node j := by
        intro ys hys j hjb hj
        have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
        rw [setAt_bind _ _ _ _ _ _ (by simp [readAt_dummy]), readAt_succ_cs]
        by_cases hlt : iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) last
        · rw [if_neg (by omega)]
          exact ys_bind node _ _ ys hys hlt _ (by simp [readAt_dummy])
        · have heq : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) last := by omega
          rw [if_pos heq, heq, hcs]
          exact IHr j (shr_eq_of_digit _ heq hjb) hj
      split
      · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
        simp only [Option.some.injEq] at hx
        subst hx
        refine ⟨rfl, fun j hjb hj => ?_⟩
        rw [readAt_succ_cs]
        exact key node.cs (Or.inl rfl) j hjb hj
      · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
        simp only [Option.some.injEq] at hx
        subst hx
        refine ⟨rfl, fun j hjb hj => ?_⟩
        rw [readAt_succ_cs, cs_inner]
        exact key _ (Or.inr rfl) j hjb hj
    | none =>
      dsimp only
      have hfirst := IHn rfl
      by_cases h0 : iIndex (5 * (k + 2)) last = 0
      · rw [if_pos (by simp [h0])]
        refine ⟨fun _ => ?_, fun x hx => by simp at hx⟩
        rw [iIndex_eq, shr_eq, ← Nat.mod_mul_right_div_self last (2 ^ (5 * (k + 2))) 32] at h0
        have hp : 2 ^ (5 * (k + 2)) * 32 = 2 ^ (5 * (k + 2) + 5) := by rw [Nat.pow_add]
        rw [hp] at h0
        have hP := pow_ge32 (5 * (k + 2)) hsh
        have := Nat.div_add_mod (last % 2 ^ (5 * (k + 2) + 5)) (2 ^ (5 * (k + 2)))
        rw [h0, Nat.mul_zero, Nat.zero_add] at this
        have hmm : last % 2 ^ (5 * (k + 2) + 5) % 2 ^ (5 * (k + 2)) = last % 2 ^ (5 * (k + 2)) :=
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
        omega
      · rw [if_neg (by simp [h0]), if_neg (by simp)]
        have hbelow : ∀ j, j >>> (5 * (k + 2) + 5) = last >>> (5 * (k + 2) + 5) → j < last - lIndex last →
            iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) last := by
          intro j hjb hj
          have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
          rcases Nat.lt_or_eq_of_le hdle with h | h
          · exact h
          · exfalso
            have hjs := shr_eq_of_digit _ h hjb
            have hjd : j / 2 ^ (5 * (k + 2)) = last / 2 ^ (5 * (k + 2)) := by rw [← shr_eq, ← shr_eq]; exact hjs
            have h1 := Nat.div_add_mod j (2 ^ (5 * (k + 2)))
            have h2 := Nat.div_add_mod last (2 ^ (5 * (k + 2)))
            rw [hjd] at h1
            rw [lIndex_eq] at hj
            have hm : last % 2 ^ (5 * (k + 2)) % 32 = last % 32 :=
              Nat.mod_mod_of_dvd _ (by have : 2 ^ 5 ∣ 2 ^ (5 * (k + 2)) := Nat.pow_dvd_pow 2 (by omega); simpa using this)
            rw [Nat.mod_eq_of_lt hfirst] at hm
            omega
        split
        · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
          simp only [Option.some.injEq] at hx
          subst hx
          exact ⟨rfl, fun j _ _ => rfl⟩
        · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
          simp only [Option.some.injEq] at hx
          subst hx
          refine ⟨rfl, fun j hjb hj => ?_⟩
          rw [readAt_succ_cs, readAt_succ_cs, cs_inner]
          unfold childCopy
          exact copyN_bind _ _ _ _ _ (readAt_dummy _ _) (hbelow j hjb hj)

/-- **Mutating slice with collapse** (what `take_mut` runs): no root iff `last` sits in the first
leaf; else a root at a shift no higher, reading as the node below `last`'s leaf. -/
theorem sliceMutInner_root_c [Inhabited α] : ∀ (k : Nat) (m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat),
    wfP k p node → validI k p last →
    ((sliceMutInner k true m e p node last n).1.2.1 = none → last % 2 ^ (5 * (k + 2)) < 32) ∧
    (∀ x, (sliceMutInner k true m e p node last n).1.2.1 = some x →
      (sliceMutInner k true m e p node last n).1.1 % 5 = 0 ∧ 5 ≤ (sliceMutInner k true m e p node last n).1.1 ∧
      (sliceMutInner k true m e p node last n).1.1 ≤ 5 * (k + 1) ∧
      ∀ j, j >>> (5 * (k + 2)) = last >>> (5 * (k + 2)) → j < last - lIndex last →
        readAt (levelOf (sliceMutInner k true m e p node last n).1.1) x j = readAt k node j) := by
  intro k
  induction k with
  | zero =>
    intro m e p node last n hw hv
    rw [sliceMutInner_zero]
    by_cases h0 : iIndex 5 last = 0
    · rw [if_pos (by simp [h0]), sliceMutLeaf_none]
      refine ⟨fun _ => ?_, fun x hx => by simp at hx⟩
      simp only [iIndex_eq, shr_eq] at h0; simp at h0 ⊢; omega
    · rw [if_neg (by simp [h0])]
      have hnone := sliceMutLeaf_none (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e
        (node.child (iIndex 5 last)) last n
      rcases hR : sliceMutLeaf (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e
        (node.child (iIndex 5 last)) last n with ⟨⟨a, b, c, d⟩, e'⟩
      rw [hR] at hnone
      simp only at hnone
      subst hnone
      dsimp only
      rw [if_neg (by simp [h0]), if_neg (by simp)]
      split
      · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
        simp only [Option.some.injEq] at hx
        subst hx
        dsimp only
        refine ⟨by simp, Nat.le_refl _, Nat.le_refl _, fun j _ _ => ?_⟩
        rw [show levelOf 5 = 0 from rfl]
      · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
        simp only [Option.some.injEq] at hx
        subst hx
        dsimp only
        refine ⟨by simp, Nat.le_refl _, Nat.le_refl _, fun j hjb hj => ?_⟩
        have hd := digit5_lt j last (by simpa using hjb) hj
        rw [show levelOf 5 = 0 from rfl]
        rw [readAt_zero_cs, readAt_zero_cs, cs_inner]
        unfold childCopy
        exact copyN_bind _ _ _ _ _ (by simp [leafOpt, Node.dummy]) hd
  | succ k ih =>
    intro m e p node last n hw hv
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
    rw [sliceMutInner_succ]
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    have e3 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e3]
    rw [child_of_getElem? _ _ _ hcs]
    by_cases h0 : iIndex (5 * (k + 2)) last = 0
    · rw [if_pos (by simp [h0])]
      rw [h0] at hcs hwc hv2 ⊢
      obtain ⟨IHn, IHs⟩ := ih (m && node.canMutate e) e _ ch last n hwc hv2
      refine ⟨fun h => low_of_digit0 _ last hsh h0 (IHn h), fun x hx => ?_⟩
      obtain ⟨a1, a2, a3, IHr⟩ := IHs x hx
      refine ⟨a1, a2, by omega, fun j hjb hj => ?_⟩
      have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
      have hd0 : iIndex (5 * (k + 2)) j = 0 := by omega
      rw [IHr j (shr_eq_of_digit _ (by rw [hd0, h0]) hjb) hj, readAt_succ_cs, hd0, hcs]
      rfl
    · rw [if_neg (by simp [h0])]
      have IH := sliceMutInner_root_nc k (m && node.canMutate e) e _ ch last n hwc hv2
      rcases hR : sliceMutInner k false (m && node.canMutate e) e
        (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last)) ch last n with ⟨⟨a, b, c, d⟩, e'⟩
      rw [hR] at IH
      simp only at IH
      obtain ⟨IHn, IHs⟩ := IH
      have hlv : levelOf (5 * (k + 2)) = k + 1 := by unfold levelOf; omega
      cases b with
      | some nx =>
        dsimp only
        obtain ⟨_, IHr⟩ := IHs nx rfl
        have key : ∀ (ys : List (Node α)), (ys = node.cs ∨ ys = childCopy node (iIndex (5 * (k + 2)) last)) →
            ∀ j, j >>> (5 * (k + 2) + 5) = last >>> (5 * (k + 2) + 5) → j < last - lIndex last →
            ((setAt Node.dummy ys (iIndex (5 * (k + 2)) last) nx)[iIndex (5 * (k + 2)) j]?).bind
              (fun c => readAt k c j) = readAt (k + 1) node j := by
          intro ys hys j hjb hj
          have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
          rw [setAt_bind _ _ _ _ _ _ (by simp [readAt_dummy]), readAt_succ_cs]
          by_cases hlt : iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) last
          · rw [if_neg (by omega)]
            exact ys_bind node _ _ ys hys hlt _ (by simp [readAt_dummy])
          · have heq : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) last := by omega
            rw [if_pos heq, heq, hcs]
            exact IHr j (shr_eq_of_digit _ heq hjb) hj
        split
        · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
          simp only [Option.some.injEq] at hx
          subst hx
          dsimp only
          refine ⟨by omega, by omega, Nat.le_refl _, fun j hjb hj => ?_⟩
          rw [hlv, readAt_succ_cs]
          exact key node.cs (Or.inl rfl) j hjb hj
        · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
          simp only [Option.some.injEq] at hx
          subst hx
          dsimp only
          refine ⟨by omega, by omega, Nat.le_refl _, fun j hjb hj => ?_⟩
          rw [hlv, readAt_succ_cs, cs_inner]
          exact key _ (Or.inr rfl) j hjb hj
      | none =>
        dsimp only
        have hfirst := IHn rfl
        rw [if_neg (by simp [h0])]
        have hbelow : ∀ j, j >>> (5 * (k + 2) + 5) = last >>> (5 * (k + 2) + 5) → j < last - lIndex last →
            iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) last := by
          intro j hjb hj
          have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
          rcases Nat.lt_or_eq_of_le hdle with h | h
          · exact h
          · exfalso
            have hjs := shr_eq_of_digit _ h hjb
            have hjd : j / 2 ^ (5 * (k + 2)) = last / 2 ^ (5 * (k + 2)) := by rw [← shr_eq, ← shr_eq]; exact hjs
            have h1 := Nat.div_add_mod j (2 ^ (5 * (k + 2)))
            have h2 := Nat.div_add_mod last (2 ^ (5 * (k + 2)))
            rw [hjd] at h1
            rw [lIndex_eq] at hj
            have hm : last % 2 ^ (5 * (k + 2)) % 32 = last % 32 :=
              Nat.mod_mod_of_dvd _ (by have : 2 ^ 5 ∣ 2 ^ (5 * (k + 2)) := Nat.pow_dvd_pow 2 (by omega); simpa using this)
            rw [Nat.mod_eq_of_lt hfirst] at hm
            omega
        by_cases h1 : iIndex (5 * (k + 2)) last = 1
        · rw [if_pos (by simp [h1] <;> omega)]
          refine ⟨fun h => by simp at h, fun x hx => ?_⟩
          simp only [Option.some.injEq] at hx
          subst hx
          dsimp only
          have hlv' : levelOf (5 * (k + 2) - 5) = k := by unfold levelOf; omega
          refine ⟨by omega, by omega, by omega, fun j hjb hj => ?_⟩
          rw [hlv']
          have hd0 : iIndex (5 * (k + 2)) j = 0 := by have := hbelow j hjb hj; omega
          rw [readAt_succ_cs, hd0, child_read]
        · rw [if_neg (by simp [h1])]
          split
          · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
            simp only [Option.some.injEq] at hx
            subst hx
            dsimp only
            refine ⟨by omega, by omega, by omega, fun j _ _ => ?_⟩
            rw [hlv]
          · refine ⟨fun h => by simp at h, fun x hx => ?_⟩
            simp only [Option.some.injEq] at hx
            subst hx
            dsimp only
            refine ⟨by omega, by omega, by omega, fun j hjb hj => ?_⟩
            rw [hlv, readAt_succ_cs, readAt_succ_cs, cs_inner]
            unfold childCopy
            exact copyN_bind _ _ _ _ _ (readAt_dummy _ _) (hbelow j hjb hj)

/-! ## `take_mut` -/

/-- **`nth` after `take_mut`** (so after `pop!`): for every well-formed tree and every owner token,
the first `k` elements are unchanged. -/
theorem get_takeMut [Inhabited α] (t : Tree α) (hw : t.wfT) (e k n j : Nat) (hk : k ≤ t.size) (hj : j < k) :
    (t.takeMut e k n).1.get j = t.get j := by
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  have hpos : 0 < t.size := by omega
  have hf := tail_facts t.size hpos
  by_cases hks : k = t.size
  · subst hks; unfold Tree.takeMut; simp [show t.size ≠ 0 by omega]
  have hk' : k < t.size := by omega
  by_cases htk : tailOffset t.size < k
  · -- the tail is cut: in place (`destroy_n`) or copied (`copy_leaf_e`)
    have hto : tailOffset k = tailOffset t.size := by
      rw [tailOffset_eq, tailOffset_eq, if_neg (by omega), if_neg (by omega)]
      rw [tailOffset_eq, if_neg (by omega)] at htk hf; omega
    cases ht : t.tail with
    | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
    | leaf a b xs =>
    rw [ht] at htlen
    simp only [Node.xs] at htlen
    have hA : ∃ (a' b' : Nat) (ys : List α), (t.takeMut e k n).1 = { t with size := k, tail := .leaf a' b' ys } ∧
        ∀ c, c < k - tailOffset t.size → ys[c]? = xs[c]? := by
      unfold Tree.takeMut
      simp only [show (k == 0) = false by simp; omega, show ¬ k ≥ t.size by omega, htk, Bool.false_eq_true,
        ite_false, ite_true]
      split
      · refine ⟨a, b, xs.take (k - tailOffset t.size), by simp [ht, Node.id, Node.tok, Node.xs], fun c hc => ?_⟩
        rw [List.getElem?_take, if_pos hc]
      · refine ⟨n, e, leafCopy (Node.leaf a b xs) (k - tailOffset t.size), by rw [ht], fun c hc => ?_⟩
        exact leafCopy_getElem? _ _ _ hc (by simp [Node.xs]; omega)
    obtain ⟨a', b', ys, hR, hys⟩ := hA
    rw [hR]
    by_cases hjt : tailOffset t.size ≤ j
    · rw [get_tail_leaf ({ t with size := k, tail := .leaf a' b' ys } : Tree α) j a' b' ys rfl
          (by show tailOffset k ≤ j; rw [hto]; exact hjt),
        get_tail_leaf t j a b xs ht hjt, lIndex_tail t.size j hjt (by omega)]
      exact hys _ (by omega)
    · have hjt' : j < tailOffset t.size := by omega
      have e1 := get_of_root ({ t with size := k, tail := .leaf a' b' ys } : Tree α) j
        (by show j < tailOffset k; rw [hto]; exact hjt') hs2
      rw [e1, get_of_root t j hjt' hs2]
  · -- `slice_right_mut_visitor` on the root
    have hkt : k ≤ tailOffset t.size := by omega
    obtain ⟨hcap, hwr⟩ := hroot (by omega)
    have hL := levelOf_eq t.shift hs5 hs1
    have hcap' : tailOffset t.size ≤ 2 ^ (5 * (levelOf t.shift + 2)) := by rw [← hL]; exact hcap
    have hvl := validI_sub _ _ (k - 1) (by omega) hcap'
    have hTO := tailOffset_take k (by omega)
    have RC := sliceMutInner_root_c (levelOf t.shift) true e (.sub (tailOffset t.size)) t.root (k - 1) n hwr hvl
    have TR := fun j hjb hjl =>
      sliceMutInner_tail_read (levelOf t.shift) true true e (.sub (tailOffset t.size)) t.root (k - 1) n j hwr hvl hjb hjl
    have hblk : ∀ i, i < tailOffset t.size → i >>> (5 * (levelOf t.shift + 2)) = 0 :=
      fun i hi => shr_zero_of_lt _ (by omega)
    rw [get_of_root t j (by omega) hs2]
    unfold Tree.takeMut
    have c1 : (k == 0) = false := by simp; omega
    have c2 : ¬ (k ≥ t.size) := by omega
    have c3 : ¬ (k > tailOffset t.size) := by omega
    simp only [c1, c2, c3, Bool.false_eq_true, ite_false]
    rcases hR : sliceMutInner (levelOf t.shift) true true e (.sub (tailOffset t.size)) t.root (k - 1) n
      with ⟨⟨ns, nr, ts, nt⟩, m⟩
    rw [hR] at RC TR
    simp only at RC TR
    obtain ⟨RCn, RCs⟩ := RC
    by_cases hjt : tailOffset k ≤ j
    · have hjb : j >>> 5 = (k - 1) >>> 5 := by
        rw [hTO, lIndex_eq] at hjt; simp only [shr_eq]; simp; omega
      have hjl : lIndex j ≤ lIndex (k - 1) := by
        rw [hTO, lIndex_eq] at hjt; simp only [lIndex_eq]; omega
      obtain ⟨hleaf, hread⟩ := TR j hjb hjl
      cases nt with
      | inner => simp [Node.isLeaf] at hleaf
      | leaf a b xs =>
        cases nr with
        | none =>
          dsimp only
          rw [get_of_tail _ _ hjt]
          simpa [Node.xs] using hread
        | some r =>
          dsimp only
          rw [get_of_tail _ _ hjt]
          simpa [Node.xs] using hread
    · have hjt' : j < tailOffset k := by omega
      cases nr with
      | none =>
        exfalso
        have h1 := RCn rfl
        rw [← hL] at h1
        rw [Nat.mod_eq_of_lt (by omega)] at h1
        rw [hTO, lIndex_eq] at hjt'
        omega
      | some r =>
        obtain ⟨a1, a2, a3, rd⟩ := RCs r rfl
        dsimp only
        rw [get_of_root _ _ hjt' (by show ns ≤ 30; omega)]
        exact rd j (by rw [hblk j (by omega), hblk (k - 1) (by omega)]) (by rw [← hTO]; exact hjt')

/-- **`nth` after `pop!`** (transient_vector.cpp `pop_in_place`: `data.take(data.size() - 1)`, i.e.
`vector_transient::take` → `take_mut` with the transient's owner token): for every well-formed tree
and token, every remaining element reads as before. -/
theorem get_popBang [Inhabited α] (t : Transient α) (hw : t.tree.wfT) (n j : Nat) (hj : j < t.tree.size - 1) :
    (t.take (t.tree.size - 1) n).1.tree.get j = t.tree.get j := by
  have key := get_takeMut t.tree hw t.tok (t.tree.size - 1) n j (Nat.sub_le _ _) hj
  rcases h : t.tree.takeMut t.tok (t.tree.size - 1) n with ⟨tr, m⟩
  rw [h] at key
  simp only [Transient.take, h]
  exact key

/-- **`nth` after `conj!`** at the transient level (`Transient.pushBack` = `push_back_mut` with the
transient's token). -/
theorem get_conjBang [Inhabited α] (t : Transient α) (hw : t.tree.wfT) (hsz : t.tree.size < 2 ^ 35) (x : α)
    (n j : Nat) (hj : j ≤ t.tree.size) :
    (t.pushBack x n).1.tree.get j = if j < t.tree.size then t.tree.get j else some x := by
  have key := get_pushBackMut t.tree hw hsz t.tok x n j hj
  rcases h : t.tree.pushBackMut t.tok x n with ⟨tr, m⟩
  rw [h] at key
  simp only [Transient.pushBack, h]
  exact key

end Jank.R3.Immer.Rbts

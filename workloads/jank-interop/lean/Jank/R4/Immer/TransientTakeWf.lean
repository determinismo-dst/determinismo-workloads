import Jank.R4.Immer.TransientTake
import Jank.R3.Immer.RbtsLaws

/-!
# `take_mut` keeps a tree well formed (round 4)

With `get_takeMut`, this gives `nth` after any chain of `pop!`s and `conj!`s (`get_bangs`). The
slice root is well formed at the regular position of the new tail offset `s = last - lIndex last`
(positions carry absolute sizes, rbts/position.hpp `regular_pos`): the children before the cut are
full, the cut child is the sliced one (or, when the cut falls on a child boundary, the previous
full child is now the last one).
-/

namespace Jank.R3.Immer.Rbts

variable {α : Type}

/-- A full node is well formed at a regular position whose size is a multiple of its block. -/
theorem wfP_full_reg : ∀ (k s : Nat) (node : Node α), 0 < s → s % 2 ^ (5 * (k + 2)) = 0 →
    wfP k .full node → wfP k (.reg s) node := by
  intro k
  induction k with
  | zero =>
    intro s node hs h hw
    have hc := count_reg_full 5 s hs (by simpa using h)
    obtain ⟨hnl, hch⟩ := hw
    refine ⟨hnl, fun c hc' => ?_⟩
    rw [hc] at hc'
    obtain ⟨a, b, xs, hx, hl⟩ := hch c (by simp [IPos.count]; exact hc')
    refine ⟨a, b, xs, hx, ?_⟩
    simp only [IPos.towardsL, LPos.count] at hl
    simp only [IPos.towardsL, hc, IPos.size]
    split
    · simpa [LPos.count] using hl
    · simp only [LPos.count, and31]
      have : (s - 1) % 32 = 31 := by
        have hd : 32 ∣ 2 ^ (5 * (0 + 2)) := ⟨32, rfl⟩
        have := Nat.mod_mod_of_dvd s hd
        rw [h] at this; omega
      omega
  | succ k ih =>
    intro s node hs h hw
    have e : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e] at h
    have hc := count_reg_full (5 * (k + 2)) s hs h
    obtain ⟨hnl, hch⟩ := hw
    refine ⟨hnl, fun c hc' => ?_⟩
    rw [hc] at hc'
    obtain ⟨ch, hx, hwc⟩ := hch c (by simp [IPos.count]; exact hc')
    refine ⟨ch, hx, ?_⟩
    simp only [IPos.towardsI] at hwc
    simp only [IPos.towardsI, hc, IPos.size]
    split
    · exact hwc
    · exact ih s ch hs (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega))
        (Nat.dvd_of_mod_eq_zero h))) hwc

/-! ## Digit arithmetic for the cut -/

/-- `last - lIndex last` is `last` with its low 5 bits cleared. -/
theorem cut_eq (last : Nat) : last - lIndex last = last / 32 * 32 := by
  rw [lIndex_eq]; omega

/-- When `last` is past the first leaf of its child block (shift `a`), the cut minus one is in the
same child: same digit at `a`, same blocks above. -/
theorem cut_same_child (a last : Nat) (ha : 5 ≤ a) (h : 32 ≤ last % 2 ^ a) :
    iIndex a (last - lIndex last - 1) = iIndex a last ∧
    (last - lIndex last - 1) >>> (a + 5) = last >>> (a + 5) := by
  have hP := pow_ge32 a ha
  have hd : 32 ∣ 2 ^ a := by
    have : 2 ^ 5 ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha
    simpa using this
  have hm : last % 2 ^ a % 32 = last % 32 := Nat.mod_mod_of_dvd _ hd
  have hrlt := Nat.mod_lt last (show 0 < 2 ^ a by omega)
  have hs2 : last / 2 ^ a * 2 ^ a + last % 2 ^ a = last := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod last (2 ^ a)
  have hq : (last - lIndex last - 1) / 2 ^ a = last / 2 ^ a := by
    apply Nat.div_eq_of_lt_le
    · rw [lIndex_eq]
      generalize last / 2 ^ a * 2 ^ a = A at hs2 ⊢
      omega
    · rw [lIndex_eq, Nat.add_mul, Nat.one_mul]
      generalize last / 2 ^ a * 2 ^ a = A at hs2 ⊢
      omega
  constructor
  · rw [iIndex_eq, iIndex_eq, shr_eq, shr_eq, hq]
  · rw [shr_add5, shr_add5, shr_eq, shr_eq, hq]

/-- When `last` sits in the first leaf of child `idx > 0`, the cut is that child's start: a
multiple of the child block, and the cut minus one is in child `idx - 1` of the same block. -/
theorem cut_boundary (a last : Nat) (ha : 5 ≤ a) (h : last % 2 ^ a < 32) (hidx : iIndex a last ≠ 0) :
    (last - lIndex last) % 2 ^ a = 0 ∧ 0 < last - lIndex last ∧
    iIndex a (last - lIndex last - 1) + 1 = iIndex a last ∧
    (last - lIndex last - 1) >>> (a + 5) = last >>> (a + 5) := by
  have hP := pow_ge32 a ha
  have hd : 32 ∣ 2 ^ a := by
    have : 2 ^ 5 ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha
    simpa using this
  have hm : last % 2 ^ a % 32 = last % 32 := Nat.mod_mod_of_dvd _ hd
  rw [Nat.mod_eq_of_lt h] at hm
  have hs2 : last / 2 ^ a * 2 ^ a + last % 2 ^ a = last := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod last (2 ^ a)
  have hq : 0 < last / 2 ^ a := by
    rcases Nat.eq_zero_or_pos (last / 2 ^ a) with h0 | h0
    · exfalso; apply hidx; rw [iIndex_eq, shr_eq, h0]
    · exact h0
  have hlo : last / 2 ^ a % 32 ≠ 0 := by rw [iIndex_eq, shr_eq] at hidx; exact hidx
  have hc2 : last - lIndex last = last / 2 ^ a * 2 ^ a := by rw [lIndex_eq]; omega
  have hdiv : (last - lIndex last - 1) / 2 ^ a = last / 2 ^ a - 1 := by
    rw [hc2]
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, Nat.one_mul]
      have : 2 ^ a ≤ last / 2 ^ a * 2 ^ a := Nat.le_mul_of_pos_left _ hq
      omega
    · rw [Nat.sub_add_cancel hq]
      have : 2 ^ a ≤ last / 2 ^ a * 2 ^ a := Nat.le_mul_of_pos_left _ hq
      omega
  refine ⟨by rw [hc2]; exact Nat.mul_mod_left _ _, ?_, ?_, ?_⟩
  · rw [hc2]; exact Nat.mul_pos hq (by omega)
  · rw [iIndex_eq, iIndex_eq, shr_eq, shr_eq, hdiv]; omega
  · rw [shr_add5, shr_add5, shr_eq, shr_eq, hdiv]; omega

/-- A nonzero digit at `a` puts `last` at least 32 into its block of `a + 5` bits. -/
theorem ge32_of_digit (a last : Nat) (ha : 5 ≤ a) (h : iIndex a last ≠ 0) : 32 ≤ last % 2 ^ (a + 5) := by
  have hP := pow_ge32 a ha
  rw [iIndex_eq, shr_eq, ← Nat.mod_mul_right_div_self last (2 ^ a) 32] at h
  have hp : 2 ^ a * 32 = 2 ^ (a + 5) := by rw [Nat.pow_add]
  rw [hp] at h
  have h1 : 1 ≤ last % 2 ^ (a + 5) / 2 ^ a := by
    rcases Nat.eq_zero_or_pos (last % 2 ^ (a + 5) / 2 ^ a) with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have := (Nat.le_div_iff_mul_le (show 0 < 2 ^ a by omega)).mp h1
  omega

/-- A number whose blocks above `a` are zero and whose digit at `a` is zero is below `2 ^ a`. -/
theorem lt_of_digit0 (a x : Nat) (hb : x >>> (a + 5) = 0) (hd : iIndex a x = 0) : x < 2 ^ a := by
  rw [shr_add5] at hb
  rw [iIndex_eq] at hd
  have : x >>> a = 0 := by omega
  rw [shr_eq] at this
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos a)).mp this

theorem towardsI_full_of_lt (p : IPos) (sh c : Nat) (h : c + 1 < p.count sh) : p.towardsI sh c = .full := by
  cases p with
  | full => rfl
  | sub s => simp only [IPos.towardsI]; rw [if_pos (by simp; omega)]
  | reg s => simp only [IPos.towardsI]; rw [if_pos (by simp; omega)]

theorem towardsL_full_of_lt (p : IPos) (sh c : Nat) (h : c + 1 < p.count sh) : p.towardsL sh c = .fullLeaf := by
  cases p with
  | full => rfl
  | sub s => simp only [IPos.towardsL]; rw [if_pos (by simp; omega)]
  | reg s => simp only [IPos.towardsL]; rw [if_pos (by simp; omega)]

theorem towardsL_count_le (p : IPos) (sh c : Nat) : (p.towardsL sh c).count ≤ 32 := by
  cases p with
  | full => simp [IPos.towardsL, LPos.count]
  | sub s =>
    simp only [IPos.towardsL]; split
    · simp [LPos.count]
    · simp only [LPos.count, and31]; omega
  | reg s =>
    simp only [IPos.towardsL]; split
    · simp [LPos.count]
    · simp only [LPos.count, and31]; omega

theorem reg_count (sh s : Nat) : (IPos.reg s).count sh = iIndex sh (s - 1) + 1 := rfl

/-- The new position's child `c`: full below the last child, `.reg s` for the last. -/
theorem towardsI_reg (sh s c : Nat) :
    (IPos.reg s).towardsI sh c = if c + 1 = iIndex sh (s - 1) + 1 then .reg s else .full := by
  by_cases h : c + 1 = iIndex sh (s - 1) + 1
  · simp only [iIndex] at h; simp [IPos.towardsI, IPos.count, IPos.size, iIndex, h]
  · simp only [iIndex] at h; simp [IPos.towardsI, IPos.count, IPos.size, iIndex, h]

/-- **A mutating slice without collapse leaves a well-formed root** at the regular position of the
cut `last - lIndex last`, and only when `last` is past the first leaf of its block. -/
theorem sliceMut_nc_wf [Inhabited α] : ∀ (k : Nat) (m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat),
    wfP k p node → validI k p last →
    ∀ x, (sliceMutInner k false m e p node last n).1.2.1 = some x →
      32 ≤ last % 2 ^ (5 * (k + 2)) ∧ wfP k (.reg (last - lIndex last)) x := by
  intro k
  induction k with
  | zero =>
    intro m e p node last n hw hv x hx
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    rw [sliceMutInner_zero, if_neg (by simp)] at hx
    have hnone := sliceMutLeaf_none (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e
      (node.child (iIndex 5 last)) last n
    rcases hR : sliceMutLeaf (p.towardsL 5 (iIndex 5 last)) (m && node.canMutate e) e
      (node.child (iIndex 5 last)) last n with ⟨⟨a, b, c, d⟩, e'⟩
    rw [hR] at hx hnone
    simp only at hnone
    subst hnone
    dsimp only at hx
    by_cases h0 : iIndex 5 last = 0
    · rw [if_pos (by simp [h0])] at hx; simp at hx
    rw [if_neg (by simp [h0]), if_neg (by simp)] at hx
    obtain ⟨hs0, hspos, hsd, _⟩ := cut_boundary 5 last (Nat.le_refl _) (by simp; omega) h0
    have hcnt : (IPos.reg (last - lIndex last)).count 5 = iIndex 5 last := by rw [reg_count]; omega
    have key : ∀ (ys : List (Node α)), (ys = node.cs ∨ ys = childCopy node (iIndex 5 last)) →
        wfP 0 (.reg (last - lIndex last)) (.inner 0 0 ys) := by
      intro ys hys
      refine ⟨rfl, fun c hc => ?_⟩
      rw [hcnt] at hc
      obtain ⟨lid, ltok, lxs, hx', hlen⟩ := hch c (by omega)
      obtain ⟨hyc, _⟩ := ys_get node _ c ys hys hc (lt_of_getElem? _ _ _ hx')
      refine ⟨lid, ltok, lxs, by simp only [Node.cs]; rw [hyc, hx'], ?_⟩
      rw [towardsL_full_of_lt p 5 c (by omega)] at hlen
      simp only [LPos.count] at hlen
      have := towardsL_count_le (IPos.reg (last - lIndex last)) 5 c
      omega
    have h32 : 32 ≤ last % 2 ^ (5 * (0 + 2)) := by
      have := ge32_of_digit 5 last (Nat.le_refl _) h0; simpa using this
    split at hx
    · simp only [Option.some.injEq] at hx
      subst hx
      refine ⟨h32, ?_⟩
      have := key node.cs (Or.inl rfl)
      exact ⟨hnl, this.2⟩
    · simp only [Option.some.injEq] at hx
      subst hx
      refine ⟨h32, ?_⟩
      have := key _ (Or.inr rfl)
      exact ⟨rfl, this.2⟩
  | succ k ih =>
    intro m e p node last n hw hv x hx
    have hw' := hw
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    rw [sliceMutInner_succ, if_neg (by simp), child_of_getElem? _ _ _ hcs] at hx
    have RN := sliceMutInner_root_nc k (m && node.canMutate e) e _ ch last n hwc hv2
    have IH := ih (m && node.canMutate e) e _ ch last n hwc hv2
    rcases hR : sliceMutInner k false (m && node.canMutate e) e
      (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last)) ch last n with ⟨⟨a, b, c, d⟩, e'⟩
    rw [hR] at hx RN IH
    simp only at RN IH
    have e3 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e3]
    cases b with
    | some nx =>
      obtain ⟨h32c, hwnx⟩ := IH nx rfl
      obtain ⟨hsd, _⟩ := cut_same_child (5 * (k + 2)) last hsh h32c
      have h32 : 32 ≤ last % 2 ^ (5 * (k + 2) + 5) := by
        have hm : last % 2 ^ (5 * (k + 2) + 5) % 2 ^ (5 * (k + 2)) = last % 2 ^ (5 * (k + 2)) :=
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
        have := Nat.mod_le (last % 2 ^ (5 * (k + 2) + 5)) (2 ^ (5 * (k + 2)))
        omega
      have hcnt : (IPos.reg (last - lIndex last)).count (5 * (k + 2)) = iIndex (5 * (k + 2)) last + 1 := by
        rw [reg_count, hsd]
      have key : ∀ (ys : List (Node α)), (ys = node.cs ∨ ys = childCopy node (iIndex (5 * (k + 2)) last)) →
          wfP (k + 1) (.reg (last - lIndex last)) (.inner 0 0 (setAt Node.dummy ys (iIndex (5 * (k + 2)) last) nx)) := by
        intro ys hys
        refine ⟨rfl, fun c hc => ?_⟩
        rw [hcnt] at hc
        simp only [Node.cs]
        by_cases hlt : c < iIndex (5 * (k + 2)) last
        · obtain ⟨chc, hxc, hwcc⟩ := hch c (by omega)
          obtain ⟨hyc, hyl⟩ := ys_get node _ c ys hys hlt (lt_of_getElem? _ _ _ hxc)
          refine ⟨chc, by rw [setAt_get_of_lt _ _ _ _ _ hlt hyl, hyc, hxc], ?_⟩
          rw [towardsI_full_of_lt p _ c (by omega)] at hwcc
          rw [towardsI_reg, if_neg (by rw [hsd]; omega)]
          exact hwcc
        · have hceq : c = iIndex (5 * (k + 2)) last := by omega
          subst hceq
          refine ⟨nx, setAt_get_self _ _ _ _, ?_⟩
          rw [towardsI_reg, if_pos (by rw [hsd])]
          exact hwnx
      dsimp only at hx
      split at hx
      · simp only [Option.some.injEq] at hx
        subst hx
        exact ⟨h32, ⟨rfl, (key node.cs (Or.inl rfl)).2⟩⟩
      · simp only [Option.some.injEq] at hx
        subst hx
        exact ⟨h32, ⟨rfl, (key _ (Or.inr rfl)).2⟩⟩
    | none =>
      have hfirst := RN.1 rfl
      dsimp only at hx
      by_cases h0 : iIndex (5 * (k + 2)) last = 0
      · rw [if_pos (by simp [h0])] at hx; simp at hx
      rw [if_neg (by simp [h0]), if_neg (by simp)] at hx
      obtain ⟨hs0, hspos, hsd, _⟩ := cut_boundary (5 * (k + 2)) last hsh hfirst h0
      have h32 := ge32_of_digit (5 * (k + 2)) last hsh h0
      have hcnt : (IPos.reg (last - lIndex last)).count (5 * (k + 2)) = iIndex (5 * (k + 2)) last := by
        rw [reg_count]; omega
      have key : ∀ (ys : List (Node α)), (ys = node.cs ∨ ys = childCopy node (iIndex (5 * (k + 2)) last)) →
          wfP (k + 1) (.reg (last - lIndex last)) (.inner 0 0 ys) := by
        intro ys hys
        refine ⟨rfl, fun c hc => ?_⟩
        rw [hcnt] at hc
        simp only [Node.cs]
        obtain ⟨chc, hxc, hwcc⟩ := hch c (by omega)
        obtain ⟨hyc, _⟩ := ys_get node _ c ys hys hc (lt_of_getElem? _ _ _ hxc)
        refine ⟨chc, by rw [hyc, hxc], ?_⟩
        rw [towardsI_full_of_lt p _ c (by omega)] at hwcc
        rw [towardsI_reg]
        split
        · exact wfP_full_reg k _ chc hspos hs0 hwcc
        · exact hwcc
      split at hx
      · simp only [Option.some.injEq] at hx
        subst hx
        exact ⟨h32, ⟨hnl, (key node.cs (Or.inl rfl)).2⟩⟩
      · simp only [Option.some.injEq] at hx
        subst hx
        exact ⟨h32, ⟨rfl, (key _ (Or.inr rfl)).2⟩⟩

/-! ## With collapse (what `take_mut` runs) -/

theorem sliceMut_c_eq_nc_zero [Inhabited α] (m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat)
    (h0 : iIndex 5 last ≠ 0) :
    sliceMutInner 0 true m e p node last n = sliceMutInner 0 false m e p node last n := by
  rw [sliceMutInner_zero, sliceMutInner_zero]
  simp [h0]

theorem sliceMut_c_eq_nc_succ [Inhabited α] (k : Nat) (m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat)
    (h0 : iIndex (5 * (k + 2)) last ≠ 0) (h1 : iIndex (5 * (k + 2)) last ≠ 1) :
    sliceMutInner (k + 1) true m e p node last n = sliceMutInner (k + 1) false m e p node last n := by
  rw [sliceMutInner_succ, sliceMutInner_succ]
  simp [h0, h1]

theorem sliceMut_c_eq_nc_some [Inhabited α] (k : Nat) (m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat)
    (h0 : iIndex (5 * (k + 2)) last ≠ 0)
    (hsome : (sliceMutInner k false (m && node.canMutate e) e (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last))
      (node.child (iIndex (5 * (k + 2)) last)) last n).1.2.1.isSome = true) :
    sliceMutInner (k + 1) true m e p node last n = sliceMutInner (k + 1) false m e p node last n := by
  rw [sliceMutInner_succ, sliceMutInner_succ, if_neg (by simp [h0]), if_neg (by simp)]
  rcases hR : sliceMutInner k false (m && node.canMutate e) e (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last))
      (node.child (iIndex (5 * (k + 2)) last)) last n with ⟨⟨a, b, c, d⟩, e'⟩
  rw [hR] at hsome
  cases b with
  | none => simp at hsome
  | some nx => rfl

/-- **A mutating slice with collapse leaves a well-formed root** at the regular position of the cut,
at its (possibly lower) shift, and the cut fits under that shift. -/
theorem sliceMut_c_wf [Inhabited α] : ∀ (k : Nat) (m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat),
    wfP k p node → validI k p last → last < 2 ^ (5 * (k + 2)) →
    ∀ x, (sliceMutInner k true m e p node last n).1.2.1 = some x →
      wfP (levelOf (sliceMutInner k true m e p node last n).1.1) (.reg (last - lIndex last)) x ∧
      last - lIndex last ≤ 2 ^ ((sliceMutInner k true m e p node last n).1.1 + 5) := by
  intro k
  induction k with
  | zero =>
    intro m e p node last n hw hv hlt x hx
    by_cases h0 : iIndex 5 last = 0
    · rw [sliceMutInner_zero, if_pos (by simp [h0]), sliceMutLeaf_none] at hx; simp at hx
    rw [sliceMut_c_eq_nc_zero m e p node last n h0] at hx ⊢
    obtain ⟨_, hwf⟩ := sliceMut_nc_wf 0 m e p node last n hw hv x hx
    obtain ⟨_, RS⟩ := sliceMutInner_root_nc 0 m e p node last n hw hv
    obtain ⟨hsh, _⟩ := RS x hx
    rw [hsh]
    refine ⟨hwf, ?_⟩
    simp at hlt ⊢; omega
  | succ k ih =>
    intro m e p node last n hw hv hlt x hx
    have hw' := hw
    have hv' := hv
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    have e3 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e3] at hlt
    have hblk : last >>> (5 * (k + 2) + 5) = 0 := shr_zero_of_lt _ hlt
    have hsle : last - lIndex last ≤ last := Nat.sub_le _ _
    by_cases h0 : iIndex (5 * (k + 2)) last = 0
    · -- collapse into child 0
      obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
      rw [sliceMutInner_succ, if_pos (by simp [h0])] at hx ⊢
      rw [child_of_getElem? _ _ _ hcs] at hx ⊢
      exact ih _ e _ ch last n hwc hv2 (lt_of_digit0 _ last hblk h0) x hx
    by_cases h1 : iIndex (5 * (k + 2)) last = 1
    · obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
      have RN := sliceMutInner_root_nc k (m && node.canMutate e) e _ ch last n hwc hv2
      rcases hR : sliceMutInner k false (m && node.canMutate e) e
        (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last)) ch last n with ⟨⟨a, b, c, d⟩, e'⟩
      rw [hR] at RN
      simp only at RN
      cases b with
      | some nx =>
        have hsome : (sliceMutInner k false (m && node.canMutate e) e
            (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last))
            (node.child (iIndex (5 * (k + 2)) last)) last n).1.2.1.isSome = true := by
          rw [child_of_getElem? _ _ _ hcs, hR]; rfl
        rw [sliceMut_c_eq_nc_some k m e p node last n h0 hsome] at hx ⊢
        obtain ⟨_, hwf⟩ := sliceMut_nc_wf (k + 1) m e p node last n hw' hv' x hx
        obtain ⟨_, RS⟩ := sliceMutInner_root_nc (k + 1) m e p node last n hw' hv'
        obtain ⟨hshift, _⟩ := RS x hx
        rw [hshift]
        have hlv : levelOf (5 * (k + 1 + 1)) = k + 1 := by unfold levelOf; omega
        rw [hlv]
        exact ⟨hwf, by rw [show 5 * (k + 1 + 1) + 5 = 5 * (k + 2) + 5 by omega]; omega⟩
      | none =>
        have hfirst := RN.1 rfl
        rw [sliceMutInner_succ, if_neg (by simp [h0]), child_of_getElem? _ _ _ hcs, hR] at hx ⊢
        dsimp only at hx ⊢
        rw [if_neg (by simp [h0]), if_pos (by simp [h1] <;> omega)] at hx ⊢
        simp only [Option.some.injEq] at hx
        subst hx
        obtain ⟨hs0, hspos, hsd, hsb⟩ := cut_boundary (5 * (k + 2)) last hsh hfirst h0
        have hsd0 : iIndex (5 * (k + 2)) (last - lIndex last - 1) = 0 := by omega
        have hslt := lt_of_digit0 (5 * (k + 2)) (last - lIndex last - 1) (by rw [hsb, hblk]) hsd0
        obtain ⟨ch0, hcs0, hwc0⟩ := hch 0 (by omega)
        rw [child_of_getElem? _ _ _ hcs0]
        rw [towardsI_full_of_lt p _ 0 (by omega)] at hwc0
        have hlv : levelOf (5 * (k + 2) - 5) = k := by unfold levelOf; omega
        rw [hlv]
        refine ⟨wfP_full_reg k _ ch0 hspos hs0 hwc0, ?_⟩
        rw [show 5 * (k + 2) - 5 + 5 = 5 * (k + 2) by omega]
        omega
    · rw [sliceMut_c_eq_nc_succ k m e p node last n h0 h1] at hx ⊢
      obtain ⟨_, hwf⟩ := sliceMut_nc_wf (k + 1) m e p node last n hw' hv' x hx
      obtain ⟨_, RS⟩ := sliceMutInner_root_nc (k + 1) m e p node last n hw' hv'
      obtain ⟨hshift, _⟩ := RS x hx
      rw [hshift]
      have hlv : levelOf (5 * (k + 1 + 1)) = k + 1 := by unfold levelOf; omega
      rw [hlv]
      exact ⟨hwf, by rw [show 5 * (k + 1 + 1) + 5 = 5 * (k + 2) + 5 by omega]; omega⟩

/-! ## The tail a mutating slice ends with holds the cut's leaf -/

theorem sliceMutLeaf_len [Inhabited α] (p : LPos) (m : Bool) (e : Nat) (node : Node α) (last n : Nat)
    (hl : p.count ≤ node.xs.length) (hlast : lIndex last < p.count) :
    lIndex last + 1 ≤ (sliceMutLeaf p m e node last n).1.2.2.2.xs.length := by
  unfold sliceMutLeaf; dsimp only
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    show lIndex last + 1 ≤ node.xs.length
    omega
  · split
    · show lIndex last + 1 ≤ (node.xs.take (lIndex last + 1)).length
      rw [List.length_take]; omega
    · show lIndex last + 1 ≤ (leafCopy node (lIndex last + 1)).length
      exact Nat.le_of_eq (by rw [leafCopy, copyN_length])

theorem sliceMutInner_tail_len [Inhabited α] : ∀ (k : Nat) (c m : Bool) (e : Nat) (p : IPos) (node : Node α) (last n : Nat),
    wfP k p node → validI k p last →
    lIndex last + 1 ≤ (sliceMutInner k c m e p node last n).1.2.2.2.xs.length := by
  intro k
  induction k with
  | zero =>
    intro c m e p node last n hw hv
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨lid, ltok, lxs, hcs, hlen⟩ := hch _ hv1
    rw [sliceMutInner_tail_zero, child_of_getElem? _ _ _ hcs]
    exact sliceMutLeaf_len _ _ e _ last n (by simpa [Node.xs] using hlen) hv2
  | succ k ih =>
    intro c m e p node last n hw hv
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
    rw [sliceMutInner_tail_succ, child_of_getElem? _ _ _ hcs]
    exact ih _ _ e _ ch last n hwc hv2

/-! ## `take_mut` -/

/-- **`take_mut` keeps a tree well formed** (so `pop!` does), for every owner token. -/
theorem takeMut_wfT [Inhabited α] (t : Tree α) (hw : t.wfT) (e k n : Nat) (hk : k ≤ t.size) :
    (t.takeMut e k n).1.wfT := by
  have hw0 := hw
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  by_cases hk0 : k = 0
  · subst hk0; unfold Tree.takeMut; simp only [beq_self_eq_true, if_true]; exact empty_wfT
  by_cases hks : k = t.size
  · subst hks; unfold Tree.takeMut; simp [show t.size ≠ 0 by omega]; exact hw0
  have hpos : 0 < t.size := by omega
  have hf := tail_facts t.size hpos
  by_cases htk : tailOffset t.size < k
  · have hto : tailOffset k = tailOffset t.size := by
      rw [tailOffset_eq, tailOffset_eq, if_neg (by omega), if_neg (by omega)]
      rw [tailOffset_eq, if_neg (by omega)] at htk hf; omega
    cases ht : t.tail with
    | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
    | leaf a b xs =>
    rw [ht] at htlen
    simp only [Node.xs] at htlen
    have hA : ∃ (a' b' : Nat) (ys : List α), (t.takeMut e k n).1 = { t with size := k, tail := .leaf a' b' ys } ∧
        k - tailOffset t.size ≤ ys.length := by
      unfold Tree.takeMut
      simp only [show (k == 0) = false by simp; omega, show ¬ k ≥ t.size by omega, htk, Bool.false_eq_true,
        ite_false, ite_true]
      split
      · refine ⟨a, b, xs.take (k - tailOffset t.size), by simp [ht, Node.id, Node.tok, Node.xs], ?_⟩
        simp; omega
      · refine ⟨n, e, leafCopy (Node.leaf a b xs) (k - tailOffset t.size), by rw [ht], ?_⟩
        exact Nat.le_of_eq (by rw [leafCopy, copyN_length])
    obtain ⟨a', b', ys, hR, hyl⟩ := hA
    rw [hR]
    refine ⟨hs5, hs1, hs2, rfl, ?_, ?_⟩
    · show k - tailOffset k ≤ ys.length; rw [hto]; exact hyl
    · intro h
      have h' : 0 < tailOffset t.size := by rw [← hto]; exact h
      show tailOffset k ≤ 2 ^ (t.shift + 5) ∧ wfP (levelOf t.shift) (.sub (tailOffset k)) t.root
      rw [hto]; exact hroot h'
  · have hkt : k ≤ tailOffset t.size := by omega
    obtain ⟨hcap, hwr⟩ := hroot (by omega)
    have hL := levelOf_eq t.shift hs5 hs1
    have hcap' : tailOffset t.size ≤ 2 ^ (5 * (levelOf t.shift + 2)) := by rw [← hL]; exact hcap
    have hvl := validI_sub _ _ (k - 1) (by omega) hcap'
    have hTO := tailOffset_take k (by omega)
    have RC := sliceMutInner_root_c (levelOf t.shift) true e (.sub (tailOffset t.size)) t.root (k - 1) n hwr hvl
    have WF := sliceMut_c_wf (levelOf t.shift) true e (.sub (tailOffset t.size)) t.root (k - 1) n hwr hvl (by omega)
    have TL := sliceMutInner_tail_read (levelOf t.shift) true true e (.sub (tailOffset t.size)) t.root (k - 1) n (k - 1)
      hwr hvl rfl (Nat.le_refl _)
    have TN := sliceMutInner_tail_len (levelOf t.shift) true true e (.sub (tailOffset t.size)) t.root (k - 1) n hwr hvl
    unfold Tree.takeMut
    have c1 : (k == 0) = false := by simp; omega
    have c2 : ¬ (k ≥ t.size) := by omega
    have c3 : ¬ (k > tailOffset t.size) := by omega
    simp only [c1, c2, c3, Bool.false_eq_true, ite_false]
    rcases hR : sliceMutInner (levelOf t.shift) true true e (.sub (tailOffset t.size)) t.root (k - 1) n
      with ⟨⟨ns, nr, ts, nt⟩, m⟩
    rw [hR] at RC WF TL TN
    simp only at RC WF TL TN
    obtain ⟨RCn, RCs⟩ := RC
    have htk' : k - tailOffset k = lIndex (k - 1) + 1 := by rw [hTO]; rw [lIndex_eq]; omega
    cases nr with
    | none =>
      dsimp only
      refine ⟨by show (5 : Nat) % 5 = 0; decide, by show (5 : Nat) ≤ 5; omega, by show (5 : Nat) ≤ 30; omega,
        TL.1, by show k - tailOffset k ≤ nt.xs.length; rw [htk']; exact TN, fun h => ?_⟩
      exfalso
      have h1 := RCn rfl
      rw [← hL, Nat.mod_eq_of_lt (by omega)] at h1
      rw [hTO, lIndex_eq] at h
      omega
    | some r =>
      obtain ⟨a1, a2, a3, _⟩ := RCs r rfl
      obtain ⟨hwfr, hbound⟩ := WF r rfl
      dsimp only
      have hlvl : levelOf t.shift ≤ 5 := by unfold levelOf; omega
      refine ⟨a1, a2, by show ns ≤ 30; omega, TL.1,
        by show k - tailOffset k ≤ nt.xs.length; rw [htk']; exact TN, fun h => ?_⟩
      have hLn := levelOf_eq ns a1 a2
      have hs : tailOffset k = k - 1 - lIndex (k - 1) := hTO
      rw [hs]
      refine ⟨hbound, ?_⟩
      rw [hs] at h
      rw [wfP_sub_reg _ _ _ (by rw [← hLn]; exact hbound) h]
      exact hwfr

/-! ## Any chain of `conj!` and `pop!` -/

/-- A transient operation as jank runs it: `conj!` (`push_back_mut`) or `pop!` (`take_mut` to
`size - 1`; jank throws on an empty transient, transient_vector.cpp `pop_in_place`, which leaves
the tree as it is here). -/
inductive Bang (α : Type) where
  | conj (x : α)
  | pop

def Bang.run [Inhabited α] (e : Nat) (acc : Tree α × Nat) : Bang α → Tree α × Nat
  | .conj x => acc.1.pushBackMut e x acc.2
  | .pop => if acc.1.size = 0 then acc else acc.1.takeMut e (acc.1.size - 1) acc.2

/-- Clojure's transient vector as a list. -/
def Bang.model (xs : List α) : Bang α → List α
  | .conj x => xs ++ [x]
  | .pop => xs.dropLast

/-- **`nth` after any chain of `conj!` and `pop!`**: for every well-formed vector (with round 3's
`empty_wfT`, `(transient [])`), every owner token and every chain staying below `2^35` elements,
the transient stays well formed and reads at every index as Clojure's list of its elements. -/
theorem get_bangs [Inhabited α] : ∀ (bs : List (Bang α)) (acc : Tree α × Nat) (xs : List α) (e : Nat),
    acc.1.wfT → acc.1.size = xs.length → (∀ j, j < acc.1.size → acc.1.get j = xs[j]?) →
    acc.1.size + bs.length < 2 ^ 35 →
    (bs.foldl (Bang.run e) acc).1.wfT ∧ (bs.foldl (Bang.run e) acc).1.size = (bs.foldl Bang.model xs).length ∧
      ∀ j, j < (bs.foldl (Bang.run e) acc).1.size →
        (bs.foldl (Bang.run e) acc).1.get j = (bs.foldl Bang.model xs)[j]? := by
  intro bs
  induction bs with
  | nil => intro acc xs e hw hs hg _; exact ⟨hw, hs, hg⟩
  | cons b bs ih =>
    intro acc xs e hw hs hg hsz
    simp only [List.length_cons] at hsz
    simp only [List.foldl_cons]
    cases b with
    | conj x =>
      have hw1 := pushBackMut_wfT acc.1 hw (by omega) e x acc.2
      have hs1 := pushBackMut_size1 acc.1 e x acc.2
      refine ih (acc.1.pushBackMut e x acc.2) (xs ++ [x]) e hw1
        (by rw [hs1, hs, List.length_append]; rfl) ?_ (by rw [hs1]; omega)
      intro j hj
      rw [hs1] at hj
      rw [get_pushBackMut acc.1 hw (by omega) e x acc.2 j (by omega)]
      by_cases hjs : j < acc.1.size
      · rw [if_pos hjs, hg j hjs, List.getElem?_append_left (by omega)]
      · rw [if_neg hjs, List.getElem?_append_right (by omega), show j - xs.length = 0 by omega]; rfl
    | pop =>
      by_cases h0 : acc.1.size = 0
      · have hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hr : Bang.run e acc .pop = acc := by simp [Bang.run, h0]
        have hm : Bang.model xs .pop = xs := by simp [Bang.model, hx0]
        rw [hr, hm]
        exact ih acc xs e hw hs hg (by omega)
      · have hr : Bang.run e acc .pop = acc.1.takeMut e (acc.1.size - 1) acc.2 := by simp [Bang.run, h0]
        have hm : Bang.model xs .pop = xs.dropLast := rfl
        rw [hr, hm]
        have hw1 := takeMut_wfT acc.1 hw e (acc.1.size - 1) acc.2 (by omega)
        have hs1 := takeMut_size acc.1 e (acc.1.size - 1) acc.2 (by omega)
        refine ih _ xs.dropLast e hw1 (by rw [hs1, List.length_dropLast, hs]) ?_ (by rw [hs1]; omega)
        intro j hj
        rw [hs1] at hj
        rw [get_takeMut acc.1 hw e (acc.1.size - 1) acc.2 j (by omega) hj, hg j (by omega),
          List.dropLast_eq_take, List.getElem?_take, if_pos (by omega)]

end Jank.R3.Immer.Rbts

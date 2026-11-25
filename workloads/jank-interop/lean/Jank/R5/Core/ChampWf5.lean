import Jank.R5.Core.ChampLaws5

/-!
# Round 5, core: `add` keeps a champ well formed, and add is idempotent

- ★ `makeMerged_wf`, ★ `doAdd_wf`, ★ `add_wf`: `do_add` turns a well-formed node into a well-formed
  node (bitmaps disjoint and below 2^32, buffers holding their popcounts, children well formed,
  collision nodes of at least two values), so every champ built by `assoc`/`conj` from
  `champ::empty()` satisfies the premise of round 3's `get_add` and of this round's laws.
- ★ `size_add_add`, ★ `get_add_add`: adding the same value twice changes neither the count nor
  what `get` returns, for every well-formed champ.
-/

namespace Jank.R3.Immer.Champ

variable {α κ : Type}

/-! ## Popcounts -/

theorem countP_range_or (p : Nat → Bool) (d : Nat) (hp : p d = false) :
    ∀ n, d < n → (List.range n).countP (fun i => p i || decide (d = i)) = (List.range n).countP p + 1
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.countP_append, List.countP_append]
    by_cases hdn : d < n
    · rw [countP_range_or p d hp n hdn]
      have : d ≠ n := by omega
      simp [this] <;> omega
    · have hd : d = n := by omega
      rw [← hd]
      have e : (List.range d).countP (fun i => p i || decide (d = i)) = (List.range d).countP p := by
        apply List.countP_congr
        intro i hi
        rw [List.mem_range] at hi
        have : d ≠ i := by omega
        simp [this]
      rw [e]
      simp [hp] <;> omega

theorem popcount_or_pow (x d : Nat) (hd : d < 32) (hx : x.testBit d = false) :
    popcount (x ||| 2 ^ d) = popcount x + 1 := by
  unfold popcount
  have e : (fun i => (x ||| 2 ^ d).testBit i) = (fun i => x.testBit i || decide (d = i)) := by
    funext i; rw [Nat.testBit_or, Nat.testBit_two_pow]
  rw [e]
  exact countP_range_or (fun i => x.testBit i) d hx 32 hd

theorem clearBit_testBit (x d i : Nat) (hi : i < 32) :
    (clearBit x (2 ^ d)).testBit i = (x.testBit i && !decide (d = i)) := by
  unfold clearBit
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow,
    show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem popcount_clear (x d : Nat) (hd : d < 32) (hx : x.testBit d = true) :
    popcount (clearBit x (2 ^ d)) + 1 = popcount x := by
  unfold popcount
  have e1 : (List.range 32).countP (fun i => (clearBit x (2 ^ d)).testBit i) =
      (List.range 32).countP (fun i => x.testBit i && !decide (d = i)) := by
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [clearBit_testBit x d i hi]
  have e2 : (List.range 32).countP (fun i => x.testBit i) =
      (List.range 32).countP (fun i => (x.testBit i && !decide (d = i)) || decide (d = i)) := by
    apply List.countP_congr
    intro i _
    by_cases h : d = i
    · subst h; simp [hx]
    · simp [h]
  rw [e1, e2, countP_range_or (fun i => x.testBit i && !decide (d = i)) d (by simp) 32 hd]

theorem popcount_eq_zero (x : Nat) (hx : x < 2 ^ 32) (h : popcount x = 0) : x = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases hi : i < 32
  · unfold popcount at h
    rw [List.countP_eq_zero] at h
    have := h i (List.mem_range.mpr hi)
    simpa using this
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))

theorem pow_lt32 (d : Nat) (hd : d < 32) : 2 ^ d < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) hd

theorem popcount_pos (x d : Nat) (hd : d < 32) (hx : x.testBit d = true) : 1 ≤ popcount x := by
  have := popcount_lt x d hd hx
  omega

theorem popcount_two (a b : Nat) (ha : a < 32) (hb : b < 32) (hab : a ≠ b) :
    popcount (2 ^ a ||| 2 ^ b) = 2 := by
  have hx : (2 ^ b).testBit a = false := by rw [Nat.testBit_two_pow]; simp <;> omega
  rw [Nat.or_comm, popcount_or_pow (2 ^ b) a ha hx, popcount_pow b hb]

/-! ## Lists -/

theorem length_setL {β : Type} (l : List β) (i : Nat) (x : β) : (setL l i x).length = l.length := by
  unfold setL; simp

theorem mem_setL {β : Type} (l : List β) (i : Nat) (x y : β) (h : y ∈ setL l i x) : y ∈ l ∨ y = x :=
  List.mem_or_eq_of_mem_set h

theorem length_insertAt {β : Type} (l : List β) (i : Nat) (x : β) (h : i ≤ l.length) :
    (insertAt l i x).length = l.length + 1 := by
  unfold insertAt; simp <;> omega

theorem mem_insertAt {β : Type} (l : List β) (i : Nat) (x y : β) (h : y ∈ insertAt l i x) : y ∈ l ∨ y = x := by
  unfold insertAt at h
  simp only [List.append_assoc, List.mem_append, List.mem_singleton] at h
  rcases h with h | h | h
  · exact Or.inl (List.mem_of_mem_take h)
  · exact Or.inr h
  · exact Or.inl (List.mem_of_mem_drop h)

theorem length_eraseAt {β : Type} (l : List β) (i : Nat) (h : i < l.length) :
    (eraseAt l i).length + 1 = l.length := by
  unfold eraseAt; simp <;> omega

theorem length_eraseAt_ge {β : Type} (l : List β) (i : Nat) : l.length ≤ (eraseAt l i).length + 1 := by
  unfold eraseAt; simp <;> omega

/-! ## Well-formedness, introduced -/

/-- The values pointer of a well-formed inner node: a buffer holding the data popcount, or null
with an empty datamap. -/
def valsOk (dm : Nat) : Option (Vals α) → Prop
  | some vs => popcount dm ≤ vs.xs.length
  | none => dm = 0

theorem wf_inner_intro (r nid tok nm dm : Nat) (v : Option (Vals α)) (cs : List (Node α))
    (h1 : nm &&& dm = 0) (h2 : nm < 2 ^ 32) (h3 : dm < 2 ^ 32) (h4 : popcount nm ≤ cs.length)
    (h5 : valsOk dm v)
    (h6 : ∀ c ∈ cs.take (popcount nm), wfNode r c = true) :
    wfNode (r + 1) (.inner nid tok nm dm v cs) = true := by
  first
  | (simp only [wfNode, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
     refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩, h6⟩
     cases v with
     | none => simpa [valsOk] using h5
     | some vs => simpa [valsOk] using h5)
  | (cases v <;> simp_all [wfNode, valsOk])

/-- `make_inner_n` with fresh values: well formed when the bitmaps are, the values fill the data
popcount exactly, and the children are well formed. -/
theorem wf_mkInner (r nm dm : Nat) (xs : List α) (cs : List (Node α)) (s : Al)
    (h1 : nm &&& dm = 0) (h2 : nm < 2 ^ 32) (h3 : dm < 2 ^ 32) (h4 : popcount nm ≤ cs.length)
    (h5 : popcount dm = xs.length) (h6 : ∀ c ∈ cs.take (popcount nm), wfNode r c = true) :
    wfNode (r + 1) ((mkInner nm dm xs cs).run s).1 = true := by
  cases xs with
  | nil =>
    have : dm = 0 := popcount_eq_zero dm h3 (by simpa using h5)
    exact wf_inner_intro r _ 0 nm dm none cs h1 h2 h3 h4 this h6
  | cons x xs =>
    exact wf_inner_intro r _ 0 nm dm (some _) cs h1 h2 h3 h4 (by simp [valsOk, h5]) h6

/-- What a well-formed inner node gives. -/
theorem wf_inner_facts (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) :
    ∃ nid tok nm dm v cs, N = .inner nid tok nm dm v cs ∧ nm &&& dm = 0 ∧ nm < 2 ^ 32 ∧ dm < 2 ^ 32 ∧
      popcount nm ≤ cs.length ∧ valsOk dm v ∧
      ∀ c ∈ cs.take (popcount nm), wfNode r c = true := by
  cases N with
  | collision => simp [wfNode] at hw
  | inner nid tok nm dm v cs =>
    simp only [wfNode, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hw
    refine ⟨nid, tok, nm, dm, v, cs, rfl, h1, h2, h3, h4, ?_, h6⟩
    cases v with
    | none => simpa [valsOk] using h5
    | some vs => simpa [valsOk] using h5

/-! ## `make_merged` -/

theorem makeMerged_wf (v1 v2 : α) (h1 h2 : Nat) :
    ∀ r (s : Al), wfNode r ((makeMerged none r v1 h1 v2 h2).run s).1 = true := by
  intro r
  induction r with
  | zero => intro s; rfl
  | succ r ih =>
    intro s
    have hA := idxAt_lt h1 (maxShift - 5 * (r + 1))
    have hB := idxAt_lt h2 (maxShift - 5 * (r + 1))
    generalize hAdef : idxAt h1 (maxShift - 5 * (r + 1)) = A at hA
    generalize hBdef : idxAt h2 (maxShift - 5 * (r + 1)) = B at hB
    by_cases hc : (A == B) = true
    · have hAB : A = B := by simpa using hc
      have e : ((makeMerged none (r + 1) v1 h1 v2 h2).run s).1 =
          ((mkInner (1 <<< A) 0 [] [((makeMerged none r v1 h1 v2 h2).run s).1]).run
            ((makeMerged none r v1 h1 v2 h2).run s).2).1 := by
        rw [makeMerged.eq_2]; dsimp only; rw [hAdef, hBdef, if_pos hc]; rfl
      rw [e, one_shl]
      apply wf_mkInner
      · simp
      · exact pow_lt32 A hA
      · decide
      · simp [popcount_pow A hA]
      · exact popcount_zero
      · intro c hcm
        have hcm' := List.mem_of_mem_take hcm
        simp at hcm'
        rw [hcm']; exact ih _
    · have hne : A ≠ B := by intro h; apply hc; simp [h]
      have e : ((makeMerged none (r + 1) v1 h1 v2 h2).run s).1 =
          ((mkInner 0 ((1 <<< A) ||| (1 <<< B)) (if A < B then [v1, v2] else [v2, v1]) []).run s).1 := by
        rw [makeMerged.eq_2]; dsimp only; rw [hAdef, hBdef, if_neg hc]; rfl
      rw [e, one_shl, one_shl]
      apply wf_mkInner
      · simp
      · decide
      · exact Nat.or_lt_two_pow (pow_lt32 A hA) (pow_lt32 B hB)
      · simp [popcount_zero]
      · rw [popcount_two A B hA hB hne]; split <;> rfl
      · intro c hcm; simp at hcm

/-! ## `do_add` keeps well-formedness -/

theorem doAdd_wf [Inhabited α] (cfg : Cfg α κ) (v : α) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      wfNode r ((doAdd cfg r N v h).run s).1.1 = true := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      have hl : xs.length ≥ 2 := by simpa [wfNode, Node.collisions] using hw
      rw [doAdd.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        show decide ((v :: xs).length ≥ 2) = true
        simp <;> omega
      | some pos =>
        show decide ((v :: eraseAt xs pos).length ≥ 2) = true
        have := length_eraseAt_ge xs pos
        simp <;> omega
  | succ r ih =>
    intro hr N s hw
    obtain ⟨_, hvals, _⟩ := wf_facts r N hw
    obtain ⟨nid, tok, nm, dm, vv, cs, hN, h1, h2, h3, h4, h5, h6⟩ := wf_inner_facts r N hw
    have h1' : N.nodemap &&& N.datamap = 0 := by subst hN; exact h1
    have h2' : N.nodemap < 2 ^ 32 := by subst hN; exact h2
    have h3' : N.datamap < 2 ^ 32 := by subst hN; exact h3
    have h4' : popcount N.nodemap ≤ N.cs.length := by subst hN; exact h4
    have h5' : valsOk N.datamap N.vals := by
      subst hN; exact h5
    have h6' : ∀ c ∈ N.cs.take (popcount N.nodemap), wfNode r c = true := by subst hN; exact h6
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    have htake_len : (N.cs.take N.childrenCount).length = popcount N.nodemap := by
      unfold Node.childrenCount; simp <;> omega
    have htake_wf : ∀ c ∈ N.cs.take N.childrenCount, wfNode r c = true := h6'
    by_cases hA : N.nodemap.testBit D = true
    · -- the child on the path: `copy_inner_replace`
      have hA' : (N.nodemap &&& bitAt h (maxShift - 5 * (r + 1)) != 0) = true := by
        rw [hbit, and_pow_bne]; exact hA
      have hoff : N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))) = popcount (N.nodemap &&& (2 ^ D - 1)) := by
        unfold Node.childrenCountBit; rw [hbit]
      have hlt := popcount_lt N.nodemap D hD hA
      have hch : wfNode r (N.child (N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))))) = true := by
        apply h6'
        rw [hoff]
        exact getD_mem_take _ _ _ _ hlt (by omega)
      obtain ⟨nid', hR⟩ : ∃ nid', ((doAdd cfg (r + 1) N v h).run s).1.1 =
          .inner nid' 0 N.nodemap N.datamap N.vals
            (setL (N.cs.take N.childrenCount) (N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))))
              ((doAdd cfg r (N.child (N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))))) v h).run s).1.1) := by
        rw [doAdd.eq_2]; dsimp only; rw [if_pos hA']; exact ⟨_, rfl⟩
      rw [hR]
      refine wf_inner_intro r _ 0 N.nodemap N.datamap N.vals _ h1' h2' h3' ?_ h5' ?_
      · exact Nat.le_of_eq (by rw [length_setL, htake_len])
      intro c hc
      replace hc := List.mem_of_mem_take hc
      rcases mem_setL _ _ _ _ hc with hc | hc
      · exact htake_wf c hc
      · rw [hc]; exact ih (by omega) _ s hch
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& bitAt h (maxShift - 5 * (r + 1)) != 0) = true := by
        rw [hbit, and_pow_bne]; exact hA
      have hoffD : N.dataCountBit (bitAt h (maxShift - 5 * (r + 1))) = popcount (N.datamap &&& (2 ^ D - 1)) := by
        unfold Node.dataCountBit; rw [hbit]
      have hleD := popcount_and_le N.datamap (2 ^ D - 1)
      have hvals_len : (N.values.take N.dataCount).length = popcount N.datamap := by
        unfold Node.dataCount; simp <;> omega
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& bitAt h (maxShift - 5 * (r + 1)) != 0) = true := by
          rw [hbit, and_pow_bne]; exact hB
        have hltD := popcount_lt N.datamap D hD hB
        by_cases hE : cfg.eqTT (N.values.getD (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) default) v = true
        · -- `copy_inner_replace_value`
          have e : ((doAdd cfg (r + 1) N v h).run s).1.1 =
              ((mkInner N.nodemap N.datamap
                (setL (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) v)
                (N.cs.take N.childrenCount)).run s).1 := by
            rw [doAdd.eq_2]; dsimp only; rw [if_neg hA', if_pos hB', if_pos hE]; rfl
          rw [e]
          apply wf_mkInner r N.nodemap N.datamap _ _ s h1' h2' h3' (Nat.le_of_eq htake_len.symm)
          · rw [length_setL, hvals_len]
          · intro c hc
            replace hc := List.mem_of_mem_take hc
            exact htake_wf c hc
        · -- `make_merged` below, `copy_inner_replace_merged`
          have e : ((doAdd cfg (r + 1) N v h).run s).1.1 =
              ((mkInner (N.nodemap ||| bitAt h (maxShift - 5 * (r + 1)))
                (clearBit N.datamap (bitAt h (maxShift - 5 * (r + 1))))
                (eraseAt (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))))
                (insertAt (N.cs.take N.childrenCount) (N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))))
                  ((makeMerged none r v h (N.values.getD (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) default)
                    (cfg.hashT (N.values.getD (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) default))).run s).1)).run
                ((makeMerged none r v h (N.values.getD (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) default)
                    (cfg.hashT (N.values.getD (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) default))).run s).2).1 := by
            rw [doAdd.eq_2]; dsimp only; rw [if_neg hA', if_pos hB', if_neg hE]; rfl
          generalize N.values.getD (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) default = val at e
          have hoffN : N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))) = popcount (N.nodemap &&& (2 ^ D - 1)) := by
            unfold Node.childrenCountBit; rw [hbit]
          have hleN := popcount_and_le N.nodemap (2 ^ D - 1)
          have hcs_len : (insertAt (N.cs.take N.childrenCount) (N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))))
              ((makeMerged none r v h val (cfg.hashT val)).run s).1).length = popcount (N.nodemap ||| 2 ^ D) := by
            have hle' : N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))) ≤ (N.cs.take N.childrenCount).length := by
              rw [hoffN, htake_len]; exact hleN
            rw [length_insertAt _ _ _ hle', htake_len, popcount_or_pow N.nodemap D hD hA0]
          rw [e, hbit]
          rw [hbit] at hcs_len
          apply wf_mkInner
          · apply Nat.eq_of_testBit_eq
            intro i
            have hi := congrArg (fun x => Nat.testBit x i) h1'
            simp only [Nat.testBit_and, Nat.zero_testBit] at hi
            unfold clearBit
            simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow, Nat.zero_testBit]
            by_cases hdi : D = i
            · subst hdi
              rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]
              simp [hD]
            · simp only [hdi, decide_false, Bool.or_false]
              cases hn : N.nodemap.testBit i <;> cases hd : N.datamap.testBit i <;> simp_all
          · exact Nat.or_lt_two_pow h2' (pow_lt32 D hD)
          · exact Nat.lt_of_le_of_lt Nat.and_le_left h3'
          · exact Nat.le_of_eq hcs_len.symm
          · have hc1 := popcount_clear N.datamap D hD hB
            have hc2 := length_eraseAt (N.values.take N.dataCount) (popcount (N.datamap &&& (2 ^ D - 1)))
              (by rw [hvals_len]; exact hltD)
            rw [hvals_len] at hc2
            rw [show N.dataCountBit (2 ^ D) = popcount (N.datamap &&& (2 ^ D - 1)) from rfl]
            omega
          · intro c hc
            replace hc := List.mem_of_mem_take hc
            rcases mem_insertAt _ _ _ _ hc with hc | hc
            · exact htake_wf c hc
            · rw [hc]; exact makeMerged_wf v val h (cfg.hashT val) r _
      · -- an empty slot: `copy_inner_insert_value`
        have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& bitAt h (maxShift - 5 * (r + 1)) != 0) = true := by
          rw [hbit, and_pow_bne]; exact hB
        have e : ((doAdd cfg (r + 1) N v h).run s).1.1 =
            ((mkInner N.nodemap (N.datamap ||| bitAt h (maxShift - 5 * (r + 1)))
              (insertAt (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) v)
              (N.cs.take N.childrenCount)).run s).1 := by
          rw [doAdd.eq_2]; dsimp only; rw [if_neg hA', if_neg hB']; rfl
        have hvl2 : (insertAt (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) v).length =
            popcount (N.datamap ||| 2 ^ D) := by
          have hle' : N.dataCountBit (bitAt h (maxShift - 5 * (r + 1))) ≤ (N.values.take N.dataCount).length := by
            rw [hoffD, hvals_len]; exact hleD
          rw [length_insertAt _ _ _ hle', hvals_len, popcount_or_pow N.datamap D hD hB0]
        rw [e, hbit]
        rw [hbit] at hvl2
        apply wf_mkInner r N.nodemap (N.datamap ||| 2 ^ D) _ _ s
        · apply Nat.eq_of_testBit_eq
          intro i
          have hi := congrArg (fun x => Nat.testBit x i) h1'
          simp only [Nat.testBit_and, Nat.zero_testBit] at hi
          simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow, Nat.zero_testBit]
          by_cases hdi : D = i
          · subst hdi; simp [hA0]
          · simp only [hdi, decide_false, Bool.or_false]; exact hi
        · exact h2'
        · exact Nat.or_lt_two_pow h3' (pow_lt32 D hD)
        · exact Nat.le_of_eq htake_len.symm
        · exact hvl2.symm
        · intro c hc
          replace hc := List.mem_of_mem_take hc
          exact htake_wf c hc

/-- ★ `champ::add` keeps a champ well formed. -/
theorem add_wf [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (v : α) (s : Al) (hw : wfNode 13 c.root = true) :
    wfNode 13 ((c.add cfg v).run s).1.root = true :=
  doAdd_wf cfg v (cfg.hashT v) 13 (Nat.le_refl _) c.root s hw

/-- `champ::empty()` is well formed. -/
theorem empty_wf : wfNode 13 (Champ.empty (α := α)).root = true := rfl

/-- ★ **Adding a value twice** changes nothing the second time: the count stays, and `get` still
returns the value (for any hash, and any equality under which the value equals its key). -/
theorem size_add_add [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (v : α) (k : κ) (s s' : Al)
    (hw : wfNode 13 c.root = true) (hk : cfg.hashK k = cfg.hashT v)
    (he : ∀ x, cfg.eqTK x k = cfg.eqTT x v) (hv : cfg.eqTK v k = true) :
    ((((c.add cfg v).run s).1).add cfg v).run s' |>.1.size = ((c.add cfg v).run s).1.size := by
  rw [size_add cfg _ v k s' (add_wf cfg c v s hw) hk he, get_add cfg c v k s hw hk hv]
  rfl

theorem get_add_add [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (v : α) (k : κ) (s s' : Al)
    (hw : wfNode 13 c.root = true) (hk : cfg.hashK k = cfg.hashT v) (hv : cfg.eqTK v k = true) :
    Champ.get cfg (((((c.add cfg v).run s).1).add cfg v).run s').1 k = some v :=
  get_add cfg _ v k s' (add_wf cfg c v s hw) hk hv

end Jank.R3.Immer.Champ

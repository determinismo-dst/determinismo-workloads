import Jank.R3.Immer.Objects

/-!
# A CHAMP law for every input: `get` after `add`

`get_add`: for every champ satisfying `wfNode` (bitmaps below `2^32`, disjoint, buffers holding
their popcounts, children well formed, collision nodes at depth 13: what `do_check_champ` and the
searches' `structure` check verify after every step), every value `v` and query `k` with
`hashK k = hashT v` and `Equal{}(v, k)`, `champ::get(k)` after `champ::add(v)` returns `v` itself.

Nothing else is assumed of the hash or the equality: other stored values may be `=` to `k` under
any hash (D12), the result is still `v`, because `get` follows `k`'s hash digits, which are `v`'s,
and every branch of `do_add` puts `v` where that walk ends (the first data slot, or the front of a
collision node). For jank's maps (`mapCfg`: `hashT (k, x) = jHash k`, `eqTK (k', _) k = jEq k' k`)
this is `(find (assoc m k x) k)` = the new pair whenever `(= k k)`; with IM1 the pair's key is the
one just passed, not the one stored before.
-/

namespace Jank.R3.Immer.Champ

variable {α κ : Type}

/-! ## Bits and popcounts -/

theorem one_shl (d : Nat) : 1 <<< d = 2 ^ d := by rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem idxAt_eq (h s : Nat) : idxAt h s = (h >>> s) &&& 31 := by
  unfold idxAt
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_shiftLeft]

theorem idxAt_lt (h s : Nat) : idxAt h s < 32 := by
  rw [idxAt_eq]
  have := @Nat.and_le_right (h >>> s) 31
  omega

theorem bitAt_eq (h s : Nat) : bitAt h s = 2 ^ idxAt h s := by
  unfold bitAt; rw [one_shl]

theorem and_two_pow' (x d : Nat) : x &&& 2 ^ d = if x.testBit d = true then 2 ^ d else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hdi : d = i
  · subst hdi
    split
    · next hx => simp [hx, Nat.testBit_two_pow]
    · next hx => simp at hx; simp [hx]
  · split <;> simp [Nat.testBit_two_pow, hdi]

theorem and_pow_bne (x d : Nat) : (x &&& 2 ^ d != 0) = x.testBit d := by
  rw [and_two_pow']
  have : 2 ^ d ≠ 0 := by have := Nat.two_pow_pos d; omega
  cases hx : x.testBit d <;> simp [this]

theorem pow_and_mask (d : Nat) : 2 ^ d &&& (2 ^ d - 1) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
  by_cases h : d = i
  · subst h; simp
  · simp [h]

theorem or_pow_mask (x d : Nat) : (x ||| 2 ^ d) &&& (2 ^ d - 1) = x &&& (2 ^ d - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h : i < d
  · have : d ≠ i := by omega
    simp [h, this]
  · simp [h]

theorem two_bits_mask (a b : Nat) (hab : a ≠ b) :
    (2 ^ a ||| 2 ^ b) &&& (2 ^ a - 1) = if b < a then 2 ^ b else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
  split
  · next h =>
    rw [Nat.testBit_two_pow]
    by_cases h1 : a = i <;> by_cases h2 : b = i <;> simp [h1, h2] <;> omega
  · next h =>
    rw [Nat.zero_testBit]
    by_cases h1 : a = i <;> by_cases h2 : b = i <;> simp [h1, h2] <;> omega

theorem popcount_zero : popcount 0 = 0 := by decide

theorem popcount_pow : ∀ b, b < 32 → popcount (2 ^ b) = 1 := by decide

theorem countP_lt {β : Type} (p q : β → Bool) : ∀ (l : List β),
    (∀ y ∈ l, p y = true → q y = true) → (∃ y ∈ l, q y = true ∧ p y = false) →
    l.countP p < l.countP q
  | [], _, ⟨_, hy, _⟩ => by simp at hy
  | a :: l, hpq, ⟨y, hy, hqy, hpy⟩ => by
    have hpq' : ∀ z ∈ l, p z = true → q z = true := fun z hz hpz => hpq z (by simp [hz]) hpz
    have hmono : l.countP p ≤ l.countP q := List.countP_mono_left hpq'
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp hy with h | h
    · subst h; simp [hqy, hpy]; omega
    · have := countP_lt p q l hpq' ⟨y, h, hqy, hpy⟩
      by_cases hpa : p a = true
      · have hqa := hpq a (by simp) hpa
        simp [hpa, hqa]; omega
      · simp only [Bool.not_eq_true] at hpa
        rw [if_neg (show ¬ p a = true by simp [hpa])]
        split <;> omega

theorem popcount_lt (x d : Nat) (hd : d < 32) (hx : x.testBit d = true) :
    popcount (x &&& (2 ^ d - 1)) < popcount x := by
  unfold popcount
  apply countP_lt
  · intro i _ hi
    simp only [Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.1
  · refine ⟨d, by simp [hd], hx, ?_⟩
    simp [Nat.testBit_and]

theorem popcount_and_le (x m : Nat) : popcount (x &&& m) ≤ popcount x := by
  unfold popcount
  apply List.countP_mono_left
  intro i _ hi
  simp only [Nat.testBit_and, Bool.and_eq_true] at hi
  exact hi.1

theorem shr_step (h r : Nat) (hr : r + 1 ≤ 13) : (h >>> (65 - 5 * (r + 1))) >>> 5 = h >>> (65 - 5 * r) := by
  rw [← Nat.shiftRight_add]
  congr 1
  omega

theorem hidx (h r : Nat) : (h >>> (65 - 5 * (r + 1))) &&& 31 = idxAt h (maxShift - 5 * (r + 1)) := by
  rw [idxAt_eq]; rfl

/-! ## Lists -/

theorem setL_getD {β : Type} (l : List β) (i : Nat) (x d : β) (h : i < l.length) : (setL l i x).getD i d = x := by
  unfold setL
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

theorem setL_getElem? {β : Type} (l : List β) (i : Nat) (x : β) (h : i < l.length) : (setL l i x)[i]? = some x := by
  unfold setL
  exact List.getElem?_set_self h

theorem insertAt_getElem? {β : Type} (l : List β) (i : Nat) (x : β) (h : i ≤ l.length) :
    (insertAt l i x)[i]? = some x := by
  unfold insertAt
  have hl : (l.take i).length = i := by simp only [List.length_take]; omega
  rw [List.append_assoc, List.getElem?_append_right (Nat.le_of_eq hl), hl, Nat.sub_self]
  simp

theorem insertAt_getD {β : Type} (l : List β) (i : Nat) (x d : β) (h : i ≤ l.length) :
    (insertAt l i x).getD i d = x := by
  rw [List.getD_eq_getElem?_getD, insertAt_getElem? l i x h]
  rfl

theorem getD_mem_take {β : Type} (l : List β) (p i : Nat) (d : β) (hp : i < p) (hl : i < l.length) :
    l.getD i d ∈ l.take p := by
  have e : l[i]? = some l[i] := List.getElem?_eq_getElem hl
  have hg : l.getD i d = l[i] := by rw [List.getD_eq_getElem?_getD, e]; rfl
  rw [hg, List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take_of_lt hp, e]⟩

/-! ## Node constructors, run -/

theorem mkInner_run (nm dm : Nat) (xs : List α) (cs : List (Node α)) (s : Al) :
    ∃ nid vv, ((mkInner nm dm xs cs).run s).1 = .inner nid 0 nm dm vv cs ∧
      (Node.inner nid 0 nm dm vv cs).values = xs := by
  cases xs with
  | nil => exact ⟨_, _, rfl, rfl⟩
  | cons x xs => exact ⟨_, _, rfl, rfl⟩

/-- Well-formedness, as the facts `do_add` and `get` use. -/
theorem wf_facts (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) :
    popcount N.nodemap ≤ N.cs.length ∧ popcount N.datamap ≤ N.values.length ∧
    ∀ c ∈ N.cs.take (popcount N.nodemap), wfNode r c = true := by
  cases N with
  | collision => simp [wfNode] at hw
  | inner id tok nm dm vals cs =>
    simp only [wfNode, Bool.and_eq_true] at hw
    obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, hd⟩, he⟩, hf⟩ := hw
    refine ⟨of_decide_eq_true hd, ?_, List.all_eq_true.mp hf⟩
    cases vals with
    | none =>
      have : dm = 0 := by simpa using he
      subst this
      simp [Node.values, Node.datamap, popcount_zero]
    | some vs =>
      exact of_decide_eq_true he

/-! ## `get` on an inner node -/

theorem getLoop_child (cfg : Cfg α κ) (k : κ) (r nid tok nm dm : Nat) (vv : Option (Vals α))
    (cs : List (Node α)) (hash d : Nat) (hhash : hash &&& 31 = d) (h1 : nm.testBit d = true) :
    getLoop cfg k (r + 1) (.inner nid tok nm dm vv cs) hash =
      getLoop cfg k r (cs.getD (popcount (nm &&& (2 ^ d - 1))) Node.dummy) (hash >>> 5) := by
  rw [getLoop.eq_2]
  dsimp only
  rw [hhash, one_shl]
  split
  · rfl
  · next hc =>
    exact absurd (by show (nm &&& 2 ^ d != 0) = true; rw [and_pow_bne]; exact h1) hc

theorem getLoop_data (cfg : Cfg α κ) (k : κ) (r nid tok nm dm : Nat) (vv : Option (Vals α))
    (cs : List (Node α)) (hash d : Nat) (x : α) (hhash : hash &&& 31 = d) (h1 : nm.testBit d = false)
    (h2 : dm.testBit d = true)
    (hval : (Node.inner nid tok nm dm vv cs).values[popcount (dm &&& (2 ^ d - 1))]? = some x)
    (hx : cfg.eqTK x k = true) :
    getLoop cfg k (r + 1) (.inner nid tok nm dm vv cs) hash = some x := by
  rw [getLoop.eq_2]
  dsimp only
  rw [hhash, one_shl]
  split
  · next hc =>
    have : (nm &&& 2 ^ d != 0) = true := hc
    rw [and_pow_bne, h1] at this
    simp at this
  · split
    · split
      · next v' heq =>
        have e := hval.symm.trans heq
        cases e
        simp [hx]
      · next heq =>
        have e := hval.symm.trans heq
        cases e
    · next hc =>
      exact absurd (by show (dm &&& 2 ^ d != 0) = true; rw [and_pow_bne]; exact h2) hc

/-! ## `make_merged` -/

theorem get_makeMerged (cfg : Cfg α κ) (k : κ) (v1 v2 : α) (h1 h2 : Nat) (hv : cfg.eqTK v1 k = true) :
    ∀ r, r ≤ 13 → ∀ s, getLoop cfg k r ((makeMerged none r v1 h1 v2 h2).run s).1 (h1 >>> (65 - 5 * r)) = some v1 := by
  intro r
  induction r with
  | zero =>
    intro _ s
    have e : ((makeMerged none 0 v1 h1 v2 h2).run s).1.collisions = [v1, v2] := rfl
    rw [getLoop.eq_1, e]
    simp [hv]
  | succ r ih =>
    intro hr s
    have hD := idxAt_lt h1 (maxShift - 5 * (r + 1))
    by_cases hc : (idxAt h1 (maxShift - 5 * (r + 1)) == idxAt h2 (maxShift - 5 * (r + 1))) = true
    · have e : ((makeMerged none (r + 1) v1 h1 v2 h2).run s).1 =
          ((mkInner (1 <<< idxAt h1 (maxShift - 5 * (r + 1))) 0 [] [((makeMerged none r v1 h1 v2 h2).run s).1]).run
            ((makeMerged none r v1 h1 v2 h2).run s).2).1 := by
        rw [makeMerged.eq_2]; dsimp only; rw [if_pos hc]; rfl
      obtain ⟨nid, vv, e2, _⟩ := mkInner_run (1 <<< idxAt h1 (maxShift - 5 * (r + 1))) 0 []
        [((makeMerged none r v1 h1 v2 h2).run s).1] ((makeMerged none r v1 h1 v2 h2).run s).2
      rw [e, e2, one_shl, getLoop_child cfg k r nid 0 (2 ^ idxAt h1 (maxShift - 5 * (r + 1))) 0 vv _ _ _
          (hidx h1 r) (by simp [Nat.testBit_two_pow]),
        pow_and_mask, popcount_zero, shr_step h1 r hr]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some]
      exact ih (by omega) _
    · have hne : idxAt h1 (maxShift - 5 * (r + 1)) ≠ idxAt h2 (maxShift - 5 * (r + 1)) := by
        intro heq; apply hc; simp [heq]
      have hD2 := idxAt_lt h2 (maxShift - 5 * (r + 1))
      generalize hA : idxAt h1 (maxShift - 5 * (r + 1)) = A at hne hD
      generalize hB : idxAt h2 (maxShift - 5 * (r + 1)) = B at hne hD2
      have e : ((makeMerged none (r + 1) v1 h1 v2 h2).run s).1 =
          ((mkInner 0 ((1 <<< A) ||| (1 <<< B)) (if A < B then [v1, v2] else [v2, v1]) []).run s).1 := by
        rw [makeMerged.eq_2]; dsimp only; rw [if_neg hc, hA, hB]; rfl
      obtain ⟨nid, vv, e2, ev⟩ := mkInner_run 0 ((1 <<< A) ||| (1 <<< B)) (if A < B then [v1, v2] else [v2, v1]) [] s
      rw [e, e2]
      simp only [one_shl] at ev ⊢
      have hh : (h1 >>> (65 - 5 * (r + 1))) &&& 31 = A := by rw [hidx]; exact hA
      refine getLoop_data cfg k r nid 0 0 (2 ^ A ||| 2 ^ B) vv [] _ A v1 hh (Nat.zero_testBit A)
        (by simp [Nat.testBit_or, Nat.testBit_two_pow]) ?_ hv
      rw [ev, two_bits_mask A B hne]
      by_cases hBA : B < A
      · rw [if_pos hBA, popcount_pow B hD2, if_neg (show ¬ A < B by omega)]; rfl
      · rw [if_neg hBA, popcount_zero, if_pos (show A < B by omega)]; rfl

/-! ## `do_add` and `get` -/

theorem get_doAdd [Inhabited α] (cfg : Cfg α κ) (k : κ) (v : α) (h : Nat) (hv : cfg.eqTK v k = true) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      getLoop cfg k r ((doAdd cfg r N v h).run s).1.1 (h >>> (65 - 5 * r)) = some v := by
  intro r
  induction r with
  | zero =>
    intro _ N s _
    have hcol : ∃ rest, ((doAdd cfg 0 N v h).run s).1.1.collisions = v :: rest := by
      rw [doAdd.eq_1]
      cases findIdx? N.collisions (fun x => cfg.eqTT x v) with
      | some pos => exact ⟨_, rfl⟩
      | none => exact ⟨_, rfl⟩
    obtain ⟨rest, hr⟩ := hcol
    rw [getLoop.eq_1, hr]
    simp [hv]
  | succ r ih =>
    intro hr N s hw
    obtain ⟨hcs, hvals, hch⟩ := wf_facts r N hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    have hh : (h >>> (65 - 5 * (r + 1))) &&& 31 = D := by rw [hidx]; exact hDdef
    by_cases hA : N.nodemap.testBit D = true
    · -- a child on the path: `copy_inner_replace` with the child's `do_add`
      have hA' : (N.nodemap &&& bitAt h (maxShift - 5 * (r + 1)) != 0) = true := by
        rw [hbit, and_pow_bne]; exact hA
      have hoff : N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))) = popcount (N.nodemap &&& (2 ^ D - 1)) := by
        unfold Node.childrenCountBit; rw [hbit]
      obtain ⟨nid, hR⟩ : ∃ nid, ((doAdd cfg (r + 1) N v h).run s).1.1 =
          .inner nid 0 N.nodemap N.datamap N.vals
            (setL (N.cs.take N.childrenCount) (N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))))
              ((doAdd cfg r (N.child (N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))))) v h).run s).1.1) := by
        rw [doAdd.eq_2]; dsimp only; rw [if_pos hA']; exact ⟨_, rfl⟩
      have hlt := popcount_lt N.nodemap D hD hA
      rw [hR, getLoop_child cfg k r nid 0 _ _ _ _ _ D hh hA, hoff, setL_getD, shr_step h r hr]
      · apply ih (by omega)
        apply hch
        exact getD_mem_take _ _ _ _ hlt (by omega)
      · rw [List.length_take]; unfold Node.childrenCount; omega
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& bitAt h (maxShift - 5 * (r + 1)) != 0) = true := by
        rw [hbit, and_pow_bne]; exact hA
      have hoffD : N.dataCountBit (bitAt h (maxShift - 5 * (r + 1))) = popcount (N.datamap &&& (2 ^ D - 1)) := by
        unfold Node.dataCountBit; rw [hbit]
      have hle := popcount_and_le N.datamap (2 ^ D - 1)
      have hlenV : (N.values.take N.dataCount).length = popcount N.datamap := by
        rw [List.length_take]; unfold Node.dataCount; omega
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& bitAt h (maxShift - 5 * (r + 1)) != 0) = true := by
          rw [hbit, and_pow_bne]; exact hB
        have hltD := popcount_lt N.datamap D hD hB
        by_cases hE : cfg.eqTT (N.values.getD (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) default) v = true
        · -- an `Equal` value in the slot: `copy_inner_replace_value` (IM1)
          have e : ((doAdd cfg (r + 1) N v h).run s).1.1 =
              ((mkInner N.nodemap N.datamap
                (setL (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) v)
                (N.cs.take N.childrenCount)).run s).1 := by
            rw [doAdd.eq_2]; dsimp only; rw [if_neg hA', if_pos hB', if_pos hE]; rfl
          obtain ⟨nid, vv, e2, ev⟩ := mkInner_run N.nodemap N.datamap
            (setL (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) v)
            (N.cs.take N.childrenCount) s
          rw [e, e2]
          refine getLoop_data cfg k r nid 0 _ _ vv _ _ D v hh hA0 hB ?_ hv
          rw [ev, hoffD]
          exact setL_getElem? _ _ _ (by omega)
        · -- another value in the slot: `make_merged` below, `copy_inner_replace_merged`
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
          obtain ⟨nid, vv, e2, _⟩ := mkInner_run (N.nodemap ||| bitAt h (maxShift - 5 * (r + 1)))
            (clearBit N.datamap (bitAt h (maxShift - 5 * (r + 1))))
            (eraseAt (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))))
            (insertAt (N.cs.take N.childrenCount) (N.childrenCountBit (bitAt h (maxShift - 5 * (r + 1))))
              ((makeMerged none r v h val (cfg.hashT val)).run s).1) ((makeMerged none r v h val (cfg.hashT val)).run s).2
          have hleN := popcount_and_le N.nodemap (2 ^ D - 1)
          rw [e, e2, hbit, getLoop_child cfg k r nid 0 (N.nodemap ||| 2 ^ D) _ vv _ _ D hh
              (by simp [Nat.testBit_or, Nat.testBit_two_pow]),
            or_pow_mask, show N.childrenCountBit (2 ^ D) = popcount (N.nodemap &&& (2 ^ D - 1)) from rfl,
            insertAt_getD, shr_step h r hr]
          · exact get_makeMerged cfg k v val h (cfg.hashT val) hv r (by omega) _
          · rw [List.length_take]; unfold Node.childrenCount; omega
      · -- an empty slot: `copy_inner_insert_value`
        have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& bitAt h (maxShift - 5 * (r + 1)) != 0) = true := by
          rw [hbit, and_pow_bne]; exact hB
        have e : ((doAdd cfg (r + 1) N v h).run s).1.1 =
            ((mkInner N.nodemap (N.datamap ||| bitAt h (maxShift - 5 * (r + 1)))
              (insertAt (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) v)
              (N.cs.take N.childrenCount)).run s).1 := by
          rw [doAdd.eq_2]; dsimp only; rw [if_neg hA', if_neg hB']; rfl
        obtain ⟨nid, vv, e2, ev⟩ := mkInner_run N.nodemap (N.datamap ||| bitAt h (maxShift - 5 * (r + 1)))
          (insertAt (N.values.take N.dataCount) (N.dataCountBit (bitAt h (maxShift - 5 * (r + 1)))) v)
          (N.cs.take N.childrenCount) s
        rw [e, e2]
        refine getLoop_data cfg k r nid 0 _ _ vv _ _ D v hh hA0 ?_ ?_ hv
        · rw [hbit]; simp [Nat.testBit_or, Nat.testBit_two_pow]
        · rw [ev, hoffD, hbit, or_pow_mask]
          exact insertAt_getElem? _ _ _ (by omega)

/-- **`get` after `add`**, for every well-formed champ: `champ::get(k)` after `champ::add(v)`
returns `v` whenever `k` hashes as `v` and `Equal{}(v, k)`. -/
theorem get_add [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (v : α) (k : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hk : cfg.hashK k = cfg.hashT v) (hv : cfg.eqTK v k = true) :
    Champ.get cfg ((c.add cfg v).run s).1 k = some v := by
  have e : ((c.add cfg v).run s).1.root = ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.1 := rfl
  have := get_doAdd cfg k v (cfg.hashT v) hv 13 (Nat.le_refl _) c.root s hw
  rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero] at this
  unfold Champ.get
  rw [e, hk]
  exact this

open Objects in
/-- jank's hash maps: `(find (assoc m k x) k)` is the pair just assoc'ed, for every well-formed
map and every key `=` to itself. -/
theorem map_get_assoc (c : Champ (Jank.Equality.V × Jank.Equality.V)) (k x : Jank.Equality.V) (s : Al)
    (hw : wfNode 13 c.root = true) (hkk : jEq k k = true) :
    Champ.get mapCfg ((c.add mapCfg (k, x)).run s).1 k = some (k, x) :=
  get_add mapCfg c (k, x) k s hw rfl hkk

open Objects in
/-- jank's hash sets: `(get (conj s x) x)` is `x` itself, for every well-formed set and every
element `=` to itself. -/
theorem set_get_conj (c : Champ Jank.Equality.V) (x : Jank.Equality.V) (s : Al)
    (hw : wfNode 13 c.root = true) (hxx : jEq x x = true) :
    Champ.get setCfg ((c.add setCfg x).run s).1 x = some x :=
  get_add setCfg c x x s hw rfl hxx

end Jank.R3.Immer.Champ

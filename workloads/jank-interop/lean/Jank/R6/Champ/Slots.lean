import Jank.R5.Core.ChampSub5

/-!
# Round 6, CHAMP: a node as 32 slots

Round 3's replica of immer's `champ.hpp` (`Jank/R3/Immer/Champ.lean`) keeps an inner node as two
bitmaps and two packed buffers: bit `d` of `nodemap` names the child at
`popcount(nodemap & (2^d - 1))`, bit `d` of `datamap` the value at `popcount(datamap & (2^d - 1))`
(node.hpp `children_count(bit)`, `data_count(bit)`). Every operation edits one bit's entry and moves
the packed buffers around it (`insertAt`, `eraseAt`, `setL` at those positions).

Here a well-formed inner node is read as a function from the 32 bits to a slot (empty, a value, a
child), once, so that each later proof is about one slot:

- `getLoop_slot`: `champ::get`'s loop body is "look at the slot of the hash's next 5 bits";
- `getLoop_walk`: `get` is `find?` of the equality over the list `walk` reaches (a collision
  node's values, one value, or nothing);
- `iter_split`: the iteration (`champ_iterator`, replica `iterNode`) of a node is a permutation of
  one slot's entries followed by the other 31 slots' entries;
- per constructor of node.hpp (`copy_inner_replace`, `_replace_value`, `_insert_value`,
  `_replace_merged`, `_replace_inline`, `_remove_value`, `make_inner_n`): the result is well formed
  and its slots are the source's except the one edited.
-/

namespace Jank.R6.Champ

open Jank.R3.Immer.Champ

variable {α κ : Type}

/-! ## Positions in the packed buffers -/

/-- `popcount(m & (2^d - 1))`: the buffer position of bit `d`'s entry. -/
abbrev pos (m d : Nat) : Nat := popcount (m &&& (2 ^ d - 1))

theorem countP_range_min (p : Nat → Bool) (d : Nat) :
    ∀ n, (List.range n).countP (fun i => p i && decide (i < d)) = (List.range (min n d)).countP p
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append, countP_range_min p d n]
    by_cases h : n < d
    · rw [show min (n + 1) d = min n d + 1 by omega, show min n d = n by omega, List.range_succ,
        List.countP_append]
      simp [h]
    · rw [show min (n + 1) d = min n d by omega]
      simp [h]

theorem pos_eq (m d : Nat) (hd : d ≤ 32) : pos m d = (List.range d).countP m.testBit := by
  unfold pos popcount
  have e : (fun i => (m &&& (2 ^ d - 1)).testBit i) = (fun i => m.testBit i && decide (i < d)) := by
    funext i; rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  rw [e, countP_range_min, show min 32 d = d by omega]

theorem popcount_eq_pos (m : Nat) : popcount m = pos m 32 := by
  rw [pos_eq m 32 (Nat.le_refl _)]; rfl

theorem pos_succ (m d : Nat) (hd : d < 32) : pos m (d + 1) = pos m d + (if m.testBit d then 1 else 0) := by
  rw [pos_eq m (d + 1) hd, pos_eq m d (by omega), List.range_succ, List.countP_append]
  simp

theorem pos_mono (m a : Nat) : ∀ b, a ≤ b → b ≤ 32 → pos m a ≤ pos m b
  | 0, h, _ => by rw [show a = 0 by omega]; exact Nat.le_refl _
  | b + 1, h, hb => by
    by_cases hab : a = b + 1
    · rw [hab]; exact Nat.le_refl _
    · have := pos_mono m a b (by omega) (by omega)
      rw [pos_succ m b (by omega)]
      omega

theorem pos_lt (m d d' : Nat) (h : d < d') (hd' : d' ≤ 32) (hm : m.testBit d = true) : pos m d < pos m d' := by
  have h1 := pos_mono m (d + 1) d' (by omega) hd'
  rw [pos_succ m d (by omega), if_pos hm] at h1
  omega

theorem pos_lt_popcount (m d : Nat) (hd : d < 32) (hm : m.testBit d = true) : pos m d < popcount m := by
  rw [popcount_eq_pos]; exact pos_lt m d 32 hd (Nat.le_refl _) hm

theorem pos_le_popcount (m d : Nat) (hd : d ≤ 32) : pos m d ≤ popcount m := by
  rw [popcount_eq_pos]; exact pos_mono m d 32 hd (Nat.le_refl _)

/-- Two set bits have different positions. -/
theorem pos_ne (m d d' : Nat) (hd : d < 32) (hd' : d' < 32) (h : d ≠ d') (hm : m.testBit d = true)
    (hm' : m.testBit d' = true) : pos m d ≠ pos m d' := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := pos_lt m d d' h (by omega) hm; omega
  · have := pos_lt m d' d h (by omega) hm'; omega

theorem pos_or (m D d : Nat) (hD : D < 32) (hd : d ≤ 32) (hm : m.testBit D = false) :
    pos (m ||| 2 ^ D) d = pos m d + (if D < d then 1 else 0) := by
  rw [pos_eq _ d hd, pos_eq m d hd]
  have e : List.countP (m ||| 2 ^ D).testBit (List.range d) =
      List.countP (fun i => m.testBit i || decide (D = i)) (List.range d) := by
    apply List.countP_congr
    intro i _
    rw [Nat.testBit_or, Nat.testBit_two_pow]
  rw [e]
  by_cases h : D < d
  · rw [if_pos h]; exact countP_range_or (fun i => m.testBit i) D hm d h
  · rw [if_neg h, Nat.add_zero]
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    have : D ≠ i := by omega
    simp [this]

theorem pos_clear (m D d : Nat) (hD : D < 32) (hd : d ≤ 32) (hm : m.testBit D = true) :
    pos (clearBit m (2 ^ D)) d + (if D < d then 1 else 0) = pos m d := by
  rw [pos_eq _ d hd, pos_eq m d hd]
  have e : (List.range d).countP (fun i => (clearBit m (2 ^ D)).testBit i) =
      (List.range d).countP (fun i => m.testBit i && !decide (D = i)) := by
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [clearBit_testBit m D i (by omega)]
  rw [e]
  by_cases h : D < d
  · rw [if_pos h, ← countP_range_or (fun i => m.testBit i && !decide (D = i)) D (by simp) d h]
    apply List.countP_congr
    intro i _
    by_cases hi : D = i
    · subst hi; simp [hm]
    · simp [hi]
  · rw [if_neg h, Nat.add_zero]
    apply List.countP_congr
    intro i hi
    rw [List.mem_range] at hi
    have : D ≠ i := by omega
    simp [this]

theorem testBit_or_ne (m D d : Nat) (h : D ≠ d) : (m ||| 2 ^ D).testBit d = m.testBit d := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]; simp [h]

theorem testBit_or_self (m D : Nat) : (m ||| 2 ^ D).testBit D = true := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]; simp

theorem testBit_clear_ne (m D d : Nat) (hd : d < 32) (h : D ≠ d) : (clearBit m (2 ^ D)).testBit d = m.testBit d := by
  rw [clearBit_testBit m D d hd]; simp [h]

theorem testBit_clear_self (m D : Nat) (hD : D < 32) : (clearBit m (2 ^ D)).testBit D = false := by
  rw [clearBit_testBit m D D hD]; simp

theorem clear_lt (m D : Nat) (hm : m < 2 ^ 32) : clearBit m (2 ^ D) < 2 ^ 32 :=
  Nat.lt_of_le_of_lt Nat.and_le_left hm

/-! ## Lists at positions -/

section lists
variable {β : Type}

theorem getD_take (L : List β) (n j : Nat) (d : β) (h : j < n) : (L.take n).getD j d = L.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem getD_setL_ne (L : List β) (i j : Nat) (a d : β) (h : i ≠ j) : (setL L i a).getD j d = L.getD j d := by
  unfold setL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getD_setL_self (L : List β) (i : Nat) (a d : β) (h : i < L.length) : (setL L i a).getD i d = a :=
  setL_getD L i a d h

theorem getD_insertAt_lt (L : List β) (i j : Nat) (a d : β) (h : j < i) (hi : i ≤ L.length) :
    (insertAt L i a).getD j d = L.getD j d := by
  unfold insertAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h]

theorem getD_insertAt_ge (L : List β) (i j : Nat) (a d : β) (h : i ≤ j) (hi : i ≤ L.length) :
    (insertAt L i a).getD (j + 1) d = L.getD j d := by
  unfold insertAt
  have hl : (L.take i).length = i := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by omega), hl, show j + 1 - i = (j - i) + 1 by omega,
    List.singleton_append, List.getElem?_cons_succ, List.getElem?_drop, show i + (j - i) = j by omega]

theorem getD_eraseAt_lt (L : List β) (i j : Nat) (d : β) (h : j < i) :
    (eraseAt L i).getD j d = L.getD j d := by
  unfold eraseAt
  by_cases hi : i ≤ L.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h]
  · rw [List.drop_eq_nil_of_le (by omega), List.append_nil, getD_take L i j d h]

theorem getD_eraseAt_ge (L : List β) (i j : Nat) (d : β) (h : i ≤ j) (hi : i < L.length) :
    (eraseAt L i).getD j d = L.getD (j + 1) d := by
  unfold eraseAt
  have hl : (L.take i).length = i := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hl, List.getElem?_drop, show i + 1 + (j - i) = j + 1 by omega]

theorem mem_eraseAt {y : β} (L : List β) (i : Nat) (h : y ∈ eraseAt L i) : y ∈ L := by
  unfold eraseAt at h
  rcases List.mem_append.mp h with h | h
  · exact List.mem_of_mem_take h
  · exact List.mem_of_mem_drop h

theorem length_take_of_le (L : List β) (n : Nat) (h : n ≤ L.length) : (L.take n).length = n := by
  simp; omega

/-- `l ~ l[i] :: eraseAt l i`. -/
theorem perm_eraseAt (L : List β) (i : Nat) (d : β) (h : i < L.length) :
    L.Perm (L.getD i d :: eraseAt L i) := by
  unfold eraseAt
  have e : L = L.take i ++ L.drop i := (List.take_append_drop i L).symm
  have hd : L.drop i = L.getD i d :: L.drop (i + 1) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, List.drop_eq_getElem_cons h]
    rfl
  conv => lhs; rw [e, hd]
  exact List.perm_middle

theorem perm_insertAt (L : List β) (i : Nat) (a : β) : (insertAt L i a).Perm (a :: L) := by
  unfold insertAt
  have := (List.perm_middle (a := a) (l₁ := L.take i) (l₂ := L.drop i))
  rw [List.take_append_drop] at this
  simpa using this

theorem perm_setL (L : List β) (i : Nat) (a d : β) (h : i < L.length) :
    (setL L i a).Perm (a :: eraseAt L i) := by
  have h' : i < (setL L i a).length := by rw [length_setL]; exact h
  have p := perm_eraseAt (setL L i a) i d h'
  rw [getD_setL_self L i a d h] at p
  have e : eraseAt (setL L i a) i = eraseAt L i := by
    unfold eraseAt setL
    rw [List.take_set_of_le (Nat.le_refl _), List.drop_set_of_lt (by omega)]
  rw [e] at p
  exact p

end lists

/-! ## Slots -/

inductive Slot (α : Type) where
  | empty
  | data (x : α)
  | child (c : Node α)

/-- Bit `d` of an inner node: its child, its value, or nothing (`get`'s three branches). -/
def slot [Inhabited α] (N : Node α) (d : Nat) : Slot α :=
  if N.nodemap.testBit d then .child (N.cs.getD (pos N.nodemap d) Node.dummy)
  else if N.datamap.testBit d then .data (N.values.getD (pos N.datamap d) default)
  else .empty

/-- The values a slot holds, in iteration order. -/
def slotL (r : Nat) : Slot α → List α
  | .empty => []
  | .data x => [x]
  | .child c => iterNode r c

/-- Every child of a well-formed inner node is well formed. -/
theorem slot_child_wf [Inhabited α] (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (d : Nat) (hd : d < 32)
    (c : Node α) (hc : slot N d = .child c) : wfNode r c = true := by
  obtain ⟨hcs, _, hch⟩ := wf_facts r N hw
  unfold slot at hc
  split at hc
  · next hm =>
    cases hc
    exact hch _ (getD_mem_take _ _ _ _ (pos_lt_popcount _ d hd hm) (by have := pos_lt_popcount _ d hd hm; omega))
  · split at hc <;> cases hc

/-- `champ::get`'s loop body at an inner node is a look at one slot. -/
theorem getLoop_slot [Inhabited α] (cfg : Cfg α κ) (k : κ) (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true)
    (hash : Nat) :
    getLoop cfg k (r + 1) N hash = (match slot N (hash &&& 31) with
      | .child c => getLoop cfg k r c (hash >>> 5)
      | .data x => if cfg.eqTK x k then some x else none
      | .empty => none) := by
  obtain ⟨_, hvals, _⟩ := wf_facts r N hw
  rw [getLoop.eq_2]
  dsimp only
  have hd : hash &&& 31 < 32 := by have := @Nat.and_le_right hash 31; omega
  generalize hash &&& 31 = d at hd ⊢
  rw [one_shl]
  unfold slot
  by_cases hA : N.nodemap.testBit d = true
  · rw [if_pos (show (N.nodemap &&& 2 ^ d != 0) = true by rw [and_pow_bne]; exact hA), if_pos hA]
    rfl
  · rw [if_neg (show ¬ (N.nodemap &&& 2 ^ d != 0) = true by rw [and_pow_bne]; exact hA), if_neg hA]
    by_cases hB : N.datamap.testBit d = true
    · rw [if_pos (show (N.datamap &&& 2 ^ d != 0) = true by rw [and_pow_bne]; exact hB), if_pos hB]
      have hlt := pos_lt_popcount _ d hd hB
      rw [show N.dataCountBit (2 ^ d) = pos N.datamap d from rfl, getElem?_of_lt _ _ (by omega)]
    · rw [if_neg (show ¬ (N.datamap &&& 2 ^ d != 0) = true by rw [and_pow_bne]; exact hB), if_neg hB]


/-! ## `get` as `find?` over the slot it walks to -/

/-- The values `get`'s walk reaches for a hash: a collision node's, one value, or none. -/
def walk [Inhabited α] : (r : Nat) → Node α → Nat → List α
  | 0, N, _ => N.collisions
  | r + 1, N, h => match slot N (h &&& 31) with
    | .child c => walk r c (h >>> 5)
    | .data x => [x]
    | .empty => []

theorem and31_lt (h : Nat) : h &&& 31 < 32 := by have := @Nat.and_le_right h 31; omega

/-- `get` is the first value of its walk that `Equal` accepts. -/
theorem getLoop_walk [Inhabited α] (cfg : Cfg α κ) (k : κ) :
    ∀ r (N : Node α) h, wfNode r N = true → getLoop cfg k r N h = (walk r N h).find? (fun x => cfg.eqTK x k)
  | 0, N, h, _ => by rw [getLoop.eq_1, walk.eq_1]
  | r + 1, N, h, hw => by
    rw [getLoop_slot cfg k r N hw h, walk.eq_2]
    generalize hs : slot N (h &&& 31) = sl
    cases sl with
    | empty => rfl
    | data x => dsimp only; rw [List.find?_cons, List.find?_nil]; cases cfg.eqTK x k <;> rfl
    | child c => exact getLoop_walk cfg k r c _ (slot_child_wf r N hw _ (and31_lt h) c hs)

/-! ## Iteration as slots -/

theorem map_getD_filter {β : Type} (m : Nat) (L : List β) (dflt : β) :
    ∀ n, n ≤ 32 → (List.range n).countP m.testBit ≤ L.length →
      ((List.range n).filter m.testBit).map (fun d => L.getD (pos m d) dflt) =
        L.take ((List.range n).countP m.testBit)
  | 0, _, _ => by simp
  | n + 1, hn, hl => by
    have hc : (List.range (n + 1)).countP m.testBit =
        (List.range n).countP m.testBit + (if m.testBit n then 1 else 0) := by
      rw [List.range_succ, List.countP_append]; simp
    have hl' : (List.range n).countP m.testBit + (if m.testBit n then 1 else 0) ≤ L.length := hc ▸ hl
    have hl0 : (List.range n).countP m.testBit ≤ L.length := by split at hl' <;> omega
    rw [hc, List.range_succ, List.filter_append, List.map_append, map_getD_filter m L dflt n (by omega) hl0]
    by_cases hb : m.testBit n = true
    · have hl1 : (List.range n).countP m.testBit + 1 ≤ L.length := by rw [if_pos hb] at hl'; exact hl'
      rw [if_pos hb, List.take_add_one]
      simp only [List.filter_cons, List.filter_nil, hb, if_true, List.map_cons, List.map_nil]
      rw [pos_eq m n (by omega), List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    · have hb' : m.testBit n = false := by simpa using hb
      rw [if_neg hb]
      simp [hb']

theorem flatMap_congr' {β γ : Type} (f g : β → List γ) :
    ∀ (l : List β), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      flatMap_congr' f g l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem perm_flatMap_split {β : Type} (F : Nat → List β) (D : Nat) :
    ∀ (l : List Nat), D ∈ l → l.Nodup → (l.flatMap F).Perm (F D ++ (l.filter (· != D)).flatMap F)
  | [], h, _ => by simp at h
  | a :: l, h, hn => by
    rw [List.nodup_cons] at hn
    by_cases ha : a = D
    · subst ha
      have e : (l.filter (· != a)) = l := by
        rw [List.filter_eq_self]
        intro b hb
        have : b ≠ a := fun e => hn.1 (e ▸ hb)
        simpa using this
      simp [e]
    · have hD : D ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm ha
        · exact h
      have ih := perm_flatMap_split F D l hD hn.2
      have ha' : (a != D) = true := by simpa using ha
      rw [List.flatMap_cons, List.filter_cons, if_pos ha', List.flatMap_cons]
      exact (ih.append_left (F a)).trans (List.perm_append_comm_assoc _ _ _)

/-- The other 31 slots' values. -/
def rest [Inhabited α] (r : Nat) (N : Node α) (D : Nat) : List α :=
  ((List.range 32).filter (· != D)).flatMap (fun d => slotL r (slot N d))

theorem rest_congr [Inhabited α] (r : Nat) (N N' : Node α) (D : Nat)
    (h : ∀ d, d < 32 → d ≠ D → slot N' d = slot N d) : rest r N' D = rest r N D := by
  unfold rest
  apply flatMap_congr'
  intro d hd
  rw [List.mem_filter, List.mem_range] at hd
  rw [h d hd.1 (by simpa using hd.2)]

theorem flatMap_slots [Inhabited α] (r : Nat) (N : Node α) :
    ∀ (l : List Nat), (∀ d ∈ l, ¬ (N.nodemap.testBit d = true ∧ N.datamap.testBit d = true)) →
      (l.flatMap (fun d => slotL r (slot N d))).Perm
        ((l.filter N.datamap.testBit).map (fun d => N.values.getD (pos N.datamap d) default) ++
          ((l.filter N.nodemap.testBit).map (fun d => N.cs.getD (pos N.nodemap d) Node.dummy)).flatMap (iterNode r))
  | [], _ => by simp
  | d :: l, hdis => by
    have ih := flatMap_slots r N l (fun d' hd' => hdis d' (List.mem_cons_of_mem _ hd'))
    have hd := hdis d (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    by_cases hA : N.nodemap.testBit d = true
    · have hB : N.datamap.testBit d = false := by
        cases hb : N.datamap.testBit d
        · rfl
        · exact absurd ⟨hA, hb⟩ hd
      have e : slot N d = .child (N.cs.getD (pos N.nodemap d) Node.dummy) := by unfold slot; rw [if_pos hA]
      rw [e, List.filter_cons, List.filter_cons]
      simp only [hA, hB, if_true, Bool.false_eq_true, if_false, List.map_cons, List.flatMap_cons, slotL]
      exact (ih.append_left _).trans (List.perm_append_comm_assoc _ _ _)
    · have hA' : N.nodemap.testBit d = false := by simpa using hA
      by_cases hB : N.datamap.testBit d = true
      · have e : slot N d = .data (N.values.getD (pos N.datamap d) default) := by
          unfold slot; rw [if_neg hA, if_pos hB]
        rw [e, List.filter_cons, List.filter_cons]
        simp only [hA', hB, if_true, Bool.false_eq_true, if_false, List.map_cons, slotL, List.cons_append,
          List.nil_append]
        exact ih.cons _
      · have hB' : N.datamap.testBit d = false := by simpa using hB
        have e : slot N d = .empty := by unfold slot; rw [if_neg hA, if_neg hB]
        rw [e, List.filter_cons, List.filter_cons]
        simp only [hA', hB', Bool.false_eq_true, if_false, slotL, List.nil_append]
        exact ih

theorem disjoint_bits (a b : Nat) (h : a &&& b = 0) (d : Nat) : ¬ (a.testBit d = true ∧ b.testBit d = true) := by
  intro ⟨ha, hb⟩
  have := congrArg (fun x => Nat.testBit x d) h
  simp [Nat.testBit_and, ha, hb] at this

/-- ★ The iteration of a well-formed inner node is, up to order, its 32 slots' values. -/
theorem iter_slots [Inhabited α] (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) :
    (iterNode (r + 1) N).Perm ((List.range 32).flatMap (fun d => slotL r (slot N d))) := by
  obtain ⟨hcs, hvals, _⟩ := wf_facts r N hw
  obtain ⟨nid, tok, nm, dm, v, cs, hN, h1, _, _, _, _, _⟩ := wf_inner_facts r N hw
  have hdis : ∀ d ∈ List.range 32, ¬ (N.nodemap.testBit d = true ∧ N.datamap.testBit d = true) := by
    intro d _; subst hN; exact disjoint_bits nm dm h1 d
  refine List.Perm.trans ?_ (flatMap_slots r N (List.range 32) hdis).symm
  rw [iterNode.eq_2]
  have ev := map_getD_filter N.datamap N.values default 32 (Nat.le_refl _) hvals
  have ec := map_getD_filter N.nodemap N.cs Node.dummy 32 (Nat.le_refl _) hcs
  rw [ev, ec]
  rfl

theorem iter_split [Inhabited α] (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (D : Nat) (hD : D < 32) :
    (iterNode (r + 1) N).Perm (slotL r (slot N D) ++ rest r N D) :=
  (iter_slots r N hw).trans
    (perm_flatMap_split _ D (List.range 32) (List.mem_range.mpr hD) List.nodup_range)

theorem mem_iter_of_slot [Inhabited α] (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (d : Nat) (hd : d < 32)
    (x : α) (hx : x ∈ slotL r (slot N d)) : x ∈ iterNode (r + 1) N :=
  (iter_split r N hw d hd).symm.subset (List.mem_append_left _ hx)

/-- Every value `get`'s walk reaches is stored. -/
theorem walk_sub [Inhabited α] : ∀ r (N : Node α) h, wfNode r N = true → ∀ x ∈ walk r N h, x ∈ iterNode r N
  | 0, N, h, _, x, hx => by rw [walk.eq_1] at hx; rw [iterNode.eq_1]; exact hx
  | r + 1, N, h, hw, x, hx => by
    rw [walk.eq_2] at hx
    generalize hs : slot N (h &&& 31) = sl at hx
    have hd := and31_lt h
    cases sl with
    | empty => cases hx
    | data y =>
      apply mem_iter_of_slot r N hw _ hd
      rw [hs]; exact hx
    | child c =>
      apply mem_iter_of_slot r N hw _ hd
      rw [hs]
      exact walk_sub r c _ (slot_child_wf r N hw _ hd c hs) x hx


/-! ## Node constructors, as edits of one slot -/

theorem slot_inner [Inhabited α] (nid tok nm dm : Nat) (vv : Option (Vals α)) (cs : List (Node α)) (d : Nat) :
    slot (.inner nid tok nm dm vv cs) d = if nm.testBit d then .child (cs.getD (pos nm d) Node.dummy)
      else if dm.testBit d then .data ((Node.inner nid tok nm dm vv cs).values.getD (pos dm d) default)
      else .empty := rfl

theorem slot_mkInner [Inhabited α] (nm dm : Nat) (xs : List α) (cs : List (Node α)) (s : Al) (d : Nat) :
    slot ((mkInner nm dm xs cs).run s).1 d = if nm.testBit d then .child (cs.getD (pos nm d) Node.dummy)
      else if dm.testBit d then .data (xs.getD (pos dm d) default) else .empty := by
  obtain ⟨nid, vv, e, ev⟩ := mkInner_run nm dm xs cs s
  rw [e, slot_inner, ev]

theorem values_vals (N : Node α) (a b c d : Nat) (e : List (Node α)) :
    (Node.inner a b c d N.vals e).values = N.values := by
  cases N with
  | inner _ _ _ _ v _ => cases v <;> rfl
  | collision => rfl

/-- `N'` is well formed and has `N`'s slots except slot `D`, which is `X`. -/
def Edit [Inhabited α] (r : Nat) (N N' : Node α) (D : Nat) (X : Slot α) : Prop :=
  wfNode (r + 1) N' = true ∧ ∀ d, d < 32 → slot N' d = if d = D then X else slot N d

/-- The parts of a well-formed inner node. -/
theorem wf_parts (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) :
    N.nodemap &&& N.datamap = 0 ∧ N.nodemap < 2 ^ 32 ∧ N.datamap < 2 ^ 32 ∧
      popcount N.nodemap ≤ N.cs.length ∧ popcount N.datamap ≤ N.values.length ∧
      valsOk N.datamap N.vals ∧ (∀ c ∈ N.cs.take (popcount N.nodemap), wfNode r c = true) ∧
      N = .inner N.id N.tok N.nodemap N.datamap N.vals N.cs := by
  obtain ⟨_, hvals, _⟩ := wf_facts r N hw
  obtain ⟨nid, tok, nm, dm, v, cs, hN, h1, h2, h3, h4, h5, h6⟩ := wf_inner_facts r N hw
  subst hN
  exact ⟨h1, h2, h3, h4, hvals, h5, h6, rfl⟩

section helpers
variable {β : Type}

theorem getD_take_pos (m d : Nat) (L : List β) (dflt : β) (hd : d < 32) (hm : m.testBit d = true) :
    (L.take (popcount m)).getD (pos m d) dflt = L.getD (pos m d) dflt :=
  getD_take L _ _ dflt (pos_lt_popcount m d hd hm)

theorem getD_setL_pos (m D d : Nat) (L : List β) (a dflt : β) (hD : D < 32) (hd : d < 32) (hne : d ≠ D)
    (hmD : m.testBit D = true) (hm : m.testBit d = true) :
    (setL (L.take (popcount m)) (pos m D) a).getD (pos m d) dflt = L.getD (pos m d) dflt := by
  rw [getD_setL_ne _ _ _ _ _ (pos_ne m D d hD hd (Ne.symm hne) hmD hm), getD_take_pos m d L dflt hd hm]

theorem getD_insertAt_pos (m D d : Nat) (L : List β) (a dflt : β) (hD : D < 32) (hd : d < 32) (hne : d ≠ D)
    (hmD : m.testBit D = false) (hm : m.testBit d = true) (hl : popcount m ≤ L.length) :
    (insertAt (L.take (popcount m)) (pos m D) a).getD (pos (m ||| 2 ^ D) d) dflt = L.getD (pos m d) dflt := by
  have hlen : pos m D ≤ (L.take (popcount m)).length := by
    rw [length_take_of_le L _ hl]; exact pos_le_popcount m D (by omega)
  rw [pos_or m D d hD (by omega) hmD]
  by_cases h : D < d
  · rw [if_pos h, getD_insertAt_ge _ _ _ _ _ (pos_mono m D d (by omega) (by omega)) hlen,
      getD_take_pos m d L dflt hd hm]
  · rw [if_neg h, Nat.add_zero, getD_insertAt_lt _ _ _ _ _ (pos_lt m d D (by omega) (by omega) hm) hlen,
      getD_take_pos m d L dflt hd hm]

theorem getD_insertAt_self (m D : Nat) (L : List β) (a dflt : β) (hD : D < 32) (hmD : m.testBit D = false)
    (hl : popcount m ≤ L.length) :
    (insertAt (L.take (popcount m)) (pos m D) a).getD (pos (m ||| 2 ^ D) D) dflt = a := by
  rw [pos_or m D D hD (by omega) hmD, if_neg (Nat.lt_irrefl D), Nat.add_zero]
  apply insertAt_getD
  rw [length_take_of_le L _ hl]; exact pos_le_popcount m D (by omega)

theorem getD_eraseAt_pos (m D d : Nat) (L : List β) (dflt : β) (hD : D < 32) (hd : d < 32) (hne : d ≠ D)
    (hmD : m.testBit D = true) (hm : m.testBit d = true) (hl : popcount m ≤ L.length) :
    (eraseAt (L.take (popcount m)) (pos m D)).getD (pos (clearBit m (2 ^ D)) d) dflt = L.getD (pos m d) dflt := by
  have hc := pos_clear m D d hD (by omega) hmD
  have hlen : pos m D < (L.take (popcount m)).length := by
    rw [length_take_of_le L _ hl]; exact pos_lt_popcount m D hD hmD
  by_cases h : D < d
  · rw [if_pos h] at hc
    have hge : pos m D ≤ pos (clearBit m (2 ^ D)) d := by
      have := pos_lt m D d h (by omega) hmD; omega
    rw [getD_eraseAt_ge _ _ _ _ hge hlen, hc, getD_take_pos m d L dflt hd hm]
  · rw [if_neg h, Nat.add_zero] at hc
    have hlt : pos (clearBit m (2 ^ D)) d < pos m D := by
      have := pos_lt m d D (by omega) (by omega) hm; omega
    rw [getD_eraseAt_lt _ _ _ _ hlt, hc, getD_take_pos m d L dflt hd hm]

end helpers

theorem disjoint_of_bits (a b : Nat) (h : ∀ i, ¬ (a.testBit i = true ∧ b.testBit i = true)) : a &&& b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  have := h i
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem clearBit_testBit' (m D i : Nat) (hm : m < 2 ^ 32) :
    (clearBit m (2 ^ D)).testBit i = (m.testBit i && !decide (D = i)) := by
  by_cases hi : i < 32
  · exact clearBit_testBit m D i hi
  · have h0 : m.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
    have h1 : (clearBit m (2 ^ D)).testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (clear_lt m D hm) (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h0, h1]; rfl

theorem bits_disjoint (nm dm : Nat) (h : nm &&& dm = 0) (i : Nat) (hn : nm.testBit i = true) : dm.testBit i = false := by
  cases hd : dm.testBit i
  · rfl
  · exact absurd ⟨hn, hd⟩ (disjoint_bits nm dm h i)

/-- `copy_inner_replace(src, offset, child)` at a child slot. -/
theorem edit_replace [Inhabited α] (r : Nat) (N c' : Node α) (D : Nat) (s : Al) (hw : wfNode (r + 1) N = true)
    (hD : D < 32) (hA : N.nodemap.testBit D = true) (hc : wfNode r c' = true) :
    Edit r N ((copyInnerReplace N (pos N.nodemap D) c').run s).1 D (.child c') := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hlen : (N.cs.take (popcount N.nodemap)).length = popcount N.nodemap := length_take_of_le _ _ h4
  have e : ((copyInnerReplace N (pos N.nodemap D) c').run s).1 =
      .inner s.next 0 N.nodemap N.datamap N.vals (setL (N.cs.take (popcount N.nodemap)) (pos N.nodemap D) c') := rfl
  rw [e]
  constructor
  · apply wf_inner_intro r _ 0 _ _ _ _ h1 h2 h3 (by rw [length_setL, hlen]; exact Nat.le_refl _) h5'
    intro c hcm
    rcases mem_setL _ _ _ _ (List.mem_of_mem_take hcm) with hcm | hcm
    · exact h6 c hcm
    · rw [hcm]; exact hc
  · intro d hd
    have ev : (Node.inner s.next 0 N.nodemap N.datamap N.vals
        (setL (N.cs.take (popcount N.nodemap)) (pos N.nodemap D) c')).values = N.values := values_vals N _ _ _ _ _
    rw [slot_inner, ev]
    by_cases hdD : d = D
    · subst hdD
      rw [if_pos hA, if_pos rfl, getD_setL_self _ _ _ _ (by rw [hlen]; exact pos_lt_popcount _ d hd hA)]
    · rw [if_neg hdD]
      unfold slot
      by_cases hm : N.nodemap.testBit d = true
      · rw [if_pos hm, if_pos hm, getD_setL_pos N.nodemap D d N.cs c' Node.dummy hD hd hdD hA hm]
      · rw [if_neg hm, if_neg hm]

/-- `copy_inner_replace_value(src, offset, v)` at a data slot. -/
theorem edit_replaceValue [Inhabited α] (r : Nat) (N : Node α) (v : α) (D : Nat) (s : Al)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hA : N.nodemap.testBit D = false)
    (hB : N.datamap.testBit D = true) :
    Edit r N ((copyInnerReplaceValue N (pos N.datamap D) v).run s).1 D (.data v) := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hlenV : (N.values.take (popcount N.datamap)).length = popcount N.datamap := length_take_of_le _ _ h5
  have hlenC : (N.cs.take (popcount N.nodemap)).length = popcount N.nodemap := length_take_of_le _ _ h4
  have e : ((copyInnerReplaceValue N (pos N.datamap D) v).run s).1 =
      ((mkInner N.nodemap N.datamap (setL (N.values.take (popcount N.datamap)) (pos N.datamap D) v)
        (N.cs.take (popcount N.nodemap))).run s).1 := rfl
  rw [e]
  constructor
  · apply wf_mkInner r _ _ _ _ s h1 h2 h3 (by rw [hlenC]; exact Nat.le_refl _) (by rw [length_setL, hlenV])
    intro c hcm
    exact h6 c (by rw [List.take_take, Nat.min_self] at hcm; exact hcm)
  · intro d hd
    rw [slot_mkInner]
    by_cases hdD : d = D
    · subst hdD
      rw [if_neg (by simp [hA]), if_pos hB, if_pos rfl,
        getD_setL_self _ _ _ _ (by rw [hlenV]; exact pos_lt_popcount _ d hd hB)]
    · rw [if_neg hdD]
      unfold slot
      by_cases hm : N.nodemap.testBit d = true
      · rw [if_pos hm, if_pos hm, getD_take_pos _ d N.cs _ hd hm]
      · rw [if_neg hm, if_neg hm]
        by_cases hb : N.datamap.testBit d = true
        · rw [if_pos hb, if_pos hb, getD_setL_pos N.datamap D d N.values v default hD hd hdD hB hb]
        · rw [if_neg hb, if_neg hb]

/-- `copy_inner_insert_value(src, bit, v)` at an empty slot. -/
theorem edit_insertValue [Inhabited α] (r : Nat) (N : Node α) (v : α) (D : Nat) (s : Al)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hA : N.nodemap.testBit D = false)
    (hB : N.datamap.testBit D = false) :
    Edit r N ((copyInnerInsertValue N (2 ^ D) v).run s).1 D (.data v) := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hlenV : (N.values.take (popcount N.datamap)).length = popcount N.datamap := length_take_of_le _ _ h5
  have hlenC : (N.cs.take (popcount N.nodemap)).length = popcount N.nodemap := length_take_of_le _ _ h4
  have e : ((copyInnerInsertValue N (2 ^ D) v).run s).1 =
      ((mkInner N.nodemap (N.datamap ||| 2 ^ D) (insertAt (N.values.take (popcount N.datamap)) (pos N.datamap D) v)
        (N.cs.take (popcount N.nodemap))).run s).1 := rfl
  rw [e]
  constructor
  · apply wf_mkInner r _ _ _ _ s
    · apply disjoint_of_bits
      intro i ⟨ha, hb⟩
      rw [Nat.testBit_or, Nat.testBit_two_pow] at hb
      by_cases hi : D = i
      · subst hi; rw [hA] at ha; cases ha
      · simp [hi] at hb; exact disjoint_bits _ _ h1 i ⟨ha, hb⟩
    · exact h2
    · exact Nat.or_lt_two_pow h3 (pow_lt32 D hD)
    · rw [hlenC]; exact Nat.le_refl _
    · rw [length_insertAt _ _ _ (by rw [hlenV]; exact pos_le_popcount _ D (by omega)), hlenV,
        popcount_or_pow _ D hD hB]
    · intro c hcm
      exact h6 c (by rw [List.take_take, Nat.min_self] at hcm; exact hcm)
  · intro d hd
    rw [slot_mkInner]
    by_cases hdD : d = D
    · subst hdD
      rw [if_neg (by simp [hA]), if_pos (testBit_or_self _ _), if_pos rfl,
        getD_insertAt_self _ d N.values v default hD hB h5]
    · rw [if_neg hdD, testBit_or_ne _ _ _ (Ne.symm hdD)]
      unfold slot
      by_cases hm : N.nodemap.testBit d = true
      · rw [if_pos hm, if_pos hm, getD_take_pos _ d N.cs _ hd hm]
      · rw [if_neg hm, if_neg hm]
        by_cases hb : N.datamap.testBit d = true
        · rw [if_pos hb, if_pos hb, getD_insertAt_pos N.datamap D d N.values v default hD hd hdD hB hb h5]
        · rw [if_neg hb, if_neg hb]


/-- `copy_inner_replace_merged(src, bit, voffset, node)`: a data slot becomes a child. -/
theorem edit_replaceMerged [Inhabited α] (r : Nat) (N m : Node α) (D : Nat) (s : Al)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hA : N.nodemap.testBit D = false)
    (hB : N.datamap.testBit D = true) (hm : wfNode r m = true) :
    Edit r N ((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D) m).run s).1 D (.child m) := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hlenV : (N.values.take (popcount N.datamap)).length = popcount N.datamap := length_take_of_le _ _ h5
  have hlenC : (N.cs.take (popcount N.nodemap)).length = popcount N.nodemap := length_take_of_le _ _ h4
  have e : ((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D) m).run s).1 =
      ((mkInner (N.nodemap ||| 2 ^ D) (clearBit N.datamap (2 ^ D))
        (eraseAt (N.values.take (popcount N.datamap)) (pos N.datamap D))
        (insertAt (N.cs.take (popcount N.nodemap)) (pos N.nodemap D) m)).run s).1 := rfl
  rw [e]
  have hins : (insertAt (N.cs.take (popcount N.nodemap)) (pos N.nodemap D) m).length = popcount N.nodemap + 1 :=
    by rw [length_insertAt _ _ _ (by rw [hlenC]; exact pos_le_popcount _ D (by omega)), hlenC]
  constructor
  · apply wf_mkInner r _ _ _ _ s
    · apply disjoint_of_bits
      intro i ⟨ha, hb⟩
      rw [Nat.testBit_or, Nat.testBit_two_pow] at ha
      rw [clearBit_testBit' _ D i h3] at hb
      by_cases hi : D = i
      · subst hi; simp at hb
      · simp [hi] at ha hb; exact disjoint_bits _ _ h1 i ⟨ha, hb⟩
    · exact Nat.or_lt_two_pow h2 (pow_lt32 D hD)
    · exact clear_lt _ D h3
    · rw [hins, popcount_or_pow _ D hD hA]; exact Nat.le_refl _
    · have := popcount_clear _ D hD hB
      have := length_eraseAt (N.values.take (popcount N.datamap)) (pos N.datamap D)
        (by rw [hlenV]; exact pos_lt_popcount _ D hD hB)
      omega
    · intro c hcm
      rcases mem_insertAt _ _ _ _ (List.mem_of_mem_take hcm) with hcm | hcm
      · exact h6 c hcm
      · rw [hcm]; exact hm
  · intro d hd
    rw [slot_mkInner]
    by_cases hdD : d = D
    · subst hdD
      rw [if_pos (testBit_or_self _ _), if_pos rfl, getD_insertAt_self _ d N.cs m Node.dummy hD hA h4]
    · rw [if_neg hdD, testBit_or_ne _ _ _ (Ne.symm hdD), testBit_clear_ne _ _ _ hd (Ne.symm hdD)]
      unfold slot
      by_cases hn : N.nodemap.testBit d = true
      · rw [if_pos hn, if_pos hn, getD_insertAt_pos N.nodemap D d N.cs m Node.dummy hD hd hdD hA hn h4]
      · rw [if_neg hn, if_neg hn]
        by_cases hb : N.datamap.testBit d = true
        · rw [if_pos hb, if_pos hb, getD_eraseAt_pos N.datamap D d N.values default hD hd hdD hB hb h5]
        · rw [if_neg hb, if_neg hb]

/-- `copy_inner_replace_inline(src, bit, noffset, value)`: a child slot becomes a value. -/
theorem edit_replaceInline [Inhabited α] (r : Nat) (N : Node α) (x : α) (D : Nat) (s : Al)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hA : N.nodemap.testBit D = true) :
    Edit r N ((copyInnerReplaceInline N (2 ^ D) (pos N.nodemap D) x).run s).1 D (.data x) := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hB : N.datamap.testBit D = false := bits_disjoint _ _ h1 D hA
  have hlenV : (N.values.take (popcount N.datamap)).length = popcount N.datamap := length_take_of_le _ _ h5
  have hlenC : (N.cs.take (popcount N.nodemap)).length = popcount N.nodemap := length_take_of_le _ _ h4
  have e : ((copyInnerReplaceInline N (2 ^ D) (pos N.nodemap D) x).run s).1 =
      ((mkInner (clearBit N.nodemap (2 ^ D)) (N.datamap ||| 2 ^ D)
        (insertAt (N.values.take (popcount N.datamap)) (pos N.datamap D) x)
        (eraseAt (N.cs.take (popcount N.nodemap)) (pos N.nodemap D))).run s).1 := rfl
  rw [e]
  constructor
  · apply wf_mkInner r _ _ _ _ s
    · apply disjoint_of_bits
      intro i ⟨ha, hb⟩
      rw [clearBit_testBit' _ D i h2] at ha
      rw [Nat.testBit_or, Nat.testBit_two_pow] at hb
      by_cases hi : D = i
      · subst hi; simp at ha
      · simp [hi] at ha hb; exact disjoint_bits _ _ h1 i ⟨ha, hb⟩
    · exact clear_lt _ D h2
    · exact Nat.or_lt_two_pow h3 (pow_lt32 D hD)
    · have := popcount_clear _ D hD hA
      have := length_eraseAt (N.cs.take (popcount N.nodemap)) (pos N.nodemap D)
        (by rw [hlenC]; exact pos_lt_popcount _ D hD hA)
      omega
    · rw [length_insertAt _ _ _ (by rw [hlenV]; exact pos_le_popcount _ D (by omega)), hlenV,
        popcount_or_pow _ D hD hB]
    · intro c hcm
      exact h6 c (mem_eraseAt _ _ (List.mem_of_mem_take hcm))
  · intro d hd
    rw [slot_mkInner]
    by_cases hdD : d = D
    · subst hdD
      rw [if_neg (by rw [testBit_clear_self _ _ hd]; simp), if_pos (testBit_or_self _ _), if_pos rfl,
        getD_insertAt_self _ d N.values x default hD hB h5]
    · rw [if_neg hdD, testBit_or_ne _ _ _ (Ne.symm hdD), testBit_clear_ne _ _ _ hd (Ne.symm hdD)]
      unfold slot
      by_cases hn : N.nodemap.testBit d = true
      · rw [if_pos hn, if_pos hn, getD_eraseAt_pos N.nodemap D d N.cs Node.dummy hD hd hdD hA hn h4]
      · rw [if_neg hn, if_neg hn]
        by_cases hb : N.datamap.testBit d = true
        · rw [if_pos hb, if_pos hb, getD_insertAt_pos N.datamap D d N.values x default hD hd hdD hB hb h5]
        · rw [if_neg hb, if_neg hb]

/-- `copy_inner_remove_value(src, bit, voffset)` (and the root's two-value collapse): a data slot
emptied. -/
theorem edit_removeValue [Inhabited α] (r : Nat) (N : Node α) (D : Nat) (s : Al)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hA : N.nodemap.testBit D = false)
    (hB : N.datamap.testBit D = true) :
    Edit r N ((mkInner N.nodemap (clearBit N.datamap (2 ^ D))
        (eraseAt (N.values.take (popcount N.datamap)) (pos N.datamap D))
        (N.cs.take (popcount N.nodemap))).run s).1 D .empty := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hlenV : (N.values.take (popcount N.datamap)).length = popcount N.datamap := length_take_of_le _ _ h5
  have hlenC : (N.cs.take (popcount N.nodemap)).length = popcount N.nodemap := length_take_of_le _ _ h4
  constructor
  · apply wf_mkInner r _ _ _ _ s
    · apply disjoint_of_bits
      intro i ⟨ha, hb⟩
      rw [clearBit_testBit' _ D i h3] at hb
      simp at hb
      exact disjoint_bits _ _ h1 i ⟨ha, hb.1⟩
    · exact h2
    · exact clear_lt _ D h3
    · rw [hlenC]; exact Nat.le_refl _
    · have := popcount_clear _ D hD hB
      have := length_eraseAt (N.values.take (popcount N.datamap)) (pos N.datamap D)
        (by rw [hlenV]; exact pos_lt_popcount _ D hD hB)
      omega
    · intro c hcm
      exact h6 c (by rw [List.take_take, Nat.min_self] at hcm; exact hcm)
  · intro d hd
    rw [slot_mkInner]
    by_cases hdD : d = D
    · subst hdD
      rw [if_neg (by simp [hA]), if_neg (by rw [testBit_clear_self _ _ hd]; simp), if_pos rfl]
    · rw [if_neg hdD, testBit_clear_ne _ _ _ hd (Ne.symm hdD)]
      unfold slot
      by_cases hn : N.nodemap.testBit d = true
      · rw [if_pos hn, if_pos hn, getD_take_pos _ d N.cs _ hd hn]
      · rw [if_neg hn, if_neg hn]
        by_cases hb : N.datamap.testBit d = true
        · rw [if_pos hb, if_pos hb, getD_eraseAt_pos N.datamap D d N.values default hD hd hdD hB hb h5]
        · rw [if_neg hb, if_neg hb]

theorem copyInnerRemoveValue_eq [Inhabited α] (N : Node α) (D : Nat) (s : Al) :
    ((copyInnerRemoveValue N (2 ^ D) (pos N.datamap D)).run s).1 =
      ((mkInner N.nodemap (clearBit N.datamap (2 ^ D))
        (eraseAt (N.values.take (popcount N.datamap)) (pos N.datamap D))
        (N.cs.take (popcount N.nodemap))).run s).1 := rfl

/-- A bitmap with one bit set has no other. -/
theorem only_bit (m D d : Nat) (hD : D < 32) (hd : d < 32) (hne : d ≠ D) (hm : m.testBit D = true)
    (h1 : popcount m = 1) : m.testBit d = false := by
  cases hb : m.testBit d
  · rfl
  · have := pos_ne m d D hd hD hne hb hm
    have := pos_lt_popcount m d hd hb
    have := pos_lt_popcount m D hD hm
    omega

/-- The root's collapse of two values to one (`make_inner_n(0, datamap & ~bit, values[!offset])`). -/
theorem edit_rootCollapse [Inhabited α] (r : Nat) (N : Node α) (D : Nat) (s : Al)
    (hw : wfNode (r + 1) N = true) (hD : D < 32) (hB : N.datamap.testBit D = true)
    (hn0 : N.nodemap = 0) (hdc : popcount N.datamap = 2) :
    Edit r N ((mkInner 0 (clearBit N.datamap (2 ^ D))
        [N.values.getD (if (pos N.datamap D == 0) = true then 1 else 0) default] ([] : List (Node α))).run s).1
      D .empty := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  have hA : N.nodemap.testBit D = false := by rw [hn0]; exact Nat.zero_testBit D
  have hp : pos N.datamap D < 2 := by rw [← hdc]; exact pos_lt_popcount _ D hD hB
  have e1 : [N.values.getD (if (pos N.datamap D == 0) = true then 1 else 0) default] =
      eraseAt (N.values.take (popcount N.datamap)) (pos N.datamap D) := by
    rw [hdc]
    have hl : 2 ≤ N.values.length := by omega
    match N.values, hl with
    | a :: b :: _, _ =>
      rcases (show pos N.datamap D = 0 ∨ pos N.datamap D = 1 by omega) with h | h <;> rw [h] <;> rfl
  have e2 : ([] : List (Node α)) = N.cs.take (popcount N.nodemap) := by rw [hn0, popcount_zero]; rfl
  rw [e1, e2, ← hn0]
  exact edit_removeValue r N D s hw hD hA hB

/-- `empty()`: the root's last value removed. -/
theorem edit_empty [Inhabited α] (r : Nat) (N : Node α) (D : Nat) (hw : wfNode (r + 1) N = true) (hD : D < 32)
    (hB : N.datamap.testBit D = true) (hn0 : N.nodemap = 0) (hdc : popcount N.datamap = 1) :
    Edit r N (Champ.empty (α := α)).root D .empty := by
  refine ⟨rfl, ?_⟩
  intro d hd
  have e : slot (Champ.empty (α := α)).root d = .empty := by
    show (if (0 : Nat).testBit d then _ else if (0 : Nat).testBit d then _ else _) = _
    simp [Nat.zero_testBit]
  rw [e]
  by_cases hdD : d = D
  · rw [if_pos hdD]
  · rw [if_neg hdD]
    unfold slot
    rw [hn0, Nat.zero_testBit, only_bit _ D d hD hd hdD hB hdc]
    rfl

end Jank.R6.Champ

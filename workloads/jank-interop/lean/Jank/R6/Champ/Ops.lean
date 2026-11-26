import Jank.R6.Champ.Slots

/-!
# Round 6, CHAMP: the hash-path invariant, and what `add` and `sub` do to the iteration

**The hash-path invariant** `HP` (immer's `do_check_champ`, `champ.hpp`, made a predicate): in every
inner node, the value in bit `d`'s data slot has `d` as its hash's 5-bit chunk at that level, and
every value under bit `d`'s child has `d` there too, at every level down to the collision nodes
(which `wfNode` puts at the last level only). So every value sits at the path its hash's chunks
name, and two values in one collision node agree on all 65 bits `get` reads.

For every hash function and every equality (nothing assumed of either), over round 3's replica:

- ★ `add_step`: `do_add` keeps `wfNode` and `HP`, and its iteration is the old one with the value
  added (`added`) or with one value `Equal` to it replaced by it (not `added`).
- ★ `sub_step`: `do_sub` returns nothing, a value passed up (from a subtree holding exactly it and
  the removed value), or a tree that keeps `wfNode` and `HP` and iterates as the old one without one
  value `Equal` to the key. Every collapse is covered: a collision node shrunk or collapsed, a data
  slot removed, a two-value node collapsed and inlined by the first ancestor that keeps other
  entries, the root's collapse to one value, and `empty()`.
-/

namespace Jank.R6.Champ

open Jank.R3.Immer.Champ

variable {α κ : Type}

/-- The 5-bit chunk of hash `h` that a node `r + 1` levels above the collision level reads. -/
abbrev chunk (r h : Nat) : Nat := idxAt h (maxShift - 5 * (r + 1))

/-- What the invariant asks of slot `d` of a node `r + 1` levels up (`P` is the invariant below). -/
def SlotOK (P : Node α → Prop) (cfg : Cfg α κ) (r d : Nat) : Slot α → Prop
  | .empty => True
  | .data x => chunk r (cfg.hashT x) = d
  | .child c => (∀ x ∈ iterNode r c, chunk r (cfg.hashT x) = d) ∧ P c

/-- **The hash-path invariant.** -/
def HP [Inhabited α] (cfg : Cfg α κ) : Nat → Node α → Prop
  | 0, _ => True
  | r + 1, N => ∀ d, d < 32 → SlotOK (HP cfg r) cfg r d (slot N d)

theorem HP_succ [Inhabited α] (cfg : Cfg α κ) (r : Nat) (N : Node α) :
    HP cfg (r + 1) N = ∀ d, d < 32 → SlotOK (HP cfg r) cfg r d (slot N d) := rfl

/-- An edit of one slot keeps the invariant when the new slot meets it. -/
theorem HP_edit [Inhabited α] (cfg : Cfg α κ) (r : Nat) (N N' : Node α) (D : Nat) (X : Slot α)
    (he : Edit r N N' D X) (hp : HP cfg (r + 1) N) (hX : SlotOK (HP cfg r) cfg r D X) : HP cfg (r + 1) N' := by
  intro d hd
  rw [he.2 d hd]
  by_cases h : d = D
  · subst h; rw [if_pos rfl]; exact hX
  · rw [if_neg h]; exact hp d hd

/-- The iteration of an edited node: the new slot's values, then the same 31 others. -/
theorem iter_edit [Inhabited α] (r : Nat) (N N' : Node α) (D : Nat) (X : Slot α) (hw : wfNode (r + 1) N = true)
    (hD : D < 32) (he : Edit r N N' D X) :
    (iterNode (r + 1) N).Perm (slotL r (slot N D) ++ rest r N D) ∧
      (iterNode (r + 1) N').Perm (slotL r X ++ rest r N D) := by
  refine ⟨iter_split r N hw D hD, ?_⟩
  have h1 := iter_split r N' he.1 D hD
  rw [he.2 D hD, if_pos rfl, rest_congr r N N' D (fun d hd hne => by rw [he.2 d hd, if_neg hne])] at h1
  exact h1

/-! ## Owners and moves change nothing the invariants read -/

theorem slot_owned [Inhabited α] (n : Node α) (e d : Nat) : slot (owned n e) d = slot n d := by
  cases n with
  | inner id t nm dm v cs => cases v <;> (simp only [owned]; rfl)
  | collision => (simp only [owned]; rfl)

theorem iter_owned (n : Node α) (e : Nat) : ∀ r, iterNode r (owned n e) = iterNode r n := by
  intro r
  cases r with
  | zero => cases n with
    | inner id t nm dm v cs => cases v <;> (simp only [owned]; rw [iterNode.eq_1, iterNode.eq_1]; rfl)
    | collision => (simp only [owned]; rw [iterNode.eq_1, iterNode.eq_1]; rfl)
  | succ r => cases n with
    | inner id t nm dm v cs => cases v <;> (simp only [owned]; rw [iterNode.eq_2, iterNode.eq_2]; rfl)
    | collision => (simp only [owned]; rw [iterNode.eq_2, iterNode.eq_2]; rfl)

theorem wf_owned (n : Node α) (e : Nat) : ∀ r, wfNode r (owned n e) = wfNode r n := by
  intro r
  cases r with
  | zero => cases n with
    | inner id t nm dm v cs => cases v <;> (simp only [owned]; simp [wfNode])
    | collision => (simp only [owned]; simp [wfNode, Node.collisions])
  | succ r => cases n with
    | inner id t nm dm v cs => cases v <;> (simp only [owned]; simp [wfNode])
    | collision => (simp only [owned]; simp [wfNode])

theorem HP_owned [Inhabited α] (cfg : Cfg α κ) (n : Node α) (e : Nat) : ∀ r, HP cfg r (owned n e) = HP cfg r n := by
  intro r; cases r with
  | zero => rfl
  | succ r => simp only [HP_succ, slot_owned]

theorem slot_ownedValues [Inhabited α] (n : Node α) (e d : Nat) : slot (ownedValues n e) d = slot n d := by
  cases n with
  | inner id t nm dm v cs => cases v <;> (simp only [ownedValues]; rfl)
  | collision => (simp only [ownedValues]; rfl)

theorem iter_ownedValues (n : Node α) (e : Nat) : ∀ r, iterNode r (ownedValues n e) = iterNode r n := by
  intro r
  cases r with
  | zero => cases n with
    | inner id t nm dm v cs => cases v <;> (simp only [ownedValues]; rw [iterNode.eq_1, iterNode.eq_1]; rfl)
    | collision => (simp only [ownedValues]; rw [iterNode.eq_1, iterNode.eq_1]; rfl)
  | succ r => cases n with
    | inner id t nm dm v cs => cases v <;> (simp only [ownedValues]; rw [iterNode.eq_2, iterNode.eq_2]; rfl)
    | collision => (simp only [ownedValues]; rw [iterNode.eq_2, iterNode.eq_2]; rfl)

theorem wf_ownedValues (n : Node α) (e : Nat) : ∀ r, wfNode r (ownedValues n e) = wfNode r n := by
  intro r
  cases r with
  | zero => cases n with
    | inner id t nm dm v cs => cases v <;> (simp only [ownedValues]; simp [wfNode])
    | collision => (simp only [ownedValues]; simp [wfNode, Node.collisions])
  | succ r => cases n with
    | inner id t nm dm v cs => cases v <;> (simp only [ownedValues]; simp [wfNode])
    | collision => (simp only [ownedValues]; simp [wfNode])

theorem HP_ownedValues [Inhabited α] (cfg : Cfg α κ) (n : Node α) (e : Nat) :
    ∀ r, HP cfg r (ownedValues n e) = HP cfg r n := by
  intro r; cases r with
  | zero => rfl
  | succ r => simp only [HP_succ, slot_ownedValues]

/-! ## `make_merged` (with or without an owner) -/

theorem makeMerged_zero (own : Option Nat) (v1 v2 : α) (h1 h2 : Nat) (s : Al) :
    ((makeMerged own 0 v1 h1 v2 h2).run s).1.collisions = [v1, v2] := by
  cases own <;> rfl

theorem makeMerged_same (own : Option Nat) (r : Nat) (v1 v2 : α) (h1 h2 : Nat) (s : Al)
    (hc : idxAt h1 (maxShift - 5 * (r + 1)) = idxAt h2 (maxShift - 5 * (r + 1))) :
    ∃ nid tok, ((makeMerged own (r + 1) v1 h1 v2 h2).run s).1 =
      .inner nid tok (2 ^ idxAt h1 (maxShift - 5 * (r + 1))) 0 none [((makeMerged own r v1 h1 v2 h2).run s).1] := by
  rw [makeMerged.eq_2]
  dsimp only
  rw [if_pos (by simp [hc]), one_shl]
  cases own <;> exact ⟨_, _, rfl⟩

theorem makeMerged_diff (own : Option Nat) (r : Nat) (v1 v2 : α) (h1 h2 : Nat) (s : Al)
    (hc : idxAt h1 (maxShift - 5 * (r + 1)) ≠ idxAt h2 (maxShift - 5 * (r + 1))) :
    ∃ nid tok vv, ((makeMerged own (r + 1) v1 h1 v2 h2).run s).1 =
      .inner nid tok 0 (2 ^ idxAt h1 (maxShift - 5 * (r + 1)) ||| 2 ^ idxAt h2 (maxShift - 5 * (r + 1))) (some vv) [] ∧
      vv.xs = (if idxAt h1 (maxShift - 5 * (r + 1)) < idxAt h2 (maxShift - 5 * (r + 1)) then [v1, v2] else [v2, v1]) := by
  rw [makeMerged.eq_2]
  dsimp only
  rw [if_neg (by simp [hc]), one_shl, one_shl]
  cases own <;> (split <;> exact ⟨_, _, _, rfl, rfl⟩)

theorem iter_makeMerged (own : Option Nat) (v1 v2 : α) (h1 h2 : Nat) :
    ∀ r (s : Al), (iterNode r ((makeMerged own r v1 h1 v2 h2).run s).1).Perm [v1, v2] := by
  intro r
  induction r with
  | zero => intro s; rw [iterNode.eq_1, makeMerged_zero]
  | succ r ih =>
    intro s
    have hA := idxAt_lt h1 (maxShift - 5 * (r + 1))
    by_cases hc : idxAt h1 (maxShift - 5 * (r + 1)) = idxAt h2 (maxShift - 5 * (r + 1))
    · obtain ⟨nid, tok, e⟩ := makeMerged_same own r v1 v2 h1 h2 s hc
      rw [e, iterNode.eq_2]
      show (List.take (popcount 0) [] ++ List.flatMap (iterNode r)
        (List.take (popcount (2 ^ idxAt h1 (maxShift - 5 * (r + 1)))) [((makeMerged own r v1 h1 v2 h2).run s).1])).Perm _
      rw [popcount_pow _ hA]
      simpa using ih s
    · obtain ⟨nid, tok, vv, e, ex⟩ := makeMerged_diff own r v1 v2 h1 h2 s hc
      have hB := idxAt_lt h2 (maxShift - 5 * (r + 1))
      rw [e, iterNode.eq_2]
      show (List.take (popcount (2 ^ idxAt h1 (maxShift - 5 * (r + 1)) ||| 2 ^ idxAt h2 (maxShift - 5 * (r + 1)))) vv.xs ++
        List.flatMap (iterNode r) (List.take (popcount 0) [])).Perm _
      rw [popcount_two _ _ hA hB hc, ex]
      split
      · simp
      · simpa using List.Perm.swap v1 v2 []

theorem wf_makeMerged (own : Option Nat) (v1 v2 : α) (h1 h2 : Nat) :
    ∀ r (s : Al), wfNode r ((makeMerged own r v1 h1 v2 h2).run s).1 = true := by
  intro r
  induction r with
  | zero => intro s; cases own <;> rfl
  | succ r ih =>
    intro s
    have hA := idxAt_lt h1 (maxShift - 5 * (r + 1))
    by_cases hc : idxAt h1 (maxShift - 5 * (r + 1)) = idxAt h2 (maxShift - 5 * (r + 1))
    · obtain ⟨nid, tok, e⟩ := makeMerged_same own r v1 v2 h1 h2 s hc
      rw [e]
      apply wf_inner_intro
      · simp
      · exact pow_lt32 _ hA
      · decide
      · simp [popcount_pow _ hA]
      · show (0 : Nat) = 0; rfl
      · intro c hcm
        rw [popcount_pow _ hA] at hcm
        simp at hcm
        rw [hcm]; exact ih s
    · obtain ⟨nid, tok, vv, e, ex⟩ := makeMerged_diff own r v1 v2 h1 h2 s hc
      have hB := idxAt_lt h2 (maxShift - 5 * (r + 1))
      rw [e]
      apply wf_inner_intro
      · simp
      · decide
      · exact Nat.or_lt_two_pow (pow_lt32 _ hA) (pow_lt32 _ hB)
      · simp [popcount_zero]
      · show popcount _ ≤ vv.xs.length
        rw [popcount_two _ _ hA hB hc, ex]; split <;> simp
      · intro c hcm; simp at hcm

theorem slot_pow_one [Inhabited α] (nid tok i d : Nat) (m : Node α) (hi : i < 32) :
    slot (.inner nid tok (2 ^ i) 0 none [m]) d = if d = i then .child m else .empty := by
  rw [slot_inner, Nat.testBit_two_pow]
  by_cases h : d = i
  · subst h
    rw [if_pos (by simp), if_pos rfl, show pos (2 ^ d) d = 0 by unfold pos; rw [pow_and_mask, popcount_zero]]
    rfl
  · rw [if_neg (by simp; omega), if_neg h, Nat.zero_testBit]
    rfl

theorem slot_two [Inhabited α] (nid tok a b d : Nat) (vv : Vals α) (v1 v2 : α) (ha : a < 32) (hb : b < 32) (hab : a ≠ b)
    (ex : vv.xs = if a < b then [v1, v2] else [v2, v1]) :
    slot (.inner nid tok 0 (2 ^ a ||| 2 ^ b) (some vv) ([] : List (Node α))) d =
      if d = a then .data v1 else if d = b then .data v2 else .empty := by
  rw [slot_inner, Nat.zero_testBit, if_neg (by simp)]
  show (if (2 ^ a ||| 2 ^ b).testBit d = true then Slot.data (vv.xs.getD (pos (2 ^ a ||| 2 ^ b) d) default) else .empty) = _
  rw [ex]
  by_cases h1 : d = a
  · subst h1
    have hp : pos (2 ^ d ||| 2 ^ b) d = if b < d then 1 else 0 := by
      unfold pos; rw [two_bits_mask d b hab]; split
      · exact popcount_pow b hb
      · exact popcount_zero
    rw [if_pos (by simp [Nat.testBit_or, Nat.testBit_two_pow]), if_pos rfl, hp]
    by_cases hlt : d < b
    · rw [if_pos hlt, if_neg (by omega)]; rfl
    · rw [if_neg hlt, if_pos (by omega)]; rfl
  · by_cases h2 : d = b
    · subst h2
      have hp : pos (2 ^ a ||| 2 ^ d) d = if a < d then 1 else 0 := by
        unfold pos; rw [Nat.or_comm, two_bits_mask d a (Ne.symm hab)]; split
        · exact popcount_pow a ha
        · exact popcount_zero
      rw [if_pos (by simp [Nat.testBit_or, Nat.testBit_two_pow]), if_neg h1, if_pos rfl, hp]
      by_cases hlt : a < d
      · rw [if_pos hlt, if_pos hlt]; rfl
      · rw [if_neg hlt, if_neg hlt]; rfl
    · rw [if_neg (by simp [Nat.testBit_or, Nat.testBit_two_pow]; omega), if_neg h1, if_neg h2]

/-- `make_merged` puts each value on its own hash's path. -/
theorem HP_makeMerged [Inhabited α] (cfg : Cfg α κ) (own : Option Nat) (v1 v2 : α) (h1 h2 : Nat)
    (hv1 : cfg.hashT v1 = h1) (hv2 : cfg.hashT v2 = h2) :
    ∀ r (s : Al), HP cfg r ((makeMerged own r v1 h1 v2 h2).run s).1 := by
  intro r
  induction r with
  | zero => intro s; trivial
  | succ r ih =>
    intro s
    have hA := idxAt_lt h1 (maxShift - 5 * (r + 1))
    have hB := idxAt_lt h2 (maxShift - 5 * (r + 1))
    by_cases hc : idxAt h1 (maxShift - 5 * (r + 1)) = idxAt h2 (maxShift - 5 * (r + 1))
    · obtain ⟨nid, tok, e⟩ := makeMerged_same own r v1 v2 h1 h2 s hc
      rw [e, HP_succ]
      intro d hd
      rw [slot_pow_one _ _ _ _ _ hA]
      by_cases hdi : d = idxAt h1 (maxShift - 5 * (r + 1))
      · rw [if_pos hdi]
        refine ⟨?_, ih s⟩
        intro x hx
        have hx' := (iter_makeMerged own v1 v2 h1 h2 r s).subset hx
        simp at hx'
        rcases hx' with hx' | hx'
        · rw [hx', hv1]; exact hdi.symm
        · rw [hx', hv2]; show idxAt h2 (maxShift - 5 * (r + 1)) = d; rw [← hc]; exact hdi.symm
      · rw [if_neg hdi]; trivial
    · obtain ⟨nid, tok, vv, e, ex⟩ := makeMerged_diff own r v1 v2 h1 h2 s hc
      rw [e, HP_succ]
      intro d hd
      rw [slot_two nid tok _ _ d vv v1 v2 hA hB hc ex]
      by_cases h1' : d = idxAt h1 (maxShift - 5 * (r + 1))
      · rw [if_pos h1']; show chunk r (cfg.hashT v1) = d; rw [hv1]; exact h1'.symm
      · rw [if_neg h1']
        by_cases h2' : d = idxAt h2 (maxShift - 5 * (r + 1))
        · rw [if_pos h2']; show chunk r (cfg.hashT v2) = d; rw [hv2]; exact h2'.symm
        · rw [if_neg h2']; trivial

/-! ## `do_add` -/

/-- What `do_add` gives back for a node `N` (`N'`, `added`): well formed; its iteration is `N`'s
with `v` added, or with one stored value `Equal` to `v` replaced by `v`; the invariant kept. -/
structure AddOut [Inhabited α] (cfg : Cfg α κ) (r : Nat) (N : Node α) (v : α) (N' : Node α) (added : Bool) : Prop where
  wf : wfNode r N' = true
  grew : added = true → (iterNode r N').Perm (v :: iterNode r N)
  replaced : added = false → ∃ x ∈ iterNode r N, cfg.eqTT x v = true ∧ (v :: iterNode r N).Perm (x :: iterNode r N')
  hp : HP cfg r N → HP cfg r N'

theorem AddOut.mem [Inhabited α] {cfg : Cfg α κ} {r : Nat} {N : Node α} {v : α} {N' : Node α} {added : Bool}
    (o : AddOut cfg r N v N' added) : ∀ x ∈ iterNode r N', x = v ∨ x ∈ iterNode r N := by
  intro x hx
  cases ha : added
  · obtain ⟨y, _, _, hp⟩ := o.replaced ha
    exact List.mem_cons.mp (hp.symm.subset (List.mem_cons_of_mem _ hx))
  · exact List.mem_cons.mp ((o.grew ha).subset hx)

theorem getD_mem' {β : Type} (l : List β) (i : Nat) (d : β) (h : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

theorem getD_eq_getElem' {β : Type} (l : List β) (i : Nat) (d : β) (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- ★ `do_add`, one level at a time, for every hash and every equality. -/
theorem add_step [Inhabited α] (cfg : Cfg α κ) (v : α) (h : Nat) (hv : cfg.hashT v = h) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      AddOut cfg r N v ((doAdd cfg r N v h).run s).1.1 ((doAdd cfg r N v h).run s).1.2 := by
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
      cases hf : xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show decide ((v :: xs).length ≥ 2) = true
          simp; omega
        · intro _; exact List.Perm.refl _
        · intro hc; cases hc
        · intro _; trivial
      | some pos =>
        obtain ⟨hpos, hpx, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        refine ⟨?_, ?_, ?_, ?_⟩
        · show decide ((v :: eraseAt xs pos).length ≥ 2) = true
          have := length_eraseAt_ge xs pos
          simp; omega
        · intro hc; cases hc
        · intro _
          refine ⟨xs.getD pos default, getD_mem' xs pos default hpos, ?_, ?_⟩
          · rw [getD_eq_getElem' xs pos default hpos]; exact hpx
          · show (v :: xs).Perm (xs.getD pos default :: v :: eraseAt xs pos)
            exact ((perm_eraseAt xs pos default hpos).cons v).trans (List.Perm.swap _ _ _)
        · intro _; trivial
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    have hvD : chunk r (cfg.hashT v) = D := by rw [hv]; exact hDdef
    by_cases hA : N.nodemap.testBit D = true
    · -- the child on the path: `copy_inner_replace` over the child's `do_add`
      have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have e : ((doAdd cfg (r + 1) N v h).run s).1 =
          (((copyInnerReplace N (pos N.nodemap D) ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      rw [e]
      have o := ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
      generalize (doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s = q at o ⊢
      obtain ⟨⟨c1, a1⟩, s1⟩ := q
      dsimp only at o ⊢
      have hE := edit_replace r N c1 D s1 hw hD hA o.wf
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
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have hs : slot N D = .data (N.values.getD (pos N.datamap D) default) := by
          unfold slot; rw [if_neg hA, if_pos hB]
        have hvalm := mem_iter_of_slot r N hw D hD (N.values.getD (pos N.datamap D) default) (by rw [hs]; simp [slotL])
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · -- `copy_inner_replace_value`: the stored value replaced (S59)
          have e : ((doAdd cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceValue N (pos N.datamap D) v).run s).1, false) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]; rfl
          rw [e]
          have hE' := edit_replaceValue r N v D s hw hD hA0 hB
          obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
          rw [hs] at p0
          simp only [slotL] at p0 p1
          refine ⟨hE'.1, (fun hc => by cases hc), ?_, ?_⟩
          · intro _
            refine ⟨_, hvalm, hE, ?_⟩
            exact (p0.cons v).trans ((List.Perm.swap _ _ _).trans (p1.symm.cons _))
          · intro hpN
            exact HP_edit cfg r N _ D _ hE' hpN hvD
        · -- `make_merged` below, `copy_inner_replace_merged`
          have hE0 : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = false := by simpa using hE
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
          generalize hval : N.values.getD (pos N.datamap D) default = val at hs hE hE0 hvalm ⊢
          generalize hq : (makeMerged none r v h val (cfg.hashT val)).run s = q
          obtain ⟨m, s1⟩ := q
          dsimp only
          have hmw : wfNode r m = true := by
            have := wf_makeMerged none v val h (cfg.hashT val) r s; rw [hq] at this; exact this
          have hmi : (iterNode r m).Perm [v, val] := by
            have := iter_makeMerged none v val h (cfg.hashT val) r s; rw [hq] at this; exact this
          have hE' := edit_replaceMerged r N m D s1 hw hD hA0 hB hmw
          obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
          rw [hs] at p0
          simp only [slotL] at p0 p1
          refine ⟨hE'.1, ?_, (fun hc => by cases hc), ?_⟩
          · intro _
            exact p1.trans ((hmi.append_right _).trans (p0.symm.cons v))
          · intro hpN
            have hok := hpN D hD
            rw [hs] at hok
            have hvalD : chunk r (cfg.hashT val) = D := hok
            apply HP_edit cfg r N _ D _ hE' hpN
            refine ⟨?_, ?_⟩
            · intro x hx
              have := hmi.subset hx
              simp at this
              rcases this with hx | hx <;> rw [hx]
              · exact hvD
              · exact hvalD
            · have := HP_makeMerged cfg none v val h (cfg.hashT val) hv rfl r s
              rw [hq] at this; exact this
      · -- an empty slot: `copy_inner_insert_value`
        have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have hs : slot N D = .empty := by unfold slot; rw [if_neg hA, if_neg hB]
        have e : ((doAdd cfg (r + 1) N v h).run s).1 = (((copyInnerInsertValue N (2 ^ D) v).run s).1, true) := by
          rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']; rfl
        rw [e]
        have hE' := edit_insertValue r N v D s hw hD hA0 hB0
        obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
        rw [hs] at p0
        simp only [slotL, List.nil_append] at p0 p1
        refine ⟨hE'.1, ?_, (fun hc => by cases hc), ?_⟩
        · intro _
          exact p1.trans (p0.symm.cons v)
        · intro hpN
          exact HP_edit cfg r N _ D _ hE' hpN hvD

/-! ## `do_sub` -/

/-- What `do_sub` gives back for a node `N`: nothing; a value passed up from a subtree that held
exactly it and one value `Equal` to the key; or a well-formed tree iterating as `N` without one
value `Equal` to the key, the invariant kept. -/
def SubOut [Inhabited α] (cfg : Cfg α κ) (k : κ) (r : Nat) (N : Node α) : Jank.R3.Immer.Champ.Sub α → Prop
  | .nothing => True
  | .singleton x => ∃ y, cfg.eqTK y k = true ∧ (iterNode r N).Perm [y, x]
  | .tree t => wfNode r t = true ∧ (∃ y, cfg.eqTK y k = true ∧ (iterNode r N).Perm (y :: iterNode r t)) ∧
      (HP cfg r N → HP cfg r t)

theorem rest_nil [Inhabited α] (r : Nat) (N : Node α) (D : Nat)
    (h : ∀ d, d < 32 → d ≠ D → slot N d = .empty) : rest r N D = [] := by
  unfold rest
  rw [flatMap_congr' _ (fun _ => ([] : List α))]
  · simp
  · intro d hd
    rw [List.mem_filter, List.mem_range] at hd
    rw [h d hd.1 (by simpa using hd.2)]; rfl

/-- A node whose only entry is the child at `D` iterates as that child. -/
theorem iter_only [Inhabited α] (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (D : Nat) (hD : D < 32)
    (hA : N.nodemap.testBit D = true) (hdm : N.datamap = 0) (hc : popcount N.nodemap = 1) :
    (iterNode (r + 1) N).Perm (iterNode r (N.cs.getD (pos N.nodemap D) Node.dummy)) := by
  have p := iter_split r N hw D hD
  have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
  rw [hs, rest_nil r N D, List.append_nil] at p
  · exact p
  · intro d hd hne
    unfold slot
    rw [only_bit _ D d hD hd hne hA hc, hdm, Nat.zero_testBit]
    rfl

/-- A node of two values and no child iterates as them. -/
theorem iter_two [Inhabited α] (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (D : Nat) (hD : D < 32)
    (hB : N.datamap.testBit D = true) (hn0 : N.nodemap = 0) (hdc : popcount N.datamap = 2) :
    (iterNode (r + 1) N).Perm [N.values.getD (pos N.datamap D) default,
      N.values.getD (if (pos N.datamap D == 0) = true then 1 else 0) default] := by
  obtain ⟨_, _, _, _, h5, _, _, _⟩ := wf_parts r N hw
  have hp : pos N.datamap D < 2 := by rw [← hdc]; exact pos_lt_popcount _ D hD hB
  rw [iterNode.eq_2]
  show (N.values.take (popcount N.datamap) ++ (N.cs.take (popcount N.nodemap)).flatMap (iterNode r)).Perm _
  rw [hn0, popcount_zero, hdc, List.take_zero, List.flatMap_nil, List.append_nil]
  have hl : 2 ≤ N.values.length := by omega
  generalize N.values = xs at hl ⊢
  generalize pos N.datamap D = p at hp ⊢
  match xs, hl with
  | a :: b :: _, _ =>
    rcases (show p = 0 ∨ p = 1 by omega) with h | h <;> subst h
    · exact List.Perm.refl _
    · exact List.Perm.swap _ _ _

/-- ★ `do_sub`, one level at a time, for every hash and every equality. -/
theorem sub_step [Inhabited α] (cfg : Cfg α κ) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true → SubOut cfg k r N ((doSub cfg k r N h).run s).1 := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    have hl : N.collisions.length ≥ 2 := by
      cases N with
      | inner => simp [wfNode] at hw
      | collision nid tok xs => simpa [wfNode, Node.collisions] using hw
    rw [doSub.eq_1]
    unfold findIdx?
    cases hf : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => trivial
    | some cur =>
      obtain ⟨hcur, hpc, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      dsimp only
      split
      · next hlen =>
        refine ⟨?_, ⟨N.collisions.getD cur default, ?_, ?_⟩, fun _ => trivial⟩
        · show decide ((eraseAt N.collisions cur).length ≥ 2) = true
          have := length_eraseAt N.collisions cur hcur
          simp; omega
        · rw [getD_eq_getElem' _ _ _ hcur]; exact hpc
        · show N.collisions.Perm (N.collisions.getD cur default :: eraseAt N.collisions cur)
          exact perm_eraseAt _ _ _ hcur
      · next hlen =>
        refine ⟨N.collisions.getD cur default, ?_, ?_⟩
        · rw [getD_eq_getElem' _ _ _ hcur]; exact hpc
        · show N.collisions.Perm [N.collisions.getD cur default, N.collisions.getD (if cur == 0 then 1 else 0) default]
          have h2 : N.collisions.length = 2 := by omega
          generalize N.collisions = xs at hcur h2 ⊢
          match xs, h2 with
          | [a, b], _ =>
            rcases (show cur = 0 ∨ cur = 1 by simp at hcur; omega) with hc | hc <;> subst hc
            · exact List.Perm.refl _
            · exact List.Perm.swap _ _ _
  | succ r ih =>
    intro hr N s hw
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
      have o : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
          ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
        ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
      simp only [StateT.run_bind]
      generalize hq : (doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q at o
      obtain ⟨sub, s1⟩ := q
      cases sub with
      | nothing => trivial
      | singleton x =>
        obtain ⟨y, hy, hp⟩ := o
        split
        · next hc =>
          show ∃ y, cfg.eqTK y k = true ∧ (iterNode (r + 1) N).Perm [y, x]
          have hdm : N.datamap = 0 := by simp at hc; exact hc.1.1
          have hcc : popcount N.nodemap = 1 := by simp at hc; exact hc.1.2
          exact ⟨y, hy, (iter_only r N hw D hD hA hdm hcc).trans hp⟩
        · next hc =>
          show SubOut cfg k (r + 1) N (.tree ((copyInnerReplaceInline N (2 ^ D) (pos N.nodemap D) x).run s1).1)
          have hE := edit_replaceInline r N x D s1 hw hD hA
          obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE
          rw [hs] at p0
          simp only [slotL] at p0 p1
          refine ⟨hE.1, ⟨y, hy, p0.trans ((hp.append_right _).trans (p1.symm.cons y))⟩, ?_⟩
          intro hpN
          have hok := hpN D hD
          rw [hs] at hok
          obtain ⟨hk1, _⟩ := hok
          exact HP_edit cfg r N _ D _ hE hpN (hk1 x (hp.symm.subset (by simp)))
      | tree t =>
        obtain ⟨htw, ⟨y, hy, hp⟩, hhp⟩ := o
        show SubOut cfg k (r + 1) N (.tree ((copyInnerReplace N (pos N.nodemap D) t).run s1).1)
        have hE := edit_replace r N t D s1 hw hD hA htw
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
          have hdc1 := pos_lt_popcount N.datamap D hD hB
          by_cases c1 : (N.nodemap != 0 || decide (N.dataCount > 2)) = true
          · rw [if_pos c1]
            show SubOut cfg k (r + 1) N (.tree ((copyInnerRemoveValue N (2 ^ D) (pos N.datamap D)).run s).1)
            rw [copyInnerRemoveValue_eq]
            have hE' := edit_removeValue r N D s hw hD hA0 hB
            obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
            rw [hs] at p0
            simp only [slotL, List.nil_append] at p0 p1
            exact ⟨hE'.1, ⟨_, hE, p0.trans (p1.symm.cons _)⟩, fun hpN => HP_edit cfg r N _ D _ hE' hpN trivial⟩
          · rw [if_neg c1]
            have hn0 : N.nodemap = 0 := by simp at c1; exact c1.1
            have hle : popcount N.datamap ≤ 2 := by simp at c1; exact c1.2
            by_cases c2 : (N.dataCount == 2) = true
            · rw [if_pos c2]
              have hdc : popcount N.datamap = 2 := (by simpa using c2 : N.dataCount = 2)
              split
              · show ∃ y, cfg.eqTK y k = true ∧ (iterNode (r + 1) N).Perm
                  [y, N.values.getD (if (pos N.datamap D == 0) = true then 1 else 0) default]
                exact ⟨_, hE, iter_two r N hw D hD hB hn0 hdc⟩
              · show SubOut cfg k (r + 1) N (.tree ((mkInner 0 (clearBit N.datamap (2 ^ D))
                  [N.values.getD (if (pos N.datamap D == 0) = true then 1 else 0) default] ([] : List (Node α))).run s).1)
                have hE' := edit_rootCollapse r N D s hw hD hB hn0 hdc
                obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
                rw [hs] at p0
                simp only [slotL, List.nil_append] at p0 p1
                exact ⟨hE'.1, ⟨_, hE, p0.trans (p1.symm.cons _)⟩, fun hpN => HP_edit cfg r N _ D _ hE' hpN trivial⟩
            · rw [if_neg c2]
              have hdc : popcount N.datamap = 1 := by
                have : popcount N.datamap ≠ 2 := (by simpa using c2 : ¬ N.dataCount = 2)
                omega
              show SubOut cfg k (r + 1) N (.tree (Champ.empty (α := α)).root)
              have hE' := edit_empty r N D hw hD hB hn0 hdc
              obtain ⟨p0, p1⟩ := iter_edit r N _ D _ hw hD hE'
              rw [hs] at p0
              simp only [slotL, List.nil_append] at p0 p1
              exact ⟨hE'.1, ⟨_, hE, p0.trans (p1.symm.cons _)⟩, fun hpN => HP_edit cfg r N _ D _ hE' hpN trivial⟩
        · rw [if_neg (show ¬ cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)]
          trivial
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_neg hB']
        trivial

end Jank.R6.Champ

import Jank.R8.Champ.LawMut

/-!
# Round 8, CHAMP: transient steps against persistent steps, node by node

Round 7 compared transients with persistent operations by contents only (`buildT_same_keys`). Here
one transient step and the persistent step from the SAME node are compared node by node: every inner
node slot by slot (`slot`: empty, the same value, or agreeing children; node ids, owner tokens,
values-buffer ids and the unused tails of buffers ignored), and every collision node by its list.

- ★ `subMut_agree`: `do_sub_mut` (`dissoc!`/`disj!`) and `do_sub` (`dissoc`/`disj`) give the same
  result kind, the same passed-up value, and trees that agree node by node EXACTLY (collision lists
  equal), for every well-formed node, every hash, every equality, every owner token.
- ★ `addMut_agree`: `do_add_mut` (`assoc!`/`conj!`) and `do_add` (`assoc`/`conj`) give the same
  `added` flag and trees that agree node by node, every collision list equal except at most one: where
  `do_add_mut` writes a value in place into a collision node the transient owns (`*fst = std::move(v)`,
  champ.hpp 652-655), it is `xs.set pos v`, and `do_add`'s `copy_collision_replace` (node.hpp 495-)
  gives `v :: eraseAt xs pos`, `pos` being the first stored value `Equal` to `v` (`InPlace`).
  These two lists are equal exactly when `pos = 0` (★ `inPlace_eq_iff`).
- ★ `addMut_root_agree`, ★ `subMut_root_agree`: the same at the root, sizes equal.
- `inPlace_differs` (`decide +kernel`): the difference is real. In a champ a transient built (two keys
  of one full hash, in one collision node it owns), `assoc!` of the second-stored key keeps the
  iteration order and `assoc` reverses it (the H8-1 programs, `Programs.lean`).
-/

namespace Jank.R8.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ

variable {α κ : Type} [Inhabited α]

/-! ## Agreement, slot by slot -/

/-- Two slots agree: both empty, the same value, or children related by `R`. -/
def SlotRel (R : Node α → Node α → Prop) : Slot α → Slot α → Prop
  | .empty, .empty => True
  | .data x, .data y => x = y
  | .child a, .child b => R a b
  | _, _ => False

/-- Two nodes agree: at an inner level, slot by slot (identities, owner tokens, value-buffer
identities and buffer tails ignored); at the collision level, their lists are related by `C`. -/
def Agree (C : List α → List α → Prop) : Nat → Node α → Node α → Prop
  | 0, A, B => C A.collisions B.collisions
  | r + 1, A, B => ∀ d, d < 32 → SlotRel (fun a b => Agree C r a b) (slot A d) (slot B d)

theorem agree_zero (C : List α → List α → Prop) (A B : Node α) : Agree C 0 A B = C A.collisions B.collisions := rfl

theorem agree_succ (C : List α → List α → Prop) (r : Nat) (A B : Node α) :
    Agree C (r + 1) A B = ∀ d, d < 32 → SlotRel (fun a b => Agree C r a b) (slot A d) (slot B d) := rfl

theorem slotRel_refl (R : Node α → Node α → Prop) (hR : ∀ a, R a a) (x : Slot α) : SlotRel R x x := by
  cases x with
  | empty => trivial
  | data x => rfl
  | child c => exact hR c

theorem agree_refl (C : List α → List α → Prop) (hC : ∀ l, C l l) : ∀ r (A : Node α), Agree C r A A
  | 0, A => hC _
  | r + 1, A => fun _ _ => slotRel_refl _ (agree_refl C hC r) _

theorem slotRel_mono (R R' : Node α → Node α → Prop) (h : ∀ a b, R a b → R' a b) :
    ∀ x y : Slot α, SlotRel R x y → SlotRel R' x y
  | .empty, .empty, _ => trivial
  | .data _, .data _, hx => hx
  | .child a, .child b, hx => h a b hx
  | .empty, .data _, hx | .empty, .child _, hx | .data _, .empty, hx | .data _, .child _, hx
  | .child _, .empty, hx | .child _, .data _, hx => hx.elim

theorem agree_mono (C C' : List α → List α → Prop) (h : ∀ a b, C a b → C' a b) :
    ∀ r (A B : Node α), Agree C r A B → Agree C' r A B
  | 0, A, B, hx => h _ _ hx
  | r + 1, A, B, hx => fun d hd => slotRel_mono _ _ (agree_mono C C' h r) _ _ (hx d hd)

theorem agree_owned_left (C : List α → List α → Prop) (A B : Node α) (e : Nat) :
    ∀ r, Agree C r (owned A e) B ↔ Agree C r A B
  | 0 => by rw [agree_zero, agree_zero, collisions_owned]
  | r + 1 => by rw [agree_succ, agree_succ]; simp only [slot_owned]

theorem agree_ownedValues_left (C : List α → List α → Prop) (A B : Node α) (e : Nat) :
    ∀ r, Agree C r (ownedValues A e) B ↔ Agree C r A B
  | 0 => by rw [agree_zero, agree_zero, collisions_ownedValues]
  | r + 1 => by rw [agree_succ, agree_succ]; simp only [slot_ownedValues]

/-- Two edits of one slot of the same node agree when the new slots do. -/
theorem agree_edits (C : List α → List α → Prop) (hC : ∀ l, C l l) (r : Nat) (N A B : Node α) (D : Nat)
    (XA XB : Slot α) (hA : Edit r N A D XA) (hB : Edit r N B D XB)
    (hX : SlotRel (fun a b => Agree C r a b) XA XB) : Agree C (r + 1) A B := by
  intro d hd
  rw [hA.2 d hd, hB.2 d hd]
  by_cases h : d = D
  · rw [if_pos h, if_pos h]; exact hX
  · rw [if_neg h, if_neg h]; exact slotRel_refl _ (agree_refl C hC r) _

/-- `make_merged` and `make_merged_e` (any owners, any allocation states) agree. -/
theorem agree_makeMerged (C : List α → List α → Prop) (hC : ∀ l, C l l) (own own' : Option Nat)
    (v1 v2 : α) (h1 h2 : Nat) : ∀ r (s s' : Al),
      Agree C r ((makeMerged own r v1 h1 v2 h2).run s).1 ((makeMerged own' r v1 h1 v2 h2).run s').1 := by
  intro r
  induction r with
  | zero =>
    intro s s'
    rw [agree_zero, makeMerged_zero, makeMerged_zero]; exact hC _
  | succ r ih =>
    intro s s'
    have hA := idxAt_lt h1 (maxShift - 5 * (r + 1))
    by_cases hc : idxAt h1 (maxShift - 5 * (r + 1)) = idxAt h2 (maxShift - 5 * (r + 1))
    · obtain ⟨nid, tok, e⟩ := makeMerged_same own r v1 v2 h1 h2 s hc
      obtain ⟨nid', tok', e'⟩ := makeMerged_same own' r v1 v2 h1 h2 s' hc
      rw [e, e']
      intro d hd
      rw [slot_pow_one _ _ _ _ _ hA, slot_pow_one _ _ _ _ _ hA]
      split
      · exact ih s s'
      · trivial
    · obtain ⟨nid, tok, vv, e, ex⟩ := makeMerged_diff own r v1 v2 h1 h2 s hc
      obtain ⟨nid', tok', vv', e', ex'⟩ := makeMerged_diff own' r v1 v2 h1 h2 s' hc
      have hB := idxAt_lt h2 (maxShift - 5 * (r + 1))
      rw [e, e']
      intro d hd
      rw [slot_two nid tok _ _ d vv v1 v2 hA hB hc ex, slot_two nid' tok' _ _ d vv' v1 v2 hA hB hc ex']
      exact slotRel_refl _ (agree_refl C hC r) _

/-! ## The collision lists: written in place, or moved to the front -/

/-- The collision lists of `do_add_mut` and `do_add`: equal, or `xs` written in place at `pos`
against `v` moved to the front. -/
def InPlace (a b : List α) : Prop :=
  a = b ∨ ∃ (xs : List α) (pos : Nat) (v : α), pos < xs.length ∧ a = xs.set pos v ∧ b = v :: eraseAt xs pos

theorem inPlace_refl (l : List α) : InPlace l l := Or.inl rfl

/-- ★ The in-place write and the move to the front give the same list exactly when the position is 0,
for every list, position and value, when `pos` is the first index whose value `Equal` accepts and
`Equal` accepts `v` itself (every jank value but a NaN-like one). -/
theorem inPlace_eq_iff (eq : α → α → Bool) (xs : List α) (pos : Nat) (v : α) (hp : pos < xs.length)
    (hfirst : ∀ j (hj : j < pos), eq (xs[j]'(by omega)) v = false) (hv : eq v v = true) :
    xs.set pos v = v :: eraseAt xs pos ↔ pos = 0 := by
  constructor
  · intro h
    by_cases h0 : pos = 0
    · exact h0
    · exfalso
      have h1 := congrArg (fun l => l[0]?) h
      simp only [List.getElem?_cons_zero] at h1
      rw [List.getElem?_set, if_neg h0, List.getElem?_eq_getElem (by omega)] at h1
      have h2 := hfirst 0 (by omega)
      rw [Option.some.inj h1, hv] at h2
      cases h2
  · intro h0
    subst h0
    cases xs with
    | nil => simp at hp
    | cons a l => simp [eraseAt]

/-! ## `do_add_mut` against `do_add` -/

/-- ★ **`do_add_mut` (`assoc!`/`conj!`) against `do_add` (`assoc`/`conj`) from the same node**: the same
`added` flag, and trees that agree node by node, every collision list equal but for one in-place
write (`InPlace`). For every well-formed node, every hash, every equality, every owner token (the
in-place child and value writes, `ensure_mutable_values`, the moves, the copies below a node the
transient does not own, `make_merged_e` against `make_merged`). -/
theorem addMut_agree (cfg : Cfg α κ) (e : Nat) (v : α) (h : Nat) (hv : cfg.hashT v = h) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      Agree InPlace r ((doAddMut cfg e r N v h).run s).1.1 ((doAdd cfg r N v h).run s).1.1 ∧
        ((doAddMut cfg e r N v h).run s).1.2.1 = ((doAdd cfg r N v h).run s).1.2 := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      rw [doAddMut.eq_1, doAdd.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases hf : xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        dsimp only
        split
        · show InPlace (v :: xs) (v :: xs) ∧ true = true
          exact ⟨inPlace_refl _, rfl⟩
        · show InPlace (v :: xs) (v :: xs) ∧ true = true
          exact ⟨inPlace_refl _, rfl⟩
      | some pos =>
        obtain ⟨hpos, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        dsimp only
        split
        · show InPlace (setL xs pos v) (v :: eraseAt xs pos) ∧ false = false
          exact ⟨Or.inr ⟨xs, pos, v, hpos, rfl, rfl⟩, rfl⟩
        · show InPlace (v :: eraseAt xs pos) (v :: eraseAt xs pos) ∧ false = false
          exact ⟨inPlace_refl _, rfl⟩
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have eP : ((doAdd cfg (r + 1) N v h).run s).1 =
          (((copyInnerReplace N (pos N.nodemap D) ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1).run
            ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).2).1,
           ((doAdd cfg r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2) := by
        rw [doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA']; rfl
      by_cases hm : N.canMutate e = true
      · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (.inner N.id N.tok N.nodemap N.datamap N.vals (setL N.cs (pos N.nodemap D)
              ((doAddMut cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1),
             ((doAddMut cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2.1, true) := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_pos hA', if_pos hm]
          cases N with
          | inner => rfl
          | collision => simp [wfNode] at hw
        rw [e1, eP]
        dsimp only
        have oM := addMut_step cfg e v h hv r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        have oP := add_step cfg v h hv r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        have ihc := ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        exact ⟨agree_edits InPlace inPlace_refl r N _ _ D _ _ (edit_setChild r N _ D hw hD hA oM.wf)
          (edit_replace r N _ D _ hw hD hA oP.wf) ihc.1, ihc.2⟩
      · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (owned ((doAdd cfg (r + 1) N v h).run s).1.1 e, ((doAdd cfg (r + 1) N v h).run s).1.2, false) := by
          rw [doAddMut.eq_2, doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA', if_neg hm, if_pos hA']; rfl
        rw [e1]
        dsimp only
        exact ⟨(agree_owned_left InPlace _ _ e (r + 1)).mpr (agree_refl InPlace inPlace_refl _ _), rfl⟩
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · have eP : ((doAdd cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceValue N (pos N.datamap D) v).run s).1, false) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]; rfl
          by_cases hm : N.canMutate e = true
          · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
                (writeValue ((ensureMutableValues N e).run s).1 (pos N.datamap D) v, false, true) := by
              rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_pos hm]
              rfl
            rw [e1, eP]
            dsimp only
            exact ⟨agree_edits InPlace inPlace_refl r N _ _ D _ _ (edit_ensureWrite r N v D e s hw hD hA0 hB)
              (edit_replaceValue r N v D s hw hD hA0 hB) rfl, rfl⟩
          · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
                (ownedValues ((doAdd cfg (r + 1) N v h).run s).1.1 e, ((doAdd cfg (r + 1) N v h).run s).1.2, false) := by
              rw [doAddMut.eq_2, doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB', if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_neg hm,
                if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]
              rfl
            rw [e1]
            dsimp only
            exact ⟨(agree_ownedValues_left InPlace _ _ e (r + 1)).mpr (agree_refl InPlace inPlace_refl _ _), rfl⟩
        · generalize hval : N.values.getD (pos N.datamap D) default = val at hE
          have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
              (ownedValues ((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).2).1 e, true, N.canMutate e) := by
            rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            split <;> rfl
          have eP : ((doAdd cfg (r + 1) N v h).run s).1 =
              (((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged none r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged none r v h val (cfg.hashT val)).run s).2).1, true) := by
            rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            rfl
          rw [e1, eP]
          dsimp only
          rw [agree_ownedValues_left]
          have hag := agree_makeMerged InPlace inPlace_refl (some e) none v val h (cfg.hashT val) r s s
          have hw1 := wf_makeMerged (some e) v val h (cfg.hashT val) r s
          have hw2 := wf_makeMerged none v val h (cfg.hashT val) r s
          generalize (makeMerged (some e) r v h val (cfg.hashT val)).run s = q1 at hag hw1
          generalize (makeMerged none r v h val (cfg.hashT val)).run s = q2 at hag hw2
          obtain ⟨m1, s1⟩ := q1
          obtain ⟨m2, s2⟩ := q2
          dsimp only at hag hw1 hw2 ⊢
          exact ⟨agree_edits InPlace inPlace_refl r N _ _ D _ _ (edit_replaceMerged r N m1 D s1 hw hD hA0 hB hw1)
            (edit_replaceMerged r N m2 D s2 hw hD hA0 hB hw2) hag, rfl⟩
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (ownedValues ((copyInnerInsertValue N (2 ^ D) v).run s).1 e, true, N.canMutate e) := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']
          split <;> rfl
        have eP : ((doAdd cfg (r + 1) N v h).run s).1 = (((copyInnerInsertValue N (2 ^ D) v).run s).1, true) := by
          rw [doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']; rfl
        rw [e1, eP]
        dsimp only
        exact ⟨(agree_ownedValues_left InPlace _ _ e (r + 1)).mpr (agree_refl InPlace inPlace_refl _ _), rfl⟩

/-- ★ At the root: `add_mut` and `add` from the same champ agree node by node up to one in-place
collision write, with the same size. -/
theorem addMut_root_agree (cfg : Cfg α κ) (c : Champ α) (e : Nat) (v : α) (s : Al) (hw : wfNode 13 c.root = true) :
    Agree InPlace 13 ((c.addMut cfg e v).run s).1.root ((c.add cfg v).run s).1.root ∧
      ((c.addMut cfg e v).run s).1.size = ((c.add cfg v).run s).1.size := by
  obtain ⟨h1, h2⟩ := addMut_agree cfg e v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw
  refine ⟨h1, ?_⟩
  show c.size + (if ((doAddMut cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1 then 1 else 0) =
    c.size + (if ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.2 then 1 else 0)
  rw [h2]

/-! ## `do_sub_mut` against `do_sub` -/

/-- Two `sub_result`s agree: both nothing, the same value passed up, or related trees. -/
def SubAgree (R : Node α → Node α → Prop) : Jank.R3.Immer.Champ.Sub α → Jank.R3.Immer.Champ.Sub α → Prop
  | .nothing, .nothing => True
  | .singleton x, .singleton y => x = y
  | .tree a, .tree b => R a b
  | _, _ => False

theorem subAgree_tree_ownedValues (r : Nat) (A : Node α) (e : Nat) :
    SubAgree (Agree Eq r) (.tree (ownedValues A e)) (.tree A) :=
  (agree_ownedValues_left Eq A A e r).mpr (agree_refl Eq (fun _ => rfl) r A)

theorem subAgree_tree_owned (r : Nat) (A : Node α) (e : Nat) :
    SubAgree (Agree Eq r) (.tree (owned A e)) (.tree A) :=
  (agree_owned_left Eq A A e r).mpr (agree_refl Eq (fun _ => rfl) r A)

theorem subAgree_tree_refl (r : Nat) (A : Node α) : SubAgree (Agree Eq r) (.tree A) (.tree A) :=
  agree_refl Eq (fun _ => rfl) r A

/-- ★ **`do_sub_mut` (`dissoc!`/`disj!`) against `do_sub` (`dissoc`/`disj`) from the same node agree
EXACTLY**: the same result kind, the same value passed up, and trees agreeing node by node with every
collision list equal. For every well-formed node, every hash, every equality, every owner token (the
in-place child write, the moves, the value passed up and inlined by a mutable or a copied ancestor,
the copies below a node the transient does not own). -/
theorem subMut_agree (cfg : Cfg α κ) (e : Nat) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      SubAgree (Agree Eq r) ((doSubMut cfg e k r N h).run s).1.r ((doSub cfg k r N h).run s).1 := by
  intro r
  induction r with
  | zero =>
    intro _ N s _
    rw [doSubMut.eq_1, doSub.eq_1]
    unfold findIdx?
    cases hf : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => trivial
    | some cur =>
      dsimp only
      by_cases hl : N.collisions.length ≤ 2
      · rw [if_pos hl, if_neg (show ¬ N.collisions.length > 2 by omega)]
        split <;> rfl
      · rw [if_neg hl, if_pos (show N.collisions.length > 2 by omega)]
        split <;> rfl
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    rw [doSubMut.eq_2, doSub.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_pos hA', if_pos hA']
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have oP : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
          ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
        sub_step cfg k h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
      by_cases hm : N.canMutate e = true
      · simp only [hm, ↓reduceIte]
        have oM : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
            ((doSubMut cfg e k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1.r :=
          subMut_step cfg e k h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        have iw : SubAgree (Agree Eq r) ((doSubMut cfg e k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1.r
            ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
          ih (by omega) (N.child (N.childrenCountBit (2 ^ D))) s hcw
        simp only [StateT.run_bind]
        generalize (doSubMut cfg e k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q1 at oM iw
        generalize (doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q2 at oP iw
        obtain ⟨⟨res1, ow, mu⟩, s1⟩ := q1
        obtain ⟨res2, s2⟩ := q2
        dsimp only at oM oP iw ⊢
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
            split
            · next hc => (try rw [if_pos hc]); rfl
            · next hc =>
              try rw [if_neg hc]
              show Agree Eq (r + 1) (ownedValues ((copyInnerReplaceInline N (2 ^ D) (pos N.nodemap D) x).run s1).1 e)
                ((copyInnerReplaceInline N (2 ^ D) (pos N.nodemap D) x).run s2).1
              rw [agree_ownedValues_left]
              exact agree_edits Eq (fun _ => rfl) r N _ _ D _ _ (edit_replaceInline r N x D s1 hw hD hA)
                (edit_replaceInline r N x D s2 hw hD hA) rfl
        | tree t1 =>
          cases res2 with
          | nothing => exact (iw : False).elim
          | singleton _ => exact (iw : False).elim
          | tree t2 =>
            have ht : Agree Eq r t1 t2 := iw
            have hw1 : wfNode r t1 = true := oM.1
            have hw2 : wfNode r t2 = true := oP.1
            try dsimp only
            cases N with
            | collision => simp [wfNode] at hw
            | inner nid tok nm dm vs cs =>
              exact agree_edits Eq (fun _ => rfl) r _ _ _ D _ _ (edit_setChild r _ t1 D hw hD hA hw1)
                (edit_replace r _ t2 D s2 hw hD hA hw2) ht
      · simp only [hm, ↓reduceIte, Bool.false_eq_true]
        simp only [StateT.run_bind]
        generalize (doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q at oP
        obtain ⟨res, s1⟩ := q
        dsimp only at oP ⊢
        cases res with
        | nothing => trivial
        | singleton x =>
          try dsimp only
          split
          · next hc => (try rw [if_pos hc]); rfl
          · next hc =>
            try rw [if_neg hc]
            exact subAgree_tree_ownedValues (r + 1) _ e
        | tree t =>
          try dsimp only
          exact subAgree_tree_owned (r + 1) _ e
    · have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_neg hA', if_neg hA']
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_pos hB', if_pos hB']
        by_cases hE : cfg.eqTK (N.values.getD (pos N.datamap D) default) k = true
        · have hE' : cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true := hE
          rw [if_pos hE', if_pos hE']
          by_cases c1 : (N.nodemap != 0 || decide (N.dataCount > 2)) = true
          · rw [if_pos c1, if_pos c1]
            split <;> exact subAgree_tree_ownedValues (r + 1) _ e
          · rw [if_neg c1, if_neg c1]
            by_cases c2 : (N.dataCount == 2) = true
            · rw [if_pos c2, if_pos c2]
              split
              · next hsh =>
                try rw [if_pos hsh]
                split <;> rfl
              · next hsh =>
                try rw [if_neg hsh]
                by_cases hm : N.canMutate e = true
                · simp only [hm, ↓reduceIte]; exact subAgree_tree_ownedValues (r + 1) _ e
                · simp only [hm, ↓reduceIte, Bool.false_eq_true]; exact subAgree_tree_ownedValues (r + 1) _ e
            · rw [if_neg c2, if_neg c2]
              split <;> exact subAgree_tree_refl (r + 1) _
        · have hE' : ¬ cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true := hE
          rw [if_neg hE', if_neg hE']
          trivial
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_neg hB', if_neg hB']
        trivial

/-- ★ At the root: `sub_mut` and `sub` from the same champ agree node by node exactly, with the same
size. -/
theorem subMut_root_agree (cfg : Cfg α κ) (c : Champ α) (e : Nat) (k : κ) (s : Al) (hw : wfNode 13 c.root = true) :
    Agree Eq 13 ((c.subMut cfg e k).run s).1.root ((c.sub cfg k).run s).1.root ∧
      ((c.subMut cfg e k).run s).1.size = ((c.sub cfg k).run s).1.size := by
  have ag := subMut_agree cfg e k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
  unfold Champ.subMut Champ.sub
  simp only [StateT.run_bind]
  generalize (doSubMut cfg e k 13 c.root (cfg.hashK k)).run s = q1 at ag
  generalize (doSub cfg k 13 c.root (cfg.hashK k)).run s = q2 at ag
  obtain ⟨⟨res1, ow, mu⟩, s1⟩ := q1
  obtain ⟨res2, s2⟩ := q2
  dsimp only at ag ⊢
  cases res1 <;> cases res2 <;> (try exact ag.elim)
  · exact ⟨agree_refl Eq (fun _ => rfl) 13 _, rfl⟩
  · exact ⟨agree_refl Eq (fun _ => rfl) 13 _, rfl⟩
  · exact ⟨ag, rfl⟩

end Jank.R8.Champ

import Jank.R8.Champ.Agree

/-!
# Round 8, CHAMP: a sequence of transient steps against its persistent twin, node by node

`Agree.lean` compares ONE transient step with the persistent step from the same node. Across a
sequence the two trees differ in collision order (`addMut_agree`), so the next step runs on different
trees. Here, under a lawful equality (round 6's `Lawful`, with `Inv`), the persistent steps are shown to
be congruences for agreement up to collision order (`AgreeP`: `Agree` with collision lists compared as
permutations), and the sequence theorem follows:

- ★ `add_congr`, ★ `sub_congr`: `do_add` and `do_sub` of the same value or key on two well-formed nodes
  that agree up to collision order (the first without two `Equal` values) give results that agree up
  to collision order, with the same `added` flag / the same result kind.
- ★ `buildT_agree`, ★ `buildT_agree_empty`: **every sequence of persistent and transient steps (any owner
  tokens) and the same sequence with every transient step made persistent give champs that agree node
  by node up to the order inside collision nodes, with the same size** (from `champ::empty()`, and from
  any two champs meeting `Inv` that agree so).
- ★ `agree_iter`: such champs iterate as permutations of each other.

Without a lawful equality the congruence fails (a collision node holding two values `Equal` to the key
finds a different one first in each order); jank's `=` is lawful on most kinds (D12, D8, R55 and NaN are
the exceptions rounds 6-7 list).
-/

namespace Jank.R8.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ

variable {α κ : Type} [Inhabited α]

/-- Collision lists compared as permutations. -/
abbrev PermL (a b : List α) : Prop := a.Perm b

/-- Agreement node by node up to the order inside collision nodes. -/
abbrev AgreeP : Nat → Node α → Node α → Prop := Agree PermL

/-! ## The relation -/

theorem slotRel_trans (R : Node α → Node α → Prop) (hR : ∀ a b c, R a b → R b c → R a c) :
    ∀ x y z : Slot α, SlotRel R x y → SlotRel R y z → SlotRel R x z := by
  intro x y z h1 h2
  cases x <;> cases y <;> cases z <;> simp only [SlotRel] at h1 h2 ⊢
  · exact h1.trans h2
  · exact hR _ _ _ h1 h2

theorem agree_trans (C : List α → List α → Prop) (hC : ∀ a b c, C a b → C b c → C a c) :
    ∀ r (A B D : Node α), Agree C r A B → Agree C r B D → Agree C r A D
  | 0, _, _, _, h1, h2 => hC _ _ _ h1 h2
  | r + 1, _, _, _, h1, h2 => fun d hd => slotRel_trans _ (agree_trans C hC r) _ _ _ (h1 d hd) (h2 d hd)

theorem inPlace_perm (a b : List α) (h : InPlace a b) : a.Perm b := by
  rcases h with h | ⟨xs, pos, v, hp, ha, hb⟩
  · rw [h]
  · rw [ha, hb]; exact perm_setL xs pos v default hp

/-- Two edits of one slot of two agreeing nodes agree when the new slots do. -/
theorem agree_edits2 (C : List α → List α → Prop) (r : Nat) (A B A' B' : Node α) (D : Nat) (XA XB : Slot α)
    (hA : Edit r A A' D XA) (hB : Edit r B B' D XB) (hAB : Agree C (r + 1) A B)
    (hX : SlotRel (fun a b => Agree C r a b) XA XB) : Agree C (r + 1) A' B' := by
  intro d hd
  rw [hA.2 d hd, hB.2 d hd]
  by_cases h : d = D
  · rw [if_pos h, if_pos h]; exact hX
  · rw [if_neg h, if_neg h]; exact hAB d hd

/-! ## Agreeing nodes have the same bitmaps and permuted iterations -/

def skind : Slot α → Nat
  | .empty => 0
  | .data _ => 1
  | .child _ => 2

theorem slotRel_kind (R : Node α → Node α → Prop) : ∀ x y : Slot α, SlotRel R x y → skind x = skind y := by
  intro x y h
  cases x <;> cases y <;> simp only [SlotRel] at h <;> rfl

theorem kind_slot (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (d : Nat) :
    N.nodemap.testBit d = (skind (slot N d) == 2) ∧ N.datamap.testBit d = (skind (slot N d) == 1) := by
  obtain ⟨h1, _⟩ := wf_parts r N hw
  unfold slot
  by_cases hn : N.nodemap.testBit d = true
  · rw [if_pos hn, bits_disjoint _ _ h1 d hn, hn]; exact ⟨rfl, rfl⟩
  · rw [if_neg hn]
    have hn' : N.nodemap.testBit d = false := by simpa using hn
    by_cases hd : N.datamap.testBit d = true
    · rw [if_pos hd, hd, hn']; exact ⟨rfl, rfl⟩
    · have hd' : N.datamap.testBit d = false := by simpa using hd
      rw [if_neg hd, hd', hn']; exact ⟨rfl, rfl⟩

theorem testBit_big (m d : Nat) (hm : m < 2 ^ 32) (hd : 32 ≤ d) : m.testBit d = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hd))

/-- Two well-formed nodes that agree slot by slot have the same bitmaps. -/
theorem agree_maps (C : List α → List α → Prop) (r : Nat) (A B : Node α) (hwA : wfNode (r + 1) A = true)
    (hwB : wfNode (r + 1) B = true) (hag : Agree C (r + 1) A B) :
    A.nodemap = B.nodemap ∧ A.datamap = B.datamap := by
  obtain ⟨_, h2A, h3A, _⟩ := wf_parts r A hwA
  obtain ⟨_, h2B, h3B, _⟩ := wf_parts r B hwB
  constructor
  · apply Nat.eq_of_testBit_eq
    intro d
    by_cases hd : d < 32
    · rw [(kind_slot r A hwA d).1, (kind_slot r B hwB d).1, slotRel_kind _ _ _ (hag d hd)]
    · rw [testBit_big _ d h2A (by omega), testBit_big _ d h2B (by omega)]
  · apply Nat.eq_of_testBit_eq
    intro d
    by_cases hd : d < 32
    · rw [(kind_slot r A hwA d).2, (kind_slot r B hwB d).2, slotRel_kind _ _ _ (hag d hd)]
    · rw [testBit_big _ d h3A (by omega), testBit_big _ d h3B (by omega)]

theorem perm_flatMap_congr {β γ : Type} (f g : β → List γ) :
    ∀ l : List β, (∀ x ∈ l, (f x).Perm (g x)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => by simp
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h x (by simp)).append (perm_flatMap_congr f g l (fun y hy => h y (by simp [hy])))

/-- ★ Nodes that agree up to collision order iterate as permutations of each other. -/
theorem agree_iter : ∀ r (A B : Node α), wfNode r A = true → wfNode r B = true → AgreeP r A B →
    (iterNode r A).Perm (iterNode r B)
  | 0, A, B, _, _, hag => by rw [iterNode.eq_1, iterNode.eq_1]; exact hag
  | r + 1, A, B, hwA, hwB, hag => by
    refine (iter_slots r A hwA).trans (List.Perm.trans ?_ (iter_slots r B hwB).symm)
    apply perm_flatMap_congr
    intro d hd
    have hd' : d < 32 := List.mem_range.mp hd
    have hs := hag d hd'
    generalize hsa : slot A d = sa at hs
    generalize hsb : slot B d = sb at hs
    cases sa <;> cases sb <;> simp only [SlotRel] at hs
    · exact List.Perm.refl _
    · rw [hs]
    · rename_i a b
      exact agree_iter r a b (slot_child_wf r A hwA d hd' a hsa) (slot_child_wf r B hwB d hd' b hsb) hs

/-! ## Uniqueness below a node, and one `Equal` value per collision list -/

variable {cfg : Cfg α κ}

theorem uniq_slot (L : Lawful cfg) (r : Nat) (N : Node α) (hw : wfNode (r + 1) N = true) (D : Nat) (hD : D < 32)
    (hu : Uniq cfg (iterNode (r + 1) N)) : Uniq cfg (slotL r (slot N D)) := by
  have p := iter_split r N hw D hD
  have := (p.pairwise_iff (hsymF L)).mp hu
  exact (List.pairwise_append.mp this).1

/-- In a list of pairwise non-`Equal` values, two values a predicate accepts are the same, when the
predicate's accepted values are pairwise `Equal`. -/
theorem one_of_uniq (L : Lawful cfg) (xs : List α) (hu : Uniq cfg xs) (q : α → Bool)
    (hq : ∀ x y, q x = true → q y = true → cfg.eqTT x y = true) :
    ∀ x ∈ xs, ∀ y ∈ xs, q x = true → q y = true → x = y :=
  fun x hx y hy hqx hqy => uniq_eq L xs hu x y hx hy (hq x y hqx hqy)

theorem eqTT_via (L : Lawful cfg) (v : α) : ∀ x y, cfg.eqTT x v = true → cfg.eqTT y v = true → cfg.eqTT x y = true := by
  intro x y hx hy
  rw [L.eqTT_key] at hx hy ⊢
  exact L.trans _ _ _ hx (L.symm _ _ hy)

theorem eqTK_via (L : Lawful cfg) (k : κ) : ∀ x y, cfg.eqTK x k = true → cfg.eqTK y k = true → cfg.eqTT x y = true :=
  fun x y hx hy => L.eq_of_eqTK x y k hx hy

/-- Two permuted lists with at most one accepted value: both find nothing, or both find that value,
and what is left after removing it is permuted too. -/
theorem perm_found (p : α → Bool) (xs ys : List α) (hp : xs.Perm ys)
    (hone : ∀ x ∈ xs, ∀ y ∈ xs, p x = true → p y = true → x = y) :
    (xs.findIdx? p = none ∧ ys.findIdx? p = none) ∨
    (∃ i j, xs.findIdx? p = some i ∧ ys.findIdx? p = some j ∧ i < xs.length ∧ j < ys.length ∧
      xs.getD i default = ys.getD j default ∧ (eraseAt xs i).Perm (eraseAt ys j)) := by
  cases hx : xs.findIdx? p with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    rw [List.findIdx?_eq_none_iff] at hx ⊢
    intro y hy
    exact hx y (hp.symm.subset hy)
  | some i =>
    right
    obtain ⟨hi, hpi, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hx
    cases hy : ys.findIdx? p with
    | none =>
      exfalso
      rw [List.findIdx?_eq_none_iff] at hy
      have h1 := hy xs[i] (hp.subset (List.getElem_mem hi))
      simp [hpi] at h1
    | some j =>
      obtain ⟨hjl, hpj, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hy
      have heq : xs[i] = ys[j] :=
        hone _ (List.getElem_mem hi) _ (hp.symm.subset (List.getElem_mem hjl)) hpi hpj
      refine ⟨i, j, rfl, rfl, hi, hjl, ?_, ?_⟩
      · rw [getD_eq_getElem' xs i default hi, getD_eq_getElem' ys j default hjl, heq]
      · have p1 := perm_eraseAt xs i default hi
        have p2 := perm_eraseAt ys j default hjl
        rw [getD_eq_getElem' xs i default hi, heq] at p1
        rw [getD_eq_getElem' ys j default hjl] at p2
        exact ((p1.symm.trans hp).trans p2).cons_inv

theorem eraseAt_two (l : List α) (cur : Nat) (hl : l.length = 2) (hc : cur < 2) :
    eraseAt l cur = [l.getD (if cur == 0 then 1 else 0) default] := by
  match l, hl with
  | [a, b], _ =>
    rcases (show cur = 0 ∨ cur = 1 by omega) with h | h <;> subst h <;> rfl

/-! ## `do_add` is a congruence -/

/-- ★ `do_add` of one value on two well-formed nodes agreeing up to collision order (the first holding
no two `Equal` values) gives trees agreeing up to collision order and the same `added` flag, under a
lawful equality. -/
theorem add_congr (L : Lawful cfg) (v : α) (h : Nat) (hv : cfg.hashT v = h) :
    ∀ r, r ≤ 13 → ∀ (A B : Node α) (s s' : Al), wfNode r A = true → wfNode r B = true →
      Uniq cfg (iterNode r A) → AgreeP r A B →
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
        have hone := one_of_uniq L xs huA (fun x => cfg.eqTT x v) (eqTT_via L v)
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
      have hua : Uniq cfg (iterNode r (A.cs.getD (pos A.nodemap D) Node.dummy)) := by
        have := uniq_slot L r A hwA D hD huA; rw [hsA] at this; exact this
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

/-! ## `do_sub` is a congruence -/

/-- ★ `do_sub` of one key on two well-formed nodes agreeing up to collision order (the first holding no
two `Equal` values) gives the same result kind, the same value passed up, and trees agreeing up to
collision order, under a lawful equality. -/
theorem sub_congr (L : Lawful cfg) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (A B : Node α) (s s' : Al), wfNode r A = true → wfNode r B = true →
      Uniq cfg (iterNode r A) → AgreeP r A B →
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
    have hone := one_of_uniq L A.collisions huA (fun x => cfg.eqTK x k) (eqTK_via L k)
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
      have hua : Uniq cfg (iterNode r (A.child (A.childrenCountBit (2 ^ D)))) := by
        have := uniq_slot L r A hwA D hD huA; rw [hsA] at this; exact this
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

/-! ## The sequence theorem -/

theorem add_root_congr (L : Lawful cfg) (A B : Champ α) (v : α) (s s' : Al) (hiA : Inv cfg A) (hiB : Inv cfg B)
    (hag : AgreeP 13 A.root B.root) (hsz : A.size = B.size) :
    AgreeP 13 ((A.add cfg v).run s).1.root ((B.add cfg v).run s').1.root ∧
      ((A.add cfg v).run s).1.size = ((B.add cfg v).run s').1.size := by
  obtain ⟨h1, h2⟩ := add_congr L v (cfg.hashT v) rfl 13 (Nat.le_refl _) A.root B.root s s' hiA.wf hiB.wf hiA.uniq hag
  refine ⟨h1, ?_⟩
  show A.size + (if ((doAdd cfg 13 A.root v (cfg.hashT v)).run s).1.2 then 1 else 0) =
    B.size + (if ((doAdd cfg 13 B.root v (cfg.hashT v)).run s').1.2 then 1 else 0)
  rw [hsz, h2]

theorem sub_root_congr (L : Lawful cfg) (A B : Champ α) (k : κ) (s s' : Al) (hiA : Inv cfg A) (hiB : Inv cfg B)
    (hag : AgreeP 13 A.root B.root) (hsz : A.size = B.size) :
    AgreeP 13 ((A.sub cfg k).run s).1.root ((B.sub cfg k).run s').1.root ∧
      ((A.sub cfg k).run s).1.size = ((B.sub cfg k).run s').1.size := by
  have ag := sub_congr L k (cfg.hashK k) 13 (Nat.le_refl _) A.root B.root s s' hiA.wf hiB.wf hiA.uniq hag
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

/-- One transient step against the same step made persistent, from the same champ. -/
theorem persist_step (c : Champ α) (op : TOp α κ) (s : Al) (hw : wfNode 13 c.root = true) :
    AgreeP 13 ((applyT cfg c op).run s).1.root ((applyT cfg c op.persist).run s).1.root ∧
      ((applyT cfg c op).run s).1.size = ((applyT cfg c op.persist).run s).1.size := by
  cases op with
  | add v => exact ⟨agree_refl PermL (fun l => List.Perm.refl l) 13 _, rfl⟩
  | sub k => exact ⟨agree_refl PermL (fun l => List.Perm.refl l) 13 _, rfl⟩
  | addMut e v =>
    obtain ⟨h1, h2⟩ := addMut_root_agree cfg c e v s hw
    exact ⟨agree_mono InPlace PermL inPlace_perm 13 _ _ h1, h2⟩
  | subMut e k =>
    obtain ⟨h1, h2⟩ := subMut_root_agree cfg c e k s hw
    exact ⟨agree_mono Eq PermL (fun a b hab => hab ▸ List.Perm.refl a) 13 _ _ h1, h2⟩

/-- The persistent step on two agreeing champs. -/
theorem congr_step (L : Lawful cfg) (A B : Champ α) (op : TOp α κ) (s s' : Al) (hiA : Inv cfg A) (hiB : Inv cfg B)
    (hag : AgreeP 13 A.root B.root) (hsz : A.size = B.size) :
    AgreeP 13 ((applyT cfg A op.persist).run s).1.root ((applyT cfg B op.persist).run s').1.root ∧
      ((applyT cfg A op.persist).run s).1.size = ((applyT cfg B op.persist).run s').1.size := by
  cases op with
  | add v => exact add_root_congr L A B v s s' hiA hiB hag hsz
  | addMut e v => exact add_root_congr L A B v s s' hiA hiB hag hsz
  | sub k => exact sub_root_congr L A B k s s' hiA hiB hag hsz
  | subMut e k => exact sub_root_congr L A B k s s' hiA hiB hag hsz

/-- ★ **A sequence of persistent and transient steps against the same sequence with every transient
step made persistent**: from two champs meeting `Inv` that agree up to collision order with the same
size, the results agree node by node up to the order inside collision nodes and have the same size,
under a lawful equality, for every sequence and every owner token. -/
theorem buildT_agree (L : Lawful cfg) :
    ∀ (ops : List (TOp α κ)) (A B : Champ α) (s s' : Al), Inv cfg A → Inv cfg B →
      AgreeP 13 A.root B.root → A.size = B.size →
      AgreeP 13 ((buildT cfg A ops).run s).1.root ((buildT cfg B (ops.map TOp.persist)).run s').1.root ∧
        ((buildT cfg A ops).run s).1.size = ((buildT cfg B (ops.map TOp.persist)).run s').1.size
  | [], _, _, _, _, _, _, hag, hsz => ⟨hag, hsz⟩
  | op :: ops, A, B, s, s', hiA, hiB, hag, hsz => by
    have eA : ((buildT cfg A (op :: ops)).run s).1 =
        ((buildT cfg ((applyT cfg A op).run s).1 ops).run ((applyT cfg A op).run s).2).1 := rfl
    have eB : ((buildT cfg B ((op :: ops).map TOp.persist)).run s').1 =
        ((buildT cfg ((applyT cfg B op.persist).run s').1 (ops.map TOp.persist)).run
          ((applyT cfg B op.persist).run s').2).1 := rfl
    rw [eA, eB]
    have h1 := persist_step (cfg := cfg) A op s hiA.wf
    have h2 := congr_step L A B op s s' hiA hiB hag hsz
    exact buildT_agree L ops _ _ _ _ (stepT L A s hiA op).1 (stepT L B s' hiB op.persist).1
      (agree_trans PermL (fun a b c h1 h2 => h1.trans h2) 13 _ _ _ h1.1 h2.1) (h1.2.trans h2.2)

/-- ★ **From `champ::empty()`**: a jank program's chain of `conj`/`assoc`/`disj`/`dissoc` and
`transient`/`conj!`/`assoc!`/`disj!`/`dissoc!`/`persistent!` and the same chain with no transient give
champs that agree node by node up to the order inside collision nodes, with the same size (lawful
equality). The collision order itself can differ (H8-1, `addMut_agree`). -/
theorem buildT_agree_empty (L : Lawful cfg) (ops : List (TOp α κ)) (s s' : Al) :
    AgreeP 13 ((buildT cfg Champ.empty ops).run s).1.root ((buildT cfg Champ.empty (ops.map TOp.persist)).run s').1.root ∧
      ((buildT cfg Champ.empty ops).run s).1.size = ((buildT cfg Champ.empty (ops.map TOp.persist)).run s').1.size :=
  buildT_agree L ops Champ.empty Champ.empty s s' (inv_empty cfg) (inv_empty cfg)
    (agree_refl PermL (fun l => List.Perm.refl l) 13 _) rfl

end Jank.R8.Champ

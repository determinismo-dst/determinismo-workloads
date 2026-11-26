import Jank.R6.Champ.Laws
import Jank.R6.Champ.Mut

/-!
# Round 7, CHAMP: the transient sequence theorem

Round 6 proved law 2 (`build_keys`: every sequence of persistent `add`/`sub` from `champ::empty()`
keeps `Inv` and yields exactly the keys Clojure's model holds) and gave the transient steps the same
one-step facts (`addMut_step`, `subMut_step`), but the sequence theorem with transient steps needed
"`do_sub_mut` of a key `get` finds is never nothing" (round 5 had it for `do_sub` only).

- ★ `doSubMut_found`: `do_sub_mut` (`dissoc!`/`disj!`) of a key `get` finds is never "nothing", and at
  the root it is a tree, on the mutating and the copying branch alike, for every hash and equality.
- ★ `subMut_cases`: so `sub_mut` either leaves the champ (key absent: round 5's `subMut_absent`) or
  removes one value `Equal` to the key with `size - 1`.
- ★ `inv_addMut`, ★ `inv_subMut`, ★ `keys_addMut`, ★ `keys_subMut`, ★ `get_addMut_other`,
  ★ `get_subMut_other`: `Inv`, law 2's one step and law 1 for the transient steps (lawful equality).
- ★ `buildT_keys`, ★ `buildT_from_empty`: **law 2 for every sequence mixing persistent and transient
  steps** (`assoc`/`conj`, `dissoc`/`disj`, `assoc!`/`conj!`, `dissoc!`/`disj!` with any owner
  tokens), from any champ meeting `Inv` and from `champ::empty()`: the invariant is kept and the keys
  are exactly the model's, which does not depend on which steps were transient.
  `transient` and `persistent!` (`Champ.transient`, `Transient.persistentL/R`) only change the owner
  token and move the champ (round 3's replica), so a jank program's sequence of
  `conj`/`disj`/`transient`/`conj!`/`disj!`/`persistent!` on one collection is such a list.
- ★ `buildT_same_keys`: a sequence and the one with every transient step made persistent yield the
  same keys (transients and persistent ops agree by contents; node shapes may differ).
-/

namespace Jank.R7.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ

variable {α κ : Type} [Inhabited α]

/-! ## `do_sub_mut` of a present key -/

theorem run_bind_eq {β γ : Type} (x : M β) (f : β → M γ) (s : Al) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

/-- ★ `do_sub_mut` of a key `get` finds is never "nothing"; at the root (shift 0) it is a tree. -/
theorem doSubMut_found (cfg : Cfg α κ) (e : Nat) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      getLoop cfg k r N (h >>> (65 - 5 * r)) ≠ none →
      ((doSubMut cfg e k r N h).run s).1.r.isNothing = false ∧
      (r = 13 → ((doSubMut cfg e k r N h).run s).1.r.isTree = true) := by
  intro r
  induction r with
  | zero =>
    intro _ N s _ hg
    rw [getLoop.eq_1] at hg
    have h2 : (N.collisions.findIdx? fun x => cfg.eqTK x k).isNone = false := by
      rw [← find_findIdx_isNone]
      cases hf : N.collisions.find? (fun x => cfg.eqTK x k)
      · exact absurd hf hg
      · rfl
    refine ⟨?_, fun h0 => absurd h0 (by omega)⟩
    rw [doSubMut.eq_1]
    unfold findIdx?
    cases hx : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => rw [hx] at h2; cases h2
    | some cur =>
      dsimp only
      split
      · split <;> rfl
      · split <;> rfl
  | succ r ih =>
    intro hr N s hw hg
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 1 <<< D := by unfold bitAt; rw [hDdef]
    have h0iff : (maxShift - 5 * (r + 1) > 0) ↔ r + 1 ≠ 13 := by unfold maxShift; omega
    rw [getLoop.eq_2] at hg
    dsimp only at hg
    rw [bit_forms, hbit] at hg
    rw [doSubMut.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : (N.nodemap &&& 1 <<< D != 0) = true
    · rw [if_pos hA, shr_step h r hr] at hg
      rw [if_pos hA]
      have hcw := child_wf r N hw D hD hA
      by_cases hm : N.canMutate e = true
      · rw [if_pos hm, run_bind_eq]
        have hn := (ih (by omega) _ s hcw hg).1
        generalize (doSubMut cfg e k r (N.child (N.childrenCountBit (1 <<< D))) h).run s = q at hn
        obtain ⟨⟨rr, ow, mu⟩, s1⟩ := q
        try dsimp only
        try dsimp only at hn
        cases rr with
        | nothing => cases hn
        | singleton x =>
          try dsimp only
          constructor
          · split <;> (try simp only [hm, ↓reduceIte]) <;> rfl
          · intro h13
            split
            · next hc =>
              exfalso
              have : maxShift - 5 * (r + 1) > 0 := by simp at hc; exact hc.2
              exact (h0iff.mp this) h13
            · (try simp only [hm, ↓reduceIte]); rfl
        | tree t =>
          try dsimp only
          constructor
          · (try simp only [hm, ↓reduceIte]); first | rfl | (split <;> rfl)
          · intro _; (try simp only [hm, ↓reduceIte]); first | rfl | (split <;> rfl)
      · rw [if_neg hm, run_bind_eq]
        have hn := (doSub_found cfg k h r (by omega) _ s hcw hg).1
        generalize (doSub cfg k r (N.child (N.childrenCountBit (1 <<< D))) h).run s = q at hn
        obtain ⟨rr, s1⟩ := q
        try dsimp only
        try dsimp only at hn
        simp only [pure_bind]
        cases rr with
        | nothing => cases hn
        | singleton x =>
          try dsimp only
          constructor
          · split <;> (try simp only [hm, ↓reduceIte, Bool.false_eq_true]) <;> rfl
          · intro h13
            split
            · next hc =>
              exfalso
              have : maxShift - 5 * (r + 1) > 0 := by simp at hc; exact hc.2
              exact (h0iff.mp this) h13
            · (try simp only [hm, ↓reduceIte, Bool.false_eq_true]); rfl
        | tree t =>
          try dsimp only
          constructor
          · (try simp only [hm, ↓reduceIte, Bool.false_eq_true]); first | rfl | (split <;> rfl)
          · intro _; (try simp only [hm, ↓reduceIte, Bool.false_eq_true]); first | rfl | (split <;> rfl)
    · by_cases hB : (N.datamap &&& 1 <<< D != 0) = true
      · have hlt := data_slot_lt r N hw D hD hB
        rw [if_neg hA, if_pos hB, getElem?_of_lt _ _ hlt] at hg
        dsimp only at hg
        have hE : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k = true := by
          cases hc : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k
          · rw [hc] at hg; simp at hg
          · rfl
        rw [if_neg hA, if_pos hB]
        rw [if_pos hE]
        constructor
        · split
          · split <;> rfl
          · split
            · split
              · split <;> rfl
              · by_cases hm : N.canMutate e = true <;> simp only [hm, ↓reduceIte] <;> rfl
            · split <;> rfl
        · intro h13
          split
          · split <;> rfl
          · split
            · split
              · next hc => exfalso; exact (h0iff.mp hc) h13
              · by_cases hm : N.canMutate e = true <;> simp only [hm, ↓reduceIte] <;> rfl
            · split <;> rfl
      · rw [if_neg hA, if_neg hB] at hg
        exact absurd rfl hg

/-! ## What `add_mut` and `sub_mut` do at the root -/

theorem addMut_root (cfg : Cfg α κ) (e : Nat) (c : Champ α) (v : α) (s : Al) :
    ((c.addMut cfg e v).run s).1.root = ((doAddMut cfg e 13 c.root v (cfg.hashT v)).run s).1.1 := rfl

theorem addMut_size (cfg : Cfg α κ) (e : Nat) (c : Champ α) (v : α) (s : Al) :
    ((c.addMut cfg e v).run s).1.size =
      c.size + (if ((doAddMut cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1 then 1 else 0) := rfl

/-- ★ `sub_mut` at the root: the same champ (key absent), or a tree without one value `Equal` to the
key, with `size - 1`. -/
theorem subMut_cases (cfg : Cfg α κ) (e : Nat) (c : Champ α) (k : κ) (s : Al) (hw : wfNode 13 c.root = true) :
    (((c.subMut cfg e k).run s).1 = c ∧ Champ.get cfg c k = none) ∨
    (∃ t, ((c.subMut cfg e k).run s).1 = { root := t, size := c.size - 1 } ∧ SubOut cfg k 13 c.root (.tree t)) := by
  by_cases hg : Champ.get cfg c k = none
  · exact Or.inl ⟨by rw [subMut_absent cfg e c k s hw hg], hg⟩
  · right
    have ⟨_, ht⟩ := doSubMut_found cfg e k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
      (by rw [shr13]; exact hg)
    have o := subMut_step cfg e k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    unfold Champ.subMut
    simp only [StateT.run_bind]
    generalize ((doSubMut cfg e k 13 c.root (cfg.hashK k)).run s) = q at ht o
    obtain ⟨res, s1⟩ := q
    obtain ⟨rr, ow, mu⟩ := res
    cases rr with
    | tree t => exact ⟨t, rfl, o⟩
    | _ => cases (ht rfl)

/-! ## The one-step laws from `AddOut`/`SubOut` (shared by the persistent and transient steps) -/

variable {cfg : Cfg α κ}

theorem hsymF (L : Lawful cfg) {a b : α} (h : cfg.eqTT a b = false) : cfg.eqTT b a = false := by
  cases h' : cfg.eqTT b a
  · rfl
  · rw [L.eqTT_symm b a h'] at h; cases h

/-- An add step (root `N'`, flag `a`, `size` grown by the flag, the flag being "`get` found
nothing") keeps `Inv`. -/
theorem inv_of_add (L : Lawful cfg) (c c' : Champ α) (v : α) (a : Bool) (hi : Inv cfg c)
    (o : AddOut cfg 13 c.root v c'.root a) (hsz : c'.size = c.size + (if a then 1 else 0))
    (hflag : a = (Champ.get cfg c (L.key v)).isNone) : Inv cfg c' := by
  obtain ⟨pg, pr⟩ := addOut_norm L c.root v _ _ o hi.uniq
  refine ⟨o.wf, o.hp hi.hp, ?_, ?_⟩
  · show Uniq cfg (iterNode 13 c'.root)
    cases ha : a
    · obtain ⟨x, rest, hxe, p1, p2⟩ := pr ha
      have hu1 := List.pairwise_cons.mp ((p1.pairwise_iff (hsymF L)).mp hi.uniq)
      apply (p2.pairwise_iff (hsymF L)).mpr
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hu1.2⟩
      cases h : cfg.eqTT v y
      · rfl
      · have := hu1.1 y hy
        rw [L.eqTT_key] at hxe this h
        rw [L.trans _ _ _ hxe h] at this; cases this
    · have hnone : Champ.get cfg c (L.key v) = none := by
        rw [ha] at hflag; exact Option.isNone_iff_eq_none.mp hflag.symm
      have hno := (get_none_iff L c hi (L.key v)).mp hnone
      apply ((pg ha).pairwise_iff (hsymF L)).mpr
      refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hi.uniq⟩
      have := hno y hy
      rw [L.eqTK_key, ← L.eqTT_key] at this
      exact hsymF L this
  · rw [hsz, hi.size]
    show (iterNode 13 c.root).length + _ = (iterNode 13 c'.root).length
    cases ha : a
    · obtain ⟨x, _, _, hp⟩ := o.replaced ha
      have := hp.length_eq
      simp only [List.length_cons] at this
      simp; omega
    · have := (o.grew ha).length_eq
      simp only [List.length_cons] at this
      simp; omega

theorem keys_of_add (L : Lawful cfg) (c c' : Champ α) (v : α) (a : Bool) (hi : Inv cfg c)
    (o : AddOut cfg 13 c.root v c'.root a) (k : κ) :
    (∃ x ∈ c'.toList, cfg.eqTK x k = true) ↔ (cfg.eqTK v k = true ∨ ∃ x ∈ c.toList, cfg.eqTK x k = true) := by
  obtain ⟨pg, pr⟩ := addOut_norm L c.root v _ _ o hi.uniq
  show (∃ x ∈ iterNode 13 c'.root, _) ↔ (_ ∨ ∃ x ∈ iterNode 13 c.root, _)
  cases ha : a
  · obtain ⟨y, rest, hye, p1, p2⟩ := pr ha
    constructor
    · intro ⟨x, hx, he⟩
      rcases List.mem_cons.mp (p2.subset hx) with h | h
      · exact Or.inl (h ▸ he)
      · exact Or.inr ⟨x, p1.symm.subset (List.mem_cons_of_mem _ h), he⟩
    · intro h
      rcases h with h | ⟨x, hx, he⟩
      · exact ⟨v, p2.symm.subset (List.mem_cons_self ..), h⟩
      · rcases List.mem_cons.mp (p1.subset hx) with h | h
        · subst h
          exact ⟨v, p2.symm.subset (List.mem_cons_self ..), L.eqTK_trans v x k (L.eqTT_symm x v hye) he⟩
        · exact ⟨x, p2.symm.subset (List.mem_cons_of_mem _ h), he⟩
  · constructor
    · intro ⟨x, hx, he⟩
      rcases List.mem_cons.mp ((pg ha).subset hx) with h | h
      · exact Or.inl (h ▸ he)
      · exact Or.inr ⟨x, h, he⟩
    · intro h
      rcases h with h | ⟨x, hx, he⟩
      · exact ⟨v, (pg ha).symm.subset (List.mem_cons_self ..), h⟩
      · exact ⟨x, (pg ha).symm.subset (List.mem_cons_of_mem _ hx), he⟩

theorem get_other_of_add (L : Lawful cfg) (c c' : Champ α) (v : α) (a : Bool) (hi : Inv cfg c)
    (hi' : Inv cfg c') (o : AddOut cfg 13 c.root v c'.root a) (k' : κ) (hne : L.eqK (L.key v) k' = false) :
    Champ.get cfg c' k' = Champ.get cfg c k' := by
  apply get_congr L _ _ hi' hi k'
  intro x hx
  have hxv : x ≠ v := by
    intro h; subst h; rw [L.eqTK_key, hne] at hx; cases hx
  obtain ⟨pg, pr⟩ := addOut_norm L c.root v _ _ o hi.uniq
  show x ∈ iterNode 13 c'.root ↔ x ∈ iterNode 13 c.root
  cases ha : a
  · obtain ⟨y, rest, hye, p1, p2⟩ := pr ha
    have hxy : x ≠ y := by
      intro h; subst h
      have : L.eqK (L.key v) k' = true :=
        L.trans _ _ _ (L.symm _ _ (by rw [← L.eqTT_key]; exact hye)) (by rw [← L.eqTK_key]; exact hx)
      rw [this] at hne; cases hne
    rw [p2.mem_iff, p1.mem_iff]
    simp [hxv, hxy]
  · rw [(pg ha).mem_iff]
    simp [hxv]

/-- A sub step's two outcomes. -/
def SubRes (cfg : Cfg α κ) (c c' : Champ α) (k : κ) : Prop :=
  (c' = c ∧ Champ.get cfg c k = none) ∨
    (∃ t, c' = { root := t, size := c.size - 1 } ∧ SubOut cfg k 13 c.root (.tree t))

theorem inv_of_sub (L : Lawful cfg) (c c' : Champ α) (k : κ) (hi : Inv cfg c) (hr : SubRes cfg c c' k) :
    Inv cfg c' := by
  rcases hr with ⟨e, _⟩ | ⟨t, e, o⟩
  · rw [e]; exact hi
  · rw [e]
    obtain ⟨hw, ⟨y, _, hp⟩, hh⟩ := o
    refine ⟨hw, hh hi.hp, ?_, ?_⟩
    · have := (hp.pairwise_iff (hsymF L)).mp hi.uniq
      exact (List.pairwise_cons.mp this).2
    · have := hp.length_eq
      simp only [List.length_cons] at this
      show c.size - 1 = (iterNode 13 t).length
      rw [hi.size]; show (iterNode 13 c.root).length - 1 = _; omega

theorem keys_of_sub (L : Lawful cfg) (c c' : Champ α) (k : κ) (hi : Inv cfg c) (hr : SubRes cfg c c' k) (k' : κ) :
    (∃ x ∈ c'.toList, cfg.eqTK x k' = true) ↔ (L.eqK k k' = false ∧ ∃ x ∈ c.toList, cfg.eqTK x k' = true) := by
  rcases hr with ⟨e, hg⟩ | ⟨t, e, o⟩
  · rw [e]
    have hno := (get_none_iff L c hi k).mp hg
    constructor
    · intro ⟨x, hx, he⟩
      refine ⟨?_, x, hx, he⟩
      cases hkk : L.eqK k k'
      · rfl
      · have := hno x hx
        rw [L.eqTK_key] at this he
        rw [L.trans _ _ _ he (L.symm _ _ hkk)] at this; cases this
    · exact fun h => h.2
  · rw [e]
    obtain ⟨_, ⟨y, hy, hp⟩, _⟩ := o
    have hu := List.pairwise_cons.mp ((hp.pairwise_iff (hsymF L)).mp hi.uniq)
    show (∃ x ∈ iterNode 13 t, _) ↔ (_ ∧ ∃ x ∈ iterNode 13 c.root, _)
    constructor
    · intro ⟨x, hx, he⟩
      refine ⟨?_, x, hp.symm.subset (List.mem_cons_of_mem _ hx), he⟩
      cases hkk : L.eqK k k'
      · rfl
      · have := hu.1 x hx
        rw [L.eqTK_key] at hy he; rw [L.eqTT_key] at this
        rw [L.trans _ _ _ hy (L.trans _ _ _ hkk (L.symm _ _ he))] at this; cases this
    · intro ⟨hkk, x, hx, he⟩
      rcases List.mem_cons.mp (hp.subset hx) with h | h
      · subst h
        rw [L.eqTK_key] at hy he
        rw [L.trans _ _ _ (L.symm _ _ hy) he] at hkk; cases hkk
      · exact ⟨x, h, he⟩

theorem get_other_of_sub (L : Lawful cfg) (c c' : Champ α) (k k' : κ) (hi : Inv cfg c) (hr : SubRes cfg c c' k)
    (hne : L.eqK k k' = false) : Champ.get cfg c' k' = Champ.get cfg c k' := by
  apply get_congr L _ _ (inv_of_sub L c c' k hi hr) hi k'
  intro x hx
  rcases hr with ⟨e, _⟩ | ⟨t, e, o⟩
  · rw [e]
  · rw [e]
    obtain ⟨_, ⟨y, hy, hp⟩, _⟩ := o
    have hxy : x ≠ y := by
      intro h; subst h
      rw [L.eqTK_key] at hx hy
      rw [L.trans _ _ _ (L.symm _ _ hy) hx] at hne; cases hne
    show x ∈ iterNode 13 t ↔ x ∈ iterNode 13 c.root
    rw [hp.mem_iff]
    simp [hxy]

/-! ## The transient steps -/

theorem addMut_out (c : Champ α) (e : Nat) (v : α) (s : Al) (hw : wfNode 13 c.root = true) :
    AddOut cfg 13 c.root v ((c.addMut cfg e v).run s).1.root ((doAddMut cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1 :=
  addMut_step cfg e v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw

theorem addMut_flag (L : Lawful cfg) (c : Champ α) (e : Nat) (v : α) (s : Al) (hw : wfNode 13 c.root = true) :
    ((doAddMut cfg e 13 c.root v (cfg.hashT v)).run s).1.2.1 = (Champ.get cfg c (L.key v)).isNone := by
  have := added_doAddMut cfg e (L.key v) v (cfg.hashT v) (fun x => by rw [L.eqTK_key, L.eqTT_key]) 13
    (Nat.le_refl _) c.root s hw
  rw [shr13] at this
  rw [this]
  unfold Champ.get
  rw [L.hashT_key]

/-- ★ `add_mut` (`assoc!`/`conj!`) keeps `Inv` under a lawful equality. -/
theorem inv_addMut (L : Lawful cfg) (c : Champ α) (e : Nat) (v : α) (s : Al) (hi : Inv cfg c) :
    Inv cfg ((c.addMut cfg e v).run s).1 :=
  inv_of_add L c _ v _ hi (addMut_out c e v s hi.wf) (addMut_size cfg e c v s) (addMut_flag L c e v s hi.wf)

/-- ★ Law 2's step for `add_mut`. -/
theorem keys_addMut (L : Lawful cfg) (c : Champ α) (e : Nat) (v : α) (s : Al) (hi : Inv cfg c) (k : κ) :
    (∃ x ∈ ((c.addMut cfg e v).run s).1.toList, cfg.eqTK x k = true) ↔
      (cfg.eqTK v k = true ∨ ∃ x ∈ c.toList, cfg.eqTK x k = true) :=
  keys_of_add L c _ v _ hi (addMut_out c e v s hi.wf) k

/-- ★ Law 1 for `add_mut`. -/
theorem get_addMut_other (L : Lawful cfg) (c : Champ α) (e : Nat) (v : α) (k' : κ) (s : Al) (hi : Inv cfg c)
    (hne : L.eqK (L.key v) k' = false) :
    Champ.get cfg ((c.addMut cfg e v).run s).1 k' = Champ.get cfg c k' :=
  get_other_of_add L c _ v _ hi (inv_addMut L c e v s hi) (addMut_out c e v s hi.wf) k' hne

/-- ★ `sub_mut` (`dissoc!`/`disj!`) keeps `Inv` under a lawful equality. -/
theorem inv_subMut (L : Lawful cfg) (c : Champ α) (e : Nat) (k : κ) (s : Al) (hi : Inv cfg c) :
    Inv cfg ((c.subMut cfg e k).run s).1 :=
  inv_of_sub L c _ k hi (subMut_cases cfg e c k s hi.wf)

/-- ★ Law 2's step for `sub_mut`. -/
theorem keys_subMut (L : Lawful cfg) (c : Champ α) (e : Nat) (k : κ) (s : Al) (hi : Inv cfg c) (k' : κ) :
    (∃ x ∈ ((c.subMut cfg e k).run s).1.toList, cfg.eqTK x k' = true) ↔
      (L.eqK k k' = false ∧ ∃ x ∈ c.toList, cfg.eqTK x k' = true) :=
  keys_of_sub L c _ k hi (subMut_cases cfg e c k s hi.wf) k'

/-- ★ Law 1 for `sub_mut`. -/
theorem get_subMut_other (L : Lawful cfg) (c : Champ α) (e : Nat) (k k' : κ) (s : Al) (hi : Inv cfg c)
    (hne : L.eqK k k' = false) :
    Champ.get cfg ((c.subMut cfg e k).run s).1 k' = Champ.get cfg c k' :=
  get_other_of_sub L c _ k k' hi (subMut_cases cfg e c k s hi.wf) hne

theorem sub_res (c : Champ α) (k : κ) (s : Al) (hw : wfNode 13 c.root = true) :
    SubRes cfg c ((c.sub cfg k).run s).1 k := sub_cases c k s hw

/-! ## Any sequence of persistent and transient steps -/

/-- A step on one collection: persistent `assoc`/`conj`, `dissoc`/`disj`, or transient
`assoc!`/`conj!`, `dissoc!`/`disj!` under owner token `e`. -/
inductive TOp (α κ : Type) where
  | add (v : α)
  | sub (k : κ)
  | addMut (e : Nat) (v : α)
  | subMut (e : Nat) (k : κ)

def applyT (cfg : Cfg α κ) (c : Champ α) : TOp α κ → M (Champ α)
  | .add v => c.add cfg v
  | .sub k => c.sub cfg k
  | .addMut e v => c.addMut cfg e v
  | .subMut e k => c.subMut cfg e k

def buildT (cfg : Cfg α κ) (c : Champ α) : List (TOp α κ) → M (Champ α)
  | [] => pure c
  | op :: ops => do buildT cfg (← applyT cfg c op) ops

/-- Clojure's model: a key is present when the last step naming an `=` key added it, whether the
step was transient or not. -/
def modelT (L : Lawful cfg) (m : κ → Bool) : List (TOp α κ) → κ → Bool
  | [] => m
  | .add v :: ops | .addMut _ v :: ops => modelT L (fun k => m k || L.eqK (L.key v) k) ops
  | .sub k0 :: ops | .subMut _ k0 :: ops => modelT L (fun k => m k && !L.eqK k0 k) ops

/-- One step's invariant and keys. -/
theorem stepT (L : Lawful cfg) (c : Champ α) (s : Al) (hi : Inv cfg c) (op : TOp α κ) :
    Inv cfg ((applyT cfg c op).run s).1 ∧
      ∀ k, (∃ x ∈ ((applyT cfg c op).run s).1.toList, cfg.eqTK x k = true) ↔
        (match op with
          | .add v | .addMut _ v => cfg.eqTK v k = true ∨ ∃ x ∈ c.toList, cfg.eqTK x k = true
          | .sub k0 | .subMut _ k0 => L.eqK k0 k = false ∧ ∃ x ∈ c.toList, cfg.eqTK x k = true) := by
  cases op with
  | add v => exact ⟨inv_add L c v s hi, keys_add L c v s hi⟩
  | sub k0 => exact ⟨inv_sub L c k0 s hi, keys_sub L c k0 s hi⟩
  | addMut e v => exact ⟨inv_addMut L c e v s hi, keys_addMut L c e v s hi⟩
  | subMut e k0 => exact ⟨inv_subMut L c e k0 s hi, keys_subMut L c e k0 s hi⟩

/-- ★ **Law 2 for every sequence of persistent and transient steps**: from a champ meeting `Inv`
whose keys are `m`, every sequence keeps `Inv` (each key stored once, `count` = the iteration's
length) and iteration yields exactly the keys the model holds. -/
theorem buildT_keys (L : Lawful cfg) :
    ∀ (ops : List (TOp α κ)) (c : Champ α) (m : κ → Bool) (s : Al), Inv cfg c →
      (∀ k, (∃ x ∈ c.toList, cfg.eqTK x k = true) ↔ m k = true) →
      Inv cfg ((buildT cfg c ops).run s).1 ∧
        ∀ k, (∃ x ∈ ((buildT cfg c ops).run s).1.toList, cfg.eqTK x k = true) ↔ modelT L m ops k = true
  | [], c, m, s, hi, hm => ⟨hi, hm⟩
  | op :: ops, c, m, s, hi, hm => by
    have e : ((buildT cfg c (op :: ops)).run s).1 =
        ((buildT cfg ((applyT cfg c op).run s).1 ops).run ((applyT cfg c op).run s).2).1 := rfl
    rw [e]
    obtain ⟨hi1, hk1⟩ := stepT L c s hi op
    cases op <;> dsimp only at hk1
    case add v =>
      exact buildT_keys L ops _ _ _ hi1 (fun k => by
        rw [hk1 k, hm k, Bool.or_eq_true, L.eqTK_key]; exact Or.comm)
    case addMut e v =>
      exact buildT_keys L ops _ _ _ hi1 (fun k => by
        rw [hk1 k, hm k, Bool.or_eq_true, L.eqTK_key]; exact Or.comm)
    case sub k0 =>
      exact buildT_keys L ops _ _ _ hi1 (fun k => by
        rw [hk1 k, hm k, Bool.and_eq_true, Bool.not_eq_true']; exact And.comm)
    case subMut e k0 =>
      exact buildT_keys L ops _ _ _ hi1 (fun k => by
        rw [hk1 k, hm k, Bool.and_eq_true, Bool.not_eq_true']; exact And.comm)

/-- ★ From `champ::empty()`. -/
theorem buildT_from_empty (L : Lawful cfg) (ops : List (TOp α κ)) (s : Al) :
    Inv cfg ((buildT cfg Champ.empty ops).run s).1 ∧
      ∀ k, (∃ x ∈ ((buildT cfg Champ.empty ops).run s).1.toList, cfg.eqTK x k = true) ↔
        modelT L (fun _ => false) ops k = true :=
  buildT_keys L ops Champ.empty _ s (inv_empty cfg) (fun k => by
    constructor
    · intro ⟨x, hx, _⟩
      rw [empty_toList] at hx; cases hx
    · intro h; cases h)

/-- Every transient step made persistent. -/
def TOp.persist : TOp α κ → TOp α κ
  | .addMut _ v => .add v
  | .subMut _ k => .sub k
  | op => op

theorem modelT_persist (L : Lawful cfg) : ∀ (ops : List (TOp α κ)) (m : κ → Bool),
    modelT L m (ops.map TOp.persist) = modelT L m ops
  | [], _ => rfl
  | op :: ops, m => by
    cases op <;> simp only [List.map_cons, TOp.persist, modelT] <;> exact modelT_persist L ops _

/-- ★ A sequence and the same sequence with every transient step made persistent yield the same keys
(from the empty champ; allocation states arbitrary). -/
theorem buildT_same_keys (L : Lawful cfg) (ops : List (TOp α κ)) (s s' : Al) (k : κ) :
    (∃ x ∈ ((buildT cfg Champ.empty ops).run s).1.toList, cfg.eqTK x k = true) ↔
      (∃ x ∈ ((buildT cfg Champ.empty (ops.map TOp.persist)).run s').1.toList, cfg.eqTK x k = true) := by
  rw [(buildT_from_empty L ops s).2 k, (buildT_from_empty L _ s').2 k, modelT_persist]

end Jank.R7.Champ

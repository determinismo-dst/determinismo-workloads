import Jank.R6.Champ.Ops

/-!
# Round 6, CHAMP: `get` of another key, and iteration, for every input

Over round 3's replica of immer's `champ.hpp`, for every champ built from `champ::empty()` by
`add` (`assoc`/`conj`) and `sub` (`dissoc`/`disj`):

- ★ `count_eq_seq_add`, ★ `count_eq_seq_sub`: `count` (immer's `size`) equals the number of values
  iteration yields, **for every hash and every equality** (nothing assumed);
- ★ `inv_add`, ★ `inv_sub`: well formed, the hash-path invariant `HP`, no two stored values `Equal`
  (each key stored once), and `size` = the iteration's length, kept by `add` and `sub`, **for every
  equality that is an equivalence compatible with the hash** (`Lawful`: `Equal` reads one key per
  value, is reflexive, symmetric, transitive, and `Equal` keys hash alike);
- ★ `get_iff`: then `get k` returns `x` exactly when `x` is stored and `Equal` to `k`;
- ★ `get_add_other`, ★ `get_sub_other` (law 1): `get` of a key not `Equal` to the one added or
  removed is unchanged;
- ★ `keys_add`, ★ `keys_sub`, ★ `build_keys` (law 2): iteration yields each stored key once, and
  exactly the keys added and not removed (Clojure's model of the set of keys).

`Lawful` is what jank's `=` and `hash` are not: D12 (equal values, different hashes) breaks
`compat`, R55/V48 and `##NaN` break `refl`. `Jank/R6/Champ/Breaks.lean` shows what each lost premise
does on the replica.
-/

namespace Jank.R6.Champ

open Jank.R3.Immer.Champ

variable {α κ : Type}

/-- The premises: `Equal` compares one key per value, is an equivalence, and agrees with the hash. -/
structure Lawful (cfg : Cfg α κ) where
  key : α → κ
  eqK : κ → κ → Bool
  hashT_key : ∀ a, cfg.hashT a = cfg.hashK (key a)
  eqTT_key : ∀ a b, cfg.eqTT a b = eqK (key a) (key b)
  eqTK_key : ∀ a k, cfg.eqTK a k = eqK (key a) k
  refl : ∀ k, eqK k k = true
  symm : ∀ a b, eqK a b = true → eqK b a = true
  trans : ∀ a b c, eqK a b = true → eqK b c = true → eqK a c = true
  compat : ∀ a b, eqK a b = true → cfg.hashK a = cfg.hashK b

/-- No two stored values `Equal` (with `refl`: each value once). -/
abbrev Uniq (cfg : Cfg α κ) (l : List α) : Prop := l.Pairwise (fun a b => cfg.eqTT a b = false)

/-- The invariant of every champ built by `add` and `sub` under a lawful equality. -/
structure Inv [Inhabited α] (cfg : Cfg α κ) (c : Champ α) : Prop where
  wf : wfNode 13 c.root = true
  hp : HP cfg 13 c.root
  uniq : Uniq cfg c.toList
  size : c.size = c.toList.length

theorem empty_toList [Inhabited α] : (Champ.empty (α := α)).toList = [] := by
  show iterNode 13 _ = []
  rw [iterNode.eq_2]; simp [Champ.empty, Node.values, Node.cs, Node.dataCount, Node.childrenCount]

theorem inv_empty [Inhabited α] (cfg : Cfg α κ) : Inv cfg (Champ.empty (α := α)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro d _
    show SlotOK (HP cfg 12) cfg 12 d (if (0 : Nat).testBit d = true then _ else if (0 : Nat).testBit d = true then _ else _)
    simp [Nat.zero_testBit, SlotOK]
  · rw [empty_toList]; exact List.Pairwise.nil
  · rw [empty_toList]; rfl

/-! ## `get` against the iteration -/

theorem shr13 (h : Nat) : h >>> (65 - 5 * 13) = h := by
  rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero]

/-- Every stored value is on the walk its own hash takes (the hash-path invariant). -/
theorem walk_complete [Inhabited α] (cfg : Cfg α κ) :
    ∀ r, r ≤ 13 → ∀ (N : Node α), wfNode r N = true → HP cfg r N →
      ∀ x ∈ iterNode r N, x ∈ walk r N (cfg.hashT x >>> (65 - 5 * r))
  | 0, _, N, _, _, x, hx => by rw [walk.eq_1]; rw [iterNode.eq_1] at hx; exact hx
  | r + 1, hr, N, hw, hp, x, hx => by
    have hx' := (iter_slots r N hw).subset hx
    rw [List.mem_flatMap] at hx'
    obtain ⟨d, hd, hxd⟩ := hx'
    rw [List.mem_range] at hd
    have hok := hp d hd
    rw [walk.eq_2, hidx]
    generalize hs : slot N d = sl at hok hxd
    cases sl with
    | empty => cases hxd
    | data y =>
      simp only [slotL, List.mem_singleton] at hxd
      subst hxd
      have hc : chunk r (cfg.hashT x) = d := hok
      rw [show idxAt (cfg.hashT x) (maxShift - 5 * (r + 1)) = d from hc, hs]
      simp
    | child c =>
      obtain ⟨hk1, hk2⟩ := hok
      have hc : chunk r (cfg.hashT x) = d := hk1 x hxd
      rw [show idxAt (cfg.hashT x) (maxShift - 5 * (r + 1)) = d from hc, hs]
      dsimp only
      rw [shr_step _ r hr]
      exact walk_complete cfg r (by omega) c (slot_child_wf r N hw d hd c hs) hk2 x hxd

/-- `get` finds only stored values `Equal` to the key (any hash, any equality). -/
theorem get_sound [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (k : κ) (x : α) (hw : wfNode 13 c.root = true)
    (hg : Champ.get cfg c k = some x) : x ∈ c.toList ∧ cfg.eqTK x k = true := by
  unfold Champ.get at hg
  rw [getLoop_walk cfg k 13 c.root _ hw] at hg
  have h1 := List.find?_some hg
  have h2 := List.mem_of_find?_eq_some hg
  exact ⟨walk_sub 13 c.root _ hw x h2, h1⟩

/-- `get` finds something whenever a stored value is `Equal` to the key and hashes as it. -/
theorem get_complete [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (k : κ) (x : α) (hw : wfNode 13 c.root = true)
    (hp : HP cfg 13 c.root) (hx : x ∈ c.toList) (hk : cfg.hashK k = cfg.hashT x) (he : cfg.eqTK x k = true) :
    Champ.get cfg c k ≠ none := by
  unfold Champ.get
  rw [getLoop_walk cfg k 13 c.root _ hw, hk]
  have := walk_complete cfg 13 (Nat.le_refl _) c.root hw hp x hx
  rw [shr13] at this
  intro hn
  rw [List.find?_eq_none] at hn
  exact absurd he (by simp [hn x this])

theorem pairwise_mem {β : Type} (R : β → β → Prop) :
    ∀ (l : List β), l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b ∨ R b a
  | [], _, a, ha, _, _, _ => by simp at ha
  | c :: l, hp, a, ha, b, hb, hab => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp ha with ha1 | ha2 <;> rcases List.mem_cons.mp hb with hb1 | hb2
    · exact absurd (ha1.trans hb1.symm) hab
    · rw [ha1]; exact Or.inl (hp.1 b hb2)
    · rw [hb1]; exact Or.inr (hp.1 a ha2)
    · exact pairwise_mem R l hp.2 a ha2 b hb2 hab

variable [Inhabited α] {cfg : Cfg α κ}

theorem Lawful.eq_of_eqTK (L : Lawful cfg) (x y : α) (k : κ) (hx : cfg.eqTK x k = true) (hy : cfg.eqTK y k = true) :
    cfg.eqTT x y = true := by
  rw [L.eqTK_key] at hx hy; rw [L.eqTT_key]
  exact L.trans _ _ _ hx (L.symm _ _ hy)

theorem Lawful.eqTT_symm (L : Lawful cfg) (x y : α) (h : cfg.eqTT x y = true) : cfg.eqTT y x = true := by
  rw [L.eqTT_key] at h ⊢; exact L.symm _ _ h

theorem Lawful.eqTK_trans (L : Lawful cfg) (x y : α) (k : κ) (h : cfg.eqTT x y = true) (hy : cfg.eqTK y k = true) :
    cfg.eqTK x k = true := by
  rw [L.eqTT_key] at h; rw [L.eqTK_key] at hy ⊢; exact L.trans _ _ _ h hy

theorem Lawful.hash_of_eqTK (L : Lawful cfg) (x : α) (k : κ) (h : cfg.eqTK x k = true) :
    cfg.hashK k = cfg.hashT x := by
  rw [L.eqTK_key] at h; rw [L.hashT_key]; exact (L.compat _ _ h).symm

theorem uniq_eq (L : Lawful cfg) (l : List α) (hu : Uniq cfg l) (x y : α) (hx : x ∈ l) (hy : y ∈ l)
    (h : cfg.eqTT x y = true) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  · rcases pairwise_mem _ l hu x hx y hy hxy with h' | h'
    · rw [h] at h'; cases h'
    · rw [L.eqTT_symm x y h] at h'; cases h'

/-- ★ Under the invariant and a lawful equality, `get k` is the stored value `Equal` to `k`. -/
theorem get_iff (L : Lawful cfg) (c : Champ α) (hi : Inv cfg c) (k : κ) (x : α) :
    Champ.get cfg c k = some x ↔ (x ∈ c.toList ∧ cfg.eqTK x k = true) := by
  constructor
  · exact get_sound cfg c k x hi.wf
  · intro ⟨hx, he⟩
    have hne := get_complete cfg c k x hi.wf hi.hp hx (L.hash_of_eqTK x k he) he
    cases hg : Champ.get cfg c k with
    | none => exact absurd hg hne
    | some y =>
      obtain ⟨hy, hye⟩ := get_sound cfg c k y hi.wf hg
      rw [uniq_eq L _ hi.uniq y x hy hx (L.eq_of_eqTK y x k hye he)]

theorem get_none_iff (L : Lawful cfg) (c : Champ α) (hi : Inv cfg c) (k : κ) :
    Champ.get cfg c k = none ↔ ∀ x ∈ c.toList, cfg.eqTK x k = false := by
  constructor
  · intro hg x hx
    cases he : cfg.eqTK x k
    · rfl
    · exact absurd hg (get_complete cfg c k x hi.wf hi.hp hx (L.hash_of_eqTK x k he) he)
  · intro h
    cases hg : Champ.get cfg c k with
    | none => rfl
    | some y =>
      obtain ⟨hy, hye⟩ := get_sound cfg c k y hi.wf hg
      rw [h y hy] at hye; cases hye

/-- Two champs whose stored values `Equal` to `k` agree give the same `get k`. -/
theorem get_congr (L : Lawful cfg) (c c' : Champ α) (hi : Inv cfg c) (hi' : Inv cfg c') (k : κ)
    (h : ∀ x, cfg.eqTK x k = true → (x ∈ c.toList ↔ x ∈ c'.toList)) :
    Champ.get cfg c k = Champ.get cfg c' k := by
  cases hg : Champ.get cfg c k with
  | none =>
    symm
    rw [get_none_iff L c' hi' k]
    intro x hx
    cases he : cfg.eqTK x k
    · rfl
    · have := (get_none_iff L c hi k).mp hg x ((h x he).mpr hx); rw [he] at this; cases this
  | some y =>
    obtain ⟨hy, hye⟩ := (get_iff L c hi k y).mp hg
    exact ((get_iff L c' hi' k y).mpr ⟨(h y hye).mp hy, hye⟩).symm

/-! ## `add` -/

theorem add_root (c : Champ α) (v : α) (s : Al) :
    ((c.add cfg v).run s).1.root = ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.1 := rfl

theorem add_size (c : Champ α) (v : α) (s : Al) :
    ((c.add cfg v).run s).1.size = c.size + (if ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.2 then 1 else 0) := rfl

/-- The root's `AddOut`, in the normal form the laws use. -/
theorem addOut_norm (L : Lawful cfg) (N : Node α) (v : α) (N' : Node α) (a : Bool)
    (o : AddOut cfg 13 N v N' a) (hu : Uniq cfg (iterNode 13 N)) :
    (a = true → (iterNode 13 N').Perm (v :: iterNode 13 N)) ∧
    (a = false → ∃ x rest, cfg.eqTT x v = true ∧ (iterNode 13 N).Perm (x :: rest) ∧
      (iterNode 13 N').Perm (v :: rest)) := by
  refine ⟨o.grew, fun ha => ?_⟩
  obtain ⟨x, hx, hxe, hp⟩ := o.replaced ha
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem hx
  have p1 : (iterNode 13 N).Perm (x :: (l1 ++ l2)) := by rw [hl]; exact List.perm_middle
  refine ⟨x, l1 ++ l2, hxe, p1, ?_⟩
  have p2 : (x :: iterNode 13 N').Perm (x :: v :: (l1 ++ l2)) :=
    hp.symm.trans ((p1.cons v).trans (List.Perm.swap x v _))
  exact p2.cons_inv

/-- ★ **`count` = `(count (seq s))` after `add`**, for every hash and every equality. -/
theorem count_eq_seq_add (c : Champ α) (v : α) (s : Al) (hw : wfNode 13 c.root = true)
    (hs : c.size = c.toList.length) :
    ((c.add cfg v).run s).1.size = ((c.add cfg v).run s).1.toList.length := by
  have o := add_step cfg v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw
  rw [add_size]
  show c.size + (if ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.2 then 1 else 0) =
    (iterNode 13 ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.1).length
  rw [hs]
  show (iterNode 13 c.root).length + _ = _
  cases ha : ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.2
  · obtain ⟨x, hx, _, hp⟩ := o.replaced ha
    have := hp.length_eq
    simp only [List.length_cons] at this
    simp; omega
  · have := (o.grew ha).length_eq
    simp only [List.length_cons] at this
    simp; omega

/-- ★ `add` keeps the invariant under a lawful equality. -/
theorem inv_add (L : Lawful cfg) (c : Champ α) (v : α) (s : Al) (hi : Inv cfg c) :
    Inv cfg ((c.add cfg v).run s).1 := by
  have o := add_step cfg v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hi.wf
  have hsym : ∀ {a b : α}, cfg.eqTT a b = false → cfg.eqTT b a = false := by
    intro a b h; cases h' : cfg.eqTT b a
    · rfl
    · rw [L.eqTT_symm b a h'] at h; cases h
  refine ⟨o.wf, o.hp hi.hp, ?_, count_eq_seq_add c v s hi.wf hi.size⟩
  show Uniq cfg (iterNode 13 ((c.add cfg v).run s).1.root)
  rw [add_root]
  obtain ⟨pg, pr⟩ := addOut_norm L c.root v _ _ o hi.uniq
  cases ha : ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.2
  · obtain ⟨x, rest, hxe, p1, p2⟩ := pr ha
    have hu1 := List.pairwise_cons.mp ((p1.pairwise_iff hsym).mp hi.uniq)
    apply (p2.pairwise_iff hsym).mpr
    refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hu1.2⟩
    cases h : cfg.eqTT v y
    · rfl
    · have := hu1.1 y hy
      rw [L.eqTT_key] at hxe this h
      rw [L.trans _ _ _ hxe h] at this; cases this
  · -- `added`: `get` of `v`'s key found nothing, so nothing stored is `Equal` to `v`
    have hadd := added_doAdd cfg (L.key v) v (cfg.hashT v)
      (fun x => by rw [L.eqTK_key, L.eqTT_key]) 13 (Nat.le_refl _) c.root s hi.wf
    rw [shr13, ha, L.hashT_key] at hadd
    have hnone : Champ.get cfg c (L.key v) = none := by
      unfold Champ.get; exact Option.isNone_iff_eq_none.mp hadd.symm
    have hno := (get_none_iff L c hi (L.key v)).mp hnone
    apply ((pg ha).pairwise_iff hsym).mpr
    refine List.pairwise_cons.mpr ⟨fun y hy => ?_, hi.uniq⟩
    have := hno y hy
    rw [L.eqTK_key, ← L.eqTT_key] at this
    exact hsym this

/-- ★ **Law 1 for `add`**: `get` of a key not `Equal` to the one added is unchanged. -/
theorem get_add_other (L : Lawful cfg) (c : Champ α) (v : α) (k' : κ) (s : Al) (hi : Inv cfg c)
    (hne : L.eqK (L.key v) k' = false) :
    Champ.get cfg ((c.add cfg v).run s).1 k' = Champ.get cfg c k' := by
  have o := add_step cfg v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hi.wf
  apply get_congr L _ _ (inv_add L c v s hi) hi k'
  intro x hx
  have hxv : x ≠ v := by
    intro h; subst h; rw [L.eqTK_key, hne] at hx; cases hx
  obtain ⟨pg, pr⟩ := addOut_norm L c.root v _ _ o hi.uniq
  show x ∈ iterNode 13 ((c.add cfg v).run s).1.root ↔ x ∈ iterNode 13 c.root
  rw [add_root]
  cases ha : ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.2
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

/-- ★ **Law 2 for `add`**: the keys after `add` are the old ones and the new one. -/
theorem keys_add (L : Lawful cfg) (c : Champ α) (v : α) (s : Al) (hi : Inv cfg c) (k : κ) :
    (∃ x ∈ ((c.add cfg v).run s).1.toList, cfg.eqTK x k = true) ↔
      (cfg.eqTK v k = true ∨ ∃ x ∈ c.toList, cfg.eqTK x k = true) := by
  have o := add_step cfg v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hi.wf
  obtain ⟨pg, pr⟩ := addOut_norm L c.root v _ _ o hi.uniq
  show (∃ x ∈ iterNode 13 ((c.add cfg v).run s).1.root, _) ↔ (_ ∨ ∃ x ∈ iterNode 13 c.root, _)
  rw [add_root]
  cases ha : ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.2
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
          exact ⟨v, p2.symm.subset (List.mem_cons_self ..),
            L.eqTK_trans v x k (L.eqTT_symm x v hye) he⟩
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

/-! ## `sub` -/

/-- What `sub` does at the root: nothing (the same champ), or a tree without one value `Equal`
to the key. -/
theorem sub_cases (c : Champ α) (k : κ) (s : Al) (hw : wfNode 13 c.root = true) :
    (((c.sub cfg k).run s).1 = c ∧ Champ.get cfg c k = none) ∨
    (∃ t, ((c.sub cfg k).run s).1 = { root := t, size := c.size - 1 } ∧ SubOut cfg k 13 c.root (.tree t)) := by
  by_cases hg : Champ.get cfg c k = none
  · exact Or.inl ⟨by rw [sub_absent cfg c k s hw hg], hg⟩
  · right
    have ⟨_, ht⟩ := doSub_found cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
      (by rw [shr13]; exact hg)
    have o := sub_step cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    unfold Champ.sub
    simp only [StateT.run_bind]
    generalize ((doSub cfg k 13 c.root (cfg.hashK k)).run s) = q at ht o
    obtain ⟨sub, s1⟩ := q
    cases sub with
    | tree t => exact ⟨t, rfl, o⟩
    | _ => cases (ht rfl)

/-- ★ **`count` = `(count (seq s))` after `sub`**, for every hash and every equality. -/
theorem count_eq_seq_sub (c : Champ α) (k : κ) (s : Al) (hw : wfNode 13 c.root = true)
    (hs : c.size = c.toList.length) :
    ((c.sub cfg k).run s).1.size = ((c.sub cfg k).run s).1.toList.length := by
  rcases sub_cases c k s hw with ⟨e, _⟩ | ⟨t, e, o⟩
  · rw [e]; exact hs
  · rw [e]
    obtain ⟨_, ⟨y, _, hp⟩, _⟩ := o
    have := hp.length_eq
    simp only [List.length_cons] at this
    show c.size - 1 = (iterNode 13 t).length
    rw [hs]; show (iterNode 13 c.root).length - 1 = _; omega

theorem inv_sub (L : Lawful cfg) (c : Champ α) (k : κ) (s : Al) (hi : Inv cfg c) :
    Inv cfg ((c.sub cfg k).run s).1 := by
  have hsym : ∀ {a b : α}, cfg.eqTT a b = false → cfg.eqTT b a = false := by
    intro a b h; cases h' : cfg.eqTT b a
    · rfl
    · rw [L.eqTT_symm b a h'] at h; cases h
  rcases sub_cases (cfg := cfg) c k s hi.wf with ⟨e, _⟩ | ⟨t, e, o⟩
  · rw [e]; exact hi
  · have hsz := count_eq_seq_sub (cfg := cfg) c k s hi.wf hi.size
    rw [e] at hsz ⊢
    obtain ⟨hw, ⟨y, _, hp⟩, hh⟩ := o
    refine ⟨hw, hh hi.hp, ?_, hsz⟩
    have := (hp.pairwise_iff hsym).mp hi.uniq
    exact (List.pairwise_cons.mp this).2

/-- ★ **Law 1 for `sub`**: `get` of a key not `Equal` to the one removed is unchanged. -/
theorem get_sub_other (L : Lawful cfg) (c : Champ α) (k k' : κ) (s : Al) (hi : Inv cfg c)
    (hne : L.eqK k k' = false) :
    Champ.get cfg ((c.sub cfg k).run s).1 k' = Champ.get cfg c k' := by
  apply get_congr L _ _ (inv_sub L c k s hi) hi k'
  intro x hx
  rcases sub_cases (cfg := cfg) c k s hi.wf with ⟨e, _⟩ | ⟨t, e, o⟩
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

/-- ★ **Law 2 for `sub`**: the keys after `sub k` are the old ones not `Equal` to `k`. -/
theorem keys_sub (L : Lawful cfg) (c : Champ α) (k : κ) (s : Al) (hi : Inv cfg c) (k' : κ) :
    (∃ x ∈ ((c.sub cfg k).run s).1.toList, cfg.eqTK x k' = true) ↔
      (L.eqK k k' = false ∧ ∃ x ∈ c.toList, cfg.eqTK x k' = true) := by
  rcases sub_cases (cfg := cfg) c k s hi.wf with ⟨e, hg⟩ | ⟨t, e, o⟩
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
    have hsym : ∀ {a b : α}, cfg.eqTT a b = false → cfg.eqTT b a = false := by
      intro a b h; cases h' : cfg.eqTT b a
      · rfl
      · rw [L.eqTT_symm b a h'] at h; cases h
    have hu := List.pairwise_cons.mp ((hp.pairwise_iff hsym).mp hi.uniq)
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

/-! ## Any sequence of `assoc`/`conj` and `dissoc`/`disj` -/

inductive Op (α κ : Type) where
  | add (v : α)
  | sub (k : κ)

def applyOp (cfg : Cfg α κ) (c : Champ α) : Op α κ → M (Champ α)
  | .add v => c.add cfg v
  | .sub k => c.sub cfg k

def buildFrom (cfg : Cfg α κ) (c : Champ α) : List (Op α κ) → M (Champ α)
  | [] => pure c
  | op :: ops => do buildFrom cfg (← applyOp cfg c op) ops

/-- Clojure's model of the key set: a key is present when the last `add` or `sub` that names an
`=` key was an `add`. -/
def model (L : Lawful cfg) (m : κ → Bool) : List (Op α κ) → κ → Bool
  | [] => m
  | .add v :: ops => model L (fun k => m k || L.eqK (L.key v) k) ops
  | .sub k0 :: ops => model L (fun k => m k && !L.eqK k0 k) ops

/-- ★ **Law 2 for every sequence**: a champ built by any `add`/`sub` sequence keeps the invariant
(each key stored once, `count` = the iteration's length), and iteration yields exactly the keys
the model holds. -/
theorem build_keys (L : Lawful cfg) :
    ∀ (ops : List (Op α κ)) (c : Champ α) (m : κ → Bool) (s : Al), Inv cfg c →
      (∀ k, (∃ x ∈ c.toList, cfg.eqTK x k = true) ↔ m k = true) →
      Inv cfg ((buildFrom cfg c ops).run s).1 ∧
        ∀ k, (∃ x ∈ ((buildFrom cfg c ops).run s).1.toList, cfg.eqTK x k = true) ↔ model L m ops k = true
  | [], c, m, s, hi, hm => ⟨hi, hm⟩
  | .add v :: ops, c, m, s, hi, hm => by
    have := build_keys L ops ((c.add cfg v).run s).1 (fun k => m k || L.eqK (L.key v) k) ((c.add cfg v).run s).2
      (inv_add L c v s hi) (fun k => by
        rw [keys_add L c v s hi k, hm k, Bool.or_eq_true, L.eqTK_key]; exact Or.comm)
    exact this
  | .sub k0 :: ops, c, m, s, hi, hm => by
    have := build_keys L ops ((c.sub cfg k0).run s).1 (fun k => m k && !L.eqK k0 k) ((c.sub cfg k0).run s).2
      (inv_sub L c k0 s hi) (fun k => by
        rw [keys_sub L c k0 s hi k, hm k, Bool.and_eq_true, Bool.not_eq_true']; exact And.comm)
    exact this

/-- ★ From `champ::empty()`. -/
theorem build_from_empty (L : Lawful cfg) (ops : List (Op α κ)) (s : Al) :
    Inv cfg ((buildFrom cfg Champ.empty ops).run s).1 ∧
      ∀ k, (∃ x ∈ ((buildFrom cfg Champ.empty ops).run s).1.toList, cfg.eqTK x k = true) ↔
        model L (fun _ => false) ops k = true :=
  build_keys L ops Champ.empty _ s (inv_empty cfg) (fun k => by
    constructor
    · intro ⟨x, hx, _⟩
      have : (Champ.empty (α := α)).toList = [] := by
        show iterNode 13 _ = []
        rw [iterNode.eq_2]; simp [Champ.empty, Node.values, Node.cs, Node.dataCount, Node.childrenCount]
      rw [this] at hx; cases hx
    · intro h; cases h)

end Jank.R6.Champ

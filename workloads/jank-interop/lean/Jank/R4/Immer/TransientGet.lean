import Jank.R3.Immer.RbtsGet

/-!
# Transient vector laws over the rbts replica (round 4)

Round 3 proved `nth` after `conj`, `pop`/`take` and `assoc!` over immer's own algorithms
(`Jank.R3.Immer.RbtsGet`), but only searched `nth` after `conj!` and `pop!` (the transient paths
`push_back_mut` / `push_tail_mut_visitor` and `take_mut` / `slice_right_mut_visitor`). This file
proves them for every input:

- `get_pushBackMut`: `(nth (conj! t x) j)` is `(nth t j)` below the count and `x` at it, for every
  well-formed tree below `2^35` elements and every owner token (nodes the transient owns are
  written in place, others copied: `make_inner_e`, `make_path_e`, `ensure_mutable_tail`);
- `pushBackMut_wfT`: `conj!` keeps the tree well formed, so the law holds for every transient
  built by `conj!` from any well-formed vector (`(transient [])` included);
- `get_takeMut`: `(nth (take_mut t k) j)` is `(nth t j)` for `j < k` (so `pop!`, which jank runs as
  `take(size - 1)`, transient_vector.cpp `pop_in_place`), in place or on copies, every token.

Nodes written in place keep their slots past the new count (immer's `destroy_n` and the in-place
`inner()[idx] = ...` leave the rest of the buffer); the laws read only through valid positions,
which never reach those slots. jank paths: transient_vector.cpp `conj_in_place` (`data.push_back`),
`pop_in_place` (`data.take(data.size() - 1)`); immer 282629d0 rbts/rbtree.hpp `push_back_mut`,
`take_mut`, rbts/operations.hpp `push_tail_mut_visitor`, `slice_right_mut_visitor`.
-/

namespace Jank.R3.Immer.Rbts

variable {α : Type}

/-! ## Slot reads after an in-place write or a copy -/

/-- A slot written at `i` (in place, or appended past the end), read through `f` (`f d = none`). -/
theorem setAt_bind {β γ : Type} (d : β) (l : List β) (i c : Nat) (x : β) (f : β → Option γ)
    (hd : f d = none) :
    ((setAt d l i x)[c]?).bind f = if c = i then f x else (l[c]?).bind f := by
  unfold setAt
  split
  · rename_i hi
    rw [List.getElem?_set]
    by_cases h : i = c
    · subst h; simp [hi]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · rename_i hi
    by_cases hc : c < l.length
    · rw [List.append_assoc, List.getElem?_append_left hc, if_neg (by omega)]
    · rw [List.getElem?_eq_none (l := l) (by omega), List.append_assoc,
        List.getElem?_append_right (by omega)]
      by_cases hci : c < i
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos (by omega),
          if_neg (by omega)]
        simp [hd]
      · rw [List.getElem?_append_right (by simp; omega)]
        by_cases hce : c = i
        · subst hce; simp
        · rw [if_neg hce]
          simp only [List.length_replicate, List.getElem?_singleton, Option.bind_none]
          rw [if_neg (by omega)]; rfl

theorem setAt_get_of_lt {β : Type} (d : β) (l : List β) (i c : Nat) (x : β) (hci : c < i)
    (hcl : c < l.length) : (setAt d l i x)[c]? = l[c]? := by
  unfold setAt
  split
  · rw [List.getElem?_set, if_neg (by omega)]
  · rw [List.append_assoc, List.getElem?_append_left hcl]

theorem setAt_get_self {β : Type} (d : β) (l : List β) (i : Nat) (x : β) :
    (setAt d l i x)[i]? = some x := by
  unfold setAt
  split
  · rename_i hi; simp [List.getElem?_set, hi]
  · rename_i hi
    rw [List.getElem?_append_right (by simp; omega)]
    have : i - (l.length + (i - l.length)) = 0 := by omega
    simp [this]

/-- The slots a node is written into: its own (in place) or a copy of its first `cnt`. -/
theorem ys_bind {γ : Type} (node : Node α) (cnt c : Nat) (ys : List (Node α))
    (hys : ys = node.cs ∨ ys = childCopy node cnt) (hc : c < cnt) (f : Node α → Option γ)
    (hd : f Node.dummy = none) : (ys[c]?).bind f = (node.cs[c]?).bind f := by
  rcases hys with h | h
  · rw [h]
  · rw [h]; exact copyN_bind _ _ _ _ _ hd hc

theorem ys_get (node : Node α) (cnt c : Nat) (ys : List (Node α))
    (hys : ys = node.cs ∨ ys = childCopy node cnt) (hc : c < cnt) (hl : c < node.cs.length) :
    ys[c]? = node.cs[c]? ∧ c < ys.length := by
  rcases hys with h | h
  · subst h; exact ⟨rfl, hl⟩
  · subst h; exact ⟨childCopy_getElem? _ _ _ hc hl, by rw [childCopy, copyN_length]; exact hc⟩

/-! ## `push_tail_mut_visitor` -/

theorem pushTailMut_eq (k : Nat) (m : Bool) (e size : Nat) (node tail : Node α) (n : Nat) :
    (pushTailMut k m e size node tail n).1 =
      if m && node.canMutate e then
        node.writeChild (iIndex (5 * (k + 1)) (size + 32 - 1))
          (if iIndex (5 * (k + 1)) (size - 1) == iIndex (5 * (k + 1)) (size + 32 - 1) then
            (match k with
             | 0 => (Node.dummy, n)
             | k' + 1 => pushTailMut k' true e size (node.child (iIndex (5 * (k + 1)) (size - 1))) tail n).1
           else (makePath e k tail n).1)
      else
        .inner n e (setAt Node.dummy (childCopy node (iIndex (5 * (k + 1)) (size + 32 - 1)))
          (iIndex (5 * (k + 1)) (size + 32 - 1))
          (if iIndex (5 * (k + 1)) (size - 1) == iIndex (5 * (k + 1)) (size + 32 - 1) then
            (match k with
             | 0 => (Node.dummy, n + 1)
             | k' + 1 => pushTailMut k' false e size (node.child (iIndex (5 * (k + 1)) (size - 1))) tail (n + 1)).1
           else (makePath e k tail (n + 1)).1)) := by
  conv => lhs; unfold pushTailMut
  dsimp only
  split <;> split <;> rfl

/-- Level 0: the node (its own slots or a copy) with the tail written at `new_idx`. -/
theorem pushTailMut_shape_zero (m : Bool) (e size : Nat) (node tail : Node α) (n : Nat) :
    ∃ (a b n' : Nat) (ys : List (Node α)),
      (ys = node.cs ∨ ys = childCopy node (iIndex 5 (size + 32 - 1))) ∧
      (pushTailMut 0 m e size node tail n).1 = .inner a b (setAt Node.dummy ys (iIndex 5 (size + 32 - 1))
        (if iIndex 5 (size - 1) == iIndex 5 (size + 32 - 1) then Node.dummy else (makePath e 0 tail n').1)) := by
  rw [pushTailMut_eq]
  split
  · exact ⟨node.id, node.tok, n, node.cs, Or.inl rfl, rfl⟩
  · exact ⟨n, e, n + 1, _, Or.inr rfl, rfl⟩

/-- Level `k + 1`: the child pushed into (with some mutating flag), or a new path. -/
theorem pushTailMut_shape_succ (k : Nat) (m : Bool) (e size : Nat) (node tail : Node α) (n : Nat) :
    ∃ (a b n' : Nat) (m' : Bool) (ys : List (Node α)),
      (ys = node.cs ∨ ys = childCopy node (iIndex (5 * (k + 2)) (size + 32 - 1))) ∧
      (pushTailMut (k + 1) m e size node tail n).1 = .inner a b (setAt Node.dummy ys
        (iIndex (5 * (k + 2)) (size + 32 - 1))
        (if iIndex (5 * (k + 2)) (size - 1) == iIndex (5 * (k + 2)) (size + 32 - 1) then
          (pushTailMut k m' e size (node.child (iIndex (5 * (k + 2)) (size - 1))) tail n').1
         else (makePath e (k + 1) tail n').1)) := by
  rw [pushTailMut_eq]
  split
  · exact ⟨node.id, node.tok, n, true, node.cs, Or.inl rfl, rfl⟩
  · exact ⟨n, e, n + 1, false, _, Or.inr rfl, rfl⟩

/-- **`push_tail_mut_visitor`**: reads below `size` are unchanged; the 32 slots from `size` read
the pushed tail (for every mutating flag and owner token). -/
theorem readAt_pushTailMut : ∀ (k : Nat) (m : Bool) (e size : Nat) (node : Node α) (tid ttok : Nat)
    (txs : List α) (n j : Nat),
    0 < size → size % 32 = 0 →
    (size - 1) >>> (5 * (k + 2)) = (size + 31) >>> (5 * (k + 2)) →
    j < size + 32 → j >>> (5 * (k + 2)) = (size - 1) >>> (5 * (k + 2)) →
    readAt k (pushTailMut k m e size node (.leaf tid ttok txs) n).1 j =
      if j < size then readAt k node j else txs[lIndex j]? := by
  intro k
  induction k with
  | zero =>
    intro m e size node tid ttok txs n j hpos h32 hb hj hjb
    obtain ⟨a, b, n', ys, hys, hR⟩ := pushTailMut_shape_zero m e size node (.leaf tid ttok txs) n
    rw [hR]
    have e1 : size + 32 - 1 = size + 31 := by omega
    simp only [e1] at hys ⊢
    have hb' : (size - 1) / 1024 = (size + 31) / 1024 := by simpa [shr_eq] using hb
    have hjb' : j / 1024 = (size - 1) / 1024 := by simpa [shr_eq] using hjb
    have hne : iIndex 5 (size - 1) ≠ iIndex 5 (size + 31) := by
      simp only [iIndex_eq, shr_eq]; simp; omega
    rw [if_neg (by simpa using hne), makePath_zero, readAt_zero_cs, readAt_zero_cs, cs_inner,
      setAt_bind _ _ _ _ _ _ (by simp [leafOpt, Node.dummy])]
    by_cases hjs : j < size
    · rw [if_pos hjs]
      have : iIndex 5 j < iIndex 5 (size + 31) := by
        simp only [iIndex_eq, shr_eq]; simp; omega
      rw [if_neg (by omega)]
      exact ys_bind node _ _ ys hys this _ (by simp [leafOpt, Node.dummy])
    · rw [if_neg hjs]
      have hj1 : iIndex 5 j = iIndex 5 (size + 31) := by
        simp only [iIndex_eq, shr_eq]; simp; omega
      rw [if_pos hj1]
      simp [leafOpt, Node.xs]
  | succ k ih =>
    intro m e size node tid ttok txs n j hpos h32 hb hj hjb
    obtain ⟨a, b, n', m', ys, hys, hR⟩ := pushTailMut_shape_succ k m e size node (.leaf tid ttok txs) n
    rw [hR]
    have e1 : size + 32 - 1 = size + 31 := by omega
    have e2 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    simp only [e1] at hys ⊢
    rw [e2] at hb hjb
    rw [readAt_succ_cs, readAt_succ_cs, cs_inner, setAt_bind _ _ _ _ _ _ (by simp [readAt_dummy])]
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    by_cases hjs : j < size
    · rw [if_pos hjs]
      have hd := digit_le (5 * (k + 2)) (show j ≤ size - 1 by omega) hjb
      have hi := digit_le (5 * (k + 2)) (show size - 1 ≤ size + 31 by omega) hb
      by_cases hlt : iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) (size + 31)
      · rw [if_neg (by omega)]; exact ys_bind node _ _ ys hys hlt _ (by simp [readAt_dummy])
      · have heq : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) (size + 31) := by omega
        have hidx : iIndex (5 * (k + 2)) (size - 1) = iIndex (5 * (k + 2)) (size + 31) := by omega
        rw [if_pos heq, if_pos (by simpa using hidx)]
        have hblk := shr_eq_of_digit _ hidx hb
        have hjblk := shr_eq_of_digit _ (show iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) (size - 1) by omega) hjb
        rw [ih m' e size _ tid ttok txs n' j hpos h32 hblk hj hjblk, if_pos hjs, child_read, hidx, heq]
    · rw [if_neg hjs]
      have hwin := shr_window (5 * (k + 2)) size j hsh h32 (by omega) hj
      have hj1 : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) (size + 31) := by
        simp only [iIndex_eq]; rw [hwin]
      rw [if_pos hj1]
      by_cases hidx : iIndex (5 * (k + 2)) (size - 1) = iIndex (5 * (k + 2)) (size + 31)
      · rw [if_pos (by simpa using hidx)]
        have hblk := shr_eq_of_digit _ hidx hb
        rw [ih m' e size _ tid ttok txs n' j hpos h32 hblk hj (by rw [hwin, hblk]), if_neg hjs]
      · rw [if_neg (by simpa using hidx)]
        apply readAt_makePath
        have hm := mod_zero_of_digit_ne (5 * (k + 2)) size hsh h32 hpos hb hidx
        have hP := pow_ge32 (5 * (k + 2)) hsh
        have : j % 2 ^ (5 * (k + 2)) = (j - size) % 2 ^ (5 * (k + 2)) := by
          conv => lhs; rw [show j = (j - size) + size by omega]
          rw [Nat.add_mod, hm, Nat.add_zero, Nat.mod_mod]
        rw [this, Nat.mod_eq_of_lt (by omega)]
        omega

/-! ## `push_back_mut` -/

theorem pushBackMut_size1 [Inhabited α] (t : Tree α) (e : Nat) (x : α) (n : Nat) :
    (t.pushBackMut e x n).1.size = t.size + 1 := by
  unfold Tree.pushBackMut Tree.ensureMutableTail; dsimp only
  repeat' split
  all_goals rfl

/-- The tree `push_back_mut` builds when the tail has room (the tail written in place or copied). -/
def smallPushMut [Inhabited α] (t : Tree α) (a b : Nat) (ys : List α) (x : α) : Tree α :=
  { size := t.size + 1, shift := t.shift, root := t.root,
    tail := Node.leaf a b (setAt default ys (t.size - tailOffset t.size) x) }

theorem pushBackMut_small [Inhabited α] (t : Tree α) (e : Nat) (x : α) (n : Nat)
    (h : t.size - tailOffset t.size < 32) :
    ∃ (a b : Nat) (ys : List α),
      (ys = t.tail.xs ∨ ys = leafCopy t.tail (t.size - tailOffset t.size)) ∧
      (t.pushBackMut e x n).1 = smallPushMut t a b ys x := by
  unfold Tree.pushBackMut Tree.ensureMutableTail
  simp only [h, if_true]
  split
  · exact ⟨t.tail.id, t.tail.tok, t.tail.xs, Or.inl rfl, rfl⟩
  · exact ⟨n, e, _, Or.inr rfl, rfl⟩

theorem pushBackMut_full_tail [Inhabited α] (t : Tree α) (e : Nat) (x : α) (n : Nat)
    (h : ¬ t.size - tailOffset t.size < 32) :
    (t.pushBackMut e x n).1.tail = .leaf n e [x] := by
  unfold Tree.pushBackMut; dsimp only; rw [if_neg h]
  repeat' split
  all_goals rfl

theorem pushBackMut_grow [Inhabited α] (t : Tree α) (e : Nat) (x : α) (n : Nat)
    (h : ¬ t.size - tailOffset t.size < 32) (hg : tailOffset t.size = 32 <<< t.shift) :
    (t.pushBackMut e x n).1.root = .inner (n + 1) e [t.root, (makePath e (t.shift / 5) t.tail (n + 2)).1] ∧
    (t.pushBackMut e x n).1.shift = t.shift + 5 := by
  unfold Tree.pushBackMut; dsimp only; rw [if_neg h, if_pos (by simpa using hg)]
  constructor <;> rfl

theorem pushBackMut_mid [Inhabited α] (t : Tree α) (e : Nat) (x : α) (n : Nat)
    (h : ¬ t.size - tailOffset t.size < 32) (hg : tailOffset t.size ≠ 32 <<< t.shift)
    (h0 : tailOffset t.size ≠ 0) :
    (t.pushBackMut e x n).1.root = (pushTailMut (levelOf t.shift) true e (tailOffset t.size) t.root t.tail (n + 1)).1 ∧
    (t.pushBackMut e x n).1.shift = t.shift := by
  unfold Tree.pushBackMut; dsimp only; rw [if_neg h, if_neg (by simpa using hg), if_pos (by simpa using h0)]
  constructor <;> rfl

theorem pushBackMut_first [Inhabited α] (t : Tree α) (e : Nat) (x : α) (n : Nat)
    (h : ¬ t.size - tailOffset t.size < 32) (hg : tailOffset t.size ≠ 32 <<< t.shift)
    (h0 : tailOffset t.size = 0) :
    (t.pushBackMut e x n).1.root = (makePath e (t.shift / 5) t.tail (n + 1)).1 ∧
    (t.pushBackMut e x n).1.shift = t.shift := by
  unfold Tree.pushBackMut; dsimp only; rw [if_neg h, if_neg (by simpa using hg), if_neg (by simpa using h0)]
  constructor <;> rfl

/-- **`nth` after `conj!`**: for every well-formed tree below `2^35` elements and every owner
token, `(nth (conj! t x) j)` is `(nth t j)` for `j < count` and `x` at `count`. -/
theorem get_pushBackMut [Inhabited α] (t : Tree α) (hw : t.wfT) (hsz : t.size < 2 ^ 35) (e : Nat)
    (x : α) (n j : Nat) (hj : j ≤ t.size) :
    (t.pushBackMut e x n).1.get j = if j < t.size then t.get j else some x := by
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  cases ht : t.tail with
  | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
  | leaf tid ttok txs =>
  rw [ht] at htlen
  simp only [Node.xs] at htlen
  by_cases hsmall : t.size - tailOffset t.size < 32
  · have hto := tailOffset_succ_of_lt _ hsmall
    obtain ⟨a, b, ys, hys, hR⟩ := pushBackMut_small t e x n hsmall
    have hyl : t.size - tailOffset t.size ≤ ys.length ∧
        ∀ c, c < t.size - tailOffset t.size → ys[c]? = txs[c]? := by
      rcases hys with h | h
      · rw [h, ht]; exact ⟨htlen, fun _ _ => rfl⟩
      · rw [h, ht]
        refine ⟨Nat.le_of_eq (by rw [leafCopy, copyN_length]), fun c hc => ?_⟩
        exact leafCopy_getElem? _ _ _ hc (by simp [Node.xs]; omega)
    obtain ⟨hyl1, hyl2⟩ := hyl
    rw [hR]
    by_cases hjt : tailOffset t.size ≤ j
    · rw [get_tail_leaf (smallPushMut t a b ys x) j a b _ rfl
          (by show tailOffset (t.size + 1) ≤ j; rw [hto]; exact hjt)]
      have hlj : lIndex j = j - tailOffset t.size := by
        have := lIndex_tail (t.size + 1) j (by rw [hto]; exact hjt) (by omega)
        rw [this, hto]
      rw [hlj]
      by_cases hjs : j < t.size
      · rw [if_pos hjs, setAt_get_of_lt _ _ _ _ _ (by omega) (by omega), hyl2 _ (by omega),
          get_tail_leaf t j tid ttok txs ht hjt, lIndex_tail _ _ hjt hjs]
      · rw [if_neg hjs, show j - tailOffset t.size = t.size - tailOffset t.size by omega,
          setAt_get_self]
    · have hjt' : j < tailOffset t.size := by omega
      rw [get_of_root (smallPushMut t a b ys x) j
          (by show j < tailOffset (t.size + 1); rw [hto]; exact hjt') hs2,
        if_pos (by have := tailOffset_le t.size; omega), get_of_root t j hjt' hs2]
      rfl
  · have hpos : 0 < t.size := by have := tailOffset_le t.size; omega
    have hf := tail_facts t.size hpos
    have hfull : t.size - tailOffset t.size = 32 := by omega
    have hto := tailOffset_succ_of_full t.size hpos (by omega)
    have h32 : t.size % 32 = 0 := by omega
    have hsz' : (t.pushBackMut e x n).1.size = t.size + 1 := pushBackMut_size1 t e x n
    by_cases hjs : j = t.size
    · subst hjs
      rw [if_neg (by omega), get_tail_leaf (t.pushBackMut e x n).1 t.size n e [x]
        (pushBackMut_full_tail _ _ _ _ hsmall) (by rw [hsz', hto]; exact Nat.le_refl _)]
      simp [lIndex_eq, h32]
    · have hjs' : j < t.size := by omega
      rw [if_pos hjs']
      have hjr : j < tailOffset (t.pushBackMut e x n).1.size := by rw [hsz', hto]; exact hjs'
      have hL := levelOf_eq t.shift hs5 hs1
      by_cases hg : tailOffset t.size = 32 <<< t.shift
      · obtain ⟨hr, hsh⟩ := pushBackMut_grow t e x n hsmall hg
        rw [shl32] at hg
        have hs25 : t.shift ≤ 25 := by
          rcases Nat.lt_or_ge t.shift 26 with hc | hc
          · omega
          · exfalso
            have h30 : t.shift = 30 := by omega
            rw [h30] at hg
            have := tailOffset_le t.size
            simp at hg hsz; omega
        rw [get_of_root _ _ hjr (by rw [hsh]; omega), hsh, hr]
        have hlv : levelOf (t.shift + 5) = levelOf t.shift + 1 := by unfold levelOf; omega
        rw [hlv, readAt_succ]
        have e5 : 5 * (levelOf t.shift + 2) = t.shift + 5 := by omega
        rw [e5]
        have hP32 := pow_ge32 (t.shift + 5) (by omega)
        by_cases hjt : j < tailOffset t.size
        · have hd : iIndex (t.shift + 5) j = 0 := by
            rw [iIndex_eq, shr_zero_of_lt _ (by rw [← hg]; exact hjt)]
          simp only [hd, List.getElem?_cons_zero, Option.bind_some]
          rw [get_of_root _ _ hjt hs2]
        · have hd : iIndex (t.shift + 5) j = 1 := by
            rw [iIndex_eq, shr_eq]
            have : j / 2 ^ (t.shift + 5) = 1 := by
              generalize 2 ^ (t.shift + 5) = P at hg hP32 ⊢
              apply Nat.div_eq_of_lt_le <;> omega
            rw [this]
          simp only [hd, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.bind_some]
          have e6 : t.shift / 5 = levelOf t.shift + 1 := by unfold levelOf; omega
          rw [e6, ht, readAt_makePath, get_tail_leaf t j tid ttok txs ht (by omega)]
          rw [e5]
          generalize 2 ^ (t.shift + 5) = P at hg hP32 ⊢
          have : j % P = j - P := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
      · by_cases h0 : tailOffset t.size = 0
        · obtain ⟨hr, hsh⟩ := pushBackMut_first t e x n hsmall hg h0
          rw [get_of_root _ _ hjr (by rw [hsh]; exact hs2), hsh, hr, get_tail_leaf t j tid ttok txs ht (by omega)]
          have e6 : t.shift / 5 = levelOf t.shift + 1 := by unfold levelOf; omega
          rw [e6, ht, readAt_makePath]
          · have hP := pow_ge32 (5 * (levelOf t.shift + 2)) (by omega)
            rw [Nat.mod_eq_of_lt (by omega)]; omega
        · obtain ⟨hr, hsh⟩ := pushBackMut_mid t e x n hsmall hg h0
          obtain ⟨hcap, _⟩ := hroot (by omega)
          rw [shl32] at hg
          have hP := pow_ge32 (t.shift + 5) (by omega)
          have hdvd : 32 ∣ 2 ^ (t.shift + 5) := by
            have : 2 ^ 5 ∣ 2 ^ (t.shift + 5) := Nat.pow_dvd_pow 2 (by omega)
            simpa using this
          have hroom : tailOffset t.size + 32 ≤ 2 ^ (t.shift + 5) := by
            obtain ⟨c, hc⟩ := hdvd; rw [hc] at hcap hg ⊢; omega
          rw [get_of_root _ _ hjr (by rw [hsh]; exact hs2), hsh, hr, ht]
          have e5 : 5 * (levelOf t.shift + 2) = t.shift + 5 := by omega
          rw [readAt_pushTailMut (levelOf t.shift) true e (tailOffset t.size) t.root tid ttok txs (n + 1) j
            (by omega) hf.2.2 (by rw [e5, shr_zero_of_lt _ (by omega), shr_zero_of_lt _ (by omega)]) (by omega)
            (by rw [e5, shr_zero_of_lt _ (by omega), shr_zero_of_lt _ (by omega)])]
          by_cases hjt : j < tailOffset t.size
          · rw [if_pos hjt, get_of_root _ _ hjt hs2]
          · rw [if_neg hjt, get_tail_leaf t j tid ttok txs ht (by omega)]


/-! ## `conj!` keeps a tree well formed -/

theorem setAt_length_ge {β : Type} (d : β) (l : List β) (i : Nat) (x : β) :
    l.length ≤ (setAt d l i x).length ∧ i < (setAt d l i x).length := by
  unfold setAt
  split
  · simp; omega
  · simp; omega

/-- `push_tail_mut_visitor` keeps the tree well formed: the node now covers 32 more elements. -/
theorem wfP_pushTailMut : ∀ (k : Nat) (m : Bool) (e size : Nat) (node : Node α) (tid ttok : Nat)
    (txs : List α) (n : Nat),
    0 < size → size % 32 = 0 →
    (size - 1) >>> (5 * (k + 2)) = (size + 31) >>> (5 * (k + 2)) → 32 ≤ txs.length →
    wfP k (.reg size) node →
    wfP k (.reg (size + 32)) (pushTailMut k m e size node (.leaf tid ttok txs) n).1 := by
  intro k
  induction k with
  | zero =>
    intro m e size node tid ttok txs n hpos h32 hb hl hw
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨a, b, n', ys, hys, hR⟩ := pushTailMut_shape_zero m e size node (.leaf tid ttok txs) n
    rw [hR]
    have e1 : size + 32 - 1 = size + 31 := by omega
    simp only [e1] at hys ⊢
    have hb' : (size - 1) / 1024 = (size + 31) / 1024 := by simpa [shr_eq] using hb
    have hne : iIndex 5 (size - 1) ≠ iIndex 5 (size + 31) := by
      simp only [iIndex_eq, shr_eq]; simp; omega
    have hsucc : iIndex 5 (size - 1) + 1 = iIndex 5 (size + 31) := by
      simp only [iIndex_eq, shr_eq]; simp; omega
    rw [if_neg (by simpa using hne), makePath_zero]
    have hcn : (IPos.reg (size + 32)).count 5 = iIndex 5 (size + 31) + 1 := by
      simp only [IPos.count, iIndex, show size + 32 - 1 = size + 31 by omega]
    have hco : (IPos.reg size).count 5 = iIndex 5 (size - 1) + 1 := rfl
    refine ⟨rfl, fun c hc => ?_⟩
    rw [hcn] at hc
    rw [cs_inner]
    by_cases hlt : c < iIndex 5 (size + 31)
    · obtain ⟨a', b', xs, hx, hlen⟩ := hch c (by rw [hco]; omega)
      obtain ⟨hyc, hyl⟩ := ys_get node _ c ys hys hlt (lt_of_getElem? _ _ _ hx)
      rw [setAt_get_of_lt _ _ _ _ _ hlt hyl, hyc]
      refine ⟨a', b', xs, hx, ?_⟩
      have hfull : 32 ≤ xs.length := by
        simp only [IPos.towardsL, hco] at hlen
        split at hlen
        · simpa [LPos.count] using hlen
        · simp only [LPos.count, IPos.size, and31] at hlen; omega
      simp only [IPos.towardsL, hcn]
      split
      · simpa [LPos.count] using hfull
      · rename_i hh; simp at hh; omega
    · have hceq : c = iIndex 5 (size + 31) := by omega
      subst hceq
      rw [setAt_get_self]
      refine ⟨tid, ttok, txs, rfl, ?_⟩
      simp only [IPos.towardsL, hcn, bne_self_eq_false, Bool.false_eq_true, ite_false, LPos.count,
        IPos.size, and31]
      omega
  | succ k ih =>
    intro m e size node tid ttok txs n hpos h32 hb hl hw
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨a, b, n', m', ys, hys, hR⟩ := pushTailMut_shape_succ k m e size node (.leaf tid ttok txs) n
    rw [hR]
    have e1 : size + 32 - 1 = size + 31 := by omega
    have e2 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    simp only [e1] at hys ⊢
    rw [e2] at hb
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    have hcn : (IPos.reg (size + 32)).count (5 * (k + 2)) = iIndex (5 * (k + 2)) (size + 31) + 1 := by
      simp only [IPos.count, iIndex, show size + 32 - 1 = size + 31 by omega]
    have hco : (IPos.reg size).count (5 * (k + 2)) = iIndex (5 * (k + 2)) (size - 1) + 1 := rfl
    have hle := digit_le (5 * (k + 2)) (show size - 1 ≤ size + 31 by omega) hb
    refine ⟨rfl, fun c hc => ?_⟩
    rw [hcn] at hc
    rw [cs_inner]
    by_cases hlt : c < iIndex (5 * (k + 2)) (size + 31)
    · have hcold : c < (IPos.reg size).count (5 * (k + 2)) := by
        rw [hco]
        by_cases hid : iIndex (5 * (k + 2)) (size - 1) = iIndex (5 * (k + 2)) (size + 31)
        · omega
        · have hm := mod_zero_of_digit_ne _ size hsh h32 hpos hb hid
          have := digit_succ _ size hsh h32 hpos hm hb
          omega
      obtain ⟨ch, hx, hwc⟩ := hch c hcold
      obtain ⟨hyc, hyl⟩ := ys_get node _ c ys hys hlt (lt_of_getElem? _ _ _ hx)
      rw [setAt_get_of_lt _ _ _ _ _ hlt hyl, hyc]
      refine ⟨ch, hx, ?_⟩
      have hnew : (IPos.reg (size + 32)).towardsI (5 * (k + 2)) c = .full := by
        simp only [IPos.towardsI, hcn]
        split
        · rfl
        · rename_i hh; simp at hh; omega
      rw [hnew]
      simp only [IPos.towardsI, hco] at hwc
      split at hwc
      · exact hwc
      · rename_i hceq
        simp at hceq
        have hid : iIndex (5 * (k + 2)) (size - 1) ≠ iIndex (5 * (k + 2)) (size + 31) := by omega
        have hm := mod_zero_of_digit_ne _ size hsh h32 hpos hb hid
        exact wfP_reg_full k size ch hpos hm hwc
    · have hceq : c = iIndex (5 * (k + 2)) (size + 31) := by omega
      subst hceq
      rw [setAt_get_self]
      refine ⟨_, rfl, ?_⟩
      have hnew : (IPos.reg (size + 32)).towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) (size + 31)) =
          .reg (size + 32) := by
        simp only [IPos.towardsI, hcn, bne_self_eq_false, Bool.false_eq_true, ite_false, IPos.size]
      rw [hnew]
      by_cases hid : iIndex (5 * (k + 2)) (size - 1) = iIndex (5 * (k + 2)) (size + 31)
      · rw [if_pos (by simpa using hid)]
        obtain ⟨ch, hx, hwc⟩ := hch (iIndex (5 * (k + 2)) (size - 1)) (by rw [hco]; omega)
        rw [child_of_getElem? _ _ _ hx]
        have hold : (IPos.reg size).towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) (size - 1)) = .reg size := by
          simp only [IPos.towardsI, hco, bne_self_eq_false, Bool.false_eq_true, ite_false, IPos.size]
        rw [hold] at hwc
        exact ih m' e size ch tid ttok txs n' hpos h32 (shr_eq_of_digit _ hid hb) hl hwc
      · rw [if_neg (by simpa using hid)]
        have hm := mod_zero_of_digit_ne _ size hsh h32 hpos hb hid
        have hP := pow_ge32 (5 * (k + 2)) hsh
        apply wfP_makePath e k (size + 32) tid ttok txs n' (by omega) (by omega) _ hl
        rw [show size + 32 - 1 = 31 + size by omega, Nat.add_mod, hm, Nat.add_zero, Nat.mod_mod,
          Nat.mod_eq_of_lt (by omega)]
        omega

/-- **`conj!` keeps a tree well formed** (below `2^35` elements), for every owner token. -/
theorem pushBackMut_wfT [Inhabited α] (t : Tree α) (hw : t.wfT) (hsz : t.size < 2 ^ 35) (e : Nat) (x : α)
    (n : Nat) : (t.pushBackMut e x n).1.wfT := by
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  cases ht : t.tail with
  | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
  | leaf tid ttok txs =>
  rw [ht] at htlen
  simp only [Node.xs] at htlen
  have hL := levelOf_eq t.shift hs5 hs1
  by_cases hsmall : t.size - tailOffset t.size < 32
  · have hto := tailOffset_succ_of_lt _ hsmall
    obtain ⟨a, b, ys, hys, hR⟩ := pushBackMut_small t e x n hsmall
    have hyl1 : t.size - tailOffset t.size ≤ ys.length := by
      rcases hys with h | h
      · rw [h, ht]; exact htlen
      · rw [h]; exact Nat.le_of_eq (by rw [leafCopy, copyN_length])
    rw [hR]
    have hlen := setAt_length_ge (default : α) ys (t.size - tailOffset t.size) x
    refine ⟨hs5, hs1, hs2, rfl, ?_, ?_⟩
    · show t.size + 1 - tailOffset (t.size + 1) ≤ (setAt default ys (t.size - tailOffset t.size) x).length
      rw [hto]; omega
    · intro h
      have h' : 0 < tailOffset t.size := by rw [← hto]; exact h
      show tailOffset (t.size + 1) ≤ 2 ^ (t.shift + 5) ∧ wfP (levelOf t.shift) (.sub (tailOffset (t.size + 1))) t.root
      rw [hto]; exact hroot h'
  · have hpos : 0 < t.size := by have := tailOffset_le t.size; omega
    have hf := tail_facts t.size hpos
    have hto := tailOffset_succ_of_full t.size hpos (by omega)
    have h32 : t.size % 32 = 0 := by omega
    have hsz' : (t.pushBackMut e x n).1.size = t.size + 1 := pushBackMut_size1 t e x n
    have htail := pushBackMut_full_tail t e x n hsmall
    have hfull32 : 32 ≤ txs.length := by omega
    have htailwf : (t.pushBackMut e x n).1.tail.isLeaf = true ∧
        (t.pushBackMut e x n).1.size - tailOffset (t.pushBackMut e x n).1.size ≤ (t.pushBackMut e x n).1.tail.xs.length := by
      rw [htail, hsz', hto]; simp [Node.isLeaf, Node.xs]
    by_cases hg : tailOffset t.size = 32 <<< t.shift
    · obtain ⟨hr, hsh⟩ := pushBackMut_grow t e x n hsmall hg
      rw [shl32] at hg
      have hs25 : t.shift ≤ 25 := by
        rcases Nat.lt_or_ge t.shift 26 with hc | hc
        · omega
        · exfalso
          have h30 : t.shift = 30 := by omega
          rw [h30] at hg
          have := tailOffset_le t.size
          simp at hg hsz; omega
      refine ⟨by rw [hsh]; omega, by rw [hsh]; omega, by rw [hsh]; omega, htailwf.1, htailwf.2, ?_⟩
      intro _
      rw [hsz', hto, hsh, hr]
      have hlv : levelOf (t.shift + 5) = levelOf t.shift + 1 := by unfold levelOf; omega
      have hP := pow_ge32 (t.shift + 5) (by omega)
      have hsz2 : t.size = 2 ^ (t.shift + 5) + 32 := by rw [← hg]; omega
      refine ⟨?_, ?_⟩
      · have h5 : (2 : Nat) ^ 5 = 32 := rfl
        rw [Nat.pow_add, h5, hsz2]
        generalize 2 ^ (t.shift + 5) = P at hP ⊢
        omega
      · rw [hlv]
        have e5 : 5 * (levelOf t.shift + 2) = t.shift + 5 := by omega
        have hcnt : (IPos.sub t.size).count (5 * (levelOf t.shift + 2)) = 2 := by
          simp only [IPos.count]; rw [e5, shr_eq]
          have : (t.size - 1) / 2 ^ (t.shift + 5) = 1 := by
            rw [hsz2]
            generalize 2 ^ (t.shift + 5) = P at hP ⊢
            apply Nat.div_eq_of_lt_le <;> omega
          rw [this]
        refine ⟨rfl, fun c hc => ?_⟩
        rw [hcnt] at hc
        obtain ⟨hcap, hwr⟩ := hroot (by omega)
        rcases (show c = 0 ∨ c = 1 by omega) with h | h
        · subst h
          refine ⟨t.root, rfl, ?_⟩
          have hnew : (IPos.sub t.size).towardsI (5 * (levelOf t.shift + 2)) 0 = .full := by
            simp only [IPos.towardsI, hcnt]; rfl
          rw [hnew]
          rw [wfP_sub_reg _ _ _ (by rw [← hL]; omega) (by omega)] at hwr
          exact wfP_reg_full _ _ _ (by omega) (by rw [← hL, hg]; simp) hwr
        · subst h
          refine ⟨_, rfl, ?_⟩
          have hnew : (IPos.sub t.size).towardsI (5 * (levelOf t.shift + 2)) 1 = .reg t.size := by
            simp only [IPos.towardsI, hcnt, IPos.size]; rfl
          rw [hnew]
          have e6 : t.shift / 5 = levelOf t.shift + 1 := by unfold levelOf; omega
          rw [e6, ht]
          apply wfP_makePath e _ t.size tid ttok txs _ hpos h32 _ hfull32
          rw [← hL, hsz2]
          generalize 2 ^ (t.shift + 5) = P at hP ⊢
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
    · by_cases h0 : tailOffset t.size = 0
      · obtain ⟨hr, hsh⟩ := pushBackMut_first t e x n hsmall hg h0
        refine ⟨by rw [hsh]; exact hs5, by rw [hsh]; exact hs1, by rw [hsh]; exact hs2, htailwf.1, htailwf.2, ?_⟩
        intro _
        rw [hsz', hto, hsh, hr]
        have hP := pow_ge32 (t.shift + 5) (by omega)
        refine ⟨by omega, ?_⟩
        rw [wfP_sub_reg _ _ _ (by rw [← hL]; omega) (by omega)]
        have e6 : t.shift / 5 = levelOf t.shift + 1 := by unfold levelOf; omega
        rw [e6, ht]
        apply wfP_makePath e _ t.size tid ttok txs _ hpos h32 _ hfull32
        have hP' := pow_ge32 (5 * (levelOf t.shift + 2)) (by omega)
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      · obtain ⟨hr, hsh⟩ := pushBackMut_mid t e x n hsmall hg h0
        obtain ⟨hcap, hwr⟩ := hroot (by omega)
        rw [shl32] at hg
        have hP := pow_ge32 (t.shift + 5) (by omega)
        have hdvd : 32 ∣ 2 ^ (t.shift + 5) := by
          have : 2 ^ 5 ∣ 2 ^ (t.shift + 5) := Nat.pow_dvd_pow 2 (by omega)
          simpa using this
        have hroom : tailOffset t.size + 32 ≤ 2 ^ (t.shift + 5) := by
          obtain ⟨c, hc⟩ := hdvd; rw [hc] at hcap hg ⊢; omega
        refine ⟨by rw [hsh]; exact hs5, by rw [hsh]; exact hs1, by rw [hsh]; exact hs2, htailwf.1, htailwf.2, ?_⟩
        intro _
        rw [hsz', hto, hsh, hr, ht]
        refine ⟨by omega, ?_⟩
        have hsize : t.size = tailOffset t.size + 32 := by omega
        rw [wfP_sub_reg _ _ _ (by rw [← hL]; omega) (by omega)]
        rw [wfP_sub_reg _ _ _ (by rw [← hL]; omega) (by omega)] at hwr
        rw [show IPos.reg t.size = IPos.reg (tailOffset t.size + 32) from congrArg _ hsize]
        exact wfP_pushTailMut _ true e _ _ tid ttok txs _ (by omega) hf.2.2
          (by rw [← hL, shr_zero_of_lt _ (by omega), shr_zero_of_lt _ (by omega)]) hfull32 hwr

/-! ## Transients: `(transient v)`, then any number of `conj!` -/

/-- **Every transient built by `conj!`s** from a well-formed vector (`vector::transient()`, any
owner token) reads, at every index, as the list of its elements: the vector's, then the pushed
values in order (below `2^35` elements). With `empty_wfT`, this covers `(transient [])`. -/
theorem get_conjs [Inhabited α] : ∀ (xs : List α) (t : Tree α) (e n : Nat), t.wfT → t.size + xs.length < 2 ^ 35 →
    let r := xs.foldl (fun (acc : Tree α × Nat) x => acc.1.pushBackMut e x acc.2) (t, n)
    r.1.wfT ∧ r.1.size = t.size + xs.length ∧
      ∀ j, j < t.size + xs.length → r.1.get j = if j < t.size then t.get j else xs[j - t.size]? := by
  intro xs
  induction xs with
  | nil =>
    intro t e n hw _
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact ⟨hw, by first | trivial | rfl, fun j hj => by simp [hj]⟩
  | cons x xs ih =>
    intro t e n hw hsz
    simp only [List.foldl_cons, List.length_cons]
    have hw1 := pushBackMut_wfT t hw (by simp at hsz; omega) e x n
    have hs1 := pushBackMut_size1 t e x n
    obtain ⟨a1, a2, a3⟩ := ih (t.pushBackMut e x n).1 e (t.pushBackMut e x n).2 hw1 (by rw [hs1]; simp at hsz; omega)
    refine ⟨a1, by rw [a2, hs1]; omega, fun j hj => ?_⟩
    rw [a3 j (by rw [hs1]; omega), hs1]
    by_cases hj1 : j < t.size + 1
    · rw [if_pos hj1, get_pushBackMut t hw (by simp at hsz; omega) e x n j (by omega)]
      by_cases hj0 : j < t.size
      · rw [if_pos hj0, if_pos hj0]
      · rw [if_neg hj0, if_neg hj0, show j - t.size = 0 by omega]; rfl
    · rw [if_neg hj1, if_neg (by omega), show j - t.size = (j - (t.size + 1)) + 1 by omega]
      rfl

end Jank.R3.Immer.Rbts

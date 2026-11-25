import Jank.R3.Immer.Rbts

/-!
# Vector laws over the rbts replica, for every well-formed tree

The laws Clojure documents for vectors, proved of immer's own algorithms as replicated in `Rbts`
(not of a list abstraction):

- `get_assoc`: `(nth (assoc v i x) j)` is `x` at `i`, `(nth v j)` elsewhere (update_visitor);
- `get_assocMut`: the same for `assoc!` (get_mut_visitor, in place or on copies, any owner token);
- `get_pushBack`: `(nth (conj v x) j)` is `(nth v j)` below the count and `x` at it (push_back,
  push_tail_visitor, make_path, root growth);
- `get_take`: `(nth (take v k) j)` is `(nth v j)` for `j < k` (slice_right_visitor with collapse);
- `pushBack_wfT`: `conj` keeps a tree well formed; `get_pop_conj`: `(nth (pop (conj v x)) j)` is
  `(nth v j)`.

`wfP k p node` says what the C++ relies on along every valid position: an inner node at level `k`
whose first `p.count` children exist, inner below level 0 and leaves at level 0, each leaf holding
at least its position's count; `Tree.wfT` adds the tree's shift (5 to 30), its tail and
`tail_off ≤ 32 << shift`. `validI k p i` says index `i` is inside the counts of the positions it
passes (true for every `i` below the size: `validI_sub`). Index arithmetic is on `Nat` with
`>>>`/`&&&` as the C++ has it (`size_t` never overflows below `2^64`); the digit lemmas convert it.
Sizes are below `2^35`: past that the root would reach shift 35, which `visit_regular_descent`
does not handle (IMMER_UNREACHABLE).
-/

namespace Jank.R3.Immer.Rbts

variable {α : Type}

/-! ## Lists -/

theorem setAt_eq_set {β : Type} (d : β) (l : List β) (i : Nat) (x : β) (h : i < l.length) :
    setAt d l i x = l.set i x := by simp [setAt, h]

theorem copyN_length {β : Type} (d : β) (l : List β) (n : Nat) : (copyN d l n).length = n := by
  simp [copyN]; omega

theorem copyN_getElem? {β : Type} (d : β) (l : List β) (n c : Nat) (hc : c < n) (hl : c < l.length) :
    (copyN d l n)[c]? = l[c]? := by
  unfold copyN
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]
  simp [hc]

/-! ## Reading -/

/-- A slot read as a leaf (`leaf_descent_pos` on a node that is a leaf), else none. -/
def leafOpt : Option (Node α) → Option (Node α)
  | some (.leaf a b c) => some (.leaf a b c)
  | _ => none

theorem descendLeaf_zero (id tok : Nat) (cs : List (Node α)) (j : Nat) :
    descendLeaf 0 (.inner id tok cs) j = leafOpt cs[iIndex 5 j]? := by
  simp only [descendLeaf]
  rcases h : cs[iIndex 5 j]? with _ | ⟨_ | _⟩ <;> simp [leafOpt]

theorem descendLeaf_succ (k id tok : Nat) (cs : List (Node α)) (j : Nat) :
    descendLeaf (k + 1) (.inner id tok cs) j = (cs[iIndex (5 * (k + 2)) j]?).bind (descendLeaf k · j) := by
  simp only [descendLeaf]
  rcases h : cs[iIndex (5 * (k + 2)) j]? with _ | _ <;> simp

/-- Element `j` read through a level-`k` inner node. -/
def readAt (k : Nat) (node : Node α) (j : Nat) : Option α :=
  (descendLeaf k node j).bind fun l => l.xs[lIndex j]?

/-- Well-formed along every valid position (see the module doc). -/
def wfP : Nat → IPos → Node α → Prop
  | 0, p, node => node.isLeaf = false ∧ ∀ c, c < p.count 5 →
      ∃ id tok xs, node.cs[c]? = some (.leaf id tok xs) ∧ (p.towardsL 5 c).count ≤ xs.length
  | k + 1, p, node => node.isLeaf = false ∧ ∀ c, c < p.count (5 * (k + 2)) →
      ∃ ch, node.cs[c]? = some ch ∧ wfP k (p.towardsI (5 * (k + 2)) c) ch

/-- Index `i` within the counts of the positions it passes. -/
def validI : Nat → IPos → Nat → Prop
  | 0, p, i => iIndex 5 i < p.count 5 ∧ lIndex i < (p.towardsL 5 (iIndex 5 i)).count
  | k + 1, p, i => iIndex (5 * (k + 2)) i < p.count (5 * (k + 2)) ∧
      validI k (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) i)) i

/-- Two indices that take the same child at every level. -/
def samePathB : Nat → Nat → Nat → Bool
  | 0, i, j => iIndex 5 i == iIndex 5 j
  | k + 1, i, j => iIndex (5 * (k + 2)) i == iIndex (5 * (k + 2)) j && samePathB k i j

theorem childCopy_getElem? (node : Node α) (cnt c : Nat) (hc : c < cnt) (hl : c < node.cs.length) :
    (childCopy node cnt)[c]? = node.cs[c]? := copyN_getElem? _ _ _ _ hc hl

theorem leafCopy_getElem? [Inhabited α] (node : Node α) (cnt c : Nat) (hc : c < cnt) (hl : c < node.xs.length) :
    (leafCopy node cnt)[c]? = node.xs[c]? := copyN_getElem? _ _ _ _ hc hl

theorem leaf_update_read [Inhabited α] (L : Node α) (c li lj : Nat) (x : α) (hc : c ≤ L.xs.length)
    (hi : li < c) (hj : lj < c) :
    (setAt default (leafCopy L c) li x)[lj]? = if li = lj then some x else L.xs[lj]? := by
  have hlen : (leafCopy L c).length = c := copyN_length _ _ _
  rw [setAt_eq_set _ _ _ _ (by omega)]
  by_cases h : li = lj
  · subst h; simp [List.getElem?_set, hlen, hi]
  · simp only [List.getElem?_set, h, if_false]
    exact leafCopy_getElem? L c lj hj (by omega)

theorem inner_set_read (node : Node α) (cnt ci cj : Nat) (ch : Node α) (hci : ci < cnt) (hcj : cj < cnt)
    (hl : cj < node.cs.length) :
    (setAt Node.dummy (childCopy node cnt) ci ch)[cj]? = if ci = cj then some ch else node.cs[cj]? := by
  have hlen : (childCopy node cnt).length = cnt := copyN_length _ _ _
  rw [setAt_eq_set _ _ _ _ (by omega)]
  by_cases h : ci = cj
  · subst h; simp [List.getElem?_set, hlen, hci]
  · simp only [List.getElem?_set, h, if_false]
    exact childCopy_getElem? node cnt cj hcj hl

theorem readAt_zero (id tok : Nat) (cs : List (Node α)) (j : Nat) :
    readAt 0 (.inner id tok cs) j = (leafOpt cs[iIndex 5 j]?).bind fun l => l.xs[lIndex j]? := by
  simp [readAt, descendLeaf_zero]

theorem readAt_succ (k id tok : Nat) (cs : List (Node α)) (j : Nat) :
    readAt (k + 1) (.inner id tok cs) j = (cs[iIndex (5 * (k + 2)) j]?).bind fun c => readAt k c j := by
  simp [readAt, descendLeaf_succ, Option.bind_assoc]

theorem updInner_zero [Inhabited α] (p : IPos) (node : Node α) (i : Nat) (x : α) (n : Nat) :
    (updInner 0 p node i x n).1 = .inner n 0 (setAt Node.dummy (childCopy node (p.count 5)) (iIndex 5 i)
      (.leaf (n + 1) 0 (setAt default (leafCopy (node.child (iIndex 5 i)) (p.towardsL 5 (iIndex 5 i)).count)
        (lIndex i) x))) := rfl

theorem updInner_succ [Inhabited α] (k : Nat) (p : IPos) (node : Node α) (i : Nat) (x : α) (n : Nat) :
    (updInner (k + 1) p node i x n).1 = .inner n 0 (setAt Node.dummy (childCopy node (p.count (5 * (k + 2))))
      (iIndex (5 * (k + 2)) i)
      (updInner k (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) i))
        (node.child (iIndex (5 * (k + 2)) i)) i x (n + 1)).1) := rfl

theorem child_of_getElem? (node : Node α) (c : Nat) (ch : Node α) (h : node.cs[c]? = some ch) :
    node.child c = ch := by
  simp [Node.child, List.getD, h]

theorem lt_of_getElem? {β : Type} (l : List β) (c : Nat) (b : β) (h : l[c]? = some b) : c < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- `nth` after `assoc` through an inner node (update_visitor), level by level. -/
theorem readAt_updInner [Inhabited α] (k : Nat) : ∀ (p : IPos) (node : Node α) (i : Nat) (x : α) (n j : Nat),
    wfP k p node → validI k p i → validI k p j →
    readAt k (updInner k p node i x n).1 j =
      if samePathB k i j && lIndex i == lIndex j then some x else readAt k node j := by
  induction k with
  | zero =>
    intro p node i x n j hw hi hj
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    cases node with
    | leaf => simp [Node.isLeaf] at hnl
    | inner id tok cs =>
    obtain ⟨lid, ltok, lxs, hcs, hlen⟩ := hch _ hi1
    obtain ⟨lid', ltok', lxs', hcs', hlen'⟩ := hch _ hj1
    have hlt : iIndex 5 j < (Node.inner id tok cs).cs.length := lt_of_getElem? _ _ _ hcs'
    rw [updInner_zero, readAt_zero, inner_set_read _ _ _ _ _ hi1 hj1 hlt]
    by_cases hij : iIndex 5 i = iIndex 5 j
    · rw [if_pos hij, child_of_getElem? _ _ _ hcs]
      simp only [leafOpt, Option.bind_some, Node.xs]
      have hj2' : lIndex j < (p.towardsL 5 (iIndex 5 i)).count := by rw [hij]; exact hj2
      rw [leaf_update_read (Node.leaf lid ltok lxs) _ (lIndex i) (lIndex j) x hlen hi2 hj2']
      have hr : readAt 0 (Node.inner id tok cs) j = lxs[lIndex j]? := by
        rw [readAt_zero]; simp only [Node.cs] at hcs; rw [← hij, hcs]; rfl
      rw [hr]
      simp [samePathB, hij, Node.xs]
    · rw [if_neg hij]
      simp [samePathB, hij, readAt_zero, Node.cs]
  | succ k ih =>
    intro p node i x n j hw hi hj
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    cases node with
    | leaf => simp [Node.isLeaf] at hnl
    | inner id tok cs =>
    obtain ⟨ch, hcs, hwc⟩ := hch _ hi1
    obtain ⟨ch', hcs', hwc'⟩ := hch _ hj1
    have hlt : iIndex (5 * (k + 2)) j < (Node.inner id tok cs).cs.length := lt_of_getElem? _ _ _ hcs'
    rw [updInner_succ, readAt_succ, inner_set_read _ _ _ _ _ hi1 hj1 hlt]
    by_cases hij : iIndex (5 * (k + 2)) i = iIndex (5 * (k + 2)) j
    · rw [if_pos hij, child_of_getElem? _ _ _ hcs]
      simp only [Option.bind_some]
      have hj2' : validI k (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) i)) j := by rw [hij]; exact hj2
      rw [ih _ _ _ _ _ _ hwc hi2 hj2']
      have hr : readAt (k + 1) (Node.inner id tok cs) j = readAt k ch j := by
        rw [readAt_succ]; simp only [Node.cs] at hcs; rw [← hij, hcs]; rfl
      rw [hr]
      simp [samePathB, hij]
    · rw [if_neg hij]
      simp [samePathB, hij, readAt_succ, Node.cs]

/-! ## Radix arithmetic -/

theorem and31 (x : Nat) : x &&& 31 = x % 32 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 5
  simpa using this

theorem shr_eq (x a : Nat) : x >>> a = x / 2 ^ a := Nat.shiftRight_eq_div_pow x a

theorem shr_add5 (x a : Nat) : x >>> (a + 5) = (x >>> a) / 32 := by
  rw [Nat.shiftRight_add, shr_eq (x >>> a) 5]

theorem iIndex_eq (sh x : Nat) : iIndex sh x = (x >>> sh) % 32 := by simp [iIndex, and31]

theorem lIndex_eq (x : Nat) : lIndex x = x % 32 := by simp [lIndex, and31]

theorem iIndex_lt (sh x : Nat) : iIndex sh x < 32 := by rw [iIndex_eq]; omega

theorem lIndex_lt (x : Nat) : lIndex x < 32 := by rw [lIndex_eq]; omega

theorem shr_mono (a : Nat) {j s : Nat} (h : j ≤ s) : j >>> a ≤ s >>> a := by
  rw [shr_eq, shr_eq]; exact Nat.div_le_div_right h

/-- Within one block (`a + 5` bits above equal), `j ≤ s` orders the digits at `a`. -/
theorem digit_le (a : Nat) {j s : Nat} (h : j ≤ s) (hb : j >>> (a + 5) = s >>> (a + 5)) :
    iIndex a j ≤ iIndex a s := by
  rw [iIndex_eq, iIndex_eq]
  rw [shr_add5, shr_add5] at hb
  have := shr_mono a h
  omega

/-- Equal digits and equal blocks above: equal at `a`. -/
theorem shr_eq_of_digit (a : Nat) {j s : Nat} (hd : iIndex a j = iIndex a s) (hb : j >>> (a + 5) = s >>> (a + 5)) :
    j >>> a = s >>> a := by
  rw [iIndex_eq, iIndex_eq] at hd
  rw [shr_add5, shr_add5] at hb
  omega

theorem shr_zero_of_lt (a : Nat) {j : Nat} (h : j < 2 ^ a) : j >>> a = 0 := by
  rw [shr_eq]; exact Nat.div_eq_of_lt h

theorem iIndex_zero (x : Nat) : iIndex 0 x = lIndex x := by simp [iIndex, lIndex]

theorem validI_full : ∀ k j, validI k IPos.full j := by
  intro k
  induction k with
  | zero => intro j; exact ⟨by simp [IPos.count]; exact iIndex_lt _ _, by simp [IPos.towardsL, LPos.count]; exact lIndex_lt _⟩
  | succ k ih => intro j; exact ⟨by simp [IPos.count]; exact iIndex_lt _ _, by simp [IPos.towardsI]; exact ih j⟩

theorem validI_reg : ∀ k s j, j ≤ s - 1 → j >>> (5 * (k + 2)) = (s - 1) >>> (5 * (k + 2)) →
    validI k (.reg s) j := by
  intro k
  induction k with
  | zero =>
    intro s j hle hb
    have hb' : j >>> (5 + 5) = (s - 1) >>> (5 + 5) := hb
    have hd := digit_le 5 hle hb'
    have hcount : IPos.count 5 (.reg s) = iIndex 5 (s - 1) + 1 := rfl
    refine ⟨by rw [hcount]; omega, ?_⟩
    simp only [IPos.towardsL]
    split
    · simp [LPos.count]; exact lIndex_lt _
    · rename_i hc
      simp only [hcount, bne_iff_ne, ne_eq, Decidable.not_not] at hc
      have heq : iIndex 5 j = iIndex 5 (s - 1) := by omega
      have h5 := shr_eq_of_digit 5 heq hb'
      have h0 : j >>> (0 + 5) = (s - 1) >>> (0 + 5) := h5
      have := digit_le 0 hle h0
      rw [iIndex_zero, iIndex_zero] at this
      simp only [LPos.count, IPos.size]
      have : lIndex (s - 1) = (s - 1) &&& 31 := rfl
      omega
  | succ k ih =>
    intro s j hle hb
    have e : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e] at hb
    have hd := digit_le (5 * (k + 2)) hle hb
    have hcount : IPos.count (5 * (k + 2)) (.reg s) = iIndex (5 * (k + 2)) (s - 1) + 1 := rfl
    refine ⟨by rw [hcount]; omega, ?_⟩
    simp only [IPos.towardsI]
    split
    · exact validI_full k j
    · rename_i hc
      simp only [hcount, bne_iff_ne, ne_eq, Decidable.not_not] at hc
      have heq : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) (s - 1) := by omega
      exact ih s j hle (shr_eq_of_digit _ heq hb)

theorem validI_sub : ∀ k s j, j < s → s ≤ 2 ^ (5 * (k + 2)) → validI k (.sub s) j := by
  intro k
  cases k with
  | zero =>
    intro s j hlt hs
    have hj : j >>> 10 = 0 := shr_zero_of_lt 10 (by simp at hs; omega)
    have hs1 : (s - 1) >>> 10 = 0 := shr_zero_of_lt 10 (by simp at hs; omega)
    have hdj : iIndex 5 j = j >>> 5 := by
      rw [iIndex_eq]; have := shr_add5 j 5; simp at this; omega
    have hds : iIndex 5 (s - 1) = (s - 1) >>> 5 := by
      rw [iIndex_eq]; have := shr_add5 (s - 1) 5; simp at this; omega
    have hmono := shr_mono 5 (show j ≤ s - 1 by omega)
    have hcount : IPos.count 5 (.sub s) = ((s - 1) >>> 5) + 1 := rfl
    refine ⟨by rw [hcount]; omega, ?_⟩
    simp only [IPos.towardsL]
    split
    · simp [LPos.count]; exact lIndex_lt _
    · rename_i hc
      simp only [hcount, bne_iff_ne, ne_eq, Decidable.not_not] at hc
      have h0 : j >>> (0 + 5) = (s - 1) >>> (0 + 5) := by simp; omega
      have := digit_le 0 (show j ≤ s - 1 by omega) h0
      rw [iIndex_zero, iIndex_zero] at this
      simp only [LPos.count, IPos.size]
      have : lIndex (s - 1) = (s - 1) &&& 31 := rfl
      omega
  | succ k =>
    intro s j hlt hs
    have e : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e] at hs
    have hj : j >>> (5 * (k + 2) + 5) = 0 := shr_zero_of_lt _ (by omega)
    have hs1 : (s - 1) >>> (5 * (k + 2) + 5) = 0 := shr_zero_of_lt _ (by omega)
    have hdj : iIndex (5 * (k + 2)) j = j >>> (5 * (k + 2)) := by
      rw [iIndex_eq]; have := shr_add5 j (5 * (k + 2)); omega
    have hmono := shr_mono (5 * (k + 2)) (show j ≤ s - 1 by omega)
    have hcount : IPos.count (5 * (k + 2)) (.sub s) = ((s - 1) >>> (5 * (k + 2))) + 1 := rfl
    refine ⟨by rw [hcount]; omega, ?_⟩
    simp only [IPos.towardsI]
    split
    · exact validI_full k j
    · rename_i hc
      simp only [hcount, bne_iff_ne, ne_eq, Decidable.not_not] at hc
      exact validI_reg k s j (by omega) (by omega)

theorem samePath_shr : ∀ k i j, samePathB k i j = true → i >>> (5 * (k + 2)) = j >>> (5 * (k + 2)) →
    i >>> 5 = j >>> 5 := by
  intro k
  induction k with
  | zero =>
    intro i j h hb
    simp only [samePathB, beq_iff_eq] at h
    exact shr_eq_of_digit 5 h hb
  | succ k ih =>
    intro i j h hb
    simp only [samePathB, Bool.and_eq_true, beq_iff_eq] at h
    have e : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e] at hb
    exact ih i j h.2 (shr_eq_of_digit _ h.1 hb)

theorem samePath_refl : ∀ k i, samePathB k i i = true := by
  intro k; induction k with
  | zero => intro i; simp [samePathB]
  | succ k ih => intro i; simp [samePathB, ih]

/-- Two indices below `2 ^ (5 * (k + 2))` with the same path and leaf slot are equal. -/
theorem eq_of_samePath (k i j : Nat) (hi : i < 2 ^ (5 * (k + 2))) (hj : j < 2 ^ (5 * (k + 2)))
    (h : samePathB k i j = true) (hl : lIndex i = lIndex j) : i = j := by
  have h1 := samePath_shr k i j h (by rw [shr_zero_of_lt _ hi, shr_zero_of_lt _ hj])
  rw [lIndex_eq, lIndex_eq] at hl
  have a := shr_add5 i 0
  have b := shr_add5 j 0
  simp at a b
  omega

/-! ## Trees -/

/-- What the C++ relies on in a tree: shift a multiple of 5 within the descent's range, a tail
leaf holding its elements, a root well formed along the positions under `tail_off`. -/
def Tree.wfT (t : Tree α) : Prop :=
  t.shift % 5 = 0 ∧ 5 ≤ t.shift ∧ t.shift ≤ 30 ∧
  t.tail.isLeaf = true ∧ t.size - tailOffset t.size ≤ t.tail.xs.length ∧
  (0 < tailOffset t.size → tailOffset t.size ≤ 2 ^ (t.shift + 5) ∧
    wfP (levelOf t.shift) (.sub (tailOffset t.size)) t.root)

theorem tailOffset_eq (s : Nat) : tailOffset s = if s = 0 then 0 else (s - 1) / 32 * 32 := by
  unfold tailOffset; split
  · rfl
  · simp [Nat.shiftLeft_eq, shr_eq]

theorem tail_facts (s : Nat) (h : 0 < s) :
    tailOffset s ≤ s - 1 ∧ s - tailOffset s ≤ 32 ∧ tailOffset s % 32 = 0 := by
  rw [tailOffset_eq, if_neg (by omega)]; omega

/-- In the tail, the slot of `j` is its distance from `tail_off`. -/
theorem lIndex_tail (s j : Nat) (h1 : tailOffset s ≤ j) (h2 : j < s) : lIndex j = j - tailOffset s := by
  have := tail_facts s (by omega)
  rw [lIndex_eq]; rw [tailOffset_eq, if_neg (by omega)] at *; omega

theorem get_of_tail (t : Tree α) (j : Nat) (h : tailOffset t.size ≤ j) :
    t.get j = (match t.tail with | .leaf _ _ xs => some xs | .inner .. => none).bind (·[lIndex j]?) := by
  unfold Tree.get Tree.arrayFor; rw [if_pos h]; rfl

theorem get_tail_leaf (t : Tree α) (j : Nat) (a b : Nat) (xs : List α) (ht : t.tail = .leaf a b xs)
    (h : tailOffset t.size ≤ j) : t.get j = xs[lIndex j]? := by
  unfold Tree.get Tree.arrayFor; rw [if_pos h, ht]; rfl

theorem get_of_root (t : Tree α) (j : Nat) (h : j < tailOffset t.size) (hs : t.shift ≤ 30) :
    t.get j = readAt (levelOf t.shift) t.root j := by
  simp only [Tree.get, Tree.arrayFor, readAt]
  rw [if_neg (by omega), if_neg (by omega), Option.bind_map]
  rfl

theorem levelOf_eq (sh : Nat) (h1 : sh % 5 = 0) (h2 : 5 ≤ sh) : sh + 5 = 5 * (levelOf sh + 2) := by
  unfold levelOf; omega

/-- **`nth` after `assoc`**: for every well-formed vector, `(nth (assoc v i x) j)` is `x` at `i`
and `(nth v j)` elsewhere (`i, j < count`; `assoc` at `count` is `conj`). -/
theorem get_assoc [Inhabited α] (t : Tree α) (hw : t.wfT) (i j : Nat) (x : α) (n : Nat)
    (hi : i < t.size) (hj : j < t.size) :
    (t.assoc i x n).1.get j = if i = j then some x else t.get j := by
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  have hf := tail_facts t.size (by omega)
  by_cases hit : tailOffset t.size ≤ i
  · -- the tail is copied with slot `i - tail_off` set
    have hA : (t.assoc i x n).1 = { t with tail := .leaf n 0 (setAt default
        (leafCopy t.tail (t.size - tailOffset t.size)) (lIndex (i - tailOffset t.size)) x) } := by
      simp [Tree.assoc, updLeaf, LPos.count, hit]
    rw [hA]
    by_cases hjt : tailOffset t.size ≤ j
    · rw [get_of_tail _ _ (by simpa using hjt), get_of_tail _ _ hjt]
      cases ht : t.tail with
      | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
      | leaf a b xs =>
        simp only [Option.bind_some]
        rw [ht] at htlen
        have hli : lIndex (i - tailOffset t.size) = i - tailOffset t.size := by
          rw [lIndex_eq]; omega
        have hlj := lIndex_tail t.size j hjt hj
        rw [hli, hlj]
        have := leaf_update_read (Node.leaf a b xs) (t.size - tailOffset t.size) (i - tailOffset t.size)
          (j - tailOffset t.size) x (by simpa [Node.xs] using htlen) (by omega) (by omega)
        rw [this]
        by_cases hij : i = j
        · simp [hij]
        · rw [if_neg (by omega), if_neg hij]; rfl
    · have hjt' : j < tailOffset t.size := by omega
      rw [get_of_root _ _ (by simpa using hjt') (by simpa using hs2), get_of_root _ _ hjt' hs2]
      rw [if_neg (by omega)]
  · have hit' : i < tailOffset t.size := by omega
    obtain ⟨hcap, hwr⟩ := hroot (by omega)
    have hA : (t.assoc i x n).1 = { t with root := (updInner (levelOf t.shift) (.sub (tailOffset t.size)) t.root i x n).1 } := by
      simp [Tree.assoc, hit]
    rw [hA]
    have hcap' : tailOffset t.size ≤ 2 ^ (5 * (levelOf t.shift + 2)) := by
      rw [← levelOf_eq _ hs5 hs1]; exact hcap
    by_cases hjt : tailOffset t.size ≤ j
    · rw [get_of_tail _ _ (by simpa using hjt), get_of_tail _ _ hjt, if_neg (by omega)]
    · have hjt' : j < tailOffset t.size := by omega
      rw [get_of_root _ _ (by simpa using hjt') (by simpa using hs2), get_of_root _ _ hjt' hs2]
      have hvi := validI_sub _ _ _ hit' hcap'
      have hvj := validI_sub _ _ _ hjt' hcap'
      rw [readAt_updInner _ _ _ _ _ _ _ hwr hvi hvj]
      by_cases hij : i = j
      · subst hij; simp [samePath_refl]
      · have : (samePathB (levelOf t.shift) i j && lIndex i == lIndex j) = false := by
          cases h : samePathB (levelOf t.shift) i j
          · rfl
          · simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq]
            intro hl
            exact hij (eq_of_samePath _ i j (by omega) (by omega) h hl)
        rw [this, if_neg hij]; rfl

/-! ## `conj`: `push_back`, `push_tail_visitor`, `make_path` -/

theorem readAt_dummy (k j : Nat) : readAt k (Node.dummy : Node α) j = none := by
  cases k <;> simp [readAt, Node.dummy, descendLeaf]

/-- Level 0 read as a bind over the child slot. -/
theorem readAt_zero' (id tok : Nat) (cs : List (Node α)) (j : Nat) :
    readAt 0 (.inner id tok cs) j = (cs[iIndex 5 j]?).bind fun c => (leafOpt (some c)).bind fun l => l.xs[lIndex j]? := by
  rw [readAt_zero]; cases cs[iIndex 5 j]? <;> simp [leafOpt]

theorem copyN_bind {β γ : Type} (d : β) (l : List β) (cnt c : Nat) (f : β → Option γ) (hd : f d = none)
    (hc : c < cnt) : ((copyN d l cnt)[c]?).bind f = (l[c]?).bind f := by
  by_cases hl : c < l.length
  · rw [copyN_getElem? d l cnt c hc hl]
  · have h1 : (copyN d l cnt)[c]? = some d := by
      unfold copyN
      rw [List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
      simp only [List.length_take]
      rw [if_pos (by omega)]
    rw [h1, List.getElem?_eq_none (by omega)]; simp [hd]

/-- `setAt` one past a copy: the copy, then the new slot. -/
theorem append_read {β : Type} (d : β) (l : List β) (cnt c : Nat) (x : β) :
    (setAt d (copyN d l cnt) cnt x)[c]? = if c < cnt then (copyN d l cnt)[c]? else if c = cnt then some x else none := by
  have hlen : (copyN d l cnt).length = cnt := copyN_length _ _ _
  unfold setAt
  rw [if_neg (by omega), hlen, Nat.sub_self, List.replicate_zero, List.append_nil]
  by_cases h : c < cnt
  · rw [if_pos h, List.getElem?_append_left (by omega)]
  · rw [if_neg h, List.getElem?_append_right (by omega), hlen]
    by_cases h2 : c = cnt
    · subst h2; simp
    · rw [if_neg h2]; simp; omega

theorem makePath_succ (tok k : Nat) (node : Node α) (n : Nat) :
    (makePath tok (k + 1) node n).1 = .inner n tok [(makePath tok k node (n + 1)).1] := rfl

theorem makePath_zero (tok : Nat) (node : Node α) (n : Nat) : (makePath tok 0 node n).1 = node := rfl

theorem pow_ge32 (a : Nat) (ha : 5 ≤ a) : 32 ≤ 2 ^ a :=
  calc 32 = 2 ^ 5 := rfl
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha

theorem iIndex_zero_of_mod (a j : Nat) (ha : 5 ≤ a) (h : j % 2 ^ (a + 5) < 32) : iIndex a j = 0 := by
  rw [iIndex_eq, shr_eq, ← Nat.mod_mul_right_div_self j (2 ^ a) 32]
  have hp : 2 ^ a * 32 = 2 ^ (a + 5) := by rw [Nat.pow_add]
  rw [hp]
  apply Nat.div_eq_of_lt
  have := pow_ge32 a ha
  omega

theorem mod_lt_of_mod_lt (j a : Nat) (h : j % 2 ^ (a + 5) < 32) : j % 2 ^ a < 32 := by
  have hd : 2 ^ a ∣ 2 ^ (a + 5) := Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_of_dvd j hd]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

/-- A path (`make_path`) reads its leaf at every index whose digits below it are zero. -/
theorem readAt_makePath (tok : Nat) : ∀ (k : Nat) (id tk : Nat) (xs : List α) (n j : Nat),
    j % 2 ^ (5 * (k + 2)) < 32 →
    readAt k (makePath tok (k + 1) (.leaf id tk xs) n).1 j = xs[lIndex j]? := by
  intro k
  induction k with
  | zero =>
    intro id tk xs n j h
    rw [makePath_succ, makePath_zero, readAt_zero]
    have : iIndex 5 j = 0 := iIndex_zero_of_mod 5 j (Nat.le_refl _) (by simpa using h)
    simp [this, leafOpt, Node.xs]
  | succ k ih =>
    intro id tk xs n j h
    rw [makePath_succ, readAt_succ]
    have e : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e] at h
    have : iIndex (5 * (k + 2)) j = 0 := iIndex_zero_of_mod _ j (by omega) h
    simp only [this, List.getElem?_cons_zero, Option.bind_some]
    exact ih id tk xs (n + 1) j (mod_lt_of_mod_lt j _ h)

/-- `(size + 31) >> a` is `size >> a` for `size` a multiple of 32 and `a ≥ 5`. -/
theorem shr_add31 (a size : Nat) (ha : 5 ≤ a) (h32 : size % 32 = 0) : (size + 31) >>> a = size >>> a := by
  have e : a = 5 + (a - 5) := by omega
  rw [e, Nat.shiftRight_add, Nat.shiftRight_add]
  congr 1
  rw [shr_eq, shr_eq]; simp; omega

/-- Different digits for `size - 1` and `size + 31` inside one block: `size` is a multiple of
`2 ^ a`. -/
theorem mod_zero_of_digit_ne (a size : Nat) (ha : 5 ≤ a) (h32 : size % 32 = 0) (hpos : 0 < size)
    (hb : (size - 1) >>> (a + 5) = (size + 31) >>> (a + 5))
    (hne : iIndex a (size - 1) ≠ iIndex a (size + 31)) : size % 2 ^ a = 0 := by
  have h1 := shr_add31 a size ha h32
  have hd : (size - 1) >>> a ≠ size >>> a := by
    intro heq; apply hne; rw [iIndex_eq, iIndex_eq, h1, heq]
  rw [shr_eq, shr_eq] at hd
  rcases Nat.eq_zero_or_pos (size % 2 ^ a) with hr | hr
  · exact hr
  · exfalso
    apply hd
    have hsplit := Nat.div_add_mod size (2 ^ a)
    have hl := Nat.mod_lt size (show 0 < 2 ^ a by have := pow_ge32 a ha; omega)
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm (size / 2 ^ a) (2 ^ a)]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (size / 2 ^ a) (2 ^ a)]; omega

theorem pushTail_def (k size : Nat) (node tail : Node α) (n : Nat) :
    (pushTail k size node tail n).1 =
      .inner n 0 (setAt Node.dummy (childCopy node (iIndex (5 * (k + 1)) (size + 32 - 1)))
        (iIndex (5 * (k + 1)) (size + 32 - 1))
        (if iIndex (5 * (k + 1)) (size - 1) == iIndex (5 * (k + 1)) (size + 32 - 1) then
          (match k with
           | 0 => (Node.dummy, n + 1)
           | k' + 1 => pushTail k' size (node.child (iIndex (5 * (k + 1)) (size - 1))) tail (n + 1)).1
         else (makePath 0 k tail (n + 1)).1)) := by
  conv => lhs; unfold pushTail
  dsimp only
  split <;> rfl

theorem cs_inner (id tok : Nat) (cs : List (Node α)) : (Node.inner id tok cs).cs = cs := rfl

theorem readAt_zero_cs (node : Node α) (j : Nat) :
    readAt 0 node j = (node.cs[iIndex 5 j]?).bind fun c => (leafOpt (some c)).bind fun l => l.xs[lIndex j]? := by
  cases node with
  | leaf => simp [readAt, descendLeaf, Node.cs]
  | inner id tok cs => exact readAt_zero' id tok cs j

theorem readAt_succ_cs (k : Nat) (node : Node α) (j : Nat) :
    readAt (k + 1) node j = (node.cs[iIndex (5 * (k + 2)) j]?).bind fun c => readAt k c j := by
  cases node with
  | leaf => simp [readAt, descendLeaf, Node.cs]
  | inner id tok cs => exact readAt_succ k id tok cs j

theorem child_read (k : Nat) (node : Node α) (c j : Nat) :
    readAt k (node.child c) j = (node.cs[c]?).bind fun ch => readAt k ch j := by
  cases h : node.cs[c]? with
  | none => simp [Node.child, List.getD, h, readAt_dummy]
  | some ch => simp [Node.child, List.getD, h]

/-- An index between `size` and `size + 31` shifts like `size + 31`. -/
theorem shr_window (a size j : Nat) (ha : 5 ≤ a) (h32 : size % 32 = 0) (h1 : size ≤ j) (h2 : j < size + 32) :
    j >>> a = (size + 31) >>> a := by
  have m1 := shr_mono a h1
  have m2 := shr_mono a (show j ≤ size + 31 by omega)
  have := shr_add31 a size ha h32
  omega

/-- **`push_tail_visitor`**: reads below `size` are unchanged; the 32 slots from `size` read the
pushed tail. -/
theorem readAt_pushTail : ∀ (k size : Nat) (node : Node α) (tid ttok : Nat) (txs : List α) (n j : Nat),
    0 < size → size % 32 = 0 →
    (size - 1) >>> (5 * (k + 2)) = (size + 31) >>> (5 * (k + 2)) →
    j < size + 32 → j >>> (5 * (k + 2)) = (size - 1) >>> (5 * (k + 2)) →
    readAt k (pushTail k size node (.leaf tid ttok txs) n).1 j =
      if j < size then readAt k node j else txs[lIndex j]? := by
  intro k
  induction k with
  | zero =>
    intro size node tid ttok txs n j hpos h32 hb hj hjb
    rw [pushTail_def]
    have e1 : size + 32 - 1 = size + 31 := by omega
    have e0 : 5 * (0 + 1) = 5 := rfl
    simp only [e1, e0]
    have hb' : (size - 1) / 1024 = (size + 31) / 1024 := by simpa [shr_eq] using hb
    have hjb' : j / 1024 = (size - 1) / 1024 := by simpa [shr_eq] using hjb
    have hne : iIndex 5 (size - 1) ≠ iIndex 5 (size + 31) := by
      simp only [iIndex_eq, shr_eq]; simp; omega
    rw [if_neg (by simpa using hne), makePath_zero, readAt_zero_cs, readAt_zero_cs, cs_inner]
    unfold childCopy
    rw [append_read]
    by_cases hjs : j < size
    · rw [if_pos hjs]
      have : iIndex 5 j < iIndex 5 (size + 31) := by
        simp only [iIndex_eq, shr_eq]; simp; omega
      rw [if_pos this]
      exact copyN_bind _ _ _ _ _ (by simp [leafOpt, Node.dummy]) this
    · rw [if_neg hjs]
      have hj1 : iIndex 5 j = iIndex 5 (size + 31) := by
        simp only [iIndex_eq, shr_eq]; simp; omega
      rw [if_neg (by omega), if_pos hj1]
      simp [leafOpt, Node.xs]
  | succ k ih =>
    intro size node tid ttok txs n j hpos h32 hb hj hjb
    rw [pushTail_def]
    have e1 : size + 32 - 1 = size + 31 := by omega
    have e2 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    have e3 : 5 * (k + 1 + 1) = 5 * (k + 2) := by omega
    simp only [e1, e3]
    rw [e2] at hb hjb
    rw [readAt_succ_cs, readAt_succ_cs, cs_inner]
    unfold childCopy
    rw [append_read]
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    by_cases hjs : j < size
    · rw [if_pos hjs]
      have hd := digit_le (5 * (k + 2)) (show j ≤ size - 1 by omega) hjb
      have hi := digit_le (5 * (k + 2)) (show size - 1 ≤ size + 31 by omega) hb
      by_cases hlt : iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) (size + 31)
      · rw [if_pos hlt]; exact copyN_bind _ _ _ _ _ (readAt_dummy _ _) hlt
      · have heq : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) (size + 31) := by omega
        have hidx : iIndex (5 * (k + 2)) (size - 1) = iIndex (5 * (k + 2)) (size + 31) := by omega
        rw [if_neg hlt, if_pos heq, if_pos (by simpa using hidx)]
        simp only [Option.bind_some]
        have hblk := shr_eq_of_digit _ hidx hb
        have hjblk := shr_eq_of_digit _ (show iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) (size - 1) by omega) hjb
        rw [ih size _ tid ttok txs (n + 1) j hpos h32 hblk hj hjblk, if_pos hjs, child_read, hidx, heq]
    · rw [if_neg hjs]
      have hwin := shr_window (5 * (k + 2)) size j hsh h32 (by omega) hj
      have hj1 : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) (size + 31) := by
        simp only [iIndex_eq]; rw [hwin]
      rw [if_neg (by omega), if_pos hj1]
      simp only [Option.bind_some]
      by_cases hidx : iIndex (5 * (k + 2)) (size - 1) = iIndex (5 * (k + 2)) (size + 31)
      · rw [if_pos (by simpa using hidx)]
        have hblk := shr_eq_of_digit _ hidx hb
        rw [ih size _ tid ttok txs (n + 1) j hpos h32 hblk hj (by rw [hwin, hblk]), if_neg hjs]
      · rw [if_neg (by simpa using hidx)]
        apply readAt_makePath
        have hm := mod_zero_of_digit_ne (5 * (k + 2)) size hsh h32 hpos hb hidx
        have hP := pow_ge32 (5 * (k + 2)) hsh
        have : j % 2 ^ (5 * (k + 2)) = (j - size) % 2 ^ (5 * (k + 2)) := by
          conv => lhs; rw [show j = (j - size) + size by omega]
          rw [Nat.add_mod, hm, Nat.add_zero, Nat.mod_mod]
        rw [this, Nat.mod_eq_of_lt (by omega)]
        omega

theorem pushBack_size1 [Inhabited α] (t : Tree α) (x : α) (n : Nat) :
    (t.pushBack x n).1.size = t.size + 1 := by
  unfold Tree.pushBack; dsimp only
  repeat' split
  all_goals rfl

theorem tailOffset_succ_of_lt (s : Nat) (h : s - tailOffset s < 32) : tailOffset (s + 1) = tailOffset s := by
  rw [tailOffset_eq, tailOffset_eq] at *
  by_cases h0 : s = 0
  · subst h0; simp
  · rw [if_neg h0] at h; rw [if_neg (by omega), if_neg h0]; omega

theorem tailOffset_succ_of_full (s : Nat) (hpos : 0 < s) (h : 32 ≤ s - tailOffset s) : tailOffset (s + 1) = s := by
  have := tail_facts s hpos
  rw [tailOffset_eq] at *
  rw [if_neg (by omega)]; rw [if_neg (by omega)] at this h; omega

theorem tailOffset_le (s : Nat) : tailOffset s ≤ s := by
  rw [tailOffset_eq]; split <;> omega

theorem shl32 (s : Nat) : 32 <<< s = 2 ^ (s + 5) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm]

theorem pushBack_full_tail [Inhabited α] (t : Tree α) (x : α) (n : Nat) (h : ¬ t.size - tailOffset t.size < 32) :
    (t.pushBack x n).1.tail = .leaf n 0 [x] := by
  unfold Tree.pushBack; dsimp only; rw [if_neg h]
  repeat' split
  all_goals rfl

theorem pushBack_grow [Inhabited α] (t : Tree α) (x : α) (n : Nat) (h : ¬ t.size - tailOffset t.size < 32)
    (hg : tailOffset t.size = 32 <<< t.shift) :
    (t.pushBack x n).1.root = .inner (n + 1) 0 [t.root, (makePath 0 (t.shift / 5) t.tail (n + 2)).1] ∧
    (t.pushBack x n).1.shift = t.shift + 5 := by
  unfold Tree.pushBack; dsimp only; rw [if_neg h, if_pos (by simpa using hg)]
  constructor <;> rfl

theorem pushBack_mid [Inhabited α] (t : Tree α) (x : α) (n : Nat) (h : ¬ t.size - tailOffset t.size < 32)
    (hg : tailOffset t.size ≠ 32 <<< t.shift) (h0 : tailOffset t.size ≠ 0) :
    (t.pushBack x n).1.root = (pushTail (levelOf t.shift) (tailOffset t.size) t.root t.tail (n + 1)).1 ∧
    (t.pushBack x n).1.shift = t.shift := by
  unfold Tree.pushBack; dsimp only; rw [if_neg h, if_neg (by simpa using hg), if_pos (by simpa using h0)]
  constructor <;> rfl

theorem pushBack_first [Inhabited α] (t : Tree α) (x : α) (n : Nat) (h : ¬ t.size - tailOffset t.size < 32)
    (hg : tailOffset t.size ≠ 32 <<< t.shift) (h0 : tailOffset t.size = 0) :
    (t.pushBack x n).1.root = (makePath 0 (t.shift / 5) t.tail (n + 1)).1 ∧
    (t.pushBack x n).1.shift = t.shift := by
  unfold Tree.pushBack; dsimp only; rw [if_neg h, if_neg (by simpa using hg), if_neg (by simpa using h0)]
  constructor <;> rfl

/-- The tree `push_back` builds when the tail has room. -/
def smallPush [Inhabited α] (t : Tree α) (x : α) (n : Nat) : Tree α :=
  { size := t.size + 1, shift := t.shift, root := t.root,
    tail := Node.leaf n 0 (leafCopy t.tail (t.size - tailOffset t.size) ++ [x]) }

theorem pushBack_small [Inhabited α] (t : Tree α) (x : α) (n : Nat) (h : t.size - tailOffset t.size < 32) :
    (t.pushBack x n).1 = (smallPush t x n) := by
  simp [Tree.pushBack, h, smallPush]

/-- **`nth` after `conj`**: for every well-formed vector below `2^35` elements, `(nth (conj v x) j)`
is `(nth v j)` for `j < count` and `x` at `count`. (At `2^35 + 32` elements the root would reach
shift 35, which `visit_regular_descent` does not handle: IMMER_UNREACHABLE.) -/
theorem get_pushBack [Inhabited α] (t : Tree α) (hw : t.wfT) (hsz : t.size < 2 ^ 35) (x : α) (n j : Nat)
    (hj : j ≤ t.size) :
    (t.pushBack x n).1.get j = if j < t.size then t.get j else some x := by
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  cases ht : t.tail with
  | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
  | leaf tid ttok txs =>
  rw [ht] at htlen
  simp only [Node.xs] at htlen
  by_cases hsmall : t.size - tailOffset t.size < 32
  · have hto := tailOffset_succ_of_lt _ hsmall
    rw [pushBack_small _ _ _ hsmall]
    have hsz1 : (smallPush t x n).size = t.size + 1 := rfl
    by_cases hjt : tailOffset t.size ≤ j
    · rw [get_tail_leaf (smallPush t x n) j n 0 _ rfl (by rw [hsz1, hto]; exact hjt)]
      have hlj : lIndex j = j - tailOffset t.size := by
        have := lIndex_tail (t.size + 1) j (by rw [hto]; exact hjt) (by omega)
        rw [this, hto]
      rw [hlj]
      have hlen : (leafCopy t.tail (t.size - tailOffset t.size)).length = t.size - tailOffset t.size :=
        copyN_length _ _ _
      by_cases hjs : j < t.size
      · rw [if_pos hjs, List.getElem?_append_left (by omega), get_tail_leaf t j tid ttok txs ht hjt,
          lIndex_tail _ _ hjt hjs]
        rw [ht]
        exact leafCopy_getElem? _ _ _ (by omega) (by simp [Node.xs]; omega)
      · rw [if_neg hjs, List.getElem?_append_right (by omega), hlen]
        have : j - tailOffset t.size - (t.size - tailOffset t.size) = 0 := by omega
        rw [this]; rfl
    · have hjt' : j < tailOffset t.size := by omega
      rw [get_of_root (smallPush t x n) j (by rw [hsz1, hto]; exact hjt') hs2,
        if_pos (by have := tailOffset_le t.size; omega), get_of_root t j hjt' hs2]
      rfl
  · have hpos : 0 < t.size := by have := tailOffset_le t.size; omega
    have hf := tail_facts t.size hpos
    have hfull : t.size - tailOffset t.size = 32 := by omega
    have hto := tailOffset_succ_of_full t.size hpos (by omega)
    have h32 : t.size % 32 = 0 := by omega
    have hsz' : (t.pushBack x n).1.size = t.size + 1 := pushBack_size1 t x n
    by_cases hjs : j = t.size
    · subst hjs
      rw [if_neg (by omega), get_tail_leaf (t.pushBack x n).1 t.size n 0 [x] (pushBack_full_tail _ _ _ hsmall)
        (by rw [hsz', hto]; exact Nat.le_refl _)]
      simp [lIndex_eq, h32]
    · have hjs' : j < t.size := by omega
      rw [if_pos hjs']
      have hjr : j < tailOffset (t.pushBack x n).1.size := by rw [hsz', hto]; exact hjs'
      have hL := levelOf_eq t.shift hs5 hs1
      by_cases hg : tailOffset t.size = 32 <<< t.shift
      · obtain ⟨hr, hsh⟩ := pushBack_grow t x n hsmall hg
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
        · obtain ⟨hr, hsh⟩ := pushBack_first t x n hsmall hg h0
          rw [get_of_root _ _ hjr (by rw [hsh]; exact hs2), hsh, hr, get_tail_leaf t j tid ttok txs ht (by omega)]
          have e6 : t.shift / 5 = levelOf t.shift + 1 := by unfold levelOf; omega
          rw [e6, ht, readAt_makePath]
          · have hP := pow_ge32 (5 * (levelOf t.shift + 2)) (by omega)
            rw [Nat.mod_eq_of_lt (by omega)]; omega
        · obtain ⟨hr, hsh⟩ := pushBack_mid t x n hsmall hg h0
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
          rw [readAt_pushTail (levelOf t.shift) (tailOffset t.size) t.root tid ttok txs (n + 1) j (by omega)
            hf.2.2 (by rw [e5, shr_zero_of_lt _ (by omega), shr_zero_of_lt _ (by omega)]) (by omega)
            (by rw [e5, shr_zero_of_lt _ (by omega), shr_zero_of_lt _ (by omega)])]
          by_cases hjt : j < tailOffset t.size
          · rw [if_pos hjt, get_of_root _ _ hjt hs2]
          · rw [if_neg hjt, get_tail_leaf t j tid ttok txs ht (by omega)]

/-! ## `pop`: `take`, `slice_right_visitor` -/

/-- The tail a slice ends with comes from the child the slice descends into. -/
theorem sliceInner_tail_zero [Inhabited α] (c : Bool) (p : IPos) (node : Node α) (last n : Nat) :
    (sliceInner 0 c p node last n).1.2.2.2 =
      (sliceLeaf (p.towardsL 5 (iIndex 5 last)) (node.child (iIndex 5 last)) last n).1.2.2.2 := by
  rw [sliceInner.eq_1]
  dsimp only
  repeat' split
  all_goals simp_all

/-- The tail does not depend on the collapse flag. -/
theorem sliceInner_tail_indep [Inhabited α] (k : Nat) : ∀ (c : Bool) (p : IPos) (node : Node α) (last n : Nat),
    (sliceInner k c p node last n).1.2.2.2 = (sliceInner k false p node last n).1.2.2.2 := by
  induction k with
  | zero => intro c p node last n; rw [sliceInner_tail_zero, sliceInner_tail_zero]
  | succ k ih =>
    intro c p node last n
    have key : ∀ c', (sliceInner (k + 1) c' p node last n).1.2.2.2 =
        (sliceInner k false (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last))
          (node.child (iIndex (5 * (k + 2)) last)) last n).1.2.2.2 := by
      intro c'
      rw [sliceInner.eq_2]
      dsimp only
      split
      · exact ih _ _ _ _ _
      · repeat' split
        all_goals simp_all
    rw [key c, key false]

theorem sliceInner_tail_step [Inhabited α] (k : Nat) (c : Bool) (p : IPos) (node : Node α) (last n : Nat) :
    (sliceInner (k + 1) c p node last n).1.2.2.2 =
      (sliceInner k false (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last))
        (node.child (iIndex (5 * (k + 2)) last)) last n).1.2.2.2 := by
  rw [sliceInner.eq_2]
  dsimp only
  split
  · exact sliceInner_tail_indep k _ _ _ _ _
  · repeat' split
    all_goals simp_all

theorem sliceInner_tail_succ [Inhabited α] (k : Nat) (c : Bool) (p : IPos) (node : Node α) (last n : Nat) :
    (sliceInner (k + 1) c p node last n).1.2.2.2 =
      (sliceInner k (c && iIndex (5 * (k + 2)) last == 0) (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last))
        (node.child (iIndex (5 * (k + 2)) last)) last n).1.2.2.2 := by
  rw [sliceInner_tail_step, sliceInner_tail_indep k (c && iIndex (5 * (k + 2)) last == 0)]

theorem sliceLeaf_tail [Inhabited α] (p : LPos) (node : Node α) (last n j : Nat)
    (hl : lIndex last + 1 ≤ node.xs.length) (hj : lIndex j ≤ lIndex last) :
    (sliceLeaf p node last n).1.2.2.2.xs[lIndex j]? = node.xs[lIndex j]? := by
  unfold sliceLeaf
  dsimp only
  split
  · rfl
  · simp only [Node.xs]
    exact leafCopy_getElem? node _ _ (by omega) (by omega)

/-- **The tail after a slice**: the leaf holding `last`, its slots up to `last` unchanged. -/
theorem sliceInner_tail_read [Inhabited α] : ∀ (k : Nat) (c : Bool) (p : IPos) (node : Node α) (last n j : Nat),
    wfP k p node → validI k p last → j >>> 5 = last >>> 5 → lIndex j ≤ lIndex last →
    (sliceInner k c p node last n).1.2.2.2.isLeaf = true ∧
    (sliceInner k c p node last n).1.2.2.2.xs[lIndex j]? = readAt k node j := by
  intro k
  induction k with
  | zero =>
    intro c p node last n j hw hv hjb hjl
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨lid, ltok, lxs, hcs, hlen⟩ := hch _ hv1
    rw [sliceInner_tail_zero, child_of_getElem? _ _ _ hcs]
    have hd : iIndex 5 j = iIndex 5 last := by
      simp only [iIndex_eq]; rw [hjb]
    constructor
    · unfold sliceLeaf; dsimp only; split <;> rfl
    · rw [sliceLeaf_tail _ _ _ _ _ (by simp [Node.xs]; omega) hjl, readAt_zero_cs, hd, hcs]
      simp [leafOpt, Node.xs]
  | succ k ih =>
    intro c p node last n j hw hv hjb hjl
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
    rw [sliceInner_tail_succ, child_of_getElem? _ _ _ hcs]
    have hd : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) last := by
      have e : 5 * (k + 2) = 5 + (5 * (k + 2) - 5) := by omega
      simp only [iIndex_eq]; rw [e, Nat.shiftRight_add, Nat.shiftRight_add, hjb]
    obtain ⟨h1, h2⟩ := ih (c && iIndex (5 * (k + 2)) last == 0) _ ch last n j hwc hv2 hjb hjl
    refine ⟨h1, ?_⟩
    rw [h2, readAt_succ_cs, hd, hcs]
    rfl

/-- Below the leaf of `last`, within its block: a digit at shift 5 smaller than `last`'s. -/
theorem digit5_lt (j last : Nat) (hb : j >>> 10 = last >>> 10) (hj : j < last - lIndex last) :
    iIndex 5 j < iIndex 5 last := by
  simp only [iIndex_eq, lIndex_eq, shr_eq] at *; simp at *; omega

theorem sliceLeaf_none [Inhabited α] (p : LPos) (node : Node α) (last n : Nat) :
    (sliceLeaf p node last n).1.2.1 = none := by
  unfold sliceLeaf; dsimp only; split <;> rfl

/-- **Slice without collapse** (`slice_right_visitor<false>`): no root iff `last` sits in the
first leaf of its block; else a root at the same shift reading as the node below `last`'s leaf. -/
theorem sliceInner_root_nc [Inhabited α] : ∀ (k : Nat) (p : IPos) (node : Node α) (last n : Nat),
    wfP k p node → validI k p last →
    ((sliceInner k false p node last n).1.2.1 = none → last % 2 ^ (5 * (k + 2)) < 32) ∧
    (∀ x, (sliceInner k false p node last n).1.2.1 = some x →
      (sliceInner k false p node last n).1.1 = 5 * (k + 1) ∧
      ∀ j, j >>> (5 * (k + 2)) = last >>> (5 * (k + 2)) → j < last - lIndex last →
        readAt k x j = readAt k node j) := by
  intro k
  induction k with
  | zero =>
    intro p node last n hw hv
    rw [sliceInner.eq_1]
    dsimp only
    try simp only [show (5 : Nat) * (0 + 1) = 5 from rfl]
    rw [if_neg (by simp)]
    have hnone := sliceLeaf_none (p.towardsL 5 (iIndex 5 last)) (node.child (iIndex 5 last)) last n
    rcases hR : sliceLeaf (p.towardsL 5 (iIndex 5 last)) (node.child (iIndex 5 last)) last n with ⟨⟨a, b, c, d⟩, e⟩
    rw [hR] at hnone
    simp only at hnone
    subst hnone
    dsimp only
    by_cases h0 : iIndex 5 last = 0
    · rw [if_pos (by simp [h0])]
      refine ⟨fun _ => ?_, fun x hx => by simp at hx⟩
      simp only [iIndex_eq, shr_eq] at h0; simp at h0 ⊢; omega
    · rw [if_neg (by simp [h0]), if_neg (by simp)]
      refine ⟨fun h => by simp at h, fun x hx => ?_⟩
      simp only [Option.some.injEq] at hx
      subst hx
      refine ⟨rfl, fun j hjb hj => ?_⟩
      have hd := digit5_lt j last (by simpa using hjb) hj
      rw [readAt_zero_cs, readAt_zero_cs, cs_inner]
      unfold childCopy
      exact copyN_bind _ _ _ _ _ (by simp [leafOpt, Node.dummy]) hd
  | succ k ih =>
    intro p node last n hw hv
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
    have IH := ih _ ch last n hwc hv2
    rw [sliceInner.eq_2]
    dsimp only
    have e2 : 5 * (k + 1 + 1) = 5 * (k + 2) := by omega
    simp only [e2]
    rw [if_neg (by simp)]
    rw [child_of_getElem? _ _ _ hcs]
    rcases hR : sliceInner k false (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last)) ch last n
      with ⟨⟨a, b, c, d⟩, e⟩
    rw [hR] at IH
    simp only at IH
    obtain ⟨IHn, IHs⟩ := IH
    have e3 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e3]
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    cases b with
    | some nx =>
      dsimp only
      refine ⟨fun h => by simp at h, fun x hx => ?_⟩
      simp only [Option.some.injEq] at hx
      subst hx
      refine ⟨rfl, fun j hjb hj => ?_⟩
      obtain ⟨_, IHr⟩ := IHs nx rfl
      have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
      rw [readAt_succ_cs, readAt_succ_cs, cs_inner]
      unfold childCopy
      rw [append_read]
      by_cases hlt : iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) last
      · rw [if_pos hlt]; exact copyN_bind _ _ _ _ _ (readAt_dummy _ _) hlt
      · have heq : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) last := by omega
        rw [if_neg hlt, if_pos heq, heq, hcs]
        simp only [Option.bind_some]
        exact IHr j (shr_eq_of_digit _ heq hjb) hj
    | none =>
      dsimp only
      have hfirst := IHn rfl
      by_cases h0 : iIndex (5 * (k + 2)) last = 0
      · rw [if_pos (by simp [h0])]
        refine ⟨fun _ => ?_, fun x hx => by simp at hx⟩
        rw [iIndex_eq, shr_eq, ← Nat.mod_mul_right_div_self last (2 ^ (5 * (k + 2))) 32] at h0
        have hp : 2 ^ (5 * (k + 2)) * 32 = 2 ^ (5 * (k + 2) + 5) := by rw [Nat.pow_add]
        rw [hp] at h0
        have hP := pow_ge32 (5 * (k + 2)) hsh
        have := Nat.div_add_mod (last % 2 ^ (5 * (k + 2) + 5)) (2 ^ (5 * (k + 2)))
        rw [h0, Nat.mul_zero, Nat.zero_add] at this
        have hmm : last % 2 ^ (5 * (k + 2) + 5) % 2 ^ (5 * (k + 2)) = last % 2 ^ (5 * (k + 2)) :=
          Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
        omega
      · rw [if_neg (by simp [h0]), if_neg (by simp)]
        refine ⟨fun h => by simp at h, fun x hx => ?_⟩
        simp only [Option.some.injEq] at hx
        subst hx
        refine ⟨rfl, fun j hjb hj => ?_⟩
        have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
        have hlt : iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) last := by
          rcases Nat.lt_or_eq_of_le hdle with h | h
          · exact h
          · exfalso
            -- `last` is in the first leaf of child `idx`; `j` is in that child below it
            have hjs := shr_eq_of_digit _ h hjb
            have hjd : j / 2 ^ (5 * (k + 2)) = last / 2 ^ (5 * (k + 2)) := by rw [← shr_eq, ← shr_eq]; exact hjs
            have h1 := Nat.div_add_mod j (2 ^ (5 * (k + 2)))
            have h2 := Nat.div_add_mod last (2 ^ (5 * (k + 2)))
            rw [hjd] at h1
            rw [lIndex_eq] at hj
            have hm : last % 2 ^ (5 * (k + 2)) % 32 = last % 32 :=
              Nat.mod_mod_of_dvd _ (by have : 2 ^ 5 ∣ 2 ^ (5 * (k + 2)) := Nat.pow_dvd_pow 2 (by omega); simpa using this)
            rw [Nat.mod_eq_of_lt hfirst] at hm
            omega
        rw [readAt_succ_cs, readAt_succ_cs, cs_inner]
        unfold childCopy
        exact copyN_bind _ _ _ _ _ (readAt_dummy _ _) hlt

theorem low_of_digit0 (a last : Nat) (ha : 5 ≤ a) (h0 : iIndex a last = 0) (hl : last % 2 ^ a < 32) :
    last % 2 ^ (a + 5) < 32 := by
  rw [iIndex_eq, shr_eq, ← Nat.mod_mul_right_div_self last (2 ^ a) 32] at h0
  have hp : 2 ^ a * 32 = 2 ^ (a + 5) := by rw [Nat.pow_add]
  rw [hp] at h0
  have := Nat.div_add_mod (last % 2 ^ (a + 5)) (2 ^ a)
  rw [h0, Nat.mul_zero, Nat.zero_add] at this
  have hmm : last % 2 ^ (a + 5) % 2 ^ a = last % 2 ^ a := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
  omega

/-- **Slice with collapse** (`slice_right_visitor<true>`, what `take` runs): no root iff `last`
sits in the first leaf; else a root at a shift no higher, reading as the node below `last`'s leaf. -/
theorem sliceInner_root_c [Inhabited α] : ∀ (k : Nat) (p : IPos) (node : Node α) (last n : Nat),
    wfP k p node → validI k p last →
    ((sliceInner k true p node last n).1.2.1 = none → last % 2 ^ (5 * (k + 2)) < 32) ∧
    (∀ x, (sliceInner k true p node last n).1.2.1 = some x →
      (sliceInner k true p node last n).1.1 % 5 = 0 ∧ 5 ≤ (sliceInner k true p node last n).1.1 ∧
      (sliceInner k true p node last n).1.1 ≤ 5 * (k + 1) ∧
      ∀ j, j >>> (5 * (k + 2)) = last >>> (5 * (k + 2)) → j < last - lIndex last →
        readAt (levelOf (sliceInner k true p node last n).1.1) x j = readAt k node j) := by
  intro k
  induction k with
  | zero =>
    intro p node last n hw hv
    rw [sliceInner.eq_1]
    dsimp only
    try simp only [show (5 : Nat) * (0 + 1) = 5 from rfl]
    by_cases h0 : iIndex 5 last = 0
    · rw [if_pos (by simp [h0]), sliceLeaf_none]
      refine ⟨fun _ => ?_, fun x hx => by simp at hx⟩
      simp only [iIndex_eq, shr_eq] at h0; simp at h0 ⊢; omega
    · rw [if_neg (by simp [h0])]
      have hnone := sliceLeaf_none (p.towardsL 5 (iIndex 5 last)) (node.child (iIndex 5 last)) last n
      rcases hR : sliceLeaf (p.towardsL 5 (iIndex 5 last)) (node.child (iIndex 5 last)) last n with ⟨⟨a, b, c, d⟩, e⟩
      rw [hR] at hnone
      simp only at hnone
      subst hnone
      dsimp only
      rw [if_neg (by simp [h0]), if_neg (by simp)]
      refine ⟨fun h => by simp at h, fun x hx => ?_⟩
      simp only [Option.some.injEq] at hx
      subst hx
      refine ⟨by simp, Nat.le_refl _, Nat.le_refl _, fun j hjb hj => ?_⟩
      have hd := digit5_lt j last (by simpa using hjb) hj
      dsimp only
      rw [show levelOf 5 = 0 from rfl]
      rw [readAt_zero_cs, readAt_zero_cs, cs_inner]
      unfold childCopy
      exact copyN_bind _ _ _ _ _ (by simp [leafOpt, Node.dummy]) hd
  | succ k ih =>
    intro p node last n hw hv
    have hw' := hw
    have hv' := hv
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hv1, hv2⟩ := hv
    obtain ⟨ch, hcs, hwc⟩ := hch _ hv1
    rw [sliceInner.eq_2]
    dsimp only
    have e2 : 5 * (k + 1 + 1) = 5 * (k + 2) := by omega
    have e3 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    simp only [e2, e3]
    rw [child_of_getElem? _ _ _ hcs]
    by_cases h0 : iIndex (5 * (k + 2)) last = 0
    · rw [if_pos (by simp [h0])]
      rw [h0] at hcs hwc hv2 ⊢
      obtain ⟨IHn, IHs⟩ := ih _ ch last n hwc hv2
      refine ⟨fun h => low_of_digit0 _ last hsh h0 (IHn h), fun x hx => ?_⟩
      obtain ⟨a1, a2, a3, IHr⟩ := IHs x hx
      refine ⟨a1, a2, by omega, fun j hjb hj => ?_⟩
      have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
      have hd0 : iIndex (5 * (k + 2)) j = 0 := by omega
      rw [IHr j (shr_eq_of_digit _ (by rw [hd0, h0]) hjb) hj, readAt_succ_cs, hd0, hcs]
      rfl
    · rw [if_neg (by simp [h0])]
      have IH := sliceInner_root_nc k _ ch last n hwc hv2
      rcases hR : sliceInner k false (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) last)) ch last n
        with ⟨⟨a, b, c, d⟩, e⟩
      rw [hR] at IH
      simp only at IH
      obtain ⟨IHn, IHs⟩ := IH
      cases b with
      | some nx =>
        dsimp only
        refine ⟨fun h => by simp at h, fun x hx => ?_⟩
        simp only [Option.some.injEq] at hx
        subst hx
        have hlv : levelOf (5 * (k + 2)) = k + 1 := by unfold levelOf; omega
        refine ⟨by omega, by omega, Nat.le_refl _, fun j hjb hj => ?_⟩
        rw [hlv]
        obtain ⟨_, IHr⟩ := IHs nx rfl
        have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
        rw [readAt_succ_cs, readAt_succ_cs, cs_inner]
        unfold childCopy
        rw [append_read]
        by_cases hlt : iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) last
        · rw [if_pos hlt]; exact copyN_bind _ _ _ _ _ (readAt_dummy _ _) hlt
        · have heq : iIndex (5 * (k + 2)) j = iIndex (5 * (k + 2)) last := by omega
          rw [if_neg hlt, if_pos heq, heq, hcs]
          simp only [Option.bind_some]
          exact IHr j (shr_eq_of_digit _ heq hjb) hj
      | none =>
        dsimp only
        have hfirst := IHn rfl
        rw [if_neg (by simp [h0])]
        -- every `j` below `last`'s leaf is in an earlier child
        have hbelow : ∀ j, j >>> (5 * (k + 2) + 5) = last >>> (5 * (k + 2) + 5) → j < last - lIndex last →
            iIndex (5 * (k + 2)) j < iIndex (5 * (k + 2)) last := by
          intro j hjb hj
          have hdle := digit_le (5 * (k + 2)) (show j ≤ last by omega) hjb
          rcases Nat.lt_or_eq_of_le hdle with h | h
          · exact h
          · exfalso
            have hjs := shr_eq_of_digit _ h hjb
            have hjd : j / 2 ^ (5 * (k + 2)) = last / 2 ^ (5 * (k + 2)) := by rw [← shr_eq, ← shr_eq]; exact hjs
            have h1 := Nat.div_add_mod j (2 ^ (5 * (k + 2)))
            have h2 := Nat.div_add_mod last (2 ^ (5 * (k + 2)))
            rw [hjd] at h1
            rw [lIndex_eq] at hj
            have hm : last % 2 ^ (5 * (k + 2)) % 32 = last % 32 :=
              Nat.mod_mod_of_dvd _ (by have : 2 ^ 5 ∣ 2 ^ (5 * (k + 2)) := Nat.pow_dvd_pow 2 (by omega); simpa using this)
            rw [Nat.mod_eq_of_lt hfirst] at hm
            omega
        by_cases h1 : iIndex (5 * (k + 2)) last = 1
        · rw [if_pos (by simp [h1] <;> omega)]
          refine ⟨fun h => by simp at h, fun x hx => ?_⟩
          simp only [Option.some.injEq] at hx
          subst hx
          dsimp only
          have hlv : levelOf (5 * (k + 2) - 5) = k := by unfold levelOf; omega
          refine ⟨by omega, by omega, by omega, fun j hjb hj => ?_⟩
          rw [hlv]
          have hd0 : iIndex (5 * (k + 2)) j = 0 := by have := hbelow j hjb hj; omega
          rw [readAt_succ_cs, hd0, child_read]
        · rw [if_neg (by simp [h1])]
          refine ⟨fun h => by simp at h, fun x hx => ?_⟩
          simp only [Option.some.injEq] at hx
          subst hx
          dsimp only
          have hlv : levelOf (5 * (k + 2)) = k + 1 := by unfold levelOf; omega
          refine ⟨by omega, by omega, by omega, fun j hjb hj => ?_⟩
          rw [hlv, readAt_succ_cs, readAt_succ_cs, cs_inner]
          unfold childCopy
          exact copyN_bind _ _ _ _ _ (readAt_dummy _ _) (hbelow j hjb hj)

theorem tailOffset_take (k : Nat) (h : 0 < k) : tailOffset k = (k - 1) - lIndex (k - 1) := by
  rw [tailOffset_eq, if_neg (by omega), lIndex_eq]; omega

/-- **`nth` after `take`** (so after `pop`): for every well-formed vector, the first `k` elements
are unchanged. -/
theorem get_take [Inhabited α] (t : Tree α) (hw : t.wfT) (k n j : Nat) (hk : k ≤ t.size) (hj : j < k) :
    (t.take k n).1.get j = t.get j := by
  have hw0 := hw
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  have hpos : 0 < t.size := by omega
  have hf := tail_facts t.size hpos
  by_cases hks : k = t.size
  · subst hks; unfold Tree.take; simp [show t.size ≠ 0 by omega]
  have hk' : k < t.size := by omega
  by_cases htk : tailOffset t.size < k
  · -- the tail is cut: `copy_leaf(tail, new_size - tail_off)`
    have hA : (t.take k n).1 = { t with size := k, tail := .leaf n 0 (leafCopy t.tail (k - tailOffset t.size)) } := by
      unfold Tree.take; simp [show k ≠ 0 by omega, show ¬ t.size ≤ k by omega, htk]
    have hto : tailOffset k = tailOffset t.size := by
      rw [tailOffset_eq, tailOffset_eq, if_neg (by omega), if_neg (by omega)]
      rw [tailOffset_eq, if_neg (by omega)] at htk hf; omega
    rw [hA]
    by_cases hjt : tailOffset t.size ≤ j
    · rw [get_of_tail _ _ (by simpa [hto] using hjt), get_of_tail _ _ hjt]
      cases ht : t.tail with
      | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
      | leaf a b xs =>
        simp only [Option.bind_some]
        rw [ht] at htlen
        rw [lIndex_tail t.size j hjt (by omega)]
        exact leafCopy_getElem? _ _ _ (by omega) (by simp [Node.xs] at htlen ⊢; omega)
    · have hjt' : j < tailOffset t.size := by omega
      have e := get_of_root ({ t with size := k, tail := .leaf n 0 (leafCopy t.tail (k - tailOffset t.size)) } : Tree α) j
        (by show j < tailOffset k; rw [hto]; exact hjt') hs2
      rw [e, get_of_root t j hjt' hs2]
  · -- `slice_right_visitor` on the root
    have hkt : k ≤ tailOffset t.size := by omega
    obtain ⟨hcap, hwr⟩ := hroot (by omega)
    have hL := levelOf_eq t.shift hs5 hs1
    have hcap' : tailOffset t.size ≤ 2 ^ (5 * (levelOf t.shift + 2)) := by rw [← hL]; exact hcap
    have hvl := validI_sub _ _ (k - 1) (by omega) hcap'
    have hTO := tailOffset_take k (by omega)
    have RC := sliceInner_root_c (levelOf t.shift) (.sub (tailOffset t.size)) t.root (k - 1) n hwr hvl
    have TR := fun j hjb hjl =>
      sliceInner_tail_read (levelOf t.shift) true (.sub (tailOffset t.size)) t.root (k - 1) n j hwr hvl hjb hjl
    have hblk : ∀ i, i < tailOffset t.size → i >>> (5 * (levelOf t.shift + 2)) = 0 :=
      fun i hi => shr_zero_of_lt _ (by omega)
    rw [get_of_root t j (by omega) hs2]
    unfold Tree.take
    have c1 : (k == 0) = false := by simp; omega
    have c2 : ¬ (k ≥ t.size) := by omega
    have c3 : ¬ (k > tailOffset t.size) := by omega
    simp only [c1, c2, c3, Bool.false_eq_true, ite_false]
    rcases hR : sliceInner (levelOf t.shift) true (.sub (tailOffset t.size)) t.root (k - 1) n
      with ⟨⟨ns, nr, ts, nt⟩, m⟩
    rw [hR] at RC TR
    simp only at RC TR
    obtain ⟨RCn, RCs⟩ := RC
    by_cases hjt : tailOffset k ≤ j
    · have hjb : j >>> 5 = (k - 1) >>> 5 := by
        rw [hTO, lIndex_eq] at hjt; simp only [shr_eq]; simp; omega
      have hjl : lIndex j ≤ lIndex (k - 1) := by
        rw [hTO, lIndex_eq] at hjt; simp only [lIndex_eq]; omega
      obtain ⟨hleaf, hread⟩ := TR j hjb hjl
      cases nt with
      | inner => simp [Node.isLeaf] at hleaf
      | leaf a b xs =>
        cases nr with
        | none =>
          dsimp only
          rw [get_of_tail _ _ hjt]
          simpa [Node.xs] using hread
        | some r =>
          dsimp only
          rw [get_of_tail _ _ hjt]
          simpa [Node.xs] using hread
    · have hjt' : j < tailOffset k := by omega
      cases nr with
      | none =>
        exfalso
        have h1 := RCn rfl
        rw [← hL] at h1
        rw [Nat.mod_eq_of_lt (by omega)] at h1
        rw [hTO, lIndex_eq] at hjt'
        omega
      | some r =>
        obtain ⟨a1, a2, a3, rd⟩ := RCs r rfl
        dsimp only
        rw [get_of_root _ _ hjt' (by show ns ≤ 30; omega)]
        exact rd j (by rw [hblk j (by omega), hblk (k - 1) (by omega)]) (by rw [← hTO]; exact hjt')

/-! ## `conj` keeps a vector well formed (for `pop` after `conj`) -/

theorem count_sub_eq_reg (sh s : Nat) (h : s ≤ 2 ^ (sh + 5)) (hs : 0 < s) :
    (IPos.sub s).count sh = (IPos.reg s).count sh := by
  simp only [IPos.count]
  have : (s - 1) >>> sh < 32 := by
    rw [shr_eq]
    apply Nat.div_lt_of_lt_mul
    rw [Nat.pow_add] at h
    have : 2 ^ sh * 2 ^ 5 = 2 ^ sh * 32 := rfl
    omega
  rw [and31, Nat.mod_eq_of_lt this]

theorem wfP_sub_reg (k s : Nat) (node : Node α) (h : s ≤ 2 ^ (5 * (k + 2))) (hs : 0 < s) :
    wfP k (.sub s) node ↔ wfP k (.reg s) node := by
  cases k with
  | zero =>
    have hc := count_sub_eq_reg 5 s (by simpa using h) hs
    simp only [wfP, IPos.towardsL, IPos.size, hc]
  | succ k =>
    have e : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e] at h
    have hc := count_sub_eq_reg (5 * (k + 2)) s h hs
    simp only [wfP, IPos.towardsI, IPos.size, hc]

theorem count_reg_full (sh s : Nat) (hs : 0 < s) (h : s % 2 ^ (sh + 5) = 0) : (IPos.reg s).count sh = 32 := by
  simp only [IPos.count, and31, shr_eq]
  rw [← Nat.mod_mul_right_div_self (s - 1) (2 ^ sh) 32]
  have hp : 2 ^ sh * 32 = 2 ^ (sh + 5) := by rw [Nat.pow_add]
  rw [hp]
  have hP : 0 < 2 ^ sh := Nat.two_pow_pos sh
  have hm : (s - 1) % 2 ^ (sh + 5) = 2 ^ (sh + 5) - 1 := by
    have h1 := Nat.div_add_mod s (2 ^ (sh + 5))
    rw [h, Nat.add_zero] at h1
    have hq : 0 < s / 2 ^ (sh + 5) := by
      rcases Nat.eq_zero_or_pos (s / 2 ^ (sh + 5)) with h0 | h0
      · rw [h0, Nat.mul_zero] at h1; omega
      · exact h0
    have hle : 2 ^ (sh + 5) ≤ 2 ^ (sh + 5) * (s / 2 ^ (sh + 5)) := Nat.le_mul_of_pos_right _ hq
    have : s - 1 = 2 ^ (sh + 5) * (s / 2 ^ (sh + 5) - 1) + (2 ^ (sh + 5) - 1) := by
      rw [Nat.mul_sub_one]; omega
    rw [this, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hm]
  have : (2 ^ (sh + 5) - 1) / 2 ^ sh = 31 := by
    apply Nat.div_eq_of_lt_le
    · rw [← hp]; omega
    · rw [← hp]; omega
  omega

theorem wfP_reg_full : ∀ (k s : Nat) (node : Node α), 0 < s → s % 2 ^ (5 * (k + 2)) = 0 →
    wfP k (.reg s) node → wfP k .full node := by
  intro k
  induction k with
  | zero =>
    intro s node hs h hw
    have hc := count_reg_full 5 s hs (by simpa using h)
    obtain ⟨hnl, hch⟩ := hw
    refine ⟨hnl, fun c hc' => ?_⟩
    simp only [IPos.count] at hc'
    obtain ⟨a, b, xs, hx, hl⟩ := hch c (by rw [hc]; exact hc')
    refine ⟨a, b, xs, hx, ?_⟩
    simp only [IPos.towardsL, hc, IPos.size] at hl
    simp only [IPos.towardsL, LPos.count]
    split at hl
    · simpa [LPos.count] using hl
    · simp only [LPos.count, and31] at hl
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
    simp only [IPos.count] at hc'
    obtain ⟨ch, hx, hwc⟩ := hch c (by rw [hc]; exact hc')
    refine ⟨ch, hx, ?_⟩
    simp only [IPos.towardsI, hc, IPos.size] at hwc
    simp only [IPos.towardsI]
    split at hwc
    · exact hwc
    · exact ih s ch hs (Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (Nat.dvd_of_mod_eq_zero h))) hwc

/-- A path (`make_path`) to a full leaf is well formed at a position whose last index sits in its
block's first leaf. -/
theorem wfP_makePath (tok : Nat) : ∀ (k : Nat) (s : Nat) (id tk : Nat) (xs : List α) (n : Nat),
    0 < s → s % 32 = 0 → (s - 1) % 2 ^ (5 * (k + 2)) < 32 → 32 ≤ xs.length →
    wfP k (.reg s) (makePath tok (k + 1) (.leaf id tk xs) n).1 := by
  intro k
  induction k with
  | zero =>
    intro s id tk xs n hs h32 hm hl
    rw [makePath_succ, makePath_zero]
    have hd : iIndex 5 (s - 1) = 0 := iIndex_zero_of_mod 5 _ (Nat.le_refl _) (by simpa using hm)
    have hc : (IPos.reg s).count 5 = 1 := by show iIndex 5 (s - 1) + 1 = 1; rw [hd]
    refine ⟨rfl, fun c hc' => ?_⟩
    rw [hc] at hc'
    have : c = 0 := by omega
    subst this
    refine ⟨id, tk, xs, rfl, ?_⟩
    simp only [IPos.towardsL, hc, bne_self_eq_false, Bool.false_eq_true, ite_false, LPos.count, IPos.size, and31]
    omega
  | succ k ih =>
    intro s id tk xs n hs h32 hm hl
    rw [makePath_succ]
    have e : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    rw [e] at hm
    have hd : iIndex (5 * (k + 2)) (s - 1) = 0 := iIndex_zero_of_mod _ _ (by omega) hm
    have hc : (IPos.reg s).count (5 * (k + 2)) = 1 := by show iIndex (5 * (k + 2)) (s - 1) + 1 = 1; rw [hd]
    refine ⟨rfl, fun c hc' => ?_⟩
    rw [hc] at hc'
    have : c = 0 := by omega
    subst this
    refine ⟨_, rfl, ?_⟩
    simp only [IPos.towardsI, hc, bne_self_eq_false, Bool.false_eq_true, ite_false, IPos.size]
    exact ih s id tk xs (n + 1) hs h32 (mod_lt_of_mod_lt _ _ hm) hl

theorem digit_succ (a size : Nat) (ha : 5 ≤ a) (h32 : size % 32 = 0) (hpos : 0 < size)
    (hm : size % 2 ^ a = 0) (hb : (size - 1) >>> (a + 5) = (size + 31) >>> (a + 5)) :
    iIndex a (size - 1) + 1 = iIndex a (size + 31) := by
  have h1 := shr_add31 a size ha h32
  have hP := pow_ge32 a ha
  have hq : (size - 1) >>> a + 1 = size >>> a := by
    rw [shr_eq, shr_eq]
    have hsplit := Nat.div_add_mod size (2 ^ a)
    rw [hm, Nat.add_zero] at hsplit
    have hqpos : 0 < size / 2 ^ a := by
      rcases Nat.eq_zero_or_pos (size / 2 ^ a) with h0 | h0
      · rw [h0, Nat.mul_zero] at hsplit; omega
      · exact h0
    have : (size - 1) / 2 ^ a = size / 2 ^ a - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]; omega
      · rw [Nat.sub_add_cancel hqpos, Nat.mul_comm]; omega
    omega
  rw [shr_add5, shr_add5, h1] at hb
  rw [iIndex_eq, iIndex_eq, h1]
  omega

/-- `push_tail_visitor` keeps the tree well formed: the node now covers 32 more elements. -/
theorem wfP_pushTail : ∀ (k size : Nat) (node : Node α) (tid ttok : Nat) (txs : List α) (n : Nat),
    0 < size → size % 32 = 0 →
    (size - 1) >>> (5 * (k + 2)) = (size + 31) >>> (5 * (k + 2)) → 32 ≤ txs.length →
    wfP k (.reg size) node →
    wfP k (.reg (size + 32)) (pushTail k size node (.leaf tid ttok txs) n).1 := by
  intro k
  induction k with
  | zero =>
    intro size node tid ttok txs n hpos h32 hb hl hw
    obtain ⟨hnl, hch⟩ := hw
    rw [pushTail_def]
    have e1 : size + 32 - 1 = size + 31 := by omega
    have e0 : 5 * (0 + 1) = 5 := rfl
    simp only [e1, e0]
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
    rw [cs_inner]; unfold childCopy; rw [append_read]
    by_cases hlt : c < iIndex 5 (size + 31)
    · rw [if_pos hlt]
      obtain ⟨a, b, xs, hx, hlen⟩ := hch c (by rw [hco]; omega)
      rw [copyN_getElem? _ _ _ _ hlt (lt_of_getElem? _ _ _ hx)]
      refine ⟨a, b, xs, hx, ?_⟩
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
      rw [if_neg hlt, if_pos hceq]
      refine ⟨tid, ttok, txs, rfl, ?_⟩
      simp only [IPos.towardsL, hcn, hceq, bne_self_eq_false, Bool.false_eq_true, ite_false, LPos.count,
        IPos.size, and31]
      omega
  | succ k ih =>
    intro size node tid ttok txs n hpos h32 hb hl hw
    obtain ⟨hnl, hch⟩ := hw
    rw [pushTail_def]
    have e1 : size + 32 - 1 = size + 31 := by omega
    have e2 : 5 * (k + 1 + 2) = 5 * (k + 2) + 5 := by omega
    have e3 : 5 * (k + 1 + 1) = 5 * (k + 2) := by omega
    simp only [e1, e3]
    rw [e2] at hb
    have hsh : 5 ≤ 5 * (k + 2) := by omega
    have hcn : (IPos.reg (size + 32)).count (5 * (k + 2)) = iIndex (5 * (k + 2)) (size + 31) + 1 := by
      simp only [IPos.count, iIndex, show size + 32 - 1 = size + 31 by omega]
    have hco : (IPos.reg size).count (5 * (k + 2)) = iIndex (5 * (k + 2)) (size - 1) + 1 := rfl
    have hle := digit_le (5 * (k + 2)) (show size - 1 ≤ size + 31 by omega) hb
    refine ⟨rfl, fun c hc => ?_⟩
    rw [hcn] at hc
    rw [cs_inner]; unfold childCopy; rw [append_read]
    by_cases hlt : c < iIndex (5 * (k + 2)) (size + 31)
    · rw [if_pos hlt]
      have hcold : c < (IPos.reg size).count (5 * (k + 2)) := by
        rw [hco]
        by_cases hid : iIndex (5 * (k + 2)) (size - 1) = iIndex (5 * (k + 2)) (size + 31)
        · omega
        · have hm := mod_zero_of_digit_ne _ size hsh h32 hpos hb hid
          have := digit_succ _ size hsh h32 hpos hm hb
          omega
      obtain ⟨ch, hx, hwc⟩ := hch c hcold
      rw [copyN_getElem? _ _ _ _ hlt (lt_of_getElem? _ _ _ hx)]
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
      rw [if_neg hlt, if_pos hceq]
      refine ⟨_, rfl, ?_⟩
      have hnew : (IPos.reg (size + 32)).towardsI (5 * (k + 2)) c = .reg (size + 32) := by
        simp only [IPos.towardsI, hcn, hceq, bne_self_eq_false, Bool.false_eq_true, ite_false, IPos.size]
      rw [hnew]
      by_cases hid : iIndex (5 * (k + 2)) (size - 1) = iIndex (5 * (k + 2)) (size + 31)
      · rw [if_pos (by simpa using hid)]
        obtain ⟨ch, hx, hwc⟩ := hch (iIndex (5 * (k + 2)) (size - 1)) (by rw [hco]; omega)
        rw [child_of_getElem? _ _ _ hx]
        have hold : (IPos.reg size).towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) (size - 1)) = .reg size := by
          simp only [IPos.towardsI, hco, bne_self_eq_false, Bool.false_eq_true, ite_false, IPos.size]
        rw [hold] at hwc
        exact ih size ch tid ttok txs (n + 1) hpos h32 (shr_eq_of_digit _ hid hb) hl hwc
      · rw [if_neg (by simpa using hid)]
        have hm := mod_zero_of_digit_ne _ size hsh h32 hpos hb hid
        have hP := pow_ge32 (5 * (k + 2)) hsh
        apply wfP_makePath 0 k (size + 32) tid ttok txs (n + 1) (by omega) (by omega) _ hl
        rw [show size + 32 - 1 = 31 + size by omega, Nat.add_mod, hm, Nat.add_zero, Nat.mod_mod,
          Nat.mod_eq_of_lt (by omega)]
        omega

/-- **`conj` keeps a vector well formed** (below `2^35` elements). -/
theorem pushBack_wfT [Inhabited α] (t : Tree α) (hw : t.wfT) (hsz : t.size < 2 ^ 35) (x : α) (n : Nat) :
    (t.pushBack x n).1.wfT := by
  have hw0 := hw
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  cases ht : t.tail with
  | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
  | leaf tid ttok txs =>
  rw [ht] at htlen
  simp only [Node.xs] at htlen
  have hL := levelOf_eq t.shift hs5 hs1
  by_cases hsmall : t.size - tailOffset t.size < 32
  · have hto := tailOffset_succ_of_lt _ hsmall
    rw [pushBack_small _ _ _ hsmall]
    refine ⟨hs5, hs1, hs2, rfl, ?_, ?_⟩
    · simp only [smallPush, Node.xs, hto, List.length_append, List.length_singleton]
      rw [leafCopy, copyN_length]; omega
    · intro h; simp only [smallPush, hto] at h ⊢; exact hroot h
  · have hpos : 0 < t.size := by have := tailOffset_le t.size; omega
    have hf := tail_facts t.size hpos
    have hto := tailOffset_succ_of_full t.size hpos (by omega)
    have h32 : t.size % 32 = 0 := by omega
    have hsz' : (t.pushBack x n).1.size = t.size + 1 := pushBack_size1 t x n
    have htail := pushBack_full_tail t x n hsmall
    have hfull32 : 32 ≤ txs.length := by omega
    -- the tail part
    have htailwf : (t.pushBack x n).1.tail.isLeaf = true ∧
        (t.pushBack x n).1.size - tailOffset (t.pushBack x n).1.size ≤ (t.pushBack x n).1.tail.xs.length := by
      rw [htail, hsz', hto]; simp [Node.isLeaf, Node.xs]
    by_cases hg : tailOffset t.size = 32 <<< t.shift
    · obtain ⟨hr, hsh⟩ := pushBack_grow t x n hsmall hg
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
          apply wfP_makePath 0 _ t.size tid ttok txs _ hpos h32 _ hfull32
          rw [← hL, hsz2]
          generalize 2 ^ (t.shift + 5) = P at hP ⊢
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
    · by_cases h0 : tailOffset t.size = 0
      · obtain ⟨hr, hsh⟩ := pushBack_first t x n hsmall hg h0
        refine ⟨by rw [hsh]; exact hs5, by rw [hsh]; exact hs1, by rw [hsh]; exact hs2, htailwf.1, htailwf.2, ?_⟩
        intro _
        rw [hsz', hto, hsh, hr]
        have hP := pow_ge32 (t.shift + 5) (by omega)
        refine ⟨by omega, ?_⟩
        rw [wfP_sub_reg _ _ _ (by rw [← hL]; omega) (by omega)]
        have e6 : t.shift / 5 = levelOf t.shift + 1 := by unfold levelOf; omega
        rw [e6, ht]
        apply wfP_makePath 0 _ t.size tid ttok txs _ hpos h32 _ hfull32
        have hP' := pow_ge32 (5 * (levelOf t.shift + 2)) (by omega)
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      · obtain ⟨hr, hsh⟩ := pushBack_mid t x n hsmall hg h0
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
        exact wfP_pushTail _ _ _ tid ttok txs _ (by omega) hf.2.2
          (by rw [← hL, shr_zero_of_lt _ (by omega), shr_zero_of_lt _ (by omega)]) hfull32 hwr

/-- **`pop` after `conj`**: for every well-formed vector below `2^35` elements,
`(nth (pop (conj v x)) j)` is `(nth v j)` for every `j < count`, and the count is `count v`. -/
theorem get_pop_conj [Inhabited α] (t : Tree α) (hw : t.wfT) (hsz : t.size < 2 ^ 35) (x : α) (n m j : Nat)
    (hj : j < t.size) :
    ((t.pushBack x n).1.take t.size m).1.get j = t.get j := by
  rw [get_take _ (pushBack_wfT t hw hsz x n) _ _ _ (by rw [pushBack_size1]; omega) hj,
    get_pushBack t hw hsz x n j (by omega), if_pos hj]

/-! ## Transient `assoc!`: `assoc_mut` through `get_mut_visitor`, in place or on copies -/

theorem write_read {β : Type} (d : β) (ys : List β) (o c : Nat) (x : β) (h : o < ys.length) :
    (setAt d ys o x)[c]? = if o = c then some x else ys[c]? := by
  rw [setAt_eq_set _ _ _ _ h]
  by_cases hoc : o = c
  · subst hoc; simp [List.getElem?_set, h]
  · simp only [List.getElem?_set, hoc, if_false]

theorem getMutLeaf_read [Inhabited α] (lp : LPos) (e : Nat) (lid ltok : Nat) (lxs : List α) (i j : Nat) (x : α)
    (n : Nat) (hc : lp.count ≤ lxs.length) (hi : lIndex i < lp.count) (hj : lIndex j < lp.count) :
    (getMutLeaf lp e (.leaf lid ltok lxs) i x n).1.isLeaf = true ∧
    (getMutLeaf lp e (.leaf lid ltok lxs) i x n).1.xs[lIndex j]? =
      if lIndex i = lIndex j then some x else lxs[lIndex j]? := by
  unfold getMutLeaf
  split
  · refine ⟨rfl, ?_⟩
    simp only [Node.writeLeaf, Node.xs]
    exact write_read _ _ _ _ _ (by omega)
  · refine ⟨rfl, ?_⟩
    simp only [Node.xs]
    exact leaf_update_read (.leaf lid ltok lxs) _ _ _ x (by simpa [Node.xs] using hc) hi hj

theorem leafOpt_leaf (c : Node α) (hc : c.isLeaf = true) (j : Nat) :
    ((leafOpt (some c)).bind fun l => l.xs[lIndex j]?) = c.xs[lIndex j]? := by
  cases c with
  | leaf => rfl
  | inner => simp [Node.isLeaf] at hc

/-- `nth` after `assoc!` through an inner node (get_mut_visitor): mutated in place when the node is
owned by the transient, else copied (`copy_inner_e`). -/
theorem readAt_getMutInner [Inhabited α] (k : Nat) : ∀ (p : IPos) (e : Nat) (node : Node α) (i : Nat) (x : α) (n j : Nat),
    wfP k p node → validI k p i → validI k p j →
    readAt k (getMutInner k p e node i x n).1 j =
      if samePathB k i j && lIndex i == lIndex j then some x else readAt k node j := by
  induction k with
  | zero =>
    intro p e node i x n j hw hi hj
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    cases node with
    | leaf => simp [Node.isLeaf] at hnl
    | inner id tok cs =>
    obtain ⟨lid, ltok, lxs, hcs, hlen⟩ := hch _ hi1
    obtain ⟨lid', ltok', lxs', hcs', hlen'⟩ := hch _ hj1
    have hlt : iIndex 5 j < cs.length := lt_of_getElem? _ _ _ hcs'
    have hlti : iIndex 5 i < cs.length := lt_of_getElem? _ _ _ hcs
    have hcl : (childCopy (Node.inner id tok cs) (p.count 5)).length = p.count 5 := copyN_length _ _ _
    -- the slot list written into: the node's own (`cs`) or its copy; both read like `cs` below the count
    have core : ∀ (ys : List (Node α)) (a b n' : Nat), iIndex 5 i < ys.length →
        ys[iIndex 5 j]? = cs[iIndex 5 j]? → ys.getD (iIndex 5 i) Node.dummy = .leaf lid ltok lxs →
        readAt 0 (Node.inner a b (setAt Node.dummy ys (iIndex 5 i)
          (getMutLeaf (p.towardsL 5 (iIndex 5 i)) e (ys.getD (iIndex 5 i) Node.dummy) i x n').1)) j =
        if samePathB 0 i j && lIndex i == lIndex j then some x else readAt 0 (Node.inner id tok cs) j := by
      intro ys a b n' hy hyj hyi
      rw [readAt_zero, write_read _ _ _ _ _ hy, hyi]
      by_cases hij : iIndex 5 i = iIndex 5 j
      · rw [if_pos hij]
        have hj2' : lIndex j < (p.towardsL 5 (iIndex 5 i)).count := by rw [hij]; exact hj2
        obtain ⟨hleaf, hread⟩ := getMutLeaf_read (p.towardsL 5 (iIndex 5 i)) e lid ltok lxs i j x n' hlen hi2 hj2'
        rw [leafOpt_leaf _ hleaf, hread]
        have hr : readAt 0 (Node.inner id tok cs) j = lxs[lIndex j]? := by
          rw [readAt_zero]; rw [← hij]; simp only [Node.cs] at hcs; rw [hcs]; rfl
        rw [hr]
        simp [samePathB, hij]
      · rw [if_neg hij, hyj]
        simp [samePathB, hij, readAt_zero, Node.cs]
    by_cases hm : (Node.inner id tok cs).canMutate e = true
    · have hR : (getMutInner 0 p e (.inner id tok cs) i x n).1 =
          .inner id tok (setAt Node.dummy cs (iIndex 5 i)
            (getMutLeaf (p.towardsL 5 (iIndex 5 i)) e (cs.getD (iIndex 5 i) Node.dummy) i x n).1) := by
        unfold getMutInner; dsimp only; rw [if_pos hm]; rfl
      rw [hR]
      exact core cs id tok n hlti rfl (by simp only [Node.cs] at hcs; simp [List.getD, hcs])
    · have hR : (getMutInner 0 p e (.inner id tok cs) i x n).1 =
          .inner n e (setAt Node.dummy (childCopy (.inner id tok cs) (p.count 5)) (iIndex 5 i)
            (getMutLeaf (p.towardsL 5 (iIndex 5 i)) e
              ((childCopy (.inner id tok cs) (p.count 5)).getD (iIndex 5 i) Node.dummy) i x (n + 1)).1) := by
        unfold getMutInner; dsimp only; rw [if_neg hm]; rfl
      rw [hR]
      have hy1 : (childCopy (Node.inner id tok cs) (p.count 5))[iIndex 5 j]? = cs[iIndex 5 j]? :=
        childCopy_getElem? _ _ _ hj1 hlt
      have hy2 : (childCopy (Node.inner id tok cs) (p.count 5))[iIndex 5 i]? = cs[iIndex 5 i]? :=
        childCopy_getElem? _ _ _ hi1 hlti
      exact core _ n e (n + 1) (by omega) hy1
        (by simp only [Node.cs] at hcs; simp [List.getD, hy2, hcs])
  | succ k ih =>
    intro p e node i x n j hw hi hj
    obtain ⟨hnl, hch⟩ := hw
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    cases node with
    | leaf => simp [Node.isLeaf] at hnl
    | inner id tok cs =>
    obtain ⟨ch, hcs, hwc⟩ := hch _ hi1
    obtain ⟨ch', hcs', hwc'⟩ := hch _ hj1
    have hlt : iIndex (5 * (k + 2)) j < cs.length := lt_of_getElem? _ _ _ hcs'
    have hlti : iIndex (5 * (k + 2)) i < cs.length := lt_of_getElem? _ _ _ hcs
    have hcl : (childCopy (Node.inner id tok cs) (p.count (5 * (k + 2)))).length = p.count (5 * (k + 2)) :=
      copyN_length _ _ _
    have core : ∀ (ys : List (Node α)) (a b n' : Nat), iIndex (5 * (k + 2)) i < ys.length →
        ys[iIndex (5 * (k + 2)) j]? = cs[iIndex (5 * (k + 2)) j]? → ys.getD (iIndex (5 * (k + 2)) i) Node.dummy = ch →
        readAt (k + 1) (Node.inner a b (setAt Node.dummy ys (iIndex (5 * (k + 2)) i)
          (getMutInner k (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) i)) e
            (ys.getD (iIndex (5 * (k + 2)) i) Node.dummy) i x n').1)) j =
        if samePathB (k + 1) i j && lIndex i == lIndex j then some x else readAt (k + 1) (Node.inner id tok cs) j := by
      intro ys a b n' hy hyj hyi
      rw [readAt_succ, write_read _ _ _ _ _ hy, hyi]
      by_cases hij : iIndex (5 * (k + 2)) i = iIndex (5 * (k + 2)) j
      · rw [if_pos hij]
        simp only [Option.bind_some]
        have hj2' : validI k (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) i)) j := by rw [hij]; exact hj2
        rw [ih _ e ch i x n' j hwc hi2 hj2']
        have hr : readAt (k + 1) (Node.inner id tok cs) j = readAt k ch j := by
          rw [readAt_succ, ← hij]; simp only [Node.cs] at hcs; rw [hcs]; rfl
        rw [hr]
        simp [samePathB, hij]
      · rw [if_neg hij, hyj]
        simp [samePathB, hij, readAt_succ, Node.cs]
    by_cases hm : (Node.inner id tok cs).canMutate e = true
    · have hR : (getMutInner (k + 1) p e (.inner id tok cs) i x n).1 =
          .inner id tok (setAt Node.dummy cs (iIndex (5 * (k + 2)) i)
            (getMutInner k (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) i)) e
              (cs.getD (iIndex (5 * (k + 2)) i) Node.dummy) i x n).1) := by
        rw [getMutInner.eq_2]; dsimp only; rw [if_pos hm]; rfl
      rw [hR]
      exact core cs id tok n hlti rfl (by simp only [Node.cs] at hcs; simp [List.getD, hcs])
    · have hR : (getMutInner (k + 1) p e (.inner id tok cs) i x n).1 =
          .inner n e (setAt Node.dummy (childCopy (.inner id tok cs) (p.count (5 * (k + 2)))) (iIndex (5 * (k + 2)) i)
            (getMutInner k (p.towardsI (5 * (k + 2)) (iIndex (5 * (k + 2)) i)) e
              ((childCopy (.inner id tok cs) (p.count (5 * (k + 2)))).getD (iIndex (5 * (k + 2)) i) Node.dummy)
              i x (n + 1)).1) := by
        rw [getMutInner.eq_2]; dsimp only; rw [if_neg hm]; rfl
      rw [hR]
      have hy1 : (childCopy (Node.inner id tok cs) (p.count (5 * (k + 2))))[iIndex (5 * (k + 2)) j]? =
          cs[iIndex (5 * (k + 2)) j]? := childCopy_getElem? _ _ _ hj1 hlt
      have hy2 : (childCopy (Node.inner id tok cs) (p.count (5 * (k + 2))))[iIndex (5 * (k + 2)) i]? =
          cs[iIndex (5 * (k + 2)) i]? := childCopy_getElem? _ _ _ hi1 hlti
      exact core _ n e (n + 1) (by omega) hy1
        (by simp only [Node.cs] at hcs; simp [List.getD, hy2, hcs])

/-- **`nth` after `assoc!`**: for every well-formed tree, every owner token and i, j < count. -/
theorem get_assocMut [Inhabited α] (t : Tree α) (hw : t.wfT) (e i j : Nat) (x : α) (n : Nat)
    (hi : i < t.size) (hj : j < t.size) :
    (t.assocMut e i x n).1.get j = if i = j then some x else t.get j := by
  obtain ⟨hs5, hs1, hs2, htl, htlen, hroot⟩ := hw
  have hf := tail_facts t.size (by omega)
  cases ht : t.tail with
  | inner => rw [ht] at htl; simp [Node.isLeaf] at htl
  | leaf tid ttok txs =>
  rw [ht] at htlen
  simp only [Node.xs] at htlen
  by_cases hit : tailOffset t.size ≤ i
  · -- the tail, made mutable (`ensure_mutable_tail`) and written in place
    have hA : ∃ a b ys, (t.assocMut e i x n).1 = { t with tail := .leaf a b (setAt default ys (lIndex i) x) } ∧
        ys.length ≥ t.size - tailOffset t.size ∧ ∀ c, c < t.size - tailOffset t.size → ys[c]? = txs[c]? := by
      unfold Tree.assocMut Tree.ensureMutableTail
      rw [ht]
      dsimp only
      rw [if_pos hit]
      split
      · exact ⟨tid, ttok, txs, by simp [Node.writeLeaf, Node.id, Node.tok, Node.xs, ht], by omega, fun _ _ => rfl⟩
      · refine ⟨n, e, leafCopy (Node.leaf tid ttok txs) (t.size - tailOffset t.size), rfl, ?_, ?_⟩
        · rw [leafCopy, copyN_length]; omega
        · intro c hc; exact leafCopy_getElem? _ _ _ hc (by simp [Node.xs]; omega)
    obtain ⟨a, b, ys, hR, hlen, hys⟩ := hA
    rw [hR]
    by_cases hjt : tailOffset t.size ≤ j
    · rw [get_tail_leaf ({ t with tail := .leaf a b (setAt default ys (lIndex i) x) } : Tree α) j a b _ rfl hjt,
        get_tail_leaf t j tid ttok txs ht hjt]
      rw [lIndex_tail t.size i hit hi, lIndex_tail t.size j hjt hj, write_read _ _ _ _ _ (by omega)]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg (by omega), if_neg hij, hys _ (by omega)]
    · have hjt' : j < tailOffset t.size := by omega
      have e1 := get_of_root ({ t with tail := .leaf a b (setAt default ys (lIndex i) x) } : Tree α) j hjt' hs2
      rw [e1, get_of_root t j hjt' hs2, if_neg (by omega)]
  · have hit' : i < tailOffset t.size := by omega
    obtain ⟨hcap, hwr⟩ := hroot (by omega)
    have hcap' : tailOffset t.size ≤ 2 ^ (5 * (levelOf t.shift + 2)) := by
      rw [← levelOf_eq _ hs5 hs1]; exact hcap
    have hR : (t.assocMut e i x n).1 =
        { t with root := (getMutInner (levelOf t.shift) (.sub (tailOffset t.size)) e t.root i x n).1 } := by
      unfold Tree.assocMut; dsimp only; rw [if_neg (by omega)]
    rw [hR]
    by_cases hjt : tailOffset t.size ≤ j
    · rw [get_tail_leaf ({ t with root := (getMutInner (levelOf t.shift) (.sub (tailOffset t.size)) e t.root i x n).1 } : Tree α)
          j tid ttok txs ht hjt, get_tail_leaf t j tid ttok txs ht hjt, if_neg (by omega)]
    · have hjt' : j < tailOffset t.size := by omega
      rw [get_of_root ({ t with root := (getMutInner (levelOf t.shift) (.sub (tailOffset t.size)) e t.root i x n).1 } : Tree α)
          j hjt' hs2, get_of_root t j hjt' hs2]
      rw [readAt_getMutInner _ _ _ _ _ _ _ _ hwr (validI_sub _ _ _ hit' hcap') (validI_sub _ _ _ hjt' hcap')]
      by_cases hij : i = j
      · subst hij; simp [samePath_refl]
      · have : (samePathB (levelOf t.shift) i j && lIndex i == lIndex j) = false := by
          cases h : samePathB (levelOf t.shift) i j
          · rfl
          · simp only [Bool.true_and, beq_eq_false_iff_ne, ne_eq]
            intro hl
            exact hij (eq_of_samePath _ i j (by omega) (by omega) h hl)
        rw [this, if_neg hij]; rfl

/-- The empty vector (`rbtree()`, shift BL = 5, the static empty root and tail) is well formed;
with `pushBack_wfT`, so is every vector `conj`ed from it (below `2^35` elements). -/
theorem empty_wfT : (Tree.empty : Tree α).wfT := by
  refine ⟨by simp [Tree.empty], by simp [Tree.empty], by simp [Tree.empty], rfl, by simp [Tree.empty, tailOffset], fun h => ?_⟩
  simp [Tree.empty, tailOffset] at h

end Jank.R3.Immer.Rbts

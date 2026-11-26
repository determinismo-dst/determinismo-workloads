import Jank.R9.Seq.Sort

/-!
# Round 9, area Seq: jank's std::stable_sort and Clojure's TimSort agree on every total preorder

The replicas of Sort.lean, for elements with an integer key `κ` compared by `<` (a total preorder:
`compare`, `<`, `>` and any comparator returning the sign of a key difference) and a tag `τ` (the
position). `R x y` is "x before y in the stable order": a smaller key, or the same key and a tag no
larger. For an input whose tags strictly increase:
- each algorithm returns a permutation of its input that is sorted by `R` (sorted by key, equal keys in
  input order): it is a stable sort;
- two such lists are equal (`eq_of_perm_of_pairwise`, `R` being antisymmetric on distinct tags).
-/

namespace Jank.R9.Seq.SortProof

open Jank.R9.Seq.Sort

section Unique

/-- Two permutations of each other, both sorted by a relation antisymmetric on their elements, are
equal. -/
theorem eq_of_perm_of_pairwise {α : Type} {r : α → α → Prop} :
    ∀ {l1 l2 : List α}, l1.Perm l2 → l1.Pairwise r → l2.Pairwise r →
      (∀ x ∈ l1, ∀ y ∈ l1, r x y → r y x → x = y) → l1 = l2
  | [], l2, hp, _, _, _ => (List.Perm.nil_eq hp)
  | a :: t, l2, hp, h1, h2, anti => by
    cases l2 with
    | nil => exact absurd hp.length_eq (by simp)
    | cons b t2 =>
      rw [List.pairwise_cons] at h1 h2
      by_cases hab : a = b
      · subst hab
        have ht := hp.cons_inv
        rw [eq_of_perm_of_pairwise ht h1.2 h2.2
          (fun x hx y hy => anti x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))]
      · exfalso
        have ha : a ∈ b :: t2 := hp.mem_iff.mp (List.mem_cons_self)
        have hb : b ∈ a :: t := hp.mem_iff.mpr (List.mem_cons_self)
        rcases List.mem_cons.mp ha with h | h
        · exact hab h
        rcases List.mem_cons.mp hb with h' | h'
        · exact hab h'.symm
        exact hab (anti a List.mem_cons_self b (List.mem_cons_of_mem _ h') (h1.1 b h') (h2.1 a h))

end Unique

section Order

variable {α : Type} (κ : α → Int) (τ : α → Nat)

/-- The comparison both sorts make: a smaller key. -/
def lessK (x y : α) : Bool := decide (κ x < κ y)

/-- The stable order: a smaller key, or the same key and a tag no larger. -/
def R (x y : α) : Prop := κ x < κ y ∨ (κ x = κ y ∧ τ x ≤ τ y)

/-- Every element of `l` has a smaller tag than every element of `r`. -/
def Before (l r : List α) : Prop := ∀ a ∈ l, ∀ b ∈ r, τ a < τ b

theorem R_trans {x y z : α} (h1 : R κ τ x y) (h2 : R κ τ y z) : R κ τ x z := by
  unfold R at *; omega

end Order

section Insertion

variable {α : Type} (κ : α → Int) (τ : α → Nat)

theorem linIns_perm (less : α → α → Bool) (v : α) : ∀ l : List α, (linIns less v l).Perm (v :: l)
  | [] => by simp [linIns]
  | y :: ys => by
    unfold linIns
    split
    · exact ((linIns_perm less v ys).cons y).trans (List.Perm.swap v y ys)
    · exact List.Perm.refl _

theorem insSortRev_perm (less : α → α → Bool) : ∀ (acc xs : List α), (insSortRev less acc xs).Perm (acc ++ xs)
  | acc, [] => by simp [insSortRev]
  | acc, x :: xs => by
    unfold insSortRev
    split
    · rename_i h
      have : acc = [] := by simpa using h
      subst this
      simpa using insSortRev_perm less [x] xs
    · rename_i fst h
      split
      · exact (insSortRev_perm less (acc ++ [x]) xs).trans (by simp)
      · refine (insSortRev_perm less (linIns less x acc) xs).trans ?_
        have := (linIns_perm less x acc).append_right xs
        refine this.trans ?_
        simp [List.perm_middle.symm]

theorem insertionSort_perm (less : α → α → Bool) (xs : List α) : (insertionSort less xs).Perm xs := by
  unfold insertionSort
  exact (List.reverse_perm _).trans (by simpa using insSortRev_perm less [] xs)

/-- The descending order: `x` after `y` in the stable order. -/
def RD (x y : α) : Prop := R κ τ y x

theorem linIns_sorted (v : α) : ∀ l : List α, l.Pairwise (RD κ τ) → (∀ y ∈ l, τ y < τ v) →
    (linIns (lessK κ) v l).Pairwise (RD κ τ)
  | [], _, _ => by simp [linIns]
  | y :: ys, hs, ht => by
    rw [List.pairwise_cons] at hs
    unfold linIns
    split
    · rename_i hlt
      simp only [lessK, decide_eq_true_eq] at hlt
      rw [List.pairwise_cons]
      refine ⟨?_, linIns_sorted v ys hs.2 (fun z hz => ht z (List.mem_cons_of_mem _ hz))⟩
      intro z hz
      have hz' := (linIns_perm (lessK κ) v ys).mem_iff.mp hz
      rcases List.mem_cons.mp hz' with h | h
      · subst h; unfold RD R; omega
      · exact hs.1 z h
    · rename_i hlt
      simp only [lessK, decide_eq_true_eq] at hlt
      have hy := ht y List.mem_cons_self
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr hs⟩
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst h; unfold RD R; omega
      · have h1 := hs.1 z h
        unfold RD at h1 ⊢
        have h2 : R κ τ y v := by unfold R; omega
        exact R_trans κ τ h1 h2

theorem last_least {acc : List α} {fst : α} (h : acc.getLast? = some fst)
    (hs : acc.Pairwise (RD κ τ)) : ∀ a ∈ acc, R κ τ fst a := by
  intro a ha
  obtain ⟨init, rfl⟩ : ∃ init, acc = init ++ [fst] := by
    rw [List.getLast?_eq_some_iff] at h
    exact h
  rw [List.pairwise_append] at hs
  rcases List.mem_append.mp ha with h1 | h1
  · exact hs.2.2 a h1 fst List.mem_cons_self
  · simp at h1; subst h1; unfold R; omega

theorem insSortRev_sorted : ∀ (acc xs : List α), acc.Pairwise (RD κ τ) →
    xs.Pairwise (fun a b => τ a < τ b) → (∀ a ∈ acc, ∀ x ∈ xs, τ a < τ x) →
    (insSortRev (lessK κ) acc xs).Pairwise (RD κ τ)
  | acc, [], hs, _, _ => by simpa [insSortRev] using hs
  | acc, x :: xs, hs, hx, ht => by
    rw [List.pairwise_cons] at hx
    unfold insSortRev
    split
    · rename_i h
      have : acc = [] := by simpa using h
      subst this
      exact insSortRev_sorted [x] xs (by simp) hx.2 (by simpa using hx.1)
    · rename_i fst h
      split
      · rename_i hlt
        simp only [lessK, decide_eq_true_eq] at hlt
        apply insSortRev_sorted
        · rw [List.pairwise_append]
          refine ⟨hs, by simp, ?_⟩
          intro a ha b hb
          simp at hb; subst hb
          have := last_least κ τ h hs a ha
          unfold RD R at *; omega
        · exact hx.2
        · intro a ha y hy
          rcases List.mem_append.mp ha with h1 | h1
          · exact ht a h1 y (List.mem_cons_of_mem _ hy)
          · simp at h1; subst h1; exact hx.1 y hy
      · apply insSortRev_sorted
        · exact linIns_sorted κ τ x acc hs (fun y hy => ht y hy x List.mem_cons_self)
        · exact hx.2
        · intro a ha y hy
          have ha' := (linIns_perm (lessK κ) x acc).mem_iff.mp ha
          rcases List.mem_cons.mp ha' with h1 | h1
          · subst h1; exact hx.1 y hy
          · exact ht a h1 y (List.mem_cons_of_mem _ hy)

/-- ★ jank's `__insertion_sort` is a stable sort: sorted by key, equal keys in input order. -/
theorem insertionSort_sorted (xs : List α) (hx : xs.Pairwise (fun a b => τ a < τ b)) :
    (insertionSort (lessK κ) xs).Pairwise (R κ τ) := by
  unfold insertionSort
  rw [List.pairwise_reverse]
  exact insSortRev_sorted κ τ [] xs (by simp) hx (by simp)

end Insertion

section Merge

variable {α : Type} (κ : α → Int) (τ : α → Nat)

theorem mergeFuel_perm (less : α → α → Bool) : ∀ (f : Nat) (l r : List α), (mergeFuel less f l r).Perm (l ++ r)
  | f, [], r => by cases f <;> simp [mergeFuel]
  | f, x :: xs, [] => by cases f <;> simp [mergeFuel]
  | 0, x :: xs, y :: ys => by simp [mergeFuel]
  | f + 1, x :: xs, y :: ys => by
    simp only [mergeFuel]
    split
    · have := (mergeFuel_perm less f (x :: xs) ys).cons y
      exact this.trans (by
        rw [List.cons_append]
        exact (List.Perm.swap x y _).trans (List.perm_middle.symm.cons x))
    · exact (mergeFuel_perm less f xs (y :: ys)).cons x

theorem mergeF_perm (less : α → α → Bool) (l r : List α) : (mergeF less l r).Perm (l ++ r) :=
  mergeFuel_perm less _ l r

/-- The forward merge (`__move_merge`) of two stably sorted runs, the left one's tags first, is
stably sorted. -/
theorem mergeFuel_sorted : ∀ (f : Nat) (l r : List α), l.length + r.length ≤ f →
    l.Pairwise (R κ τ) → r.Pairwise (R κ τ) → Before τ l r →
    (mergeFuel (lessK κ) f l r).Pairwise (R κ τ)
  | f, [], r, _, _, hr, _ => by cases f <;> simpa [mergeFuel] using hr
  | f, x :: xs, [], _, hl, _, _ => by cases f <;> simpa [mergeFuel] using hl
  | 0, x :: xs, y :: ys, hf, _, _, _ => by simp at hf
  | f + 1, x :: xs, y :: ys, hf, hl, hr, hb => by
    simp only [List.length_cons] at hf
    have hl' := List.pairwise_cons.mp hl
    have hr' := List.pairwise_cons.mp hr
    simp only [mergeFuel]
    split
    · rename_i hlt
      simp only [lessK, decide_eq_true_eq] at hlt
      rw [List.pairwise_cons]
      refine ⟨?_, mergeFuel_sorted f (x :: xs) ys (by simp; omega) hl hr'.2
        (fun a ha b hb' => hb a ha b (List.mem_cons_of_mem _ hb'))⟩
      intro z hz
      have hz' := (mergeFuel_perm (lessK κ) f (x :: xs) ys).mem_iff.mp hz
      rcases List.mem_append.mp hz' with h | h
      · rcases List.mem_cons.mp h with h | h
        · subst h; unfold R; omega
        · have := hl'.1 z h
          unfold R at this ⊢; omega
      · exact hr'.1 z h
    · rename_i hlt
      simp only [lessK, decide_eq_true_eq] at hlt
      rw [List.pairwise_cons]
      refine ⟨?_, mergeFuel_sorted f xs (y :: ys) (by simp; omega) hl'.2 hr
        (fun a ha b hb' => hb a (List.mem_cons_of_mem _ ha) b hb')⟩
      intro z hz
      have hz' := (mergeFuel_perm (lessK κ) f xs (y :: ys)).mem_iff.mp hz
      have hxy : R κ τ x y := by
        have := hb x List.mem_cons_self y List.mem_cons_self
        unfold R; omega
      rcases List.mem_append.mp hz' with h | h
      · exact hl'.1 z h
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact hxy
        · exact R_trans κ τ hxy (hr'.1 z h)

theorem mergeF_sorted (l r : List α) (hl : l.Pairwise (R κ τ)) (hr : r.Pairwise (R κ τ))
    (hb : Before τ l r) : (mergeF (lessK κ) l r).Pairwise (R κ τ) :=
  mergeFuel_sorted κ τ _ l r (Nat.le_refl _) hl hr hb

theorem mergeBRev_perm (less : α → α → Bool) : ∀ (f : Nat) (l r : List α), (mergeBRev less f l r).Perm (l ++ r)
  | f, [], r => by cases f <;> simp [mergeBRev]
  | f, x :: xs, [] => by cases f <;> simp [mergeBRev]
  | 0, x :: xs, y :: ys => by simp [mergeBRev]
  | f + 1, x :: xs, y :: ys => by
    simp only [mergeBRev]
    split
    · exact (mergeBRev_perm less f xs (y :: ys)).cons x
    · have := (mergeBRev_perm less f (x :: xs) ys).cons y
      exact this.trans (by
        rw [List.cons_append]
        exact (List.Perm.swap x y _).trans (List.perm_middle.symm.cons x))

theorem mergeB_perm (less : α → α → Bool) (l r : List α) : (mergeB less l r).Perm (l ++ r) := by
  unfold mergeB
  refine (List.reverse_perm _).trans ?_
  refine (mergeBRev_perm less _ _ _).trans ?_
  exact ((List.reverse_perm l).append (List.reverse_perm r))

/-- The backward merge (`__move_merge_adaptive_backward`), on both runs reversed: the result,
reversed, is stably sorted. -/
theorem mergeBRev_sorted : ∀ (f : Nat) (l r : List α), l.length + r.length ≤ f →
    l.Pairwise (RD κ τ) → r.Pairwise (RD κ τ) → Before τ l r →
    (mergeBRev (lessK κ) f l r).Pairwise (RD κ τ)
  | f, [], r, _, _, hr, _ => by cases f <;> simpa [mergeBRev] using hr
  | f, x :: xs, [], _, hl, _, _ => by cases f <;> simpa [mergeBRev] using hl
  | 0, x :: xs, y :: ys, hf, _, _, _ => by simp at hf
  | f + 1, x :: xs, y :: ys, hf, hl, hr, hb => by
    simp only [List.length_cons] at hf
    have hl' := List.pairwise_cons.mp hl
    have hr' := List.pairwise_cons.mp hr
    simp only [mergeBRev]
    split
    · rename_i hlt
      simp only [lessK, decide_eq_true_eq] at hlt
      rw [List.pairwise_cons]
      refine ⟨?_, mergeBRev_sorted f xs (y :: ys) (by simp; omega) hl'.2 hr
        (fun a ha b hb' => hb a (List.mem_cons_of_mem _ ha) b hb')⟩
      intro z hz
      have hz' := (mergeBRev_perm (lessK κ) f xs (y :: ys)).mem_iff.mp hz
      have hyx : R κ τ y x := by unfold R; omega
      rcases List.mem_append.mp hz' with h | h
      · exact hl'.1 z h
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact hyx
        · unfold RD; exact R_trans κ τ (hr'.1 z h) hyx
    · rename_i hlt
      simp only [lessK, decide_eq_true_eq] at hlt
      rw [List.pairwise_cons]
      refine ⟨?_, mergeBRev_sorted f (x :: xs) ys (by simp; omega) hl hr'.2
        (fun a ha b hb' => hb a ha b (List.mem_cons_of_mem _ hb'))⟩
      intro z hz
      have hz' := (mergeBRev_perm (lessK κ) f (x :: xs) ys).mem_iff.mp hz
      have hxy : R κ τ x y := by
        have := hb x List.mem_cons_self y List.mem_cons_self
        unfold R; omega
      rcases List.mem_append.mp hz' with h | h
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact hxy
        · unfold RD; exact R_trans κ τ (hl'.1 z h) hxy
      · exact hr'.1 z h

theorem pairwise_RD_reverse (l : List α) : l.reverse.Pairwise (RD κ τ) ↔ l.Pairwise (R κ τ) := by
  rw [List.pairwise_reverse]; rfl

theorem mergeB_sorted (l r : List α) (hl : l.Pairwise (R κ τ)) (hr : r.Pairwise (R κ τ))
    (hb : Before τ l r) : (mergeB (lessK κ) l r).Pairwise (R κ τ) := by
  unfold mergeB
  rw [← pairwise_RD_reverse κ τ, List.reverse_reverse]
  apply mergeBRev_sorted κ τ _ _ _ (by simp)
  · exact (pairwise_RD_reverse κ τ l).mpr hl
  · exact (pairwise_RD_reverse κ τ r).mpr hr
  · intro a ha b hb'
    exact hb a (List.mem_reverse.mp ha) b (List.mem_reverse.mp hb')

end Merge

section Stable

variable {α : Type} (κ : α → Int) (τ : α → Nat)

theorem chunks_flatten (k : Nat) (hk : 0 < k) : ∀ (fuel : Nat) (xs : List α), xs.length < fuel →
    (chunks k xs fuel).flatten = xs
  | 0, xs, h => by simp at h
  | f + 1, xs, h => by
    unfold chunks
    split
    · rename_i he; simp at he; simp [he]
    · rename_i he
      simp only [List.flatten_cons]
      rw [chunks_flatten k hk f (xs.drop k) (by simp at he ⊢; cases xs <;> simp_all; omega)]
      exact List.take_append_drop k xs

theorem chunks_length (k : Nat) (hk : 0 < k) : ∀ (fuel : Nat) (xs : List α),
    (chunks k xs fuel).length ≤ xs.length
  | 0, xs => by simp [chunks]
  | f + 1, xs => by
    unfold chunks
    split
    · simp
    · rename_i he
      simp only [List.length_cons]
      have := chunks_length k hk f (xs.drop k)
      simp at this he
      cases xs with
      | nil => simp at he
      | cons x xs' => simp at this ⊢; omega

/-- A list of runs ready to merge: each stably sorted, every run's tags below every later run's. -/
def Runs (rs : List (List α)) : Prop := (∀ r ∈ rs, r.Pairwise (R κ τ)) ∧ rs.Pairwise (Before τ)

theorem mem_mergePass_flatten (less : α → α → Bool) : ∀ (rs : List (List α)) (w : α),
    w ∈ (mergePass less rs).flatten → ∃ c ∈ rs, w ∈ c
  | a :: b :: rest, w, h => by
    simp only [mergePass, List.flatten_cons, List.mem_append] at h
    rcases h with h | h
    · have := (mergeF_perm less a b).mem_iff.mp h
      rcases List.mem_append.mp this with h' | h'
      · exact ⟨a, List.mem_cons_self, h'⟩
      · exact ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, h'⟩
    · obtain ⟨c, hc, hw⟩ := mem_mergePass_flatten less rest w h
      exact ⟨c, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc), hw⟩
  | [a], w, h => by simp [mergePass] at h; exact ⟨a, List.mem_singleton_self a, h⟩
  | [], w, h => by simp [mergePass] at h

theorem mem_of_mem_mergePass (less : α → α → Bool) : ∀ (rs : List (List α)) (m : List α) (w : α),
    m ∈ mergePass less rs → w ∈ m → ∃ c ∈ rs, w ∈ c := by
  intro rs m w hm hw
  exact mem_mergePass_flatten less rs w (List.mem_flatten.mpr ⟨m, hm, hw⟩)

theorem mergePass_runs : ∀ (rs : List (List α)), Runs κ τ rs → Runs κ τ (mergePass (lessK κ) rs)
  | a :: b :: rest, ⟨hs, hb⟩ => by
    simp only [mergePass]
    have hb' := List.pairwise_cons.mp hb
    have hb'' := List.pairwise_cons.mp hb'.2
    have ih := mergePass_runs rest ⟨fun r hr => hs r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), hb''.2⟩
    refine ⟨?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with h | h
      · subst h
        exact mergeF_sorted κ τ a b (hs a List.mem_cons_self) (hs b (List.mem_cons_of_mem _ List.mem_cons_self))
          (hb'.1 b List.mem_cons_self)
      · exact ih.1 r h
    · rw [List.pairwise_cons]
      refine ⟨?_, ih.2⟩
      intro m hm z hz w hw
      obtain ⟨c, hc, hwc⟩ := mem_of_mem_mergePass (lessK κ) rest m w hm hw
      have hz' := (mergeF_perm (lessK κ) a b).mem_iff.mp hz
      rcases List.mem_append.mp hz' with h | h
      · exact hb'.1 c (List.mem_cons_of_mem _ hc) z h w hwc
      · exact hb''.1 c hc z h w hwc
  | [a], h => by simpa [mergePass] using h
  | [], h => by simpa [mergePass] using h

theorem mergePass_flatten_perm (less : α → α → Bool) : ∀ (rs : List (List α)),
    ((mergePass less rs).flatten).Perm rs.flatten
  | a :: b :: rest => by
    simp only [mergePass, List.flatten_cons]
    rw [← List.append_assoc]
    exact (mergeF_perm less a b).append (mergePass_flatten_perm less rest)
  | [a] => by simp [mergePass]
  | [] => by simp [mergePass]

theorem mergePass_length (less : α → α → Bool) : ∀ (rs : List (List α)),
    (mergePass less rs).length ≤ (rs.length + 1) / 2
  | a :: b :: rest => by
    simp only [mergePass, List.length_cons]
    have := mergePass_length less rest
    omega
  | [a] => by simp [mergePass]
  | [] => by simp [mergePass]

theorem mergeAll_ok : ∀ (fuel : Nat) (rs : List (List α)), rs.length ≤ fuel → Runs κ τ rs →
    (mergeAll (lessK κ) rs fuel).Pairwise (R κ τ) ∧ (mergeAll (lessK κ) rs fuel).Perm rs.flatten
  | 0, rs, h, _ => by
    have : rs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [mergeAll]
  | f + 1, [], _, _ => by simp [mergeAll]
  | f + 1, [r], _, hr => by simp [mergeAll]; exact hr.1 r (List.mem_singleton_self r)
  | f + 1, a :: b :: rest, h, hr => by
    simp only [mergeAll]
    have hl := mergePass_length (lessK κ) (a :: b :: rest)
    simp only [List.length_cons] at h hl
    have := mergeAll_ok f (mergePass (lessK κ) (a :: b :: rest)) (by omega)
      (mergePass_runs κ τ _ hr)
    exact ⟨this.1, this.2.trans (mergePass_flatten_perm (lessK κ) _)⟩

theorem flatten_map_perm (g : List α → List α) (hg : ∀ l, (g l).Perm l) :
    ∀ L : List (List α), ((L.map g).flatten).Perm L.flatten
  | [] => by simp
  | l :: L => by
    simp only [List.map_cons, List.flatten_cons]
    exact (hg l).append (flatten_map_perm g hg L)

theorem mergeSortWithBuffer_ok (xs : List α) (hx : xs.Pairwise (fun a b => τ a < τ b)) :
    (mergeSortWithBuffer (lessK κ) xs).Pairwise (R κ τ) ∧ (mergeSortWithBuffer (lessK κ) xs).Perm xs := by
  unfold mergeSortWithBuffer
  have hflat := chunks_flatten 7 (by decide) (xs.length + 1) xs (by omega)
  have hlen := chunks_length 7 (by decide) (xs.length + 1) xs
  have hpw : (chunks 7 xs).flatten.Pairwise (fun a b => τ a < τ b) := by rw [hflat]; exact hx
  rw [List.pairwise_flatten] at hpw
  have hruns : Runs κ τ ((chunks 7 xs).map (insertionSort (lessK κ))) := by
    refine ⟨?_, ?_⟩
    · intro r hr
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      exact insertionSort_sorted κ τ c (hpw.1 c hc)
    · rw [List.pairwise_map]
      refine hpw.2.imp ?_
      intro c d hcd a ha b hb
      exact hcd a ((insertionSort_perm _ c).mem_iff.mp ha) b ((insertionSort_perm _ d).mem_iff.mp hb)
  have := mergeAll_ok κ τ (xs.length + 1) _ (by rw [List.length_map]; omega) hruns
  refine ⟨this.1, this.2.trans ?_⟩
  conv => rhs; rw [← hflat]
  exact flatten_map_perm (insertionSort (lessK κ)) (fun l => insertionSort_perm _ l) _

/-- ★ jank's `std::stable_sort` (the replica of libstdc++ 15's) is a stable sort: for every input
whose tags strictly increase, the result is a permutation sorted by key with equal keys in input
order. -/
theorem stableSort_ok (xs : List α) (hx : xs.Pairwise (fun a b => τ a < τ b)) :
    (stableSort (lessK κ) xs).Pairwise (R κ τ) ∧ (stableSort (lessK κ) xs).Perm xs := by
  unfold stableSort
  split
  · exact ⟨by rename_i h; simp at h; subst h; simp, List.Perm.refl _⟩
  · have hsplit : xs = xs.take ((xs.length + 1) / 2) ++ xs.drop ((xs.length + 1) / 2) :=
      (List.take_append_drop _ _).symm
    have hx' := hx
    rw [hsplit, List.pairwise_append] at hx'
    have hl := mergeSortWithBuffer_ok κ τ _ hx'.1
    have hr := mergeSortWithBuffer_ok κ τ _ hx'.2.1
    have hb : Before τ (mergeSortWithBuffer (lessK κ) (xs.take ((xs.length + 1) / 2)))
        (mergeSortWithBuffer (lessK κ) (xs.drop ((xs.length + 1) / 2))) := by
      intro a ha b hb
      exact hx'.2.2 a (hl.2.mem_iff.mp ha) b (hr.2.mem_iff.mp hb)
    have hperm : (mergeSortWithBuffer (lessK κ) (xs.take ((xs.length + 1) / 2)) ++
        mergeSortWithBuffer (lessK κ) (xs.drop ((xs.length + 1) / 2))).Perm xs := by
      conv => rhs; rw [hsplit]
      exact hl.2.append hr.2
    simp only []
    by_cases hm : (xs.length + 1) / 2 ≤ xs.length - (xs.length + 1) / 2
    · simp only [hm, ↓reduceIte]
      exact ⟨mergeF_sorted κ τ _ _ hl.1 hr.1 hb, (mergeF_perm _ _ _).trans hperm⟩
    · simp only [hm, ↓reduceIte]
      exact ⟨mergeB_sorted κ τ _ _ hl.1 hr.1 hb, (mergeB_perm _ _ _).trans hperm⟩

end Stable

section Tim

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α] (κ : α → Int) (τ : α → Nat)

/-- Clojure's comparison of two keys (`compare`, or AFunction.compare of `<`): their sign. -/
def cmpK (x y : α) : Int := if κ x < κ y then -1 else if κ y < κ x then 1 else 0

theorem cmpK_neg (x y : α) : cmpK κ x y < 0 ↔ κ x < κ y := by
  unfold cmpK; split <;> (try split) <;> omega

theorem ascRun_pos : ∀ (xs : List α), xs ≠ [] → 1 ≤ ascRun (cmpK κ) xs
  | [], h => absurd rfl h
  | [_], _ => by simp [ascRun]
  | a :: b :: rest, _ => by unfold ascRun; split <;> omega

theorem descRun_pos : ∀ (xs : List α), xs ≠ [] → 1 ≤ descRun (cmpK κ) xs
  | [], h => absurd rfl h
  | [_], _ => by simp [descRun]
  | a :: b :: rest, _ => by unfold descRun; split <;> omega

theorem descRun_le : ∀ (xs : List α), descRun (cmpK κ) xs ≤ xs.length
  | [] => by simp [descRun]
  | [_] => by simp [descRun]
  | a :: b :: rest => by
    unfold descRun
    have := descRun_le (b :: rest)
    split <;> simp_all <;> omega

theorem ascRun_sorted : ∀ (xs : List α), xs.Pairwise (fun a b => τ a < τ b) →
    (xs.take (ascRun (cmpK κ) xs)).Pairwise (R κ τ)
  | [], _ => by simp
  | [_], _ => by simp [ascRun]
  | a :: b :: rest, hx => by
    have hx' := List.pairwise_cons.mp hx
    unfold ascRun
    split
    · rename_i hge
      have hab : κ a ≤ κ b := by
        have : ¬ cmpK κ b a < 0 := by omega
        rw [cmpK_neg] at this; omega
      have ih := ascRun_sorted (b :: rest) hx'.2
      have hpos := ascRun_pos κ (b :: rest) (by simp)
      obtain ⟨k, hk⟩ : ∃ k, ascRun (cmpK κ) (b :: rest) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hk] at ih ⊢
      rw [List.take_succ_cons] at ih
      rw [List.take_succ_cons, List.take_succ_cons]
      rw [List.pairwise_cons]
      refine ⟨?_, ih⟩
      have ih' := List.pairwise_cons.mp ih
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst h; have := hx'.1 z List.mem_cons_self; unfold R; omega
      · have hbz := ih'.1 z h
        have hab' : R κ τ a b := by have := hx'.1 b List.mem_cons_self; unfold R; omega
        exact R_trans κ τ hab' hbz
    · simp

theorem descRun_strict : ∀ (xs : List α),
    (xs.take (descRun (cmpK κ) xs)).Pairwise (fun a b => κ b < κ a)
  | [] => by simp
  | [_] => by simp [descRun]
  | a :: b :: rest => by
    unfold descRun
    split
    · rename_i hlt
      rw [cmpK_neg] at hlt
      have ih := descRun_strict (b :: rest)
      have hpos := descRun_pos κ (b :: rest) (by simp)
      obtain ⟨k, hk⟩ : ∃ k, descRun (cmpK κ) (b :: rest) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hk] at ih ⊢
      rw [List.take_succ_cons] at ih
      rw [List.take_succ_cons, List.take_succ_cons]
      rw [List.pairwise_cons]
      refine ⟨?_, ih⟩
      have ih' := List.pairwise_cons.mp ih
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst h; exact hlt
      · have := ih'.1 z h; omega
    · simp

/-- What `countRunAndMakeAscending` leaves: a permutation whose first `k` elements are stably
sorted, those `k` before the rest in tag order, the rest in input order. -/
theorem countRun_ok (xs : List α) (hx : xs.Pairwise (fun a b => τ a < τ b)) :
    (countRun (cmpK κ) xs).2.Perm xs ∧
    ((countRun (cmpK κ) xs).2.take (countRun (cmpK κ) xs).1).Pairwise (R κ τ) ∧
    Before τ ((countRun (cmpK κ) xs).2.take (countRun (cmpK κ) xs).1)
      ((countRun (cmpK κ) xs).2.drop (countRun (cmpK κ) xs).1) ∧
    ((countRun (cmpK κ) xs).2.drop (countRun (cmpK κ) xs).1).Pairwise (fun a b => τ a < τ b) := by
  have hsplit : ∀ k, (xs.take k ++ xs.drop k).Pairwise (fun a b => τ a < τ b) := by
    intro k; rw [List.take_append_drop]; exact hx
  match xs, hx, hsplit with
  | [], _, _ => simp [countRun, Before]
  | [a], _, _ => simp [countRun, Before]
  | a :: b :: rest, hx, hsplit =>
    simp only [countRun]
    split
    · have hle := descRun_le κ (a :: b :: rest)
      have hk := List.pairwise_append.mp (hsplit (descRun (cmpK κ) (a :: b :: rest)))
      have hlen : ((List.take (descRun (cmpK κ) (a :: b :: rest)) (a :: b :: rest)).reverse).length
          = descRun (cmpK κ) (a :: b :: rest) := by
        rw [List.length_reverse, List.length_take]; omega
      rw [List.take_left' hlen, List.drop_left' hlen]
      refine ⟨?_, ?_, ?_, hk.2.1⟩
      · exact ((List.reverse_perm _).append (List.Perm.refl _)).trans (by rw [List.take_append_drop])
      · rw [List.pairwise_reverse]
        exact (descRun_strict κ (a :: b :: rest)).imp (fun h => by unfold R; omega)
      · intro x hx' y hy
        exact hk.2.2 x (List.mem_reverse.mp hx') y hy
    · have hk := List.pairwise_append.mp (hsplit (ascRun (cmpK κ) (a :: b :: rest)))
      exact ⟨List.Perm.refl _, ascRun_sorted κ τ _ hx, hk.2.2, hk.2.1⟩

theorem bang_eq (a : Array α) (j : Nat) (h : j < a.size) : a[j]! = a.toList[j]'(by simpa using h) := by
  rw [getElem!_pos a j h]; rfl

/-- `binarySort`'s search finds the first index whose element's key is above the pivot's, on an
array sorted by key. -/
theorem binSearch_spec (a : Array α) (p : α) (hm : ∀ i j, i ≤ j → j < a.size → κ a[i]! ≤ κ a[j]!) :
    ∀ (fuel left right : Nat), left ≤ right → right ≤ a.size → right - left < fuel →
    (∀ j, j < left → ¬ κ p < κ a[j]!) → (∀ j, right ≤ j → j < a.size → κ p < κ a[j]!) →
    (∀ j, j < binSearch (cmpK κ) a p left right fuel → ¬ κ p < κ a[j]!) ∧
    (∀ j, binSearch (cmpK κ) a p left right fuel ≤ j → j < a.size → κ p < κ a[j]!) ∧
    binSearch (cmpK κ) a p left right fuel ≤ a.size
  | 0, _, _, _, _, hf, _, _ => by omega
  | f + 1, left, right, hlr, hr, hf, hlo, hhi => by
    unfold binSearch
    split
    · rename_i hlt
      simp only []
      split
      · rename_i hp
        rw [cmpK_neg] at hp
        apply binSearch_spec a p hm f left ((left + right) / 2) (by omega) (by omega) (by omega) hlo
        intro j hj hjs
        by_cases hjr : right ≤ j
        · exact hhi j hjr hjs
        · have := hm ((left + right) / 2) j hj hjs; omega
      · rename_i hp
        rw [cmpK_neg] at hp
        apply binSearch_spec a p hm f ((left + right) / 2 + 1) right (by omega) hr (by omega) _ hhi
        intro j hj
        by_cases hjl : j < left
        · exact hlo j hjl
        · have := hm j ((left + right) / 2) (by omega) (by omega); omega
    · rename_i hlt
      have heq : left = right := by omega
      subst heq
      exact ⟨hlo, hhi, hr⟩

theorem insertAt_toList (a : Array α) (i : Nat) (p : α) :
    (insertAt a i p).toList = a.toList.take i ++ [p] ++ a.toList.drop i := rfl

theorem insertAt_sorted (a : Array α) (i : Nat) (p : α) (hs : a.toList.Pairwise (R κ τ))
    (hlo : ∀ j, j < i → ¬ κ p < κ a[j]!) (hhi : ∀ j, i ≤ j → j < a.size → κ p < κ a[j]!)
    (ht : ∀ z ∈ a.toList, τ z < τ p) : (insertAt a i p).toList.Pairwise (R κ τ) := by
  rw [insertAt_toList]
  have hsplit := hs
  rw [← List.take_append_drop i a.toList, List.pairwise_append] at hsplit
  rw [List.pairwise_append, List.pairwise_append]
  refine ⟨⟨hsplit.1, by simp, ?_⟩, hsplit.2.1, ?_⟩
  · intro z hz q hq
    simp at hq; subst hq
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hz
    rw [List.getElem_take]
    have hj' : j < a.size := by simp at hj; omega
    have := hlo j (by simp at hj; omega)
    rw [bang_eq a j hj'] at this
    have ht' := ht (a.toList[j]'(by simpa using hj')) (List.getElem_mem _)
    unfold R; omega
  · intro z hz q hq
    rcases List.mem_append.mp hz with h | h
    · exact hsplit.2.2 z h q hq
    · simp at h; subst h
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      rw [List.getElem_drop]
      have hj' : i + j < a.size := by simp at hj; omega
      have := hhi (i + j) (by omega) hj'
      rw [bang_eq a (i + j) hj'] at this
      unfold R; omega

theorem binarySort_ok : ∀ (ps : List α) (a : Array α), a.toList.Pairwise (R κ τ) →
    ps.Pairwise (fun x y => τ x < τ y) → Before τ a.toList ps →
    (binarySort (cmpK κ) a ps).toList.Pairwise (R κ τ) ∧
    (binarySort (cmpK κ) a ps).toList.Perm (a.toList ++ ps)
  | [], a, hs, _, _ => by simp [binarySort]; exact hs
  | p :: ps, a, hs, hp, hb => by
    simp only [binarySort]
    have hp' := List.pairwise_cons.mp hp
    have hm : ∀ i j, i ≤ j → j < a.size → κ a[i]! ≤ κ a[j]! := by
      intro i j hij hj
      rw [bang_eq a i (by omega), bang_eq a j hj]
      rcases Nat.lt_or_eq_of_le hij with h | h
      · have := List.pairwise_iff_getElem.mp hs i j (by simp; omega) (by simpa using hj) h
        unfold R at this; omega
      · subst h; exact Int.le_refl _
    have spec := binSearch_spec κ a p hm (a.size + 1) 0 a.size (by omega) (by omega) (by omega)
      (fun j hj => absurd hj (by omega)) (fun j hj hj' => absurd hj' (by omega))
    have hins := insertAt_sorted κ τ a _ p hs spec.1 spec.2.1 (fun z hz => hb z hz p List.mem_cons_self)
    have hperm : (insertAt a (binSearch (cmpK κ) a p 0 a.size (a.size + 1)) p).toList.Perm (a.toList ++ [p]) := by
      rw [insertAt_toList]
      conv => rhs; rw [← List.take_append_drop (binSearch (cmpK κ) a p 0 a.size (a.size + 1)) a.toList]
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ (List.perm_append_comm)
    have ih := binarySort_ok ps _ hins hp'.2 (by
      intro z hz q hq
      rcases List.mem_append.mp (hperm.mem_iff.mp hz) with h | h
      · exact hb z h q (List.mem_cons_of_mem _ hq)
      · simp at h; subst h; exact hp'.1 q hq)
    refine ⟨ih.1, ih.2.trans ?_⟩
    have := hperm.append_right ps
    refine this.trans ?_
    simp

theorem pairwise_short {r : α → α → Prop} (_hr : ∀ x, r x x) : ∀ (xs : List α), xs.length < 2 → xs.Pairwise r
  | [], _ => by simp
  | [_], _ => by simp
  | _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-- ★ Clojure's TimSort for n < 32 (`countRunAndMakeAscending`, `binarySort`) is a stable sort. -/
theorem timSortSmall_ok (xs : List α) (hx : xs.Pairwise (fun a b => τ a < τ b)) (hlen : xs.length < 32) :
    ∃ ys, timSortSmall (cmpK κ) xs = some ys ∧ ys.Pairwise (R κ τ) ∧ ys.Perm xs := by
  unfold timSortSmall
  split
  · rename_i h
    exact ⟨xs, rfl, pairwise_short (fun x => by unfold R; omega) xs h, List.Perm.refl _⟩
  · rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    have hc := countRun_ok κ τ xs hx
    obtain ⟨hperm, hsort, hbef, hrest⟩ := hc
    revert hperm hsort hbef hrest
    cases countRun (cmpK κ) xs with
    | mk k ys =>
      intro hperm hsort hbef hrest
      simp only []
      have hb := binarySort_ok κ τ (ys.drop k) (ys.take k).toArray hsort hrest hbef
      refine ⟨_, rfl, hb.1, hb.2.trans ?_⟩
      simp only [List.take_append_drop]
      exact hperm

end Tim


section Agree

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α] (κ : α → Int) (τ : α → Nat)

theorem tag_inj : ∀ (xs : List α), xs.Pairwise (fun a b => τ a < τ b) →
    ∀ x ∈ xs, ∀ y ∈ xs, τ x = τ y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: t, h, x, hx, y, hy, he => by
    have h' := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hx with hx' | hx'
    · rcases List.mem_cons.mp hy with hy' | hy'
      · rw [hx', hy']
      · subst hx'; have := h'.1 y hy'; omega
    · rcases List.mem_cons.mp hy with hy' | hy'
      · subst hy'; have := h'.1 x hx'; omega
      · exact tag_inj t h'.2 x hx' y hy' he

/-- ★ For every list of fewer than 32 elements whose tags strictly increase and every integer key,
Clojure's TimSort (the replica of `java.util.TimSort` for n < 32 with AFunction.compare of a sign
comparator) and jank's `std::stable_sort` (the replica of libstdc++ 15's with `compare(a, b) < 0`)
give the same list. So `sort`, `sort-by` and `sort` with `<`, `>` or `compare` agree on every input
whose comparisons are a total preorder; T9-1 needs one that is not (##NaN). -/
theorem sorts_agree (xs : List α) (hx : xs.Pairwise (fun a b => τ a < τ b)) (hlen : xs.length < 32) :
    timSortSmall (cmpK κ) xs = some (stableSort (lessK κ) xs) := by
  obtain ⟨ys, hys, hsort, hperm⟩ := timSortSmall_ok κ τ xs hx hlen
  rw [hys]
  have hj := stableSort_ok κ τ xs hx
  congr 1
  apply eq_of_perm_of_pairwise (hperm.trans hj.2.symm) hsort hj.1
  intro x hxm y hym h1 h2
  have hx' := hperm.mem_iff.mp hxm
  have hy' := hperm.mem_iff.mp hym
  unfold R at h1 h2
  exact tag_inj τ xs hx x hx' y hy' (by omega)

end Agree

theorem zipIdx_tags : ∀ (ks : List Int) (n : Nat), (ks.zipIdx n).Pairwise (fun a b => a.2 < b.2)
  | [], _ => by simp
  | k :: ks, n => by
    rw [List.zipIdx_cons, List.pairwise_cons]
    refine ⟨?_, zipIdx_tags ks (n + 1)⟩
    intro b hb
    have := List.mem_zipIdx hb
    simp only at this ⊢
    omega

/-- ★ The same for every list of integers (keys) tagged by position: `(sort coll)` of distinct
or repeated numbers without NaN orders the same in both, for every list of fewer than 32. -/
theorem sorts_agree_ints (ks : List Int) (h : ks.length < 32) :
    timSortSmall (cmpK Prod.fst) (ks.zipIdx) = some (stableSort (lessK Prod.fst) (ks.zipIdx)) :=
  sorts_agree Prod.fst Prod.snd _ (zipIdx_tags ks 0) (by simpa using h)


/-! ## From the generic statement to the replica's `jankSort` and `cljSort`

Both sorts only compare elements, so mapping the input through `f` commutes with them when the
comparators agree through `f` (naturality). With `f` the map from `(key, position)` to the replica's
`El`, this turns `sorts_agree_ints` into a statement about `Sort.jankSort` and `Sort.cljSort`. -/

namespace Natural

section Std

variable {α β : Type} (f : α → β) (less : β → β → Bool) (less' : α → α → Bool)
  (hf : ∀ a b, less (f a) (f b) = less' a b)
include hf

theorem linIns_map (v : α) : ∀ l : List α, linIns less (f v) (l.map f) = (linIns less' v l).map f
  | [] => by simp [linIns]
  | y :: ys => by
    simp only [List.map_cons, linIns, hf]
    split <;> simp [linIns_map v ys]

theorem insSortRev_map : ∀ (acc xs : List α),
    insSortRev less (acc.map f) (xs.map f) = (insSortRev less' acc xs).map f
  | acc, [] => by simp [insSortRev]
  | acc, x :: xs => by
    simp only [List.map_cons, insSortRev, List.getLast?_map]
    cases h : acc.getLast? with
    | none => simpa using insSortRev_map [x] xs
    | some fst =>
      simp only [Option.map_some, hf]
      split
      · simpa using insSortRev_map (acc ++ [x]) xs
      · rw [linIns_map f less less' hf x acc]; exact insSortRev_map _ xs

theorem insertionSort_map (xs : List α) :
    insertionSort less (xs.map f) = (insertionSort less' xs).map f := by
  unfold insertionSort
  have := insSortRev_map f less less' hf [] xs
  simp only [List.map_nil] at this
  rw [this, List.map_reverse]

theorem mergeFuel_map : ∀ (n : Nat) (l r : List α),
    mergeFuel less n (l.map f) (r.map f) = (mergeFuel less' n l r).map f
  | n, [], r => by cases n <;> simp [mergeFuel]
  | n, x :: xs, [] => by cases n <;> simp [mergeFuel]
  | 0, x :: xs, y :: ys => by simp [mergeFuel]
  | n + 1, x :: xs, y :: ys => by
    simp only [List.map_cons, mergeFuel, hf]
    split
    · have := mergeFuel_map n (x :: xs) ys; simp only [List.map_cons] at this; simp [this]
    · have := mergeFuel_map n xs (y :: ys); simp only [List.map_cons] at this; simp [this]

theorem mergeF_map (l r : List α) : mergeF less (l.map f) (r.map f) = (mergeF less' l r).map f := by
  unfold mergeF; simp only [List.length_map]; exact mergeFuel_map f less less' hf _ l r

theorem mergeBRev_map : ∀ (n : Nat) (l r : List α),
    mergeBRev less n (l.map f) (r.map f) = (mergeBRev less' n l r).map f
  | n, [], r => by cases n <;> simp [mergeBRev]
  | n, x :: xs, [] => by cases n <;> simp [mergeBRev]
  | 0, x :: xs, y :: ys => by simp [mergeBRev]
  | n + 1, x :: xs, y :: ys => by
    simp only [List.map_cons, mergeBRev, hf]
    split
    · have := mergeBRev_map n xs (y :: ys); simp only [List.map_cons] at this; simp [this]
    · have := mergeBRev_map n (x :: xs) ys; simp only [List.map_cons] at this; simp [this]

theorem mergeB_map (l r : List α) : mergeB less (l.map f) (r.map f) = (mergeB less' l r).map f := by
  unfold mergeB
  simp only [List.length_map, ← List.map_reverse]
  rw [mergeBRev_map f less less' hf, List.map_reverse]

theorem mergePass_map : ∀ rs : List (List α),
    mergePass less (rs.map (List.map f)) = (mergePass less' rs).map (List.map f)
  | a :: b :: rest => by
    simp only [List.map_cons, mergePass, mergeF_map f less less' hf, mergePass_map rest]
  | [a] => by simp [mergePass]
  | [] => by simp [mergePass]

theorem mergeAll_map : ∀ (n : Nat) (rs : List (List α)),
    mergeAll less (rs.map (List.map f)) n = (mergeAll less' rs n).map f
  | 0, rs => by simp [mergeAll, List.map_flatten]
  | n + 1, [] => by simp [mergeAll]
  | n + 1, [r] => by simp [mergeAll]
  | n + 1, a :: b :: rest => by
    have := mergeAll_map n (mergePass less' (a :: b :: rest))
    rw [← mergePass_map f less less' hf] at this
    simpa [mergeAll] using this

omit hf in
theorem chunks_map (k : Nat) : ∀ (fuel : Nat) (xs : List α),
    chunks k (xs.map f) fuel = (chunks k xs fuel).map (List.map f)
  | 0, xs => by simp [chunks]
  | n + 1, xs => by
    simp only [chunks, List.isEmpty_map]
    split
    · simp
    · simp only [List.map_cons, ← List.map_take]
      rw [← List.map_drop, chunks_map k n (xs.drop k)]

theorem mergeSortWithBuffer_map (xs : List α) :
    mergeSortWithBuffer less (xs.map f) = (mergeSortWithBuffer less' xs).map f := by
  unfold mergeSortWithBuffer
  simp only [List.length_map]
  rw [chunks_map f 7 (xs.length + 1) xs, List.map_map]
  have : (insertionSort less ∘ List.map f) = (List.map f ∘ insertionSort less') := by
    funext l; simp [insertionSort_map f less less' hf l]
  rw [this, ← List.map_map, mergeAll_map f less less' hf]

theorem stableSort_map (xs : List α) : stableSort less (xs.map f) = (stableSort less' xs).map f := by
  unfold stableSort
  simp only [List.isEmpty_map, List.length_map]
  split
  · rfl
  · simp only [← List.map_take, ← List.map_drop, mergeSortWithBuffer_map f less less' hf]
    split
    · exact mergeF_map f less less' hf _ _
    · exact mergeB_map f less less' hf _ _

end Std

section Tim

set_option linter.unusedSectionVars false

variable {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (cmp : β → β → Int)
  (cmp' : α → α → Int) (hf : ∀ a b, cmp (f a) (f b) = cmp' a b)
include hf

theorem ascRun_map : ∀ xs : List α, ascRun cmp (xs.map f) = ascRun cmp' xs
  | [] => by simp [ascRun]
  | [_] => by simp [ascRun]
  | a :: b :: rest => by
    have := ascRun_map (b :: rest)
    simp only [List.map_cons] at this ⊢
    simp only [ascRun, hf, this]

theorem descRun_map : ∀ xs : List α, descRun cmp (xs.map f) = descRun cmp' xs
  | [] => by simp [descRun]
  | [_] => by simp [descRun]
  | a :: b :: rest => by
    have := descRun_map (b :: rest)
    simp only [List.map_cons] at this ⊢
    simp only [descRun, hf, this]

theorem countRun_map (xs : List α) :
    countRun cmp (xs.map f) = ((countRun cmp' xs).1, (countRun cmp' xs).2.map f) := by
  match xs with
  | [] => simp [countRun]
  | [a] => simp [countRun]
  | a :: b :: rest =>
    have hd := descRun_map f cmp cmp' hf (a :: b :: rest)
    have ha := ascRun_map f cmp cmp' hf (a :: b :: rest)
    simp only [List.map_cons] at hd ha
    simp only [List.map_cons, countRun, hf]
    split
    · simp only [hd]
      rw [show f a :: f b :: List.map f rest = List.map f (a :: b :: rest) from rfl,
        ← List.map_take, ← List.map_drop, List.map_append, List.map_reverse]
    · simp only [ha, List.map_cons]

omit hf in
theorem bang_map (a : Array α) (j : Nat) (h : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos (a.map f) j (by simpa using h), getElem!_pos a j h, Array.getElem_map]

theorem binSearch_map (a : Array α) (p : α) : ∀ (n l r : Nat), r ≤ a.size →
    binSearch cmp (a.map f) (f p) l r n = binSearch cmp' a p l r n
  | 0, l, r, _ => rfl
  | n + 1, l, r, hr => by
    simp only [binSearch]
    split
    · rename_i hlt
      rw [bang_map f a ((l + r) / 2) (by omega), hf]
      split
      · exact binSearch_map a p n l ((l + r) / 2) (by omega)
      · exact binSearch_map a p n ((l + r) / 2 + 1) r hr
    · rfl

omit [Inhabited α] [Inhabited β] hf in
theorem insertAt_map (a : Array α) (i : Nat) (p : α) :
    insertAt (a.map f) i (f p) = (insertAt a i p).map f := by
  apply Array.ext'
  simp only [insertAt_toList, Array.toList_map, List.map_append, List.map_cons, List.map_nil,
    List.map_take, List.map_drop]

theorem binarySort_map : ∀ (ps : List α) (a : Array α),
    binarySort cmp (a.map f) (ps.map f) = (binarySort cmp' a ps).map f
  | [], a => by simp [binarySort]
  | p :: ps, a => by
    simp only [List.map_cons, binarySort, Array.size_map]
    rw [binSearch_map f cmp cmp' hf a p _ _ _ (Nat.le_refl _), insertAt_map f]
    exact binarySort_map ps _

theorem timSortSmall_map (xs : List α) :
    timSortSmall cmp (xs.map f) = (timSortSmall cmp' xs).map (List.map f) := by
  unfold timSortSmall
  simp only [List.length_map]
  split
  · simp
  · split
    · simp
    · rw [countRun_map f cmp cmp' hf]
      simp only [Option.map_some]
      rw [← List.map_take, ← List.map_drop]
      have := binarySort_map f cmp cmp' hf ((countRun cmp' xs).2.drop (countRun cmp' xs).1)
        ((countRun cmp' xs).2.take (countRun cmp' xs).1).toArray
      rw [show (List.map f (List.take (countRun cmp' xs).1 (countRun cmp' xs).2)).toArray
          = ((List.take (countRun cmp' xs).1 (countRun cmp' xs).2).toArray).map f by
          apply Array.ext'; simp]
      rw [this, Array.toList_map]

end Tim

end Natural

/-! ## The replica's own functions -/

/-- `(k, position)` as the replica's element. -/
def toEl (p : Int × Nat) : El := ⟨.num p.1, p.2⟩

theorem mk_num (ks : List Int) : mk (ks.map Key.num) = (ks.zipIdx).map toEl := by
  unfold mk
  rw [List.zipIdx_map, List.map_map]
  rfl

theorem numCompare_num (a b : Int) : numCompare (.num a) (.num b) = cmpK id a b := by
  simp [numCompare, cmpK]

/-- ★ For every list of numbers without NaN, of fewer than 32 elements, the replica's `(sort coll)`
gives the same list for Clojure (`cljSort none`, TimSort) and jank (`jankSort none`,
std::stable_sort). -/
theorem replica_sort_agree (ks : List Int) (h : ks.length < 32) :
    cljSort none (mk (ks.map Key.num)) = some (jankSort none (mk (ks.map Key.num))) := by
  rw [mk_num]
  simp only [cljSort, jankSort]
  have hj := Natural.stableSort_map toEl jankLessDefault (lessK Prod.fst)
    (fun a b => by simp [jankLessDefault, toEl, lessK, numCompare_num, cmpK]; split <;> (try split) <;> omega)
    ks.zipIdx
  have hc := Natural.timSortSmall_map toEl (fun x y => numCompare x.key y.key) (cmpK Prod.fst)
    (fun a b => by simp [toEl, numCompare_num, cmpK]) ks.zipIdx
  rw [hj, hc, sorts_agree_ints ks h]
  rfl

/-- ★ The same with a comparator fn: `(sort < coll)`, `(sort compare coll)` (keys ascending) and
`(sort > coll)` (keys descending), for every list of numbers without NaN of fewer than 32. -/
theorem replica_sort_agree_lt (ks : List Int) (h : ks.length < 32) :
    cljSort (some .lt) (mk (ks.map Key.num)) = some (jankSort (some .lt) (mk (ks.map Key.num))) := by
  rw [mk_num]
  simp only [cljSort, jankSort]
  have hj := Natural.stableSort_map toEl (jankLess .lt) (lessK Prod.fst)
    (fun a b => by simp [jankLess, Comp.call, keyLt, toEl, lessK]) ks.zipIdx
  have hc := Natural.timSortSmall_map toEl (cljCmp .lt) (cmpK Prod.fst)
    (fun a b => by
      simp only [cljCmp, Comp.call, keyLt, toEl, cmpK]
      by_cases h1 : a.1 < b.1
      · simp [h1]
      · by_cases h2 : b.1 < a.1 <;> simp [h1, h2]) ks.zipIdx
  rw [hj, hc, sorts_agree_ints ks h]
  rfl

theorem replica_sort_agree_compare (ks : List Int) (h : ks.length < 32) :
    cljSort (some .compare) (mk (ks.map Key.num)) =
      some (jankSort (some .compare) (mk (ks.map Key.num))) := by
  rw [mk_num]
  simp only [cljSort, jankSort]
  have hj := Natural.stableSort_map toEl (jankLess .compare) (lessK Prod.fst)
    (fun a b => by
      simp only [jankLess, Comp.call, numCompare, toEl, lessK]
      by_cases h1 : a.1 < b.1
      · simp [h1]
      · by_cases h2 : b.1 < a.1 <;> simp [h1, h2]) ks.zipIdx
  have hc := Natural.timSortSmall_map toEl (cljCmp .compare) (cmpK Prod.fst)
    (fun a b => by
      simp only [cljCmp, Comp.call, numCompare, toEl, cmpK]
      by_cases h1 : a.1 < b.1
      · simp [h1]; decide
      · by_cases h2 : b.1 < a.1
        · simp [h1, h2]; decide
        · simp [h1, h2]; decide) ks.zipIdx
  rw [hj, hc, sorts_agree_ints ks h]
  rfl

theorem replica_sort_agree_gt (ks : List Int) (h : ks.length < 32) :
    cljSort (some .gt) (mk (ks.map Key.num)) = some (jankSort (some .gt) (mk (ks.map Key.num))) := by
  rw [mk_num]
  simp only [cljSort, jankSort]
  have hj := Natural.stableSort_map toEl (jankLess .gt) (lessK (fun p : Int × Nat => -p.1))
    (fun a b => by simp [jankLess, Comp.call, keyLt, toEl, lessK]) ks.zipIdx
  have hc := Natural.timSortSmall_map toEl (cljCmp .gt) (cmpK (fun p : Int × Nat => -p.1))
    (fun a b => by
      simp only [cljCmp, Comp.call, keyLt, toEl, cmpK]
      by_cases h1 : b.1 < a.1
      · simp [h1]
      · by_cases h2 : a.1 < b.1
        · simp [h1, h2]
        · simp [h1, h2]; try omega) ks.zipIdx
  rw [hj, hc, sorts_agree (fun p : Int × Nat => -p.1) Prod.snd _ (zipIdx_tags ks 0) (by simpa using h)]
  rfl

end Jank.R9.Seq.SortProof

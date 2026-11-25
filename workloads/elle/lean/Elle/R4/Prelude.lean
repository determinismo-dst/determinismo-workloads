import Elle.Basic

/-!
# Round 4: general lemmas the proofs use

Association lists (`amGet`, `amPut`, `amUpdate`: Clojure maps in the replica), `dedup`, and loops
(`for` in `Id`, which the replica's `Id.run do` blocks compile to).
-/

namespace Elle.R4

open Elle

/-! ## Lawful equality on the replica's enumerations -/

instance : LawfulBEq OpType where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> rfl

instance : LawfulBEq F where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> rfl

instance : LawfulBEq Fn where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> rfl

/-! ## Association lists -/

section
variable {α β : Type} [BEq α] [LawfulBEq α]

theorem lookup_cons_self (k : α) (v : β) (m : List (α × β)) : ((k, v) :: m).lookup k = some v := by
  simp [List.lookup]

theorem lookup_cons_ne {k k' : α} (h : k' ≠ k) (v : β) (m : List (α × β)) : ((k, v) :: m).lookup k' = m.lookup k' := by
  have : (k' == k) = false := by simpa using h
  simp [List.lookup, this]

theorem lookup_mem {m : List (α × β)} {k : α} {v : β} (h : m.lookup k = some v) : (k, v) ∈ m := by
  induction m with
  | nil => simp [List.lookup] at h
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    by_cases hk : k = a
    · subst hk; rw [lookup_cons_self] at h; cases h; simp
    · rw [lookup_cons_ne hk] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_none_of_not_any {m : List (α × β)} {k : α} (h : ¬ (m.any fun x => x.1 == k) = true) :
    m.lookup k = none := by
  induction m with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    simp only [List.any_cons, Bool.or_eq_true, not_or] at h
    have hne : k ≠ a := by intro e; subst e; simp at h
    rw [lookup_cons_ne hne]; exact ih h.2

theorem amPut_self (m : List (α × β)) (k : α) (v : β) : (amPut m k v).lookup k = some v := by
  unfold amPut
  split
  · rename_i hany
    induction m with
    | nil => simp at hany
    | cons x xs ih =>
      obtain ⟨a, b⟩ := x
      by_cases h : a = k
      · subst h; simp [List.lookup]
      · have e : (a == k) = false := by simpa using h
        simp only [List.map_cons, e, Bool.false_eq_true, ↓reduceIte]
        rw [lookup_cons_ne (Ne.symm h)]
        apply ih
        simpa [List.any_cons, e] using hany
  · rename_i hany
    rw [List.lookup_append, lookup_none_of_not_any hany]
    simp [List.lookup]

theorem amPut_ne (m : List (α × β)) {k k' : α} (hne : k' ≠ k) (v : β) : (amPut m k v).lookup k' = m.lookup k' := by
  have e : (k' == k) = false := by simpa using hne
  unfold amPut
  split
  · rename_i hany; clear hany
    induction m with
    | nil => rfl
    | cons x xs ih =>
      obtain ⟨a, b⟩ := x
      by_cases h : a = k
      · subst h
        simp only [List.map_cons, beq_self_eq_true, ↓reduceIte]
        rw [lookup_cons_ne hne, lookup_cons_ne hne]; exact ih
      · have e2 : (a == k) = false := by simpa using h
        simp only [List.map_cons, e2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : k' = a
        · subst h3; simp [List.lookup]
        · rw [lookup_cons_ne h3, lookup_cons_ne h3]; exact ih
  · rw [List.lookup_append]
    cases m.lookup k' <;> simp [List.lookup, e]
end

theorem amUpdate_self {α β : Type} [BEq α] [LawfulBEq α] (m : List (α × β)) (k : α) (d : β) (f : β → β) :
    (amUpdate m k d f).lookup k = some (f ((m.lookup k).getD d)) := by
  unfold amUpdate amGet; exact amPut_self _ _ _

theorem amUpdate_ne {α β : Type} [BEq α] [LawfulBEq α] (m : List (α × β)) {k k' : α} (hne : k' ≠ k)
    (d : β) (f : β → β) : (amUpdate m k d f).lookup k' = m.lookup k' := by
  unfold amUpdate; exact amPut_ne _ hne _

theorem lookup_map_snd {α β γ : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (f : α → β → γ) (k : α) :
    (l.map fun x => (x.1, f x.1 x.2)).lookup k = (l.lookup k).map (f k) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    by_cases h : k = a
    · subst h; simp [List.lookup]
    · simp only [List.map_cons]; rw [lookup_cons_ne h, lookup_cons_ne h]; exact ih

/-! ## Folds -/

theorem foldl_inv {α β : Type} (l : List α) (f : β → α → β) (init : β) (P : β → Prop)
    (h0 : P init) (hs : ∀ a ∈ l, ∀ b, P b → P (f b a)) : P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h0
  | cons a as ih =>
    exact ih _ (hs a List.mem_cons_self _ h0) (fun a' h' b hb => hs a' (List.mem_cons_of_mem _ h') b hb)

/-- A property every step keeps, and that the step for some element establishes, holds at the end. -/
theorem foldl_mono_of_mem {α β : Type} (l : List α) (f : β → α → β) (init : β) (P : β → Prop)
    (a : α) (ha : a ∈ l) (hset : ∀ b, P (f b a)) (hkeep : ∀ a' ∈ l, ∀ b, P b → P (f b a')) :
    P (l.foldl f init) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rw [List.foldl_append, List.foldl_cons]
  exact foldl_inv t f _ P (hset _) (fun a' h' b hb => hkeep a' (by simp [h']) b hb)

/-! ## dedup -/

theorem foldl_dedup_mem {α : Type} [BEq α] [LawfulBEq α] (l acc : List α) (x : α) :
    x ∈ l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc ↔ x ∈ acc ∨ x ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl]
    split
    · rw [ih]; rename_i h
      simp only [List.contains_iff_mem] at h
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · rintro (h1 | h1)
        · exact Or.inl h1
        · rcases List.mem_cons.mp h1 with h2 | h2
          · subst h2; exact Or.inl h
          · exact Or.inr h2
    · rw [ih]; simp only [List.mem_append, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h1 | h1) | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1

theorem mem_dedup {α : Type} [BEq α] [LawfulBEq α] (l : List α) (x : α) : x ∈ dedup l ↔ x ∈ l := by
  unfold dedup; rw [foldl_dedup_mem]; simp

theorem foldl_dedup_nodup_self {α : Type} [BEq α] [LawfulBEq α] (l acc : List α)
    (h : (acc ++ l).Nodup) :
    l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc = acc ++ l := by
  induction l generalizing acc with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl]
    have hy : y ∉ acc := by
      intro hm
      have := (List.nodup_append.mp h).2.2
      exact this y hm y (List.mem_cons_self) rfl
    have : (acc.contains y) = false := by simpa using hy
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    rw [ih]
    · simp
    · simpa using h

theorem dedup_of_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) (h : l.Nodup) : dedup l = l := by
  unfold dedup; rw [foldl_dedup_nodup_self]; · simp
  simpa using h

/-! ## Loops in `Id` -/

/-- An invariant of a `for` loop over a list in `Id` (a body that may `yield` or stop with `done`). -/
theorem forIn_list_inv {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (P : β → Prop) (h0 : P init)
    (hs : ∀ a ∈ l, ∀ b, P b → P (f a b).run.value) : P (forIn l init f).run := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons a as ih =>
    have ha := hs a List.mem_cons_self init h0
    rw [List.forIn_cons]
    revert ha
    cases hf : f a init with
    | done b => intro ha; exact ha
    | yield b =>
      intro ha
      exact ih b ha (fun a' ha' b' hb' => hs a' (List.mem_cons_of_mem _ ha') b' hb')

theorem forIn_array_inv {α β : Type} (l : Array α) (init : β) (f : α → β → Id (ForInStep β))
    (P : β → Prop) (h0 : P init)
    (hs : ∀ a ∈ l.toList, ∀ b, P b → P (f a b).run.value) : P (forIn l init f).run := by
  rw [← Array.forIn_toList]
  exact forIn_list_inv l.toList init f P h0 hs


/-- An invariant of a `while`/`repeat` loop in `Id`, by a measure that each `yield` lowers. -/
theorem loop_inv {β : Type} (f : Unit → β → Id (ForInStep β)) (μ : β → Nat) (P Q : β → Prop)
    (hstep : ∀ b, P b → match (f () b).run with
      | .done b' => Q b'
      | .yield b' => P b' ∧ μ b' < μ b)
    (b : β) (hb : P b) : Q (forIn Lean.Loop.mk b f).run := by
  induction hm : μ b using Nat.strongRecOn generalizing b with
  | ind n ih =>
    show Q (Lean.Loop.forIn _ b f).run
    rw [Lean.Loop.forIn_eq_of_monadTail]
    have := hstep b hb
    revert this
    cases hf : f () b with
    | done b' => intro h; exact h
    | yield b' => intro ⟨h1, h2⟩; exact ih (μ b') (hm ▸ h2) b' h1 rfl

theorem nodup_foldl_dedup {α : Type} [BEq α] [LawfulBEq α] (l acc : List α) (h : acc.Nodup) :
    (l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) acc).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons y ys ih =>
    simp only [List.foldl]
    split
    · exact ih _ h
    · rename_i hy
      apply ih
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb hab; simp at hb; subst hb; subst hab; simp_all

theorem nodup_dedup {α : Type} [BEq α] [LawfulBEq α] (l : List α) : (dedup l).Nodup :=
  nodup_foldl_dedup l [] List.nodup_nil

end Elle.R4

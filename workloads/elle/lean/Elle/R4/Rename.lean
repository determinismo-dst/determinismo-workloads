import Elle.R4.LAIndex

/-!
# Round 4: D12's refinement is invariant under renaming values

Renaming every element by an injective `ρ` (appends and reads alike) renames the version order
D12's refinement picks (`sorted-values` ranked by length, then by count of elements no failed op
appended, then by first read), and renames the write and read indices: so `ww-mop-dep`'s and
`rw-mop-deps`' neighbours are the renamed ones. Elle 0.2.8's hash order (`Hash.vectorsOrder`) has
no such property: round 3 found 250 verdicts in 40,000 histories flip under renaming.
-/

namespace Elle.R4.Rename

open Elle Elle.R4 Elle.ListAppend

variable (ρ : Int → Int)

def renV : Val → Val
  | .int i => .int (ρ i)
  | .list l => .list (l.map ρ)
  | v => v

def renM (m : Mop) : Mop := { m with v := renV ρ m.v }
def renO (o : Op) : Op := { o with value := o.value.map (renM ρ) }
def renH (h : History) : History := h.map (renO ρ)

variable {ρ}

theorem toList_renV (v : Val) : ListAppend.Val.toList (renV ρ v) = (ListAppend.Val.toList v).map ρ := by
  cases v <;> rfl

theorem map_inj {l l' : List Int} (hρ : Function.Injective ρ) (h : l.map ρ = l'.map ρ) : l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp_all
  | cons x xs ih =>
    cases l' with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hρ h.1, ih h.2]

theorem beq_map_inj (hρ : Function.Injective ρ) (a k : Int) : (ρ a == ρ k) = (a == k) := by
  by_cases h : a = k
  · simp [h]
  · have h2 : ρ a ≠ ρ k := fun he => h (hρ he)
    rw [beq_false_of_ne h2, beq_false_of_ne h]

/-! ## Association lists under a renaming of keys or values -/

theorem lookup_map_key {β : Type} (hρ : Function.Injective ρ) (m : List (Int × β)) (k : Int) :
    (m.map fun x => (ρ x.1, x.2)).lookup (ρ k) = m.lookup k := by
  induction m with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    by_cases hk : k = a
    · subst hk; simp [List.lookup]
    · have : ρ k ≠ ρ a := fun he => hk (hρ he)
      simp only [List.map_cons]
      rw [lookup_cons_ne this, lookup_cons_ne hk]; exact ih

theorem any_map_key {β : Type} (hρ : Function.Injective ρ) (m : List (Int × β)) (k : Int) :
    (m.map fun x => (ρ x.1, x.2)).any (·.1 == ρ k) = m.any (·.1 == k) := by
  induction m with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.any_cons, ih, beq_map_inj hρ]

theorem amPut_map_key {β : Type} (hρ : Function.Injective ρ) (m : List (Int × β)) (k : Int) (v : β) :
    amPut (m.map fun x => (ρ x.1, x.2)) (ρ k) v = (amPut m k v).map fun x => (ρ x.1, x.2) := by
  unfold amPut
  rw [any_map_key hρ]
  split
  · simp only [List.map_map]
    congr 1
    funext x
    by_cases h : x.1 = k
    · simp [h]
    · have : ρ x.1 ≠ ρ k := fun he => h (hρ he)
      simp [h, this]
  · simp

theorem any_map_val {α β γ : Type} [BEq α] (m : List (α × β)) (H : β → γ) (k : α) :
    (m.map fun x => (x.1, H x.2)).any (·.1 == k) = m.any (·.1 == k) := by
  induction m with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem amUpdate_map_val {α β γ : Type} [BEq α] [LawfulBEq α] (m : List (α × β)) (H : β → γ) (k : α)
    (d : β) (d' : γ) (f : β → β) (f' : γ → γ) (hd : H d = d') (hf : ∀ v, f' (H v) = H (f v)) :
    amUpdate (m.map fun x => (x.1, H x.2)) k d' f' = (amUpdate m k d f).map fun x => (x.1, H x.2) := by
  unfold amUpdate amGet amPut
  have hl : (m.map fun x => (x.1, H x.2)).lookup k = (m.lookup k).map H := lookup_map_snd m (fun _ b => H b) k
  rw [hl, any_map_val]
  have hv : f' (((m.lookup k).map H).getD d') = H (f ((m.lookup k).getD d)) := by
    cases m.lookup k
    · simp only [Option.map_none, Option.getD_none]; rw [← hd, hf]
    · simp [hf]
  rw [hv]
  split
  · simp only [List.map_map]
    congr 1; funext x
    by_cases h : x.1 = k
    · simp [h]
    · have : (x.1 == k) = false := by simpa using h
      simp [this]
  · simp


/-! ## The version order -/

/-- Rename a key's read values. -/
def renVals (vs : List (List Int)) : List (List Int) := vs.map (·.map ρ)

theorem beq_list_map_inj (hρ : Function.Injective ρ) (w v : List Int) : (w.map ρ == v.map ρ) = (w == v) := by
  by_cases h : w = v
  · simp [h]
  · have h2 : w.map ρ ≠ v.map ρ := fun he => h (map_inj hρ he)
    rw [beq_false_of_ne h2, beq_false_of_ne h]

theorem contains_renVals (hρ : Function.Injective ρ) (vs : List (List Int)) (v : List Int) :
    (renVals (ρ := ρ) vs).contains (v.map ρ) = vs.contains v := by
  induction vs with
  | nil => rfl
  | cons w ws ih =>
    simp only [renVals, List.map_cons, List.contains_cons] at ih ⊢
    rw [ih, beq_list_map_inj hρ v w]

def frStep (acc : List (Nat × List (List Int))) (m : Mop) : List (Nat × List (List Int)) :=
  match m.f, m.v with
  | .r, .list v => if v.isEmpty then acc else amUpdate acc m.k [] fun vs => if vs.contains v then vs else vs ++ [v]
  | _, _ => acc

theorem fromReadsOf_eq (hs : List Op) : fromReadsOf hs = hs.foldl (fun acc o => o.value.foldl frStep acc) [] := rfl

theorem frStep_ren (hρ : Function.Injective ρ) (acc : List (Nat × List (List Int))) (m : Mop) :
    frStep (acc.map fun x => (x.1, renVals (ρ := ρ) x.2)) (renM ρ m) =
      (frStep acc m).map fun x => (x.1, renVals (ρ := ρ) x.2) := by
  unfold renM frStep
  simp only
  cases hm : m.v with
  | list v =>
    simp only [renV]
    cases hf : m.f <;> simp only
    by_cases he : v.isEmpty = true
    · have : (v.map ρ).isEmpty = true := by simpa using he
      simp [he, this]
    · have : (v.map ρ).isEmpty = false := by simpa using he
      simp only [this, Bool.false_eq_true, ↓reduceIte, he]
      apply amUpdate_map_val
      · rfl
      · intro vs
        rw [contains_renVals hρ]
        split <;> simp [renVals]
  | int i => simp [renV]
  | nil => simp [renV]
  | kmap l => simp [renV]
  | unborn => simp [renV]
  | dead => simp [renV]

theorem fromReads_ren (hρ : Function.Injective ρ) (hs : List Op) :
    fromReadsOf (hs.map (renO ρ)) = (fromReadsOf hs).map fun x => (x.1, renVals (ρ := ρ) x.2) := by
  rw [fromReadsOf_eq, fromReadsOf_eq, List.foldl_map]
  have H : ∀ (acc : List (Nat × List (List Int))) (o : Op),
      (renO ρ o).value.foldl frStep (acc.map fun x => (x.1, renVals (ρ := ρ) x.2)) =
      (o.value.foldl frStep acc).map fun x => (x.1, renVals (ρ := ρ) x.2) := by
    intro acc o
    unfold renO
    simp only
    rw [List.foldl_map]
    exact List.foldl_hom _ (fun acc2 m => frStep_ren hρ acc2 m)
  have := List.foldl_hom (l := hs) (init := []) (g₁ := fun acc o => o.value.foldl frStep acc)
    (g₂ := fun acc o => (renO ρ o).value.foldl frStep acc)
    (fun acc : List (Nat × List (List Int)) => acc.map fun x => (x.1, renVals (ρ := ρ) x.2)) H
  simpa using this


theorem amPut_map_val {α β γ : Type} [BEq α] [LawfulBEq α] (m : List (α × β)) (H : β → γ) (k : α) (v : β) :
    amPut (m.map fun x => (x.1, H x.2)) k (H v) = (amPut m k v).map fun x => (x.1, H x.2) := by
  unfold amPut
  rw [any_map_val]
  split
  · simp only [List.map_map]
    congr 1; funext x
    by_cases h : x.1 = k
    · simp [h]
    · have : (x.1 == k) = false := by simpa using h
      simp [this]
  · simp

def vsStep (acc : List (Nat × Option Int)) (mo : Mop) : List (Nat × Option Int) :=
  if mo.f != .append then acc
  else if (acc.lookup mo.k).isSome then amPut acc mo.k none
  else amPut acc mo.k (match mo.v with | .int e => some e | _ => none)

theorem vsStep_ren (acc : List (Nat × Option Int)) (mo : Mop) :
    vsStep (acc.map fun x => (x.1, x.2.map ρ)) (renM ρ mo) = (vsStep acc mo).map fun x => (x.1, x.2.map ρ) := by
  unfold vsStep renM
  simp only
  split
  · rfl
  · have hl : ((acc.map fun x => (x.1, x.2.map ρ)).lookup mo.k).isSome = (acc.lookup mo.k).isSome := by
      rw [lookup_map_snd acc (fun _ b => b.map ρ)]; cases acc.lookup mo.k <;> rfl
    rw [hl]
    split
    · exact amPut_map_val acc (Option.map ρ) mo.k none
    · have : (match renV ρ mo.v with | .int e => some e | _ => none) =
          (match mo.v with | .int e => some e | _ => none).map ρ := by
        cases mo.v <;> rfl
      rw [this]
      exact amPut_map_val acc (Option.map ρ) mo.k _

theorem vfsa_ren (hs : List Op) :
    valuesFromSingleAppends (hs.map (renO ρ)) =
      (valuesFromSingleAppends hs).map fun x => (x.1, renVals (ρ := ρ) x.2) := by
  unfold valuesFromSingleAppends
  have hfold : (hs.map (renO ρ)).foldl (fun acc o => o.value.foldl vsStep acc) [] =
      (hs.foldl (fun acc o => o.value.foldl vsStep acc) []).map fun x => (x.1, x.2.map ρ) := by
    rw [List.foldl_map]
    have := List.foldl_hom (l := hs) (init := []) (g₁ := fun acc o => o.value.foldl vsStep acc)
      (g₂ := fun acc o => (renO ρ o).value.foldl vsStep acc)
      (fun acc : List (Nat × Option Int) => acc.map fun x => (x.1, x.2.map ρ)) (by
        intro acc o
        unfold renO; simp only
        rw [List.foldl_map]
        exact List.foldl_hom _ (fun acc2 m => vsStep_ren acc2 m))
    simpa using this
  show ((hs.map (renO ρ)).foldl (fun acc o => o.value.foldl vsStep acc) []).filterMap _ = _
  rw [hfold]
  show ((hs.foldl (fun acc o => o.value.foldl vsStep acc) []).map _).filterMap _ =
    ((hs.foldl (fun acc o => o.value.foldl vsStep acc) []).filterMap _).map _
  generalize hs.foldl (fun acc o => o.value.foldl vsStep acc) [] = acc
  induction acc with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    simp only [List.map_cons, List.filterMap_cons]
    cases v with
    | none => simpa using ih
    | some e => simp only [Option.map_some, List.map_cons]; rw [ih]; rfl

theorem failedAppends_ren (hs : List Op) :
    failedAppends (hs.map (renO ρ)) = (failedAppends hs).map fun x => (x.1, ρ x.2) := by
  unfold failedAppends
  rw [List.filter_map, List.flatMap_map, List.map_flatMap]
  have hf : (Op.isFail ∘ renO ρ) = Op.isFail := by funext o; rfl
  rw [hf]
  congr 1; funext o
  simp only [Function.comp, renO, List.filterMap_map, List.map_filterMap]
  congr 1; funext m
  simp only [Function.comp, renM]
  cases m.f <;> cases m.v <;> rfl


theorem contains_map_inj (hρ : Function.Injective ρ) (l : List Int) (x : Int) : (l.map ρ).contains (ρ x) = l.contains x := by
  induction l with
  | nil => rfl
  | cons y ys ih => simp only [List.map_cons, List.contains_cons, ih, beq_map_inj hρ]

theorem dedup_map (hρ : Function.Injective ρ) (l : List Int) : dedup (l.map ρ) = (dedup l).map ρ := by
  unfold dedup
  rw [List.foldl_map]
  have := List.foldl_hom (l := l) (init := ([] : List Int)) (List.map ρ)
    (g₁ := fun acc x => if acc.contains x then acc else acc ++ [x])
    (g₂ := fun acc x => if acc.contains (ρ x) then acc else acc ++ [ρ x]) (by
      intro acc x
      rw [contains_map_inj hρ]
      split <;> simp)
  simpa using this

theorem fs_contains_ren (hρ : Function.Injective ρ) (fs : List (Nat × Int)) (k : Nat) (e : Int) :
    (fs.map fun x => (x.1, ρ x.2)).contains (k, ρ e) = fs.contains (k, e) := by
  induction fs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    simp only [List.map_cons, List.contains_cons, ih]
    congr 1
    by_cases h : (k, e) = (a, b)
    · have : (k, ρ e) = (a, ρ b) := by
        simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.1, by rw [h.2]⟩
      simp [h, this]
    · have h2 : (k, ρ e) ≠ (a, ρ b) := by
        intro he; simp only [Prod.mk.injEq] at he h; exact h ⟨he.1, hρ he.2⟩
      rw [beq_false_of_ne h2, beq_false_of_ne h]

theorem merged_ren (fr single : List (Nat × List (List Int))) :
    (single.map fun x => (x.1, renVals (ρ := ρ) x.2)).foldl
      (fun acc (x : Nat × List (List Int)) => if (acc.lookup x.1).isSome then acc else acc ++ [x])
      (fr.map fun x => (x.1, renVals (ρ := ρ) x.2)) =
    (single.foldl (fun acc (x : Nat × List (List Int)) => if (acc.lookup x.1).isSome then acc else acc ++ [x]) fr).map
      fun x => (x.1, renVals (ρ := ρ) x.2) := by
  rw [List.foldl_map]
  apply List.foldl_hom
  intro acc x
  have hl : ((acc.map fun x => (x.1, renVals (ρ := ρ) x.2)).lookup x.1).isSome = (acc.lookup x.1).isSome := by
    rw [lookup_map_snd acc (fun _ b => renVals (ρ := ρ) b)]; cases acc.lookup x.1 <;> rfl
  simp only [hl]
  split <;> simp

def mergedOf (hs : List Op) : List (Nat × List (List Int)) :=
  (valuesFromSingleAppends hs).foldl
    (fun acc (x : Nat × List (List Int)) => if (acc.lookup x.1).isSome then acc else acc ++ [x]) (fromReadsOf hs)

def cmpOf (fs : List (Nat × Int)) (k : Nat) (a b : List Int) : Bool :=
  decide (a.length < b.length) || (a.length == b.length &&
    decide ((a.filter fun e => !fs.contains (k, e)).length ≤ (b.filter fun e => !fs.contains (k, e)).length))

theorem sortedValues_some (hs : List Op) (flip byFirst : Bool) (fs : List (Nat × Int)) :
    sortedValues hs flip byFirst (some fs) = (mergedOf hs).map fun x => (x.1, x.2.mergeSort (cmpOf fs x.1)) := rfl

theorem nf_ren (hρ : Function.Injective ρ) (fs : List (Nat × Int)) (k : Nat) (a : List Int) :
    ((a.map ρ).filter fun e => !(fs.map fun x => (x.1, ρ x.2)).contains (k, e)).length =
      (a.filter fun e => !fs.contains (k, e)).length := by
  rw [List.filter_map, List.length_map]
  congr 2; funext e
  simp only [Function.comp, fs_contains_ren hρ]

/-- **D12's refinement renames with the values.** Its `sorted-values` of the renamed history is
the renamed `sorted-values` (any injective renaming): the order of reads of equal length depends
on their count of elements no failed op appended and on where each was first read, both kept by a
renaming. -/
theorem sortedValues_d12b_ren (hρ : Function.Injective ρ) (hs : List Op) (flip byFirst : Bool) :
    sortedValues (hs.map (renO ρ)) flip byFirst (some (failedAppends (hs.map (renO ρ)))) =
      (sortedValues hs flip byFirst (some (failedAppends hs))).map fun x => (x.1, renVals (ρ := ρ) x.2) := by
  rw [sortedValues_some, sortedValues_some, failedAppends_ren]
  have hm : mergedOf (hs.map (renO ρ)) = (mergedOf hs).map fun x => (x.1, renVals (ρ := ρ) x.2) := by
    unfold mergedOf; rw [fromReads_ren hρ, vfsa_ren]; exact merged_ren _ _
  rw [hm, List.map_map, List.map_map]
  congr 1; funext x
  simp only [Function.comp, Prod.mk.injEq, true_and]
  unfold renVals
  rw [← List.map_mergeSort (r := cmpOf (failedAppends hs) x.1)]
  intro a _ b _
  unfold cmpOf
  rw [List.length_map, List.length_map, nf_ren hρ, nf_ren hρ]

/-- The append index (`append-index`, the version order) under D12's refinement, renamed. -/
theorem appendIndex_d12b_ren (hρ : Function.Injective ρ) (hs : List Op) (flip byFirst : Bool) :
    appendIndex (sortedValues (hs.map (renO ρ)) flip byFirst (some (failedAppends (hs.map (renO ρ))))) =
      (appendIndex (sortedValues hs flip byFirst (some (failedAppends hs)))).map fun x => (x.1, x.2.map ρ) := by
  rw [sortedValues_d12b_ren hρ]
  unfold appendIndex
  rw [List.map_map, List.map_map]
  congr 1; funext x
  simp only [Function.comp, Prod.mk.injEq, true_and, renVals]
  rw [List.getLast?_map]
  cases x.2.getLast? with
  | none => simp [dedup]
  | some L => simp [dedup_map hρ]

end Elle.R4.Rename

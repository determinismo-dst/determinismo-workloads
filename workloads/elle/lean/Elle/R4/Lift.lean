import Elle.R4.Cycle
import Elle.Txn

/-!
# Round 4: Elle's explained cycles in every interpretation's DSG

`classify` (txn.clj's `cycle-explainer`) names a cycle by its steps: the count of anti-dependency
steps, whether two are adjacent, whether a `wr` step is there, and whether `process`/`realtime`
steps are. If each step lifts into a DSG as `StepLift` says, the DSG shows what `Claim` says, or
(only through D1's unread steps) a G-single.
-/

namespace Elle.R4

open Elle

/-- What an explained step is in a DSG: a `ww` step a path of write dependencies (or, for D1's
unread step, a G-single somewhere); `wr` a read dependency; `rw` an anti-dependency followed by
write dependencies (or, where the reader's own unread append came next, write dependencies only);
`process` a session-order edge; `realtime` a real-time edge. -/
def StepLift (D : DSG) (s : Step) (a b : Nat) : Prop :=
  (s.type = "ww" ∧ (Plus D.ww a b ∨ (s.unread = true ∧ D.GSingle .none))) ∨
  (s.type = "wr" ∧ D.wr a b) ∨
  (s.type = "rw" ∧ ((∃ c, D.rw a c ∧ Star D.ww c b) ∨ Plus D.ww a b)) ∨
  (s.type = "process" ∧ D.so a b) ∨
  (s.type = "realtime" ∧ D.rt a b)

/-- The variant `classify` names: realtime if a step is, else process if a step is. -/
def stepsVar (steps : List Step) : Var :=
  if 0 < (steps.filter (·.type == "realtime")).length then .realtime
  else if 0 < (steps.filter (·.type == "process")).length then .process else .none

/-- `classify`'s anti-dependency count. -/
def rwCount (steps : List Step) : Nat :=
  (steps.filter (·.type == "rw")).length + (steps.filter (·.type == "rwp")).length

/-- `classify`'s adjacency test (cyclic). -/
def rwAdjacent (steps : List Step) : Bool :=
  let types := steps.map (·.type)
  match types.getLast? with
  | none => false
  | some l =>
    let ts := l :: types
    (ts.zip (ts.drop 1)).any fun (a, b) => (a == "rw" || a == "rwp") && (b == "rw" || b == "rwp")

/-- What every interpretation shows, by `classify`'s branches: G1c (G0 without a `wr` step) with no
anti-dependency step; with one, G-single or G1c; with more, adjacent, G2 or G1c; non-adjacent,
G-nonadjacent, and G2 or G1c. Each with the variant of the cycle's orders. -/
def Claim (D : DSG) (steps : List Step) : Prop :=
  let x := stepsVar steps
  if rwCount steps = 0 then
    (if steps.any (·.type == "wr") then D.G1c x else D.G0 x)
  else if rwCount steps = 1 then D.GSingle x ∨ D.G1c x
  else if rwAdjacent steps then D.G2 x ∨ D.G1c x
  else D.GNonadj x ∧ (D.G2 x ∨ D.G1c x)


/-! ## Counting lemmas about the steps -/

def isRW (s : Step) : Bool := s.type == "rw" || s.type == "rwp"

theorem rwCount_eq (steps : List Step) : rwCount steps = (steps.filter isRW).length := by
  unfold rwCount isRW
  induction steps with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.filter_cons]
    by_cases h1 : s.type = "rw"
    · have h2 : ¬ s.type = "rwp" := by rw [h1]; decide
      simp [h1, ih]; omega
    · by_cases h2 : s.type = "rwp"
      · simp [h2, ih]; omega
      · simp [h1, h2, ih]

theorem two_filter {α : Type} (l : List α) (p : α → Bool) {i j : Nat} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≠ j) (hpi : p l[i] = true) (hpj : p l[j] = true) : 2 ≤ (l.filter p).length := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    rcases i with _ | i <;> rcases j with _ | j
    · exact absurd rfl hij
    · simp only [List.getElem_cons_zero] at hpi
      simp only [List.getElem_cons_succ] at hpj
      simp only [List.filter_cons, hpi, ↓reduceIte, List.length_cons]
      have hj' : j < xs.length := by simp at hj; omega
      have : 0 < (xs.filter p).length :=
        List.length_pos_iff_exists_mem.mpr ⟨xs[j], List.mem_filter.mpr ⟨List.getElem_mem hj', hpj⟩⟩
      omega
    · simp only [List.getElem_cons_zero] at hpj
      simp only [List.getElem_cons_succ] at hpi
      simp only [List.filter_cons, hpj, ↓reduceIte, List.length_cons]
      have hi' : i < xs.length := by simp at hi; omega
      have : 0 < (xs.filter p).length :=
        List.length_pos_iff_exists_mem.mpr ⟨xs[i], List.mem_filter.mpr ⟨List.getElem_mem hi', hpi⟩⟩
      omega
    · simp only [List.getElem_cons_succ] at hpi hpj
      have := ih (i := i) (j := j) (by simpa using hi) (by simpa using hj) (by omega) hpi hpj
      simp only [List.filter_cons]
      split <;> simp <;> omega

theorem rwAdjacent_of {steps : List Step} {t : Nat} (ht : t < steps.length)
    (h1 : isRW steps[t] = true) (h2 : isRW (steps[(t + 1) % steps.length]'(Nat.mod_lt _ (by omega))) = true) :
    rwAdjacent steps = true := by
  unfold rwAdjacent
  have hn : 0 < steps.length := by omega
  have hlast : (steps.map (·.type)).getLast? = some steps[steps.length - 1].type := by
    rw [List.getLast?_map, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
  simp only [hlast]
  apply List.any_eq_true.mpr
  by_cases hlt : t + 1 < steps.length
  · simp only [Nat.mod_eq_of_lt hlt] at h2
    refine ⟨(steps[t].type, steps[t + 1].type), ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      refine ⟨t + 1, by simp; omega, ?_⟩
      simp
    · simp only [isRW] at h1 h2; simp [h1, h2]
  · have ht' : t = steps.length - 1 := by omega
    have h0 : (t + 1) % steps.length = 0 := by rw [show t + 1 = 0 + steps.length by omega]; simp
    simp only [h0] at h2
    refine ⟨(steps[steps.length - 1].type, steps[0].type), ?_, ?_⟩
    · rw [List.mem_iff_getElem]
      refine ⟨0, by simp; exact hn, ?_⟩
      simp [List.getElem_zip]
    · subst ht'; simp only [isRW] at h1 h2; simp [h1, h2]


/-! ## The lift -/

theorem succ_mod (j n : Nat) (hn : 0 < n) : (j + 1) % n = if j % n + 1 < n then j % n + 1 else 0 := by
  have h := Nat.div_add_mod j n
  split
  · rename_i hl
    rw [show j + 1 = n * (j / n) + (j % n + 1) by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt hl]
  · have : j % n + 1 = n := by have := Nat.mod_lt j hn; omega
    rw [show j + 1 = n * (j / n + 1) by rw [Nat.mul_add]; omega, Nat.mul_mod_right]

theorem stepsVar_process {steps : List Step} {s : Step} (hs : s ∈ steps) (h : s.type = "process") :
    stepsVar steps ≠ .none := by
  unfold stepsVar
  have : 0 < (steps.filter (·.type == "process")).length :=
    List.length_pos_iff_exists_mem.mpr ⟨s, List.mem_filter.mpr ⟨hs, by simp [h]⟩⟩
  split
  · simp
  · simp [this]

theorem stepsVar_realtime {steps : List Step} {s : Step} (hs : s ∈ steps) (h : s.type = "realtime") :
    stepsVar steps = .realtime := by
  unfold stepsVar
  have : 0 < (steps.filter (·.type == "realtime")).length :=
    List.length_pos_iff_exists_mem.mpr ⟨s, List.mem_filter.mpr ⟨hs, by simp [h]⟩⟩
  simp [this]

/-- Each step lifts to a segment kind: `a` only for an anti-dependency step, `d` only for `wr`. -/
theorem step_kind (D : DSG) (steps : List Step) (s : Step) (hs : s ∈ steps) (a b : Nat)
    (hl : StepLift D s a b) (hu : ¬ (s.unread = true ∧ D.GSingle .none)) :
    ∃ k : Kind, D.SegOK (stepsVar steps) k a b ∧ (k = .a → s.type = "rw") ∧ (k = .d → s.type = "wr") := by
  rcases hl with ⟨ht, h | h⟩ | ⟨ht, h⟩ | ⟨ht, ⟨c, hc, hcb⟩ | h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩
  · exact ⟨.w, h.mono fun _ _ h => Or.inl h, by simp, by simp⟩
  · exact absurd h hu
  · exact ⟨.d, .one (Or.inr h), by simp, fun _ => ht⟩
  · exact ⟨.a, ⟨c, hc, hcb⟩, fun _ => ht, by simp⟩
  · exact ⟨.w, h.mono fun _ _ h => Or.inl h, by simp, by simp⟩
  · exact ⟨.w, .one (Or.inr (Or.inl ⟨stepsVar_process hs ht, h⟩)), by simp, by simp⟩
  · exact ⟨.w, .one (Or.inr (Or.inr ⟨stepsVar_realtime hs ht, h⟩)), by simp, by simp⟩

/-- **Cycle lifting.** A closed walk of explained steps (Elle's cycle: `ops` with its first vertex
repeated last, `steps[i]` explaining `ops[i] -> ops[i+1]`), each lifting into a DSG whose
anti-dependencies are irreflexive, shows what `classify`'s branch claims there, or a G-single
through one of D1's unread steps. -/
theorem lift_cycle (D : DSG) (hirr : ∀ a, ¬ D.rw a a) (ops : List Nat) (steps : List Step)
    (hlen : ops.length = steps.length + 1) (hne : steps ≠ []) (hclosed : ops.head? = ops.getLast?)
    (hlift : ∀ i (hi : i < steps.length), StepLift D steps[i] (ops.getD i 0) (ops.getD (i + 1) 0)) :
    ((∃ s ∈ steps, s.unread = true) ∧ D.GSingle .none) ∨ Claim D steps := by
  by_cases hu : (∃ s ∈ steps, s.unread = true) ∧ D.GSingle .none
  · exact Or.inl hu
  right
  have hu' : ∀ s ∈ steps, ¬ (s.unread = true ∧ D.GSingle .none) := fun s hs h => hu ⟨⟨s, hs, h.1⟩, h.2⟩
  let n := steps.length
  have hn : 0 < n := List.length_pos_iff.mpr hne
  let x := stepsVar steps
  have hk : ∀ t (ht : t < n), ∃ k : Kind, D.SegOK x k (ops.getD t 0) (ops.getD (t + 1) 0) ∧
      (k = .a → steps[t].type = "rw") ∧ (k = .d → steps[t].type = "wr") :=
    fun t ht => step_kind D steps _ (List.getElem_mem ht) _ _ (hlift t ht) (hu' _ (List.getElem_mem ht))
  let K0 : Nat → Kind := fun t => if h : t < n then Classical.choose (hk t h) else .w
  let K : Nat → Kind := fun j => K0 (j % n)
  let v : Nat → Nat := fun j => ops.getD (j % n) 0
  have hlast : ops.getD n 0 = ops.getD 0 0 := by
    have h1 : ops.getLast? = ops[n]? := by rw [List.getLast?_eq_getElem?, hlen]; rfl
    have h2 : ops.head? = ops[0]? := by cases ops <;> rfl
    rw [hclosed, h1] at h2
    simp only [List.getD_eq_getElem?_getD, ← h2]
  have hK0 : ∀ t (ht : t < n), D.SegOK x (K0 t) (ops.getD t 0) (ops.getD (t + 1) 0) ∧
      (K0 t = .a → steps[t].type = "rw") ∧ (K0 t = .d → steps[t].type = "wr") := by
    intro t ht
    simp only [K0, ht, ↓reduceDIte]
    exact Classical.choose_spec (hk t ht)
  have cyc : Cyc D x n v K := by
    refine ⟨hn, fun j => by simp [v, Nat.add_mod_right], fun j => by simp [K, Nat.add_mod_right], ?_⟩
    intro j
    have hjn : j % n < n := Nat.mod_lt _ hn
    have hseg := (hK0 (j % n) hjn).1
    have : ops.getD (j % n + 1) 0 = v (j + 1) := by
      simp only [v]
      rw [succ_mod j n hn]
      split
      · rfl
      · have : j % n + 1 = n := by omega
        rw [this, hlast]
    rw [this] at hseg
    exact hseg
  have hmodlt : ∀ t, t % n < n := fun t => Nat.mod_lt _ hn
  have ha : ∀ t, K t = .a → isRW (steps[t % n]'(hmodlt t)) = true := by
    intro t h
    have := (hK0 (t % n) (hmodlt t)).2.1 h
    simp [isRW, this]
  have hd : ∀ t, K t = .d → (steps[t % n]'(hmodlt t)).type = "wr" := fun t h => (hK0 (t % n) (hmodlt t)).2.2 h
  have hKlt : ∀ t (ht : t < n), K t = K0 t := fun t ht => by simp [K, Nat.mod_eq_of_lt ht]
  have hcount2 : ∀ i j (hi : i < n) (hj : j < n), i ≠ j → K i = .a → K j = .a → 2 ≤ rwCount steps := by
    intro i j hi hj hij hia hja
    rw [rwCount_eq]
    have h1 := ha i hia; have h2 := ha j hja
    simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h1 h2
    exact two_filter steps isRW hi hj hij h1 h2
  have hcount1 : ∀ i (hi : i < n), K i = .a → 1 ≤ rwCount steps := by
    intro i hi hia
    rw [rwCount_eq]
    have h1 := ha i hia
    simp only [Nat.mod_eq_of_lt hi] at h1
    exact List.length_pos_iff_exists_mem.mpr ⟨_, List.mem_filter.mpr ⟨List.getElem_mem hi, h1⟩⟩
  unfold Claim
  split
  · rename_i h0
    have hna : ∀ t < n, K t ≠ .a := fun t ht hka => by have := hcount1 t ht hka; omega
    split
    · exact cyc_G1c cyc hna
    · rename_i hnw
      apply cyc_G0 cyc
      intro t ht
      cases hkt : K t with
      | w => rfl
      | a => exact absurd hkt (hna t ht)
      | d =>
        have := hd t hkt
        simp only [Nat.mod_eq_of_lt ht] at this
        exact absurd (List.any_eq_true.mpr ⟨_, List.getElem_mem ht, by simp [this]⟩) hnw
  · rename_i h0
    split
    · rename_i h1
      by_cases hex : ∃ i < n, K i = .a
      · obtain ⟨i, hi, hia⟩ := hex
        left
        exact cyc_GSingle hirr cyc hi hia fun t ht hti hta => by
          have := hcount2 t i ht hi hti hta hia; omega
      · right; exact cyc_G1c cyc fun t ht h => hex ⟨t, ht, h⟩
    · split
      · by_cases hex : ∃ i < n, K i = .a
        · obtain ⟨i, hi, hia⟩ := hex
          left; exact cyc_G2 hirr cyc hi hia
        · right; exact cyc_G1c cyc fun t ht h => hex ⟨t, ht, h⟩
      · rename_i hadj
        have hgn : D.GNonadj (stepsVar steps) := by
          apply cyc_GNonadj cyc
          intro t h1 h2
          apply hadj
          have r1 := ha t h2
          have r2 := ha (t + 1) h1
          have hm : (t + 1) % n = (t % n + 1) % n := by
            rw [succ_mod t n hn, succ_mod (t % n) n hn, Nat.mod_mod]
          simp only [hm] at r2
          exact rwAdjacent_of (hmodlt t) r1 r2
        refine ⟨hgn, ?_⟩
        by_cases hex : ∃ i < n, K i = .a
        · obtain ⟨i, hi, hia⟩ := hex
          left; exact cyc_G2 hirr cyc hi hia
        · right; exact cyc_G1c cyc fun t ht h => hex ⟨t, ht, h⟩

import Jank.Lex

/-!
# The lexer's loops end on input without NUL (round 3, proofs)

Round 2 (R1) proved that each of the lexer's character-by-character loops maps its state to
itself on a NUL byte (`symbol_loop_stuck_on_nul`, `string_loop_stuck_on_nul`,
`comment_loop_stuck_on_nul`: `mbrtowc` gives NUL length 0), and found by search that without NUL
nothing hangs (complete over 1,222,981 byte strings of length ≤ 4 and 20,000 random ones ≤ 12).
Here, for every byte string without NUL, at every position:

- `mbrtowc_len_pos`: a successful decode of a non-NUL byte has length ≥ 1 (strict UTF-8 or C
  locale);
- `symbolStep_next`, `commentStep_next`, `stringStep_next`: one iteration of the symbol/keyword/
  character loop (lex.cpp:612, 1183, 1282), of the comment loops (635, 1411) and of the string loop
  (1325) either stops or moves the position forward, within the file;
- `loop_stops`: a loop whose iterations either stop or decrease a measure ends by stopping when
  its fuel exceeds the measure;
- `lexSymbol_never_hangs`: the symbol token (lex.cpp:1163-1218, the replica's `lexSymbol`) never
  reports its loop as hanging: the `file.size + 2` iterations the replica allows always suffice,
  so the C++ `while(true)` ends.
-/

namespace Jank.R3.Proofs.Lex

open Jank.LexBytes Jank.Lex

/-- No NUL byte in the file. -/
def NulFree (f : Array UInt8) : Prop := ∀ i, i < f.size → f[i]! ≠ 0

theorem go_len (f : Array UInt8) (i need : Nat) (lo hi : UInt8) (avail : Nat) :
    ∀ (fuel k acc c len : Nat), mbrtowc.go f i need lo hi avail k acc fuel = .ok c len → len = need + 1 := by
  intro fuel
  induction fuel with
  | zero => intro k acc c len h; simp only [mbrtowc.go, Mb.ok.injEq] at h; exact h.2.symm
  | succ n ih =>
    intro k acc c len h
    simp only [mbrtowc.go] at h
    by_cases h1 : k > need
    · simp only [h1, ite_true, Mb.ok.injEq] at h; exact h.2.symm
    · simp only [h1, ite_false] at h
      by_cases h2 : k > avail
      · simp [h2] at h
      · simp only [h2, ite_false] at h
        by_cases h3 : (!(if (k == 1) = true then decide (lo ≤ f[i + k]!) && decide (f[i + k]! ≤ hi)
            else isCont f[i + k]!)) = true
        · simp only [h3, ite_true] at h; cases h
        · simp only [h3, Bool.false_eq_true, ite_false] at h
          exact ih _ _ c len h

/-- `mbrtowc` on a non-NUL byte: a code point of length at least 1. -/
theorem mbrtowc_len_pos (loc : Locale) (f : Array UInt8) (i c len : Nat) (hnz : f[i]! ≠ 0)
    (h : mbrtowc loc f i = .ok c len) : 1 ≤ len := by
  unfold mbrtowc at h
  by_cases hi : i ≥ f.size
  · simp [hi] at h
  simp only [hi, ite_false] at h
  have h0 : (f[i]! == 0) = false := by simpa using hnz
  simp only [h0, Bool.false_eq_true, ite_false] at h
  by_cases h8 : f[i]! < 0x80
  · simp only [h8, ite_true, Mb.ok.injEq] at h; omega
  simp only [h8, ite_false] at h
  cases loc with
  | c => simp at h
  | utf8 =>
    simp only at h
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
      first
      | (have := go_len _ _ _ _ _ _ _ _ _ c len h; omega)
      | simp at h

/-- `peek()` on a file without NUL: the next character, of length ≥ 1, inside the file. -/
theorem peek_len (p : P) (hnf : NulFree p.file) (oc : CP) (h : p.peek = some oc) :
    1 ≤ oc.len ∧ p.pos + 1 < p.file.size := by
  unfold P.peek at h
  split at h
  · cases h
  · rename_i hlt
    have hlt' : p.pos + 1 < p.file.size := by omega
    unfold P.decode at h
    split at h
    · rename_i c l hm
      injection h with h; subst h
      exact ⟨mbrtowc_len_pos p.loc p.file (p.pos + 1) c l (hnf _ hlt') hm, hlt'⟩
    · cases h

/-- One iteration of the symbol, keyword and character loops: it stops, or moves forward inside
the file (lex.cpp:612, 1183, 1282). -/
theorem symbolStep_next (p p' : P) (hnf : NulFree p.file) (h : symbolStep p = .next p') :
    p'.file = p.file ∧ p.pos < p'.pos ∧ p.pos + 1 < p.file.size := by
  unfold symbolStep at h
  split at h
  · cases h
  · rename_i oc hpk
    split at h
    · cases h
    · injection h with h; subst h
      have := peek_len p hnf oc hpk
      exact ⟨rfl, by simp; omega, this.2⟩

/-- One iteration of a comment loop (lex.cpp:635, 1411). -/
theorem commentStep_next (p p' : P) (hnf : NulFree p.file) (h : commentStep p = .next p') :
    p'.file = p.file ∧ p.pos < p'.pos ∧ p.pos + 1 < p.file.size := by
  unfold commentStep at h
  split at h
  · cases h
  · rename_i oc hpk
    split at h
    · cases h
    · injection h with h; subst h
      have := peek_len p hnf oc hpk
      exact ⟨rfl, by simp; omega, this.2⟩

/-- One iteration of the string loop (lex.cpp:1325). -/
theorem stringStep_next (p p' : P) (e e' : Bool) (hnf : NulFree p.file)
    (h : stringStep (p, e) = some (.next (p', e'))) :
    p'.file = p.file ∧ p.pos < p'.pos ∧ p.pos + 1 < p.file.size := by
  unfold stringStep at h
  simp only at h
  split at h
  · cases h
  · rename_i oc hpk
    split at h
    · cases h
    · injection h with h; injection h with h; injection h with h1 _; subst h1
      have := peek_len p hnf oc hpk
      exact ⟨rfl, by simp; omega, this.2⟩

/-- At the end of the file, the loops stop. -/
theorem symbolStep_end (p : P) (h : p.file.size ≤ p.pos + 1) : symbolStep p = .stop p := by
  unfold symbolStep P.peek
  simp [show p.pos + 1 ≥ p.file.size from h]

/-- A loop that, from states satisfying `I`, either stops or keeps `I` and decreases `μ`, ends by
stopping once it has more iterations than `μ` of its start. -/
theorem loop_stops {α β : Type} (f : β → ForInStep β) (I : β → Prop) (μ : β → Nat)
    (hdec : ∀ b b', I b → f b = .yield b' → I b' ∧ μ b' < μ b) :
    ∀ (xs : List α) (b : β), I b → μ b < xs.length →
      ∃ b0 b', I b0 ∧ f b0 = .done b' ∧ forIn (m := Id) xs b (fun _ r => pure (f r)) = b' := by
  intro xs
  induction xs with
  | nil => intro b _ h; simp at h
  | cons a as ih =>
    intro b hb hμ
    simp only [List.forIn_cons]
    cases hf : f b with
    | done b' => exact ⟨b, b', hb, hf, by simp [hf]; rfl⟩
    | yield b' =>
      obtain ⟨hI, hlt⟩ := hdec b b' hb hf
      obtain ⟨b0, b'', hI0, h1, h2⟩ := ih b' hI (by simp at hμ; omega)
      exact ⟨b0, b'', hI0, h1, by simp [hf]; exact h2⟩

/-- The symbol loop's body as a function of the loop state. -/
def symF (s : P × Bool) : ForInStep (P × Bool) :=
  match symbolStep s.1 with
  | .stop _ => .done (s.1, true)
  | .next p' => .yield (p', s.2)

/-- The symbol loop (lex.cpp:1183) ends by its `break`, for every file without NUL and every start. -/
theorem symbol_loop_done (p : P) (hnf : NulFree p.file) (d : Bool) (n : Nat) (hn : p.file.size < n) :
    (forIn (m := Id) (List.range' 0 n 1) (p, d) (fun _ r => pure (symF r))).2 = true := by
  obtain ⟨b0, b', _, h1, h2⟩ := loop_stops symF (fun s => s.1.file = p.file) (fun s => s.1.file.size - s.1.pos)
    (by
      intro b b' hI hf
      unfold symF at hf
      split at hf
      · cases hf
      · rename_i p' hs
        injection hf with hf; subst hf
        obtain ⟨hf, hlt, _⟩ := symbolStep_next b.1 p' (by rw [hI]; exact hnf) hs
        refine ⟨by simp [hf, hI], ?_⟩
        simp only [hf]
        omega)
    (List.range' 0 n 1) (p, d) rfl (by simp; omega)
  rw [h2]
  unfold symF at h1
  split at h1
  · injection h1 with h1; subst h1; rfl
  · cases h1

/-- A loop with a `done` flag (the replica's symbol, character, comment, keyword, `#!` and
default-symbol loops): when each iteration stops with the flag set or moves forward inside the
file, `file.size + 1` iterations or more end with the flag set. -/
theorem flag_loop_done (step : P × Bool → ForInStep (P × Bool)) (f0 : Array UInt8)
    (hstep : ∀ s : P × Bool, s.1.file = f0 →
      (∃ q, step s = .done (q, true)) ∨
      (∃ p', step s = .yield (p', s.2) ∧ p'.file = f0 ∧ s.1.pos < p'.pos ∧ s.1.pos < f0.size))
    (p : P) (hp : p.file = f0) (d : Bool) (n : Nat) (hn : f0.size < n) :
    (forIn (m := Id) (List.range' 0 n 1) (p, d) (fun _ r => pure (step r))).2 = true := by
  obtain ⟨b0, b', hI0, h1, h2⟩ := loop_stops step (fun s => s.1.file = f0) (fun s => f0.size - s.1.pos)
    (by
      intro b b' hI hf
      rcases hstep b hI with ⟨q, hq⟩ | ⟨p', hp', hf', hlt, _⟩
      · rw [hq] at hf; cases hf
      · rw [hp'] at hf; injection hf with hf; subst hf
        exact ⟨hf', by simp only; omega⟩)
    (List.range' 0 n 1) (p, d) hp (by simp; omega)
  rw [h2]
  rcases hstep b0 hI0 with ⟨q, hq⟩ | ⟨p', hp', _⟩
  · rw [hq] at h1; injection h1 with h1; subst h1; rfl
  · rw [hp'] at h1; cases h1

/-- The character loop (lex.cpp:612): its iteration. -/
def charF (s : P × Bool) : ForInStep (P × Bool) :=
  if s.1.pos > s.1.file.size then .done (s.1, true) else symF s

/-- The comment loops (lex.cpp:635, 1411): their iteration. -/
def comF (s : P × Bool) : ForInStep (P × Bool) :=
  match commentStep s.1 with
  | .stop _ => .done (s.1, true)
  | .next p' => .yield (p', s.2)

/-- The default symbol loop (lex.cpp:1502): its iteration (it stops on a zero-length decode, so it
ends even on a NUL). -/
def defF (s : P × Bool) : ForInStep (P × Bool) :=
  if s.1.pos > s.1.file.size then .done (s.1, true)
  else match s.1.decode s.1.pos with
    | none => .done (s.1, true)
    | some r =>
      if !isSymbolChar s.1.loc r.c || r.len == 0 then .done (s.1, true)
      else .yield ({ s.1 with pos := s.1.pos + r.len }, s.2)

theorem decode_lt (p : P) (i : Nat) (r : CP) (h : p.decode i = some r) : i < p.file.size := by
  unfold P.decode mbrtowc at h
  by_cases hi : i ≥ p.file.size
  · simp [hi] at h
  · omega

theorem symF_spec (f0 : Array UInt8) (hnf : NulFree f0) (s : P × Bool) (hs : s.1.file = f0) :
    (∃ q, symF s = .done (q, true)) ∨
    (∃ p', symF s = .yield (p', s.2) ∧ p'.file = f0 ∧ s.1.pos < p'.pos ∧ s.1.pos < f0.size) := by
  unfold symF
  split
  · left; exact ⟨_, rfl⟩
  · rename_i p' h
    obtain ⟨hf, hlt, hsz⟩ := symbolStep_next s.1 p' (by rw [hs]; exact hnf) h
    right; exact ⟨p', rfl, by rw [hf, hs], hlt, by rw [← hs]; omega⟩

theorem charF_spec (f0 : Array UInt8) (hnf : NulFree f0) (s : P × Bool) (hs : s.1.file = f0) :
    (∃ q, charF s = .done (q, true)) ∨
    (∃ p', charF s = .yield (p', s.2) ∧ p'.file = f0 ∧ s.1.pos < p'.pos ∧ s.1.pos < f0.size) := by
  unfold charF
  split
  · left; exact ⟨_, rfl⟩
  · exact symF_spec f0 hnf s hs

theorem comF_spec (f0 : Array UInt8) (hnf : NulFree f0) (s : P × Bool) (hs : s.1.file = f0) :
    (∃ q, comF s = .done (q, true)) ∨
    (∃ p', comF s = .yield (p', s.2) ∧ p'.file = f0 ∧ s.1.pos < p'.pos ∧ s.1.pos < f0.size) := by
  unfold comF
  split
  · left; exact ⟨_, rfl⟩
  · rename_i p' h
    obtain ⟨hf, hlt, hsz⟩ := commentStep_next s.1 p' (by rw [hs]; exact hnf) h
    right; exact ⟨p', rfl, by rw [hf, hs], hlt, by rw [← hs]; omega⟩

/-- The default symbol loop ends whatever the bytes (NUL included). -/
theorem defF_spec (f0 : Array UInt8) (s : P × Bool) (hs : s.1.file = f0) :
    (∃ q, defF s = .done (q, true)) ∨
    (∃ p', defF s = .yield (p', s.2) ∧ p'.file = f0 ∧ s.1.pos < p'.pos ∧ s.1.pos < f0.size) := by
  unfold defF
  split
  · left; exact ⟨_, rfl⟩
  · split
    · left; exact ⟨_, rfl⟩
    · rename_i r hr
      split
      · left; exact ⟨_, rfl⟩
      · rename_i hc
        right
        have hlen : r.len ≠ 0 := by
          intro h0; apply hc; simp [h0]
        have := decode_lt s.1 s.1.pos r hr
        exact ⟨_, rfl, by simp [hs], by simp; omega, by rw [← hs]; exact this⟩

theorem forIn_body_eq {α β : Type} (xs : List α) (b : β) (f g : α → β → Id (ForInStep β))
    (h : ∀ x s, f x s = g x s) : forIn xs b f = forIn xs b g := by
  have : f = g := funext fun x => funext fun s => h x s
  rw [this]

theorem range_forIn_body_eq {β : Type} (r : Std.Legacy.Range) (b : β) (f g : Nat → β → Id (ForInStep β))
    (h : ∀ x s, f x s = g x s) : forIn r b f = forIn r b g := by
  have : f = g := funext fun x => funext fun s => h x s
  rw [this]

/-- The symbol token (lex.cpp:1163-1218) never reports its loop as hanging on a file without NUL:
the replica's `file.size + 2` iterations always reach the loop's `break`. -/
theorem lexSymbol_never_hangs (p : P) (hnf : NulFree p.file) (fs : Bool) (w : String) :
    (lexSymbol p fs).1 ≠ .hang w := by
  unfold lexSymbol
  simp only [Id.run]
  split
  · simp [pure]
  · generalize hr : (forIn [:p.file.size + 2] (p, false) _ : Id (P × Bool)) = r
    rw [range_forIn_body_eq _ _ _ (fun _ s => pure (symF s)) (by
      intro x s
      simp only [symF]
      cases hs : symbolStep s.1 <;> simp only [hs])] at hr
    rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hr
    have hdone : r.2 = true := by
      rw [← hr]
      exact symbol_loop_done p hnf false _ (by simp)
    simp only [bind, hdone, Bool.not_true, Bool.false_eq_true, ite_false]
    repeat' split
    all_goals simp [pure, mk]

end Jank.R3.Proofs.Lex

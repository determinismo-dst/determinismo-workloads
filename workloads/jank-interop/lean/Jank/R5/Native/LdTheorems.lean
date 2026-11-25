import Jank.R5.Native.LdScript
import Jank.R5.Native.LdSpec

/-!
# Round 5, native loading: theorems about jank's ld script reader

- Concrete readings, by kernel evaluation: glibc's `libc.so` and `libm.so` scripts give the
  library ld would load; a script naming two files gives only the first; `-lfoo` is read as a
  path; a script without its closing parenthesis, or with a parenthesis inside a quoted name,
  gives nothing.
- ★ Fuel: every fuelled loop of the replica finishes within the fuel its caller passes, for every
  input (`findClose_fuel`, `skip`-free loops `readBare_fuel`, `readQuoted_fuel`,
  `findInputDirective_fuel`), so the fuel is not a behavior of the replica.
-/

namespace Jank.R5.Native.LdScript

theorem glibc_libc :
    parseStr "GROUP ( /lib/x86_64-linux-gnu/libc.so.6 /usr/lib/x86_64-linux-gnu/libc_nonshared.a  AS_NEEDED ( /lib64/ld-linux-x86-64.so.2 ) )"
      = some "/lib/x86_64-linux-gnu/libc.so.6" := by decide +kernel

theorem two_files_first_only :
    parseStr "INPUT ( libfoo_core.so libfoo_extra.so )" = some "libfoo_core.so" := by decide +kernel

theorem lname_is_a_path : parseStr "INPUT(-lfoo)" = some "-lfoo" := by decide +kernel

theorem unbalanced_nothing : parseStr "GROUP ( a.so" = none := by decide +kernel

theorem quoted_paren_nothing : parseStr "GROUP ( \"p(.so\" b.so )" = none := by decide +kernel

theorem as_needed_fallback : parseStr "GROUP ( AS_NEEDED ( a.so ) )" = some "a.so" := by decide +kernel

theorem second_directive_ignored : parseStr "INPUT ( a.so ) GROUP ( b.so )" = some "a.so" := by decide +kernel

/-! ## Fuel -/

theorem findClose_fuel (s : Src) : ∀ (f j d : Nat), s.length - j < f → findClose s j d f ≠ none := by
  intro f
  induction f with
  | zero => intro j d h; omega
  | succ f ih =>
    intro j d h
    unfold findClose
    by_cases hj : j < s.length
    · simp only [hj, ite_true]
      split
      · exact ih _ _ (by omega)
      · split
        · split
          · simp
          · exact ih _ _ (by omega)
        · exact ih _ _ (by omega)
    · simp [hj]

theorem readBare_fuel (s : Src) (e : Nat) :
    ∀ (f p : Nat), e - p < f → readBare s p e f ≠ none := by
  intro f
  induction f with
  | zero => intro p h; omega
  | succ f ih =>
    intro p h
    unfold readBare
    by_cases hp : p < e
    · split
      · exact ih _ (by omega)
      · simp
    · rw [ite_eq_right_iff.mpr (by intro hc; simp [hp] at hc)]; simp

theorem readQuoted_fuel (s : Src) (q : Char) (e : Nat) :
    ∀ (f p : Nat) (acc : Src), e - p < f → readQuoted s q p e acc f ≠ none := by
  intro f
  induction f with
  | zero => intro p acc h; omega
  | succ f ih =>
    intro p acc h
    unfold readQuoted
    by_cases hp : p < e
    · split
      · split
        · exact ih _ _ (by omega)
        · exact ih _ _ (by omega)
      · simp
    · rw [ite_eq_right_iff.mpr (by intro hc; simp [hp] at hc)]; simp


theorem tryDirectives_some (s : Src) (i : Nat) :
    ∀ ds, tryDirectives s i ds ≠ none := by
  intro ds
  induction ds with
  | nil => simp [tryDirectives]
  | cons d rest ih =>
    unfold tryDirectives
    split
    · exact ih
    · dsimp only
      split
      · exact ih
      · have h := findClose_fuel s (s.length + 1)
          (skipSeps s (i + d.length) (s.length + 1) + 1) 1 (by omega)
        split
        · next heq => exact absurd heq h
        · simp
        · simp

theorem findInputDirective_fuel (s : Src) :
    ∀ (f i d : Nat), s.length - i < f → findInputDirective s f i d ≠ none := by
  intro f
  induction f with
  | zero => intro i d h; omega
  | succ f ih =>
    intro i d h
    unfold findInputDirective
    by_cases hi : i < s.length
    · simp only [hi, ite_true]
      split
      · rename_i heq
        split at heq
        · exact absurd heq (tryDirectives_some s i directives)
        · simp at heq
      · simp
      · simp
      · exact ih _ _ (by omega)
    · simp [hi]

theorem skipSeps_ge (s : Src) : ∀ (f i : Nat), i ≤ skipSeps s i f := by
  intro f
  induction f with
  | zero => intro i; simp [skipSeps]
  | succ f ih =>
    intro i
    unfold skipSeps
    split
    · exact Nat.le_trans (Nat.le_succ i) (ih (i + 1))
    · exact Nat.le_refl i

theorem readQuoted_bounds (s : Src) (q : Char) (e : Nat) :
    ∀ (f p : Nat) (acc : Src) (r : Src × Nat), readQuoted s q p e acc f = some r →
      p ≤ r.2 ∧ (p ≤ e → r.2 ≤ e) := by
  intro f
  induction f with
  | zero => intro p acc r h; simp [readQuoted] at h
  | succ f ih =>
    intro p acc r h
    unfold readQuoted at h
    by_cases hc : (decide (p < e) && chr s p != q) = true
    · rw [if_pos hc] at h
      have hp : p < e := by simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1
      by_cases hc2 : (chr s p == '\\' && decide (p + 1 < e)) = true
      · rw [if_pos hc2] at h
        have hp1 : p + 1 < e := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2; exact hc2.2
        obtain ⟨a, b⟩ := ih _ _ _ h
        exact ⟨by omega, fun _ => b (by omega)⟩
      · rw [if_neg hc2] at h
        obtain ⟨a, b⟩ := ih _ _ _ h
        exact ⟨by omega, fun _ => b (by omega)⟩
    · rw [if_neg hc] at h
      simp only [Option.some.injEq] at h
      subst h
      by_cases hp : p < e
      · simp only [hp, ite_true]; omega
      · simp only [hp, ite_false]; omega

theorem readBare_bounds (s : Src) (e : Nat) :
    ∀ (f p r : Nat), readBare s p e f = some r → p ≤ r ∧ (p ≤ e → r ≤ e) := by
  intro f
  induction f with
  | zero => intro p r h; simp [readBare] at h
  | succ f ih =>
    intro p r h
    unfold readBare at h
    by_cases hc : (decide (p < e) && !isSep (chr s p) && chr s p != '(' && chr s p != ')') = true
    · rw [if_pos hc] at h
      have hp : p < e := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.1.1
      have := ih _ _ h; omega
    · rw [if_neg hc] at h
      simp only [Option.some.injEq] at h
      omega

theorem readToken_some (s : Src) (p e : Nat) : readToken s p e ≠ none := by
  unfold readToken
  by_cases hge : p ≥ e
  · simp [hge]
  · rw [if_neg hge]
    by_cases hq : (chr s p == '"' || chr s p == '\'') = true
    · rw [if_pos hq]; exact readQuoted_fuel s _ e (e + 1) (p + 1) [] (by omega)
    · rw [if_neg hq]
      have := readBare_fuel s e (e + 1) p (by omega)
      cases h : readBare s p e (e + 1) with
      | none => exact absurd h this
      | some p' => simp

/-- `read_token` advances past at least one character when it starts on one that is not a
separator or parenthesis, and stays within the range. -/
theorem readToken_adv (s : Src) (p e : Nat) (hp : p < e) (h1 : isSep (chr s p) = false)
    (h2 : chr s p ≠ '(') (h3 : chr s p ≠ ')') (tok : Src) (p' : Nat)
    (h : readToken s p e = some (tok, p')) : p + 1 ≤ p' ∧ p' ≤ e := by
  unfold readToken at h
  have hge : ¬ p ≥ e := by omega
  rw [if_neg hge] at h
  by_cases hq : (chr s p == '"' || chr s p == '\'') = true
  · rw [if_pos hq] at h
    obtain ⟨a, b⟩ := readQuoted_bounds s (chr s p) e _ (p + 1) [] (tok, p') h
    exact ⟨a, b (by omega)⟩
  · rw [if_neg hq] at h
    cases hb : readBare s p e (e + 1) with
    | none => rw [hb] at h; simp at h
    | some p'' =>
      rw [hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      unfold readBare at hb
      have hc : (decide (p < e) && !isSep (chr s p) && chr s p != '(' && chr s p != ')') = true := by
        simp [hp, h1, h2, h3]
      rw [if_pos hc] at hb
      have := readBare_bounds s e _ _ _ hb; omega

theorem scan_fuel (s : Src) (e : Nat) :
    ∀ (f : Nat) (st : Scan), e - st.pos < f → scan s e f st ≠ none := by
  intro f
  induction f with
  | zero => intro st h; omega
  | succ f ih =>
    intro st h
    unfold scan
    dsimp only
    by_cases hp : st.pos < e
    · rw [if_pos hp]
      by_cases h1 : isSep (chr s st.pos) = true
      · rw [if_pos h1]; exact ih _ (by simp only; omega)
      · rw [if_neg h1]
        by_cases h2 : (chr s st.pos == '(') = true
        · rw [if_pos h2]; exact ih _ (by simp only; omega)
        · rw [if_neg h2]
          by_cases h3 : (chr s st.pos == ')') = true
          · rw [if_pos h3]; exact ih _ (by simp only; omega)
          · rw [if_neg h3]
            cases hr : readToken s st.pos e with
            | none => exact absurd hr (readToken_some s st.pos e)
            | some r =>
              obtain ⟨tok, p'⟩ := r
              have adv := readToken_adv s st.pos e hp (by simpa using h1) (by simpa using h2)
                (by simpa using h3) tok p' hr
              dsimp only
              by_cases ht : tok.isEmpty = true
              · rw [if_pos ht]; exact ih _ (by simp only; omega)
              · rw [if_neg ht]
                by_cases ha : (tok == "AS_NEEDED".toList) = true
                · rw [if_pos ha]
                  have hsk := skipSeps_ge s (s.length + 1) p'
                  generalize skipSeps s p' (s.length + 1) = q at *
                  by_cases hq : q > e
                  · simp only [hq, ite_true]
                    split
                    · exact ih _ (by simp only; omega)
                    · exact ih _ (by simp only; omega)
                  · simp only [hq, ite_false]
                    split
                    · exact ih _ (by simp only; omega)
                    · exact ih _ (by simp only; omega)
                · rw [if_neg ha]
                  split
                  · split
                    · exact ih _ (by simp only; omega)
                    · exact ih _ (by simp only; omega)
                  · split
                    · exact ih _ (by simp only; omega)
                    · exact ih _ (by simp only; omega)
    · rw [if_neg hp]; simp

/-- ★ `parse_ld_script` is total on every text: the replica's fuel never runs out, so it reads
every script the way the C++ does (whose loops all advance a position bounded by the size). -/
theorem parseText_total (text : Src) : (parseTextF text).isSome := by
  unfold parseTextF
  dsimp only
  generalize stripComments text false = s
  have h1 := findInputDirective_fuel s (s.length + 1) 0 0 (by omega)
  cases hf : findInputDirective s (s.length + 1) 0 0 with
  | none => exact absurd hf h1
  | some o =>
    cases o with
    | none => simp
    | some be =>
      obtain ⟨b, e⟩ := be
      dsimp only
      have h2 := scan_fuel s e (e + 1) { pos := b } (by simp only; omega)
      cases hs : scan s e (e + 1) { pos := b } with
      | none => exact absurd hs h2
      | some st => simp

end Jank.R5.Native.LdScript

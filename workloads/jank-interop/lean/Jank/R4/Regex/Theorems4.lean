-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (with round 3's regex replica; see README.md)
import Jank.R4.Regex.Matcher

/-!
# Round 4 regex theorems (no `sorry`, no `native_decide`, no new axiom)

For every input:
- `jankEval4_pattern_nul`: `re-pattern` of `s ++ NUL ++ t` is the pattern `s` (re_pattern.cpp 9
  builds the `std::regex` from `c_str()`), for every call, input and locale.
- `jNth_str_never_str`, `nth_no_groups_never_the_match`: on a matcher whose pattern has no groups,
  jank's `nth` reads the match string's bytes, so it never returns a string (Clojure's `(nth m 0)`
  is the match string).
- `nth_without_match_nil`: before any match jank's `(nth m n)` is nil for every `n ≥ 0`
  (Clojure throws `IllegalStateException`).
- `print_pattern_differs`: jank's `print` of a pattern never equals Clojure's `#"…"`.
- `searchFromFirst_starts_clean`: every start position of a libstdc++ search starts from the
  results the search began with (`_M_cur_results = _M_results`), the mechanism behind the
  lookahead-capture deviation.
-/

namespace Jank.R4.Regex

open Jank.R3.Regex

theorem takeWhile_ne_zero_of_no_nul (s : List Nat) (h : 0 ∉ s) : s.takeWhile (· != 0) = s := by
  induction s with
  | nil => rfl
  | cons a r ih =>
    have ha : a ≠ 0 := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : 0 ∉ r := fun e => h (List.mem_cons_of_mem _ e)
    have hb : (a != 0) = true := bne_iff_ne.mpr ha
    simp [List.takeWhile, hb, ih hr]

theorem takeWhile_ne_zero_append_nul (s t : List Nat) (h : 0 ∉ s) :
    (s ++ 0 :: t).takeWhile (· != 0) = s := by
  induction s with
  | nil => simp [List.takeWhile]
  | cons a r ih =>
    have ha : a ≠ 0 := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : 0 ∉ r := fun e => h (List.mem_cons_of_mem _ e)
    simp [List.takeWhile, ha, ih hr]

/-- `(re-pattern (str s "\u0000" t))` is `(re-pattern s)` for every call, input and limits. -/
theorem jankEval4_pattern_nul (loc : Loc) (q : Q) (s t : List Nat) (lim : Lim) (h : 0 ∉ s) :
    jankEval4 loc {} { q with pat := s ++ 0 :: t } lim = jankEval4 loc {} { q with pat := s } lim := by
  simp only [jankEval4, takeWhile_ne_zero_append_nul s t h, takeWhile_ne_zero_of_no_nul s h] <;> rfl

/-- jank's `nth` on the groups object of a pattern without groups (a string) never yields a
string. -/
theorem jNth_str_never_str (b : List Nat) (n : Int) (o : Option Unit) (b' : List Nat) :
    jNth (.str b) n o ≠ .str b' := by
  rcases o with _ | u
  all_goals
    unfold jNth
    by_cases hn : n < 0
    · simp [hn]
    · simp only [hn, if_false]
      split <;> simp

/-- For every match of a pattern without groups (`smatch_to_vector` of one sub-match is the match
string), jank's `(nth m k)` and `(nth m k nf)` never return a string; Clojure's `(nth m 0)` is the
match string. -/
theorem nth_no_groups_never_the_match (inp : Array Nat) (m : MatchRes) (hm : m.size = 1)
    (n : Int) (o : Option Unit) (b' : List Nat) :
    jNth (smatchToVector inp m) n o ≠ .str b' := by
  have : smatchToVector inp m = .str ((m.get 0).str inp) := by
    unfold smatchToVector
    simp [hm]
  rw [this]
  exact jNth_str_never_str _ n o b'

/-- Before any match (groups nil), jank's `(nth m n)` is nil for every `n ≥ 0`. -/
theorem nth_without_match_nil (n : Int) (h : 0 ≤ n) : jNth .nil n none = .nil := by
  unfold jNth
  have hn : ¬ n < 0 := by omega
  simp [hn]

theorem cljPrint_go_length (f : Nat) : ∀ (p : List Nat) (q : Bool), p.length < f →
    p.length ≤ (cljPrintPattern.go f p q).length := by
  induction f with
  | zero => intro p q h; omega
  | succ f ih =>
    intro p q hf
    cases p with
    | nil => simp [cljPrintPattern.go]
    | cons c rest =>
      have hr : rest.length < f := by simp at hf; omega
      by_cases h1 : c = 0x5C
      · subst h1
        cases rest with
        | nil => simp [cljPrintPattern.go]
        | cons c2 r2 =>
          have h2 : r2.length < f := by simp at hr; omega
          have := ih r2 (if q then c2 != 0x45 else c2 == 0x51) h2
          simp only [cljPrintPattern.go, beq_self_eq_true, ite_true, List.length_append,
            List.length_cons, List.length_nil]
          omega
      · by_cases h2 : c = 0x22
        · subst h2
          cases q
          · have := ih rest false hr
            simp [cljPrintPattern.go]
            omega
          · have := ih rest true hr
            simp [cljPrintPattern.go]
            omega
        · have := ih rest q hr
          have h1' : (c == 0x5C) = false := by simp [h1]
          have h2' : (c == 0x22) = false := by simp [h2]
          simp only [cljPrintPattern.go, h1', h2', Bool.false_eq_true, ite_false, List.length_cons]
          omega

/-- jank's `print` of a pattern (its text) is never Clojure's `print-method` output (`#"…"`). -/
theorem print_pattern_differs (p : List Nat) : jankPrintPattern p ≠ cljPrintPattern p := by
  intro h
  have hl := congrArg List.length h
  have := cljPrint_go_length (p.length + 1) p false (by omega)
  simp only [jankPrintPattern, cljPrintPattern, List.length_append, List.length_cons, List.length_nil] at hl
  omega

/-- Every start position of `_M_search` runs `_M_main_dispatch`, which starts from
`_M_cur_results = _M_results`: what an earlier position's lookahead copied into the current
results is gone. -/
theorem searchFromFirst_starts_clean (c : Ctx) (fuel : Nat) (mode : Mode) (st : ExSt) :
    (searchFromFirst c fuel mode).run st =
      ((do dfs c fuel mode 0 false; return (← get).hasSol : EM Bool).run
        { st with cur := st.begin, hasSol := false, curRes := st.res }) := by
  simp only [searchFromFirst, StateT.run_bind, StateT.run_modify, pure_bind]

end Jank.R4.Regex

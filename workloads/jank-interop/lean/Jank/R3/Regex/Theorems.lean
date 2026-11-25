import Jank.R3.Regex.JankFns

/-!
# Theorems about the replica (no `sorry`, no `native_decide`)

General statements (for every input) about the paths the deviations take, and a few concrete
programs checked by the kernel (`decide` runs the replica: scanner, compiler, executor).
-/

namespace Jank.R3.Regex

/-! ## Bracket ranges compare signed `char`s (RX: a range from ASCII to a byte ≥ 0x80) -/

/-- Every byte ≥ 0x80 is a negative `char`, below every ASCII one. -/
theorem sval_high_lt_ascii (l r : Nat) (hl : l < 128) (hr1 : 128 ≤ r) (hr2 : r < 256) :
    sval r < sval l := by
  unfold sval
  simp only [hl, if_true, show ¬ r < 128 by omega, if_false]
  omega

/-- `_M_make_range` rejects every range `[x-y]` from an ASCII `x` to a byte `y` ≥ 0x80 (the
first byte of any non-ASCII character in UTF-8), whatever the bracket so far. -/
theorem makeRange_rejects_ascii_to_high (b : Bracket) (l r : Nat) (st : CState) (hl : l < 128)
    (hr1 : 128 ≤ r) (hr2 : r < 256) :
    makeRange b l r st = .error (rxErr .range "Invalid range in bracket expression.") := by
  have h := sval_high_lt_ascii l r hl hr1 hr2
  simp [makeRange, cthrow, show sval l > sval r from h]

/-! ## `$` (R79), unmatched groups (R80), NUL (R83) -/

/-- Without `multiline`, `_M_at_end` holds only at the end: never before a final newline. -/
theorem dollar_only_at_end (c : Ctx) (st : ExSt) (h : c.fix.javaDollar = false) :
    atEnd c st = true → st.cur = c.end_ := by
  unfold atEnd
  split <;> simp_all

/-- `smatch_to_vector` never gives nil for a group: an unmatched one is `""`. -/
theorem smatch_groups_never_nil (inp : Array Nat) (m : MatchRes) (xs : List (Option (List Nat))) :
    smatchToVector inp m = .vec xs → ∀ x ∈ xs, x.isSome := by
  unfold smatchToVector
  split
  · intro h; cases h
  · split
    · intro h; cases h
    · intro h x hx
      cases h
      simp only [List.mem_map] at hx
      obtain ⟨_, _, rfl⟩ := hx
      rfl

theorem cstr_of_no_nul (s : List Nat) (h : 0 ∉ s) : cstr s = s := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    have ha : a ≠ 0 := fun e => h (e ▸ List.mem_cons_self ..)
    have ht : 0 ∉ t := fun e => h (List.mem_cons_of_mem _ e)
    simp [cstr, ha] at ih ⊢
    exact ih ht

theorem cstr_append_nul (s t : List Nat) (h : 0 ∉ s) : cstr (s ++ 0 :: t) = s := by
  induction s with
  | nil => simp [cstr]
  | cons a r ih =>
    have ha : a ≠ 0 := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : 0 ∉ r := fun e => h (List.mem_cons_of_mem _ e)
    simp [cstr, ha] at ih ⊢
    exact ih hr

/-- R83 for every input: `re-find` never looks past the first NUL. -/
theorem reFind_stops_at_nul (nfa : NFA) (s t : List Nat) (lim : Lim) (h : 0 ∉ s) :
    jReFind nfa (s ++ 0 :: t) lim = jReFind nfa s lim := by
  unfold jReFind
  rw [cstr_append_nul s t h, cstr_of_no_nul s h]

/-- R83 for every input: neither does `re-matches`. -/
theorem reMatches_stops_at_nul (nfa : NFA) (s t : List Nat) (lim : Lim) (h : 0 ∉ s) :
    jReMatches nfa (s ++ 0 :: t) lim = jReMatches nfa s lim := by
  unfold jReMatches
  rw [cstr_append_nul s t h, cstr_of_no_nul s h]

/-! ## The ECMAScript template `$nn` (R84) -/

/-- `match_results::format` reads two digits after `$` whenever two follow, and writes nothing
when that number is not a group: `"$12"` with fewer than 13 sub-matches is "" (Java: group 1,
then "2"). -/
theorem format_two_digits_out_of_range (m : MatchRes) (inp : Array Nat) (d1 d2 : Nat)
    (h1 : isDigitC d1 = true) (h2 : isDigitC d2 = true)
    (hn : m.size ≤ (d1 - 0x30) * 10 + (d2 - 0x30)) :
    format m inp [0x24, d1, d2] = [] := by
  have hd1 : d1 ≠ 0x24 ∧ d1 ≠ 0x26 ∧ d1 ≠ 0x60 ∧ d1 ≠ 0x27 := by
    simp [isDigitC] at h1; omega
  have hlt : ¬ ((d1 - 0x30) * 10 + (d2 - 0x30) < m.size) := by omega
  simp [format, format.go, List.span, List.span.loop, hd1.1, hd1.2.1, hd1.2.2.1, hd1.2.2.2, h1, h2, hlt]

/-! ## `re-seq` (R81): a find that leaves the input as it was repeats forever -/

/-- Whenever one `re_find` returns a match and leaves `match_input` unchanged (an empty match at
its start), `re-seq` is infinite: that match, again and again. -/
theorem reSeq_infinite_of_stuck (nfa : NFA) (s : List Nat) (lim : Lim) (g : V) (m' : JMatcher)
    (st : Stats) (hg : g ≠ .nil)
    (h : jReFindM nfa { input := cstr s } lim = .ok (g, m', st)) (hm : m'.input = cstr s) :
    jReSeq nfa s lim = .infinite [g, g] := by
  unfold jReSeq
  simp only [jReSeq.go, h]
  cases g with
  | nil => exact absurd rfl hg
  | _ => simp [hm]

/-! ## Lookahead (RX): the sub-executor starts a new input -/

/-- `_M_lookahead`'s sub-executor (replica, no toggle) begins at the current position; unless the
search had already moved past its first position (`match_prev_avail`), `^` holds there, whatever
was consumed before. -/
theorem lookahead_caret_holds (c : Ctx) (outer : ExSt) (hfix : c.fix = {})
    (hpa : outer.flags.prevAvail = false) (hbol : outer.flags.notBol = false) :
    atBegin (lookSub c outer) = true := by
  simp [lookSub, atBegin, hfix, hpa, hbol]

/-- In the same situation, `\b` at the lookahead's start ignores the character before it: it
is a boundary exactly when the next character is a word character. -/
theorem lookahead_boundary_ignores_left (c : Ctx) (outer : ExSt) (hfix : c.fix = {})
    (hpa : outer.flags.prevAvail = false) (hbow : outer.flags.notBow = false)
    (heow : outer.flags.notEow = false) :
    wordBoundary c (lookSub c outer) = (outer.cur != c.end_ && isWord c.nfa.loc (c.at outer.cur)) := by
  simp [lookSub, wordBoundary, hfix, hpa, hbow, heow]

end Jank.R3.Regex

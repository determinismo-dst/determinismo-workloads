import Jank.Codegen.Opt
import Jank.Codegen.Value
import Jank.Codegen.Exec

/-!
# Theorems about the code generator's replica

Each states, for every input, a fact behind a reported deviation (or a fact that rules one out).
No `sorry`, no `native_decide`.
-/

namespace Jank.Codegen.Theorems

open Jank.Codegen Jank.Codegen.Exec

/-! ## G10: `rewrite_uses` leaves a `case`'s value and a `loop`'s binding values alone -/

/-- For every rename, a `case_` instruction keeps the value it dispatches on
(rewrite.cpp `case instruction_kind::case_` rewrites only the case blocks and the merge block). -/
theorem rewrite_keeps_case_value (n : Ident) (s k : Int) (v : Ident) (cs : List (Int × Ident))
    (d m old new : Ident) :
    ∃ cs' m', ((Inst.case_ n s k v cs d m).rewriteUses old new).1 = .case_ n s k v cs' d m' := by
  exact ⟨_, _, rfl⟩

/-- For every rename, a `loop` keeps its binding shadows (their initial values included). -/
theorem rewrite_keeps_loop_values (n lb : Ident) (mb : Option Ident) (sh : Option (Ident × Jank.Analyzer.CppType))
    (bs : List LoopShadow) (old new : Ident) :
    ∃ lb' mb' sh', ((Inst.loop n lb mb sh bs).rewriteUses old new).1 = .loop n lb' mb' sh' bs := by
  exact ⟨_, _, _, rfl⟩

/-! ## G8: a `case` on a long beyond the 32-bit range dispatches on a hash -/

/-- `jank_shift_mask_case_integer(x, 0, 0)` of an integer at least 2^32, or below -2^31, is never
`x` itself: it is `hash::integer(x)`, a `u32`. So `case` with that test and no shift/mask (the
macro's keys are the test values themselves) never takes the test's branch. -/
theorem case_integer_not_self (x : Int) (h : x ≥ 4294967296 ∨ x < -2147483648) :
    shiftMaskCaseInteger (.int x) 0 0 ≠ x := by
  have hb := (hashInteger x).toNat_lt
  have hm : ((0 : Int) != 0) = false := by decide
  simp only [shiftMaskCaseInteger, toCaseIntegerOrHash, hm, Bool.false_eq_true, ↓reduceIte]
  split <;> omega

/-! ## G13: a `char const *` parameter stops at the first NUL -/

/-- What `strlen` keeps of a byte string with a NUL byte is strictly shorter: a string literal
with an embedded NUL passed to `_jank_string(char const *)` (or a character, a symbol's name) loses
everything from the NUL on. -/
theorem cstring_drops_after_nul (bs : List UInt8) (h : (0 : UInt8) ∈ bs) :
    (cString bs).length < bs.length := by
  unfold cString
  induction bs with
  | nil => simp at h
  | cons b rest ih =>
    by_cases hb : b = 0
    · subst hb; simp [List.takeWhile]
    · have hr : (0 : UInt8) ∈ rest := by
        cases h with
        | head => exact absurd rfl hb
        | tail _ h => exact h
      have : (b != 0) = true := by simp [hb]
      simp [List.takeWhile, this]
      exact ih hr

/-! ## G14: `ratio::create(i64, i64)` reads a literal above `LLONG_MAX` as negative -/

/-- An integer literal in [2^63, 2^64) has type `unsigned long long`; converted to the `i64`
parameter of `ratio::create(i64, i64)` (the overload chosen for integer arguments) it is
negative (C++20: modulo 2^64). -/
theorem big_literal_negative (d : Int) (h1 : 9223372036854775808 ≤ d) (h2 : d < 18446744073709551616) :
    toI64 d < 0 := by
  unfold toI64
  rw [BitVec.toInt_ofInt]
  simp only [Int.bmod]
  omega

/-! ## util::escape is undone by C++'s reading of a string literal -/

/-- A C++ simple escape sequence's value ([lex.ccon] Table 9), by the byte after the backslash. -/
def simpleEscape (c : UInt8) : Option UInt8 :=
  if c == 110 then some 10 else if c == 116 then some 9 else if c == 114 then some 13
  else if c == 92 then some 92 else if c == 34 then some 34 else if c == 97 then some 7
  else if c == 118 then some 11 else if c == 102 then some 12 else if c == 98 then some 8
  else if c == 39 then some 39 else if c == 63 then some 63 else none

/-- The bytes of a narrow string literal's body made only of characters and simple escapes
(what `util::escape` writes), read as C++ does; `none` for anything else. -/
def cppDecode : List UInt8 → Option (List UInt8)
  | [] => some []
  | b :: rest =>
    if b == 92 then
      match rest with
      | c :: rest' => (simpleEscape c).bind fun v => (cppDecode rest').map (v :: ·)
      | [] => none
    else (cppDecode rest).map (b :: ·)

theorem cppDecode_cons (b : UInt8) (rest : List UInt8) (h : (b == 92) = false) :
    cppDecode (b :: rest) = (cppDecode rest).map (b :: ·) := by
  rw [cppDecode.eq_def]
  simp [h]

theorem decode_escapeByte (b : UInt8) (rest : List UInt8) :
    cppDecode (escapeByte b ++ rest) = (cppDecode rest).map (b :: ·) := by
  unfold escapeByte
  split <;> rename_i h <;> simp [cppDecode, simpleEscape]
  all_goals first
    | (have hb : b = UInt8.ofNat b.toNat := (UInt8.ofNat_toNat).symm
       rw [h] at hb; subst hb; rfl)
    | (have h92 : b ≠ 92 := by
         intro e; subst e; simp_all
       have hf : (b == 92) = false := by simp [h92]
       exact cppDecode_cons b rest hf)

/-- For every byte string, the C++ string literal `"` + `escape(s)` + `"` holds exactly `s`:
`util::escape` loses nothing (a NUL included); what can lose bytes is the `char const *`
receiving the literal (`cstring_drops_after_nul`). -/
theorem decode_escape (bs : List UInt8) : cppDecode (escape bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    have e : escape (b :: rest) = escapeByte b ++ escape rest := by unfold escape; simp
    rw [e, decode_escapeByte, ih]
    rfl

end Jank.Codegen.Theorems

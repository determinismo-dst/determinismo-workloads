import Std.Tactic.BVDecide
import Jank.Lex
import Jank.Read
import Jank.ReadRoundtrip

/-!
# Theorems about the reader model

The lexer's and parser's top-level functions are `partial` (their loops run under fuel), so the
theorems are about the pieces they are built from: one iteration of each loop, the C library
models, the fixed-width arithmetic.
-/

namespace Jank.LexTheorems

open Jank.LexBytes Jank.Lex

/-- `mbrtowc` reads a NUL byte as the null wide character with length 0 (C11 7.29.6.3.2). -/
theorem mbrtowc_nul (loc : Locale) (f : Array UInt8) (i : Nat) (hi : i < f.size) (h0 : f[i]! = 0) :
    mbrtowc loc f i = .ok 0 0 := by
  unfold mbrtowc
  simp [h0, Nat.not_le.mpr hi]

/-- NUL is a symbol character for `is_symbol_char` (lex.cpp:499): not a space, not special, and
`is_utf8_char(0)`. -/
theorem nul_is_symbol_char (loc : Locale) : isSymbolChar loc 0 = true := by
  cases loc <;> decide

/-- `peek()` on a NUL byte: the code point 0 with length 0. -/
theorem peek_nul (p : P) (hi : p.pos + 1 < p.file.size) (h0 : p.file[p.pos + 1]! = 0) :
    p.peek 1 = some ⟨0, 0⟩ := by
  unfold P.peek P.decode
  simp [Nat.not_le.mpr hi, mbrtowc_nul p.loc p.file (p.pos + 1) hi h0]

/-- The symbol, keyword and character loops (lex.cpp:1183, 1282, 612) do not advance on a NUL:
the iteration maps the state to itself, so the C++ `while(true)` never ends. -/
theorem symbol_loop_stuck_on_nul (p : P) (hi : p.pos + 1 < p.file.size) (h0 : p.file[p.pos + 1]! = 0) :
    symbolStep p = .next p := by
  unfold symbolStep
  rw [peek_nul p hi h0]
  simp [nul_is_symbol_char]

/-- The string loop (lex.cpp:1325) does not advance on a NUL either (escaped or not, the state
returns to itself after at most one iteration). -/
theorem string_loop_stuck_on_nul (p : P) (hi : p.pos + 1 < p.file.size) (h0 : p.file[p.pos + 1]! = 0) :
    stringStep (p, false) = some (.next (p, false)) ∧
    stringStep (p, true) = some (.next (p, false)) := by
  simp [stringStep, peek_nul p hi h0]

/-- The comment loops (lex.cpp:635 for `;`, 1397 for `#!`) do not advance on a NUL. -/
theorem comment_loop_stuck_on_nul (p : P) (hi : p.pos + 1 < p.file.size) (h0 : p.file[p.pos + 1]! = 0) :
    commentStep p = .next p := by
  unfold commentStep
  rw [peek_nul p hi h0]
  simp

/-- A comment ends at `\n` only: a `\r` (13) is part of it (Clojure's CommentReader also stops
at `\r`). -/
theorem comment_continues_past_cr (p : P) (hi : p.pos + 1 < p.file.size) (h : p.file[p.pos + 1]! = 13) :
    commentStep p = .next { p with pos := p.pos + 1 } := by
  unfold commentStep P.peek P.decode mbrtowc
  simp [Nat.not_le.mpr hi, h]

/-- The integer path negates `strtoll` of the digits after the `-` (lex.cpp:1145-1146): a
non-negative i64 negated is never INT64_MIN, so `-9223372036854775808` can only be read as a
big integer (its digits overflow `strtoll`). -/
theorem negated_digits_never_min (x : BitVec 64) (h : x.msb = false) :
    -x ≠ 0x8000000000000000#64 := by
  bv_decide

/-- The radix of `NNNrDDD` is `static_cast<i8>(std::stoi(...))` (lex.cpp:1083): 258 wraps to 2,
so `258r11` reads as 3 (Clojure: radix at most two digits, an error). -/
theorem radix_258_is_2 : toI8 258 = 2 := by decide

/-- 130 wraps to -126, then negated to 126: out of range (an error, as in Clojure). -/
theorem radix_130 : toI8 130 = -126 := by decide

/-- `util::escape` (escape.cpp:148) prints a NUL byte as it is. -/
theorem escape_keeps_nul : Jank.ReadRoundtrip.jankEscape [0] = [0] := by decide

/-- `get_literal_from_char_bytes` (character.cpp:12) prints `(char 0)` as `\` and a NUL byte. -/
theorem char_nul_printed_raw : Jank.ReadRoundtrip.jankCharPr 0 = [92, 0] := by decide

end Jank.LexTheorems

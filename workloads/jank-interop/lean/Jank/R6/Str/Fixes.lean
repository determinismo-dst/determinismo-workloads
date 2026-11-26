import Jank.StrModel
import Jank.R6.Str.Proofs

/-!
# Round 6, strings: the fixes, modeled beside jank's code and Clojure's

Each `…Fixed` function is the C++ (or .jank) of one `fixes/<id>.diff`, written the way the diff
computes it; the unfixed function is round 2's (`Jank.Str`) or, where round 2 kept only a sign, the
exact value here. `Jank.R6.Str.Search` walks every text of a bound through all three.

Assumption StrA6-1: glibc's x86-64 `memcmp` returns the difference of the first differing bytes
(`movzbl`/`subl` in `__memcmp_avx2_movbe` and `__memcmp_evex_movbe` for a 1-byte common length; for
2–3 bytes the big-endian word difference). Only the sign is guaranteed by C; the values below are
used for W9/W10's predictions, which hold for any positive value other than 132.
-/

namespace Jank.R6.Str

open Jank.Str

/-! ## Decoding with a surrogate escape for stray bytes (the R57a diff's `next_units`) -/

/-- UTF-8 bytes to code points, a byte that does not start a complete character becoming
`0xDC00 + byte` (a lone low surrogate, which no valid UTF-8 text decodes to). -/
def decodeLossless : List UInt8 → List Nat
  | [] => []
  | b :: rest =>
    let c := b.toNat
    let n := if c < 0x80 then 1 else if c &&& 0xE0 == 0xC0 then 2 else if c &&& 0xF0 == 0xE0 then 3
      else if c &&& 0xF8 == 0xF0 then 4 else 1
    if n == 1 then (if c < 0x80 then c else 0xDC00 + c) :: decodeLossless rest
    else if rest.length < n - 1 || !((rest.take (n - 1)).all fun x => x.toNat &&& 0xC0 == 0x80) then
      (0xDC00 + c) :: decodeLossless rest
    else
      let lead := c &&& (0x7F >>> n)
      let cp := (rest.take (n - 1)).foldl (fun acc x => acc * 64 + (x.toNat &&& 0x3F)) lead
      cp :: decodeLossless (rest.drop (n - 1))
termination_by bs => bs.length
decreasing_by all_goals simp_all <;> omega

/-! ## compare (R57) -/

/-- java.lang.String.compareTo on units: the first differing units' difference, else the length
difference. -/
def javaCompare (a b : List Nat) : Int :=
  match firstDiff a b with
  | some (x, y) => (x : Int) - y
  | none => (a.length : Int) - b.length

/-- jank today: immutable_string.hpp `compare` 576–584: memcmp over the common length (StrA6-1:
the first differing bytes' difference), else `static_cast<int>(length - s_length)`. -/
def jankCompare (a b : List UInt8) : Int :=
  match firstDiff a b with
  | some (x, y) => (x.toNat : Int) - y.toNat
  | none => (a.length : Int) - b.length

/-- R57a: persistent_string.cpp `compare` walking both texts as UTF-16 units. -/
def jankCompareFixed (a b : List UInt8) : Int :=
  javaCompare ((decodeLossless a).flatMap utf16) ((decodeLossless b).flatMap utf16)

/-- R57b: character.cpp `compare`: the two code points' difference. -/
def jankCharCompareFixed (a b : List UInt8) : Int :=
  ((decodeLossless a).headD 0 : Int) - (decodeLossless b).headD 0

/-! ## index-of / last-index-of starts (R58a) -/

/-- Clojure's `(unchecked-int from-index)`. -/
def uncheckedInt (v : Int) : Int :=
  let m := v % 4294967296
  if m ≥ 2147483648 then m - 4294967296 else m

/-- R58a: string_native.cpp `index_of`: java.lang.String.indexOf's start (negative → 0; at or past
the end: the length for an empty value, else not found), after `unchecked-int`. -/
def jIndexOfFixed (s pat : List UInt8) (fromIndex : Int) : R :=
  let f := uncheckedInt fromIndex
  let n : Int := s.length
  if f ≥ n then (if pat.isEmpty then .int n else .nil)
  else match find s pat (if f < 0 then 0 else f.toNat) with
    | some i => .int i
    | none => .nil

/-- R58a: string_native.cpp `last_index_of`: java.lang.String.lastIndexOf's start (clamped to
`length - value length`; negative → not found). -/
def jLastIndexOfFixed (s pat : List UInt8) (fromIndex : Int) : R :=
  let f := uncheckedInt fromIndex
  let right : Int := (s.length : Int) - pat.length
  let g := if f > right then right else f
  if g < 0 then .nil
  else if pat.isEmpty then .int g
  else match ((List.range (g.toNat + 1)).reverse).find? (fun i => (s.drop i).take pat.length == pat) with
    | some i => .int i
    | none => .nil

/-- Clojure with `unchecked-int` (string.clj 331–338, 352–359) over cIndexOf/cLastIndexOf. -/
def cIndexOf' (s pat : List Nat) (fromIndex : Int) : R := cIndexOf s pat (uncheckedInt fromIndex)
def cLastIndexOf' (s pat : List Nat) (fromIndex : Int) : R := cLastIndexOf s pat (uncheckedInt fromIndex)

/-! ## trim / blank? (R59a, R59b) -/

/-- R59a: string_native.cpp `triml_index`/`trimr_index` test each code point with Java's
`Character.isWhitespace` (a stray byte is not whitespace). -/
def jTrimFixed (s : List UInt8) : R :=
  let cps := decodeLossless s
  .str (((cps.dropWhile javaIsWhitespace).reverse.dropWhile javaIsWhitespace).reverse.flatMap utf8Lossless)
where
  utf8Lossless (c : Nat) : List UInt8 := if 0xDC80 ≤ c ∧ c ≤ 0xDCFF then [(c - 0xDC00).toUInt8] else utf8 c

/-- R59b: immutable_string.hpp `is_blank`, by code point. -/
def jBlankFixed (s : List UInt8) : R := .bool ((decodeLossless s).all javaIsWhitespace)

/-! ## capitalize (R61a), replace "" (R62a), escape (R63a) -/

/-- R61a: util/string.cpp `capitalize` upper-cases the first character (not its first byte) of the
lower-cased text, with the same `towupper` as `to_uppercase`. -/
def jCapitalizeFixed (loc : Locale) (s : List UInt8) : R :=
  match jLower loc s with
  | .str low =>
    match decodeUtf8 low with
    | some [] => .str []
    | some (c :: rest) => .str (utf8 (towupper loc c) ++ rest.flatMap utf8)
    | none => .err "Invalid UTF-8 string."
  | r => r

/-- R62a: string_native.cpp `replace` with an empty match: the replacement around every character. -/
def jReplaceEmptyFixed (s rep : List UInt8) : R :=
  .str ((decodeLossless s).foldr (fun c acc => rep ++ (if 0xDC80 ≤ c ∧ c ≤ 0xDCFF then [(c - 0xDC00).toUInt8] else utf8 c) ++ acc) rep)

/-- R63a: string.jank `escape` walking `(seq s)`: each code-point character looked up. -/
def jEscapeFixed (s key : List UInt8) : R :=
  match decodeUtf8 s with
  | some cps => .str (cps.flatMap fun c => if utf8 c == key then "X".toUTF8.toList else utf8 c)
  | none => .err "Invalid UTF-8 string."

/-! ## seq past the end (R54a) and a cut refused (R52a) -/

/-- R54a: persistent_string_sequence.cpp `next`/`next_in_place` end the walk at `n >= size`. -/
def jSeqFixed (s : List UInt8) : R :=
  if s.isEmpty then .nil else go (s.length + 1) 0 []
where
  go : Nat → Nat → List (List UInt8) → R
    | 0, _, _ => .ub "fuel"
    | fuel + 1, i, acc =>
      match nextCharSize s i with
      | .error e => .err e
      | .ok k =>
        let ch := (s.drop i).take k
        if i + k ≥ s.length then .chars (acc ++ [ch]) else go fuel (i + k) (acc ++ [ch])

/-- A position inside a character: a continuation byte. -/
def insideChar (s : List UInt8) (i : Nat) : Bool := i < s.length && (s.getD i 0).toNat &&& 0xC0 == 0x80

/-- R52a: persistent_string.cpp `substring` refuses a start or end inside a character. -/
def jSubsFixed (s : List UInt8) (start stop : Int) : R :=
  match jSubs s start stop with
  | .str r => if insideChar s start.toNat || insideChar s stop.toNat then .err "index inside a character" else .str r
  | r => r

/-! ## Theorems on the fix models -/

theorem nextCharSize_pos {s : List UInt8} {i k : Nat} (h : nextCharSize s i = .ok k) : 1 ≤ k := by
  simp only [nextCharSize] at h
  split at h
  · cases h; omega
  · split at h
    · cases h; omega
    · split at h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h

/-- ★ R54a: for every byte string, the fixed walk never goes past the end (no `.ub`). -/
theorem jSeqFixed_go_no_ub (s : List UInt8) (fuel i : Nat) (acc : List (List UInt8))
    (hi : i < s.length) (hf : s.length < fuel + i) : ∀ w, jSeqFixed.go s fuel i acc ≠ .ub w := by
  induction fuel generalizing i acc with
  | zero => omega
  | succ f ih =>
    intro w
    simp only [jSeqFixed.go]
    split
    · simp
    · rename_i k hk
      have := nextCharSize_pos hk
      split
      · simp
      · rename_i hlt
        exact ih (i + k) _ (by omega) (by omega) w

theorem jSeqFixed_no_ub (s : List UInt8) : ∀ w, jSeqFixed s ≠ .ub w := by
  intro w
  unfold jSeqFixed
  split
  · simp
  · rename_i hne
    have : 0 < s.length := by cases s <;> simp_all
    exact jSeqFixed_go_no_ub s _ 0 [] this (by omega) w

/-- … while today's walk reads past the end of `(str "a" (nth "é" 0))` (W6). -/
theorem jSeq_cut_ub : ∃ w, jSeq [0x61, 0xC3] = .ub w := ⟨_, rfl⟩
theorem jSeqFixed_cut : jSeqFixed [0x61, 0xC3] = .chars [[0x61], [0xC3]] := by decide

/-- R57: `(compare "é" "")` and `(compare "é" "e")`: Clojure 1 and 132, jank 2 and 94 (StrA6-1),
the fix 1 and 132. -/
theorem w9_values :
    javaCompare (cstr [0xE9]) [] = 1 ∧ jankCompare (jstr [0xE9]) [] = 2 ∧
    javaCompare (cstr [0xE9]) (cstr [0x65]) = 132 ∧ jankCompare (jstr [0xE9]) (jstr [0x65]) = 94 := by
  decide

/-- R58: `(index-of "a" "" 5)` is 1 in Clojure, nil in jank, 1 with R58a. -/
theorem w11_values :
    cIndexOf' [0x61] [] 5 = .int 1 ∧ jIndexOf [0x61] [] 5 = .nil ∧ jIndexOfFixed [0x61] [] 5 = .int 1 ∧
    cIndexOf' [0x61] [0x61] (-1) = .int 0 ∧ jIndexOf [0x61] [0x61] (-1) = .nil ∧
    jIndexOfFixed [0x61] [0x61] (-1) = .int 0 := by
  decide

end Jank.R6.Str

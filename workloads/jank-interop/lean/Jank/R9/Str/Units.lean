import Jank.StrModel
import Jank.R6.Str.Proofs

/-!
# Round 9, strings as UTF-16 (area W): fix W9u's index functions, proved against Java's

A Clojure string is a list of UTF-16 code units (`us`, each below 0x10000; lone surrogates
allowed). With W9u, jank holds its bytes as canonical WTF-8: `wtf8 us`, the code points of
round 2's `unitsToCps` (a high surrogate followed by a low one makes a pair, every other unit
stays as it is), each in its UTF-8 form, a surrogate in its three-byte form (`enc`, mirroring
jtl/utf8.cpp `code_point_bytes`).

The fix reads bytes as pieces (`piece`, mirroring jtl/utf8.cpp `utf16_piece_at`): a complete
sequence of one to four bytes as its lead byte announces, else one byte standing alone (unit
0xDC00 + byte). `toUnits` is jtl `to_utf16`; `unitCount` is `utf16_length` (persistent_string
`count`); `hashUnits` is W9h's loop (immutable_string.hpp `to_hash`, before Murmur3's mix);
`indexOfJ`/`lastIndexOfJ` are java.lang.String's indexOf/lastIndexOf on units, which
`utf16_index_of`/`utf16_last_index_of` run on `to_utf16` of both strings; `locate` is
`utf16_locate`; `subsFix` is persistent_string `substring` (its fast path when every piece is one
byte, else `utf16_substr`).

The byte tests are written arithmetically; `bitops_arith` checks, for every byte, that they are
the C++'s bit tests (`(b & 0xE0) == 0xC0` and so on).

Main results (★ for every input):
- ★ `toUnits_wtf8`: the units read back from `wtf8 us` are `us`, for every Clojure string.
- ★ `count_wtf8`, ★ `hash_wtf8`, ★ `indexOf_wtf8`, ★ `lastIndexOf_wtf8`, ★ `nth_wtf8`: count, the
  hash's 31-loop, index-of, last-index-of and the value of `nth` are Java's.
- ★ `subs_whole`: `(subs s 0 (count s))` gives every byte string back, byte for byte.
- ★ `subs_tail_units`: for every Clojure string, the units of `(subs s k (count s))` are `us`
  from k on; so `(subs s (index-of s x))` starts with x (★ `subs_indexOf_startsWith`).
-/

namespace Jank.R9.Str

open Jank.Str

/-- jtl/utf8.cpp `code_point_bytes`: UTF-8 of a code point, a surrogate in three bytes. -/
def enc (c : Nat) : List Nat :=
  if c < 0x80 then [c]
  else if c < 0x800 then [0xC0 + c / 64, 0x80 + c % 64]
  else if c < 0x10000 then [0xE0 + c / 4096, 0x80 + c / 64 % 64, 0x80 + c % 64]
  else [0xF0 + c / 262144, 0x80 + c / 4096 % 64, 0x80 + c / 64 % 64, 0x80 + c % 64]

/-- Java's UTF-16 units of a code point (round 2's `utf16`, with / and %). -/
def u16 (c : Nat) : List Nat :=
  if c < 0x10000 then [c] else [0xD800 + (c - 0x10000) / 1024, 0xDC00 + (c - 0x10000) % 1024]

theorem utf16_eq_u16 (c : Nat) : utf16 c = u16 c := by
  by_cases h : c < 0x10000
  · simp [utf16, u16, h]
  · rw [Jank.R6.Str.utf16_supp_eq c (by omega)]; simp [u16, h]

/-- A Clojure string as W9u's jank holds it. -/
def wtf8 (us : List Nat) : List Nat := (unitsToCps us).flatMap enc

def isCont (b : Nat) : Bool := 0x80 ≤ b && b < 0xC0

/-- The size jtl `utf16_piece_at` reads from its lead byte (0: no sequence). -/
def leadSize (b0 : Nat) : Nat :=
  if b0 < 0x80 then 1 else if 0xC0 ≤ b0 ∧ b0 < 0xE0 then 2
  else if 0xE0 ≤ b0 ∧ b0 < 0xF0 then 3 else if 0xF0 ≤ b0 ∧ b0 < 0xF8 then 4 else 0

def leadBits (n b0 : Nat) : Nat :=
  if n = 1 then b0 else if n = 2 then b0 - 0xC0 else if n = 3 then b0 - 0xE0 else b0 - 0xF0

/-- The units of a code point as `utf16_piece_at` splits it. -/
def splitCp (cp : Nat) : List Nat :=
  if cp < 0x10000 then [cp] else [0xD800 + (cp - 0x10000) / 1024, 0xDC00 + (cp - 0x10000) % 1024]

/-- The size `utf16_piece_at` keeps: the lead's size when that many bytes remain and the ones
after the lead are continuation bytes, else 0 (a byte standing alone). -/
def pieceN (b0 : Nat) (rest : List Nat) : Nat :=
  if leadSize b0 ≠ 0 ∧ leadSize b0 - 1 ≤ rest.length ∧ (rest.take (leadSize b0 - 1)).all isCont = true
  then leadSize b0 else 0

/-- jtl/utf8.cpp `utf16_piece_at`: the piece at the head of a byte string, (size, units). -/
def piece : List Nat → Nat × List Nat
  | [] => (1, [])
  | b0 :: rest =>
    if pieceN b0 rest = 0 then (1, [0xDC00 + b0])
    else (pieceN b0 rest, splitCp ((rest.take (pieceN b0 rest - 1)).foldl
      (fun acc x => acc * 64 + (x - 0x80)) (leadBits (pieceN b0 rest) b0)))

/-- The C++ tests are these arithmetic ones, for every byte. -/
theorem bitops_arith : ∀ b, b < 256 →
    ((b &&& 0xE0 == 0xC0) = decide (0xC0 ≤ b ∧ b < 0xE0)) ∧
    ((b &&& 0xF0 == 0xE0) = decide (0xE0 ≤ b ∧ b < 0xF0)) ∧
    ((b &&& 0xF8 == 0xF0) = decide (0xF0 ≤ b ∧ b < 0xF8)) ∧
    ((b &&& 0xC0 == 0x80) = isCont b) ∧
    (0x80 ≤ b ∧ b < 0xC0 → b &&& 0x3F = b - 0x80) ∧
    (0xC0 ≤ b ∧ b < 0xE0 → b &&& (0x7F >>> 2) = b - 0xC0) ∧
    (0xE0 ≤ b ∧ b < 0xF0 → b &&& (0x7F >>> 3) = b - 0xE0) ∧
    (0xF0 ≤ b ∧ b < 0xF8 → b &&& (0x7F >>> 4) = b - 0xF0) := by
  decide +kernel

theorem piece_size_pos (b : List Nat) : 1 ≤ (piece b).1 := by
  cases b with
  | nil => simp [piece]
  | cons b0 rest =>
    simp only [piece]
    split
    · simp
    · simp only; omega

theorem splitCp_ne (cp : Nat) : splitCp cp ≠ [] := by unfold splitCp; split <;> simp

theorem piece_units_ne (b : List Nat) (h : b ≠ []) : (piece b).2 ≠ [] := by
  cases b with
  | nil => exact absurd rfl h
  | cons b0 rest =>
    simp only [piece]
    split
    · simp
    · exact splitCp_ne _

theorem piece_units_le (b : List Nat) : (piece b).2.length ≤ 2 := by
  cases b with
  | nil => simp [piece]
  | cons b0 rest =>
    simp only [piece]
    split
    · simp
    · simp only; unfold splitCp; split <;> simp

theorem pieceN_le (b0 : Nat) (rest : List Nat) : pieceN b0 rest ≤ rest.length + 1 := by
  unfold pieceN; split
  · rename_i hc; omega
  · omega

theorem piece_size_le (b : List Nat) (h : b ≠ []) : (piece b).1 ≤ b.length := by
  cases b with
  | nil => exact absurd rfl h
  | cons b0 rest =>
    simp only [piece, List.length_cons]
    have := pieceN_le b0 rest
    split
    · omega
    · simp only; omega

/-- jtl `to_utf16`. -/
def toUnits (b : List Nat) : List Nat :=
  if h : b = [] then [] else (piece b).2 ++ toUnits (b.drop (piece b).1)
termination_by b.length
decreasing_by
  have := piece_size_pos b
  have : b.length ≠ 0 := by simpa using h
  simp; omega

/-- jtl `utf16_length` (persistent_string `count`): the sum of the pieces' unit counts. -/
def unitCount (b : List Nat) : Nat :=
  if h : b = [] then 0 else (piece b).2.length + unitCount (b.drop (piece b).1)
termination_by b.length
decreasing_by
  have := piece_size_pos b
  have : b.length ≠ 0 := by simpa using h
  simp; omega

@[simp] theorem toUnits_nil : toUnits [] = [] := by rw [toUnits]; simp

theorem unitCount_eq (b : List Nat) : unitCount b = (toUnits b).length := by
  induction b using toUnits.induct with
  | case1 => simp [unitCount, toUnits]
  | case2 b h ih =>
    rw [unitCount, toUnits]; simp [h, ih]

/-! ## Decoding what `enc` wrote -/

theorem enc_ne (c : Nat) : enc c ≠ [] := by unfold enc; split <;> (try split) <;> (try split) <;> simp

theorem pieceN_1 (c : Nat) (h : c < 0x80) (rest : List Nat) : pieceN c rest = 1 := by
  simp [pieceN, leadSize, h]

theorem pieceN_2 (c : Nat) (h1 : ¬ c < 0x80) (h2 : c < 0x800) (rest : List Nat) :
    pieceN (0xC0 + c / 64) ((0x80 + c % 64) :: rest) = 2 := by
  have hl1 : ¬ (0xC0 + c / 64 < 0x80) := by omega
  have hl2 : 0xC0 ≤ 0xC0 + c / 64 ∧ 0xC0 + c / 64 < 0xE0 := by omega
  have hcont : isCont (0x80 + c % 64) = true := by simp [isCont]; omega
  simp [pieceN, leadSize, hl1, hl2, hcont]

theorem pieceN_3 (c : Nat) (h2 : ¬ c < 0x800) (h3 : c < 0x10000) (rest : List Nat) :
    pieceN (0xE0 + c / 4096) ((0x80 + c / 64 % 64) :: (0x80 + c % 64) :: rest) = 3 := by
  have hl1 : ¬ (0xE0 + c / 4096 < 0x80) := by omega
  have hl2 : ¬ (0xC0 ≤ 0xE0 + c / 4096 ∧ 0xE0 + c / 4096 < 0xE0) := by omega
  have hl3 : 0xE0 ≤ 0xE0 + c / 4096 ∧ 0xE0 + c / 4096 < 0xF0 := by omega
  have hc1 : isCont (0x80 + c / 64 % 64) = true := by simp [isCont]; omega
  have hc2 : isCont (0x80 + c % 64) = true := by simp [isCont]; omega
  simp [pieceN, leadSize, hl1, hl2, hl3, hc1, hc2]

theorem pieceN_4 (c : Nat) (h3 : ¬ c < 0x10000) (hc : c < 0x110000) (rest : List Nat) :
    pieceN (0xF0 + c / 262144)
      ((0x80 + c / 4096 % 64) :: (0x80 + c / 64 % 64) :: (0x80 + c % 64) :: rest) = 4 := by
  have hl1 : ¬ (0xF0 + c / 262144 < 0x80) := by omega
  have hl2 : ¬ (0xC0 ≤ 0xF0 + c / 262144 ∧ 0xF0 + c / 262144 < 0xE0) := by omega
  have hl3 : ¬ (0xE0 ≤ 0xF0 + c / 262144 ∧ 0xF0 + c / 262144 < 0xF0) := by omega
  have hl4 : 0xF0 ≤ 0xF0 + c / 262144 ∧ 0xF0 + c / 262144 < 0xF8 := by omega
  have hc1 : isCont (0x80 + c / 4096 % 64) = true := by simp [isCont]; omega
  have hc2 : isCont (0x80 + c / 64 % 64) = true := by simp [isCont]; omega
  have hc3 : isCont (0x80 + c % 64) = true := by simp [isCont]; omega
  simp [pieceN, leadSize, hl1, hl2, hl3, hl4, hc1, hc2, hc3]

theorem piece_enc (c : Nat) (hc : c < 0x110000) (rest : List Nat) :
    piece (enc c ++ rest) = ((enc c).length, u16 c) := by
  unfold enc u16
  by_cases h1 : c < 0x80
  · simp only [h1, ↓reduceIte, List.cons_append, List.nil_append, List.length_singleton]
    simp [piece, pieceN_1 c h1, leadBits, splitCp, show c < 0x10000 by omega]
  by_cases h2 : c < 0x800
  · simp only [h1, h2, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons,
      List.length_nil]
    have hcp : c / 64 * 64 + c % 64 = c := by omega
    simp [piece, pieceN_2 c h1 h2, leadBits, splitCp, hcp, show c < 0x10000 by omega]
  by_cases h3 : c < 0x10000
  · simp only [h1, h2, h3, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons,
      List.length_nil]
    have hcp : (c / 4096 * 64 + c / 64 % 64) * 64 + c % 64 = c := by omega
    simp [piece, pieceN_3 c h2 h3, leadBits, splitCp, hcp, h3]
  · simp only [h1, h2, h3, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons,
      List.length_nil]
    have hcp : ((c / 262144 * 64 + c / 4096 % 64) * 64 + c / 64 % 64) * 64 + c % 64 = c := by
      omega
    simp [piece, pieceN_4 c h3 hc, leadBits, splitCp, hcp, h3]

theorem toUnits_enc_append (c : Nat) (hc : c < 0x110000) (rest : List Nat) :
    toUnits (enc c ++ rest) = u16 c ++ toUnits rest := by
  rw [toUnits]
  have hne : enc c ++ rest ≠ [] := by simp [enc_ne]
  simp only [hne, ↓reduceDIte, piece_enc c hc rest]
  simp

theorem toUnits_flatMap (cps : List Nat) (hv : ∀ c ∈ cps, c < 0x110000) :
    toUnits (cps.flatMap enc) = cps.flatMap u16 := by
  induction cps with
  | nil => simp [toUnits]
  | cons c rest ih =>
    simp only [List.flatMap_cons]
    rw [toUnits_enc_append c (hv c (by simp)), ih (fun x hx => hv x (by simp [hx]))]

/-- Every code point `unitsToCps` makes from units is below U+110000, and its units are the
units it came from. -/
theorem unitsToCps_roundtrip (us : List Nat) (hu : ∀ u ∈ us, u < 0x10000) :
    (∀ c ∈ unitsToCps us, c < 0x110000) ∧ (unitsToCps us).flatMap u16 = us := by
  induction us using unitsToCps.induct with
  | case1 => simp [unitsToCps]
  | case2 u =>
    have := hu u (by simp)
    simp [unitsToCps, u16, this]; omega
  | case3 h l rest hp ih =>
    rw [unitsToCps]; simp only [hp, ↓reduceIte]
    simp only [Bool.and_eq_true, isHigh, isLow, decide_eq_true_eq] at hp
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hu x (by simp [hx]))
    refine ⟨?_, ?_⟩
    · intro c hc; simp at hc
      rcases hc with hc | hc
      · omega
      · exact ih1 c hc
    · simp only [List.flatMap_cons, ih2]
      have h1 : ¬ (0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00) < 0x10000) := by omega
      have h2 : 0xD800 + (0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00) - 0x10000) / 1024 = h := by
        omega
      have h3 : 0xDC00 + (0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00) - 0x10000) % 1024 = l := by
        omega
      simp [u16, h1, h2, h3]
  | case4 h l rest hp ih =>
    rw [unitsToCps]; simp only [hp, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hu x (by simp at hx; rcases hx with hx | hx <;> simp [hx]))
    have hh := hu h (by simp)
    refine ⟨?_, ?_⟩
    · intro c hc; simp at hc
      rcases hc with hc | hc
      · omega
      · exact ih1 c (by simp [hc])
    · simp only [List.flatMap_cons, ih2]; simp [u16, hh]

/-- ★ The units W9u reads from the bytes of any Clojure string are the string's units. -/
theorem toUnits_wtf8 (us : List Nat) (hu : ∀ u ∈ us, u < 0x10000) : toUnits (wtf8 us) = us := by
  obtain ⟨h1, h2⟩ := unitsToCps_roundtrip us hu
  rw [wtf8, toUnits_flatMap _ h1, h2]

/-- ★ `count`: String.length. -/
theorem count_wtf8 (us : List Nat) (hu : ∀ u ∈ us, u < 0x10000) :
    unitCount (wtf8 us) = us.length := by
  rw [unitCount_eq, toUnits_wtf8 us hu]

/-! ## hash (W9h) -/

def step (h u : Nat) : Nat := (31 * h + u) % 2 ^ 32

/-- W9h's loop over the pieces (immutable_string.hpp `to_hash`, u32 arithmetic). -/
def hashUnits (h : Nat) (b : List Nat) : Nat :=
  if hb : b = [] then h else hashUnits ((piece b).2.foldl step h) (b.drop (piece b).1)
termination_by b.length
decreasing_by
  have := piece_size_pos b
  have : b.length ≠ 0 := by simpa using hb
  simp; omega

/-- String.hashCode, as a u32. -/
def javaHash (us : List Nat) : Nat := us.foldl step 0

theorem hashUnits_eq (h : Nat) (b : List Nat) : hashUnits h b = (toUnits b).foldl step h := by
  induction b using toUnits.induct generalizing h with
  | case1 => simp [hashUnits, toUnits]
  | case2 b hb ih => rw [hashUnits, toUnits]; simp [hb, ih]

/-- ★ `hash` (before the Murmur3 mix both sides apply): String.hashCode of the units. -/
theorem hash_wtf8 (us : List Nat) (hu : ∀ u ∈ us, u < 0x10000) :
    hashUnits 0 (wtf8 us) = javaHash us := by
  rw [hashUnits_eq, toUnits_wtf8 us hu, javaHash]

/-! ## index-of / last-index-of -/

/-- Whether `ns` occurs in `us` at position k. -/
def occursAt (us ns : List Nat) (k : Nat) : Bool := (us.drop k).take ns.length == ns

/-- java.lang.String.indexOf(String, int) on units: -1 when absent. -/
def indexOfJ (us ns : List Nat) (fr : Int) : Int :=
  if fr ≥ us.length then (if ns = [] then us.length else -1)
  else
    match (List.range (us.length + 1 - fr.toNat)).find?
        (fun d => occursAt us ns (fr.toNat + d) && decide (fr.toNat + d + ns.length ≤ us.length)) with
    | some d => (fr.toNat + d : Nat)
    | none => -1

/-- java.lang.String.lastIndexOf(String, int) on units. -/
def lastIndexOfJ (us ns : List Nat) (fr : Int) : Int :=
  let right : Int := (us.length : Int) - ns.length
  let f := if fr > right then right else fr
  if f < 0 then -1
  else
    match (List.range (f.toNat + 1)).find? (fun d => occursAt us ns (f.toNat - d)) with
    | some d => (f.toNat - d : Nat)
    | none => -1

/-- W9u's general path: both strings decoded, then searched (`std::u16string_view::find`). -/
def indexOfFix (b n : List Nat) (fr : Int) : Int := indexOfJ (toUnits b) (toUnits n) fr
def lastIndexOfFix (b n : List Nat) (fr : Int) : Int := lastIndexOfJ (toUnits b) (toUnits n) fr

/-- ★ index-of on the bytes of two Clojure strings is String.indexOf on their units. -/
theorem indexOf_wtf8 (us ns : List Nat) (hu : ∀ u ∈ us, u < 0x10000) (hn : ∀ u ∈ ns, u < 0x10000)
    (fr : Int) : indexOfFix (wtf8 us) (wtf8 ns) fr = indexOfJ us ns fr := by
  simp [indexOfFix, toUnits_wtf8 us hu, toUnits_wtf8 ns hn]

/-- ★ last-index-of likewise. -/
theorem lastIndexOf_wtf8 (us ns : List Nat) (hu : ∀ u ∈ us, u < 0x10000)
    (hn : ∀ u ∈ ns, u < 0x10000) (fr : Int) :
    lastIndexOfFix (wtf8 us) (wtf8 ns) fr = lastIndexOfJ us ns fr := by
  simp [lastIndexOfFix, toUnits_wtf8 us hu, toUnits_wtf8 ns hn]

/-! ## locate, nth, subs -/

/-- jtl `utf16_locate`: (first byte of the piece holding unit k, whether k is its second unit);
past the last unit, (size, false). -/
def locate (b : List Nat) (k : Nat) : Nat × Bool :=
  if hb : b = [] then (0, false)
  else if k < (piece b).2.length then (0, k != 0)
  else
    let r := locate (b.drop (piece b).1) (k - (piece b).2.length)
    (r.1 + (piece b).1, r.2)
termination_by b.length
decreasing_by
  have := piece_size_pos b
  have : b.length ≠ 0 := by simpa using hb
  simp; omega

/-- The character `nth` gives for unit k (k below the count): persistent_string.cpp `unit_at`'s
general path, as the unit's value (character.cpp `to_integer` of its bytes). -/
def nthUnit (b : List Nat) (k : Nat) : Option Nat :=
  let loc := locate b k
  match (piece (b.drop loc.1)).2 with
  | [u] => some u
  | [u1, u2] => some (if loc.2 then u2 else u1)
  | _ => none

theorem nthUnit_eq (b : List Nat) (k : Nat) (hk : k < (toUnits b).length) :
    nthUnit b k = (toUnits b)[k]? := by
  induction b using toUnits.induct generalizing k with
  | case1 => simp [toUnits] at hk
  | case2 b hb ih =>
    have hlen := piece_units_le b
    have hne := piece_units_ne b hb
    rw [toUnits] at hk ⊢
    simp only [hb, ↓reduceDIte] at hk ⊢
    unfold nthUnit
    rw [locate]
    simp only [hb, ↓reduceDIte]
    by_cases hk1 : k < (piece b).2.length
    · simp only [hk1, ↓reduceIte, List.drop_zero, List.getElem?_append_left hk1]
      match hp : (piece b).2, hk1 with
      | [u], hk1 => simp at hk1; simp [hk1]
      | [u1, u2], hk1 =>
        simp at hk1
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp
      | [], hk1 => simp at hk1
      | _ :: _ :: _ :: _, _ => simp [hp] at hlen
    · simp only [hk1, ↓reduceIte]
      have hk2 : k - (piece b).2.length < (toUnits (b.drop (piece b).1)).length := by
        simp at hk; omega
      have := ih (k - (piece b).2.length) hk2
      unfold nthUnit at this
      rw [List.getElem?_append_right (by omega)]
      rw [← this]
      simp [List.drop_drop, Nat.add_comm]

/-- ★ `nth` of the bytes of a Clojure string at an index in range is the unit there. -/
theorem nth_wtf8 (us : List Nat) (hu : ∀ u ∈ us, u < 0x10000) (k : Nat) (hk : k < us.length) :
    nthUnit (wtf8 us) k = some us[k] := by
  rw [nthUnit_eq _ _ (by rw [toUnits_wtf8 us hu]; exact hk), toUnits_wtf8 us hu]
  simp [hk]

/-- The bytes of units [i, j) by persistent_string `substring` (fast path: every piece one byte)
and jtl `utf16_substr` (the general path). A half pair is the unit's `enc`. -/
def subsFix (b : List Nat) (i j : Nat) : Option (List Nat) :=
  if j < i ∨ unitCount b < j then none
  else if unitCount b = b.length then some ((b.drop i).take (j - i))
  else if i = j then some []
  else
    let f := locate b i
    let t := locate b j
    if !f.2 && !t.2 then some ((b.drop f.1).take (t.1 - f.1))
    else
      let p := piece (b.drop f.1)
      let lowPart := if f.2 then enc (p.2.getD 1 0) else []
      let fr := if f.2 then f.1 + p.1 else f.1
      let mid := if fr < t.1 then (b.drop fr).take (t.1 - fr) else []
      let highPart := if t.2 then enc ((piece (b.drop t.1)).2.getD 0 0) else []
      some (lowPart ++ mid ++ highPart)

theorem locate_end (b : List Nat) : locate b (unitCount b) = (b.length, false) := by
  induction b using toUnits.induct with
  | case1 => simp [locate, unitCount]
  | case2 b hb ih =>
    rw [locate, unitCount]
    simp only [hb, ↓reduceDIte, Nat.lt_irrefl, Nat.not_lt, Nat.le_add_right, ↓reduceIte,
      Nat.add_sub_cancel_left]
    have h1 := ih
    rw [unitCount_eq] at h1 ⊢
    simp only [Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte, Nat.add_sub_cancel_left, h1,
      List.length_drop]
    have := piece_size_pos b
    have hle := piece_size_le b hb
    simp; omega

theorem locate_zero (b : List Nat) (hb : b ≠ []) : locate b 0 = (0, false) := by
  rw [locate]
  have := piece_units_ne b hb
  have : 0 < (piece b).2.length := List.length_pos_iff.mpr this
  simp [hb, this]

/-- ★ `(subs s 0 (count s))` is s, byte for byte, for every byte string. -/
theorem subs_whole (b : List Nat) : subsFix b 0 (unitCount b) = some b := by
  unfold subsFix
  simp only [Nat.not_lt_zero, Nat.lt_irrefl, or_self, ↓reduceIte, List.drop_zero, Nat.sub_zero]
  by_cases hc : unitCount b = b.length
  · simp [hc]
  · simp only [hc, ↓reduceIte]
    by_cases hb : b = []
    · simp [hb, unitCount] at hc
    · have h0 : unitCount b ≠ 0 := by
        rw [unitCount_eq, toUnits]; simp [hb, piece_units_ne b hb]
      simp only [show ¬ (0 = unitCount b) by omega, ↓reduceIte, locate_zero b hb, locate_end b]
      simp

/-! ## The tail of a string: `(subs s k)` and `(subs s (index-of s x))` -/

theorem drop_locate (b : List Nat) (k : Nat) (hk : k < (toUnits b).length) :
    (toUnits b).drop k =
      ((piece (b.drop (locate b k).1)).2.drop (if (locate b k).2 then 1 else 0)) ++
        toUnits (b.drop ((locate b k).1 + (piece (b.drop (locate b k).1)).1)) := by
  induction b using toUnits.induct generalizing k with
  | case1 => simp [toUnits] at hk
  | case2 b hb ih =>
    have hlen := piece_units_le b
    rw [toUnits] at hk ⊢
    simp only [hb, ↓reduceDIte] at hk ⊢
    rw [locate]
    simp only [hb, ↓reduceDIte]
    by_cases hk1 : k < (piece b).2.length
    · simp only [hk1, ↓reduceIte, List.drop_zero, Nat.zero_add]
      rw [List.drop_append_of_le_length (by omega)]
      congr 1
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp
    · simp only [hk1, ↓reduceIte]
      have hk2 : k - (piece b).2.length < (toUnits (b.drop (piece b).1)).length := by
        simp only [List.length_append] at hk; omega
      have e1 : ((piece b).2 ++ toUnits (b.drop (piece b).1)).drop k
          = (toUnits (b.drop (piece b).1)).drop (k - (piece b).2.length) := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
      rw [e1, ih (k - (piece b).2.length) hk2]
      simp only [List.drop_drop]
      have e2 : (piece b).1 + (locate (b.drop (piece b).1) (k - (piece b).2.length)).1
          = (locate (b.drop (piece b).1) (k - (piece b).2.length)).1 + (piece b).1 := Nat.add_comm _ _
      rw [e2]; ac_rfl

/-- jtl `utf16_substr` from unit k to the end (the general path of `subsFix`). -/
def tailGen (b : List Nat) (k : Nat) : List Nat :=
  let f := locate b k
  let p := piece (b.drop f.1)
  if f.2 then enc (p.2.getD 1 0) ++ b.drop (f.1 + p.1) else b.drop f.1

theorem locate_second (b : List Nat) (k : Nat) (hs : (locate b k).2 = true) :
    (piece (b.drop (locate b k).1)).2.length = 2 := by
  induction b using toUnits.induct generalizing k with
  | case1 => simp [locate] at hs
  | case2 b hb ih =>
    have hlen := piece_units_le b
    rw [locate] at hs ⊢
    simp only [hb, ↓reduceDIte] at hs ⊢
    by_cases hk1 : k < (piece b).2.length
    · simp only [hk1, ↓reduceIte, bne_iff_ne, ne_eq, decide_eq_true_eq] at hs ⊢
      simp only [List.drop_zero]; omega
    · simp only [hk1, ↓reduceIte] at hs ⊢
      have := ih (k - (piece b).2.length) hs
      simpa [List.drop_drop, Nat.add_comm] using this

theorem splitCp_second (cp : Nat) (u1 u2 : Nat) (h : splitCp cp = [u1, u2]) : u2 < 0x10000 := by
  unfold splitCp at h; split at h
  · simp at h
  · simp at h; omega

theorem piece_second (b : List Nat) (u1 u2 : Nat) (h : (piece b).2 = [u1, u2]) : u2 < 0x10000 := by
  cases b with
  | nil => simp [piece] at h
  | cons b0 rest =>
    simp only [piece] at h
    split at h
    · simp at h
    · exact splitCp_second _ _ _ h

theorem tailGen_units (b : List Nat) (k : Nat) (hk : k < (toUnits b).length) :
    toUnits (tailGen b k) = (toUnits b).drop k := by
  have hd := drop_locate b k hk
  have hne : b.drop (locate b k).1 ≠ [] := by
    intro he
    have hge : b.length ≤ (locate b k).1 := by simpa using he
    rw [he] at hd
    have h1 : b.drop ((locate b k).1 + (piece ([] : List Nat)).1) = [] :=
      List.drop_eq_nil_of_le (by omega)
    rw [h1] at hd
    simp only [piece, List.drop_nil, List.nil_append, toUnits_nil] at hd
    have := List.drop_eq_nil_iff.mp hd
    omega
  unfold tailGen
  rw [hd]
  by_cases hs : (locate b k).2 = true
  · have h2 := locate_second b k hs
    obtain ⟨u1, u2, hp⟩ : ∃ u1 u2, (piece (b.drop (locate b k).1)).2 = [u1, u2] := by
      rcases h : (piece (b.drop (locate b k).1)).2 with _ | ⟨u1, _ | ⟨u2, _ | _⟩⟩ <;> simp_all
    have hu2 := piece_second _ u1 u2 hp
    simp only [hs, ↓reduceIte, hp]
    rw [show [u1, u2].getD 1 0 = u2 from rfl, toUnits_enc_append u2 (by omega)]
    simp [u16, hu2]
  · simp only [hs, ↓reduceIte, Bool.false_eq_true, List.drop_zero]
    rw [toUnits]
    simp [hne, List.drop_drop, Nat.add_comm]

/-- The fast path: when every piece of the bytes of a Clojure string is one byte, the string is
ASCII, its bytes are its units, and a tail of the bytes is the tail of the units. -/
theorem enc_length_ge (c : Nat) : (u16 c).length ≤ (enc c).length ∧
    ((u16 c).length = (enc c).length → c < 0x80) := by
  unfold u16 enc
  by_cases h1 : c < 0x80
  · simp [h1, show c < 0x10000 by omega]
  · by_cases h2 : c < 0x800
    · simp [h1, h2, show c < 0x10000 by omega]
    · by_cases h3 : c < 0x10000 <;> simp [h1, h2, h3]

theorem flatMap_length_ge (cps : List Nat) :
    (cps.flatMap u16).length ≤ (cps.flatMap enc).length ∧
    ((cps.flatMap u16).length = (cps.flatMap enc).length → ∀ c ∈ cps, c < 0x80) := by
  induction cps with
  | nil => simp
  | cons c rest ih =>
    obtain ⟨h1, h2⟩ := enc_length_ge c
    obtain ⟨ih1, ih2⟩ := ih
    simp only [List.flatMap_cons, List.length_append]
    refine ⟨by omega, ?_⟩
    intro he x hx
    simp at hx
    rcases hx with rfl | hx
    · exact h2 (by omega)
    · exact ih2 (by omega) x hx

theorem ascii_enc (cps : List Nat) (h : ∀ c ∈ cps, c < 0x80) : cps.flatMap enc = cps := by
  induction cps with
  | nil => simp
  | cons c rest ih =>
    simp [enc, h c (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem ascii_u16 (cps : List Nat) (h : ∀ c ∈ cps, c < 0x80) : cps.flatMap u16 = cps := by
  induction cps with
  | nil => simp
  | cons c rest ih =>
    have := h c (by simp)
    simp [u16, show c < 0x10000 by omega, ih (fun x hx => h x (by simp [hx]))]

/-- jtl `utf16_substr` (or the fast path's byte substr) from unit k to the end, as
`persistent_string::substring(k)` computes it. -/
def subsTail (b : List Nat) (k : Nat) : List Nat :=
  if unitCount b = b.length then b.drop k else if k = unitCount b then [] else tailGen b k

/-- ★ For every Clojure string, the units of `(subs s k)` are the string's units from k on. -/
theorem subs_tail_units (us : List Nat) (hu : ∀ u ∈ us, u < 0x10000) (k : Nat)
    (hk : k ≤ us.length) : toUnits (subsTail (wtf8 us) k) = us.drop k := by
  obtain ⟨hr1, hr2⟩ := unitsToCps_roundtrip us hu
  unfold subsTail
  by_cases hc : unitCount (wtf8 us) = (wtf8 us).length
  · simp only [hc, ↓reduceIte]
    rw [count_wtf8 us hu] at hc
    have hasc : ∀ c ∈ unitsToCps us, c < 0x80 := by
      have := (flatMap_length_ge (unitsToCps us)).2
      rw [hr2] at this
      exact this (by rw [hc, wtf8])
    have hw : wtf8 us = unitsToCps us := ascii_enc _ hasc
    have hus : unitsToCps us = us := by
      have h' := hr2; rw [ascii_u16 _ hasc] at h'; exact h'
    rw [hw, hus]
    have hasc' : ∀ c ∈ us.drop k, c < 0x80 := by
      intro c hc'; rw [← hus] at hc'; exact hasc c (List.mem_of_mem_drop hc')
    have := toUnits_flatMap (us.drop k) (fun c hc' => by have := hasc' c hc'; omega)
    rw [ascii_enc _ hasc', ascii_u16 _ hasc'] at this
    exact this
  · simp only [hc, ↓reduceIte]
    by_cases hk2 : k = unitCount (wtf8 us)
    · simp only [hk2, ↓reduceIte, count_wtf8 us hu]
      simp [toUnits]
    · simp only [hk2, ↓reduceIte]
      rw [count_wtf8 us hu] at hk2
      rw [tailGen_units _ _ (by rw [toUnits_wtf8 us hu]; omega), toUnits_wtf8 us hu]

theorem indexOfJ_occurs (us ns : List Nat) (fr : Int) (k : Nat) (h : indexOfJ us ns fr = k) :
    (us.drop k).take ns.length = ns ∧ k ≤ us.length := by
  unfold indexOfJ at h
  split at h
  · split at h
    · rename_i hn; subst hn
      have : k = us.length := by omega
      subst this; simp
    · omega
  · split at h
    · rename_i d hd
      have hp := List.find?_some hd
      simp only [occursAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
      have hk : fr.toNat + d = k := by omega
      subst hk
      exact ⟨hp.1, by omega⟩
    · omega

/-- ★ `(subs s (index-of s x from))`: whenever index-of finds x, the units of the rest of s
from there begin with x's units, for every pair of Clojure strings. -/
theorem subs_indexOf_startsWith (us ns : List Nat) (hu : ∀ u ∈ us, u < 0x10000)
    (hn : ∀ u ∈ ns, u < 0x10000) (fr : Int) (k : Nat)
    (h : indexOfFix (wtf8 us) (wtf8 ns) fr = k) :
    (toUnits (subsTail (wtf8 us) k)).take (toUnits (wtf8 ns)).length = toUnits (wtf8 ns) := by
  rw [indexOf_wtf8 us ns hu hn] at h
  obtain ⟨h1, h2⟩ := indexOfJ_occurs us ns fr k h
  rw [subs_tail_units us hu k h2, toUnits_wtf8 ns hn]
  exact h1

end Jank.R9.Str

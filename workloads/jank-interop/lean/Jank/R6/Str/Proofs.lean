import Jank.StrModel

/-!
# Round 6, strings: for-every-input proofs about `subs`, `count` and the code-point design

Built on round 2's models (`Jank.StrModel`: `utf8`, `utf16`, `jstr`, `cstr`, `unitsToCps`,
`jSubs`, `cSubs`), which replicate persistent_string.cpp `substring` 133–155 (byte offsets:
`data.substr(start, end - start)`, reached from core.cpp `subs` 398–422 through core.jank `subs`
1979–1985) and Java's `String.substring` (UTF-16 units).

A text is a list of Unicode scalar values (`valid`: below U+110000 and not a surrogate). jank holds
its UTF-8 bytes; Clojure its UTF-16 units. A result is compared as bytes (round 2's `R`), a Clojure
string's units turned into UTF-8 through `unitsToBytes` (a lone surrogate as its 3-byte form).

Main results:
- `subs1_agrees_iff` ★: `(subs s i)` gives jank's and Clojure's answer alike iff `i < 0`, or `i` is
  at most the length of `s`'s longest ASCII prefix, or `i` is past jank's byte count (both throw).
  LG3 (`(subs "é-è" 2)`) is the second case failing: the ASCII prefix of "é-è" is empty.
- `unitsToBytes_cstr` ★: Clojure's units of a valid text read back as jank's bytes (no surrogate
  pair is lost), the lemma every agreement statement here rests on.
- `cp_design_agrees_bmp` ★: the smallest design change (code-point indexing in persistent_string
  and clojure.string) gives Clojure's `count`, `nth` and `subs` for every text without a
  supplementary character; `cp_design_supplementary` shows it still differs on one.
-/

namespace Jank.R6.Str

open Jank.Str

/-- A Unicode scalar value. -/
def valid (c : Nat) : Prop := c < 0x110000 ∧ ¬(0xD800 ≤ c ∧ c ≤ 0xDFFF)

/-- The length of the longest ASCII prefix. -/
def asciiPrefix (cps : List Nat) : Nat := (cps.takeWhile (fun c => decide (c < 0x80))).length

/-! ## UTF-16 round trip -/

theorem unitsToCps_cons_nonhigh (u : Nat) (xs : List Nat) (h : isHigh u = false) :
    unitsToCps (u :: xs) = u :: unitsToCps xs := by
  cases xs with
  | nil => simp [unitsToCps]
  | cons l rest => rw [unitsToCps]; simp [h]

theorem utf16_bmp (c : Nat) (h : c < 0x10000) : utf16 c = [c] := by simp [utf16, h]

theorem utf16_supp_eq (c : Nat) (h1 : 0x10000 ≤ c) :
    utf16 c = [0xD800 + (c - 0x10000) / 1024, 0xDC00 + (c - 0x10000) % 1024] := by
  have hs : (c - 0x10000) >>> 10 = (c - 0x10000) / 1024 := by rw [Nat.shiftRight_eq_div_pow]
  have ha : (c - 0x10000) &&& 0x3FF = (c - 0x10000) % 1024 := Nat.and_two_pow_sub_one_eq_mod _ 10
  simp only [utf16, show ¬ c < 0x10000 by omega, ↓reduceIte, hs, ha]

/-- The surrogate pair of a supplementary character, and its recombination. -/
theorem utf16_supp (c : Nat) (h1 : 0x10000 ≤ c) (h2 : c < 0x110000) :
    ∃ hi lo, utf16 c = [hi, lo] ∧ isHigh hi = true ∧ isLow lo = true ∧ isHigh lo = false ∧
      0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00) = c ∧ 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF := by
  refine ⟨_, _, utf16_supp_eq c h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try simp only [isHigh, isLow, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not])
  all_goals omega

theorem unitsToCps_cstr (cps : List Nat) (hv : ∀ c ∈ cps, valid c) : unitsToCps (cstr cps) = cps := by
  induction cps with
  | nil => simp [cstr, unitsToCps]
  | cons c rest ih =>
    have hc := hv c (by simp)
    have ih' := ih (fun x hx => hv x (by simp [hx]))
    have hcs : cstr (c :: rest) = utf16 c ++ cstr rest := by simp [cstr]
    rw [hcs]
    by_cases hb : c < 0x10000
    · rw [utf16_bmp c hb]
      have : isHigh c = false := by
        simp only [isHigh, Bool.and_eq_false_iff, decide_eq_false_iff_not]; unfold valid at hc; omega
      simp only [List.singleton_append]
      rw [unitsToCps_cons_nonhigh _ _ this, ih']
    · obtain ⟨hi, lo, he, hh, hl, _, hc', _, _⟩ := utf16_supp c (by omega) hc.1
      rw [he]
      simp only [List.cons_append, List.nil_append]
      rw [unitsToCps]
      simp [hh, hl, hc', ih']

/-- ★ Clojure's units of a valid text, read back, are jank's bytes. -/
theorem unitsToBytes_cstr (cps : List Nat) (hv : ∀ c ∈ cps, valid c) :
    unitsToBytes (cstr cps) = jstr cps := by
  simp [unitsToBytes, unitsToCps_cstr cps hv, jstr]

theorem drop_append_ge {α : Type} (l1 l2 : List α) (n : Nat) (h : l1.length ≤ n) :
    (l1 ++ l2).drop n = l2.drop (n - l1.length) := by
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

/-! ## Lengths -/

theorem utf8_gt_utf16 (c : Nat) (h : 0x80 ≤ c) : (utf16 c).length < (utf8 c).length := by
  have h1 := utf8_ge_utf16 c
  have : (utf16 c).length ≠ (utf8 c).length := fun e => absurd (h1.2.mp e) (by omega)
  omega

theorem jstr_append (a b : List Nat) : jstr (a ++ b) = jstr a ++ jstr b := by simp [jstr]
theorem cstr_append (a b : List Nat) : cstr (a ++ b) = cstr a ++ cstr b := by simp [cstr]
theorem jstr_cons (c : Nat) (b : List Nat) : jstr (c :: b) = utf8 c ++ jstr b := by simp [jstr]
theorem cstr_cons (c : Nat) (b : List Nat) : cstr (c :: b) = utf16 c ++ cstr b := by simp [cstr]

theorem utf8_ascii_length (c : Nat) (h : c < 0x80) : (utf8 c).length = 1 := by
  rw [utf8_length]; simp [h]

theorem utf16_ascii_length (c : Nat) (h : c < 0x80) : (utf16 c).length = 1 := by
  rw [utf16_length]; simp [show c < 0x10000 by omega]

/-- On an all-ASCII text bytes and units are the code points' count. -/
theorem jstr_ascii_length (a : List Nat) (h : ∀ c ∈ a, c < 0x80) : (jstr a).length = a.length := by
  induction a with
  | nil => rfl
  | cons c rest ih =>
    rw [jstr_cons, List.length_append, ih (fun x hx => h x (by simp [hx])),
      utf8_ascii_length c (h c (by simp)), List.length_cons]; omega

theorem cstr_ascii_length (a : List Nat) (h : ∀ c ∈ a, c < 0x80) : (cstr a).length = a.length := by
  induction a with
  | nil => rfl
  | cons c rest ih =>
    rw [cstr_cons, List.length_append, ih (fun x hx => h x (by simp [hx])),
      utf16_ascii_length c (h c (by simp)), List.length_cons]; omega

theorem drop_jstr_ascii (a b : List Nat) (h : ∀ c ∈ a, c < 0x80) :
    (jstr (a ++ b)).drop a.length = jstr b := by
  rw [jstr_append, drop_append_ge _ _ _ (by rw [jstr_ascii_length a h]; exact Nat.le_refl _), jstr_ascii_length a h,
    Nat.sub_self, List.drop_zero]

theorem drop_cstr_ascii (a b : List Nat) (h : ∀ c ∈ a, c < 0x80) :
    (cstr (a ++ b)).drop a.length = cstr b := by
  rw [cstr_append, drop_append_ge _ _ _ (by rw [cstr_ascii_length a h]; exact Nat.le_refl _), cstr_ascii_length a h,
    Nat.sub_self, List.drop_zero]

theorem units_le_bytes (cps : List Nat) : (cstr cps).length ≤ (jstr cps).length := count_ge cps

theorem unitsToBytes_low_cons (lo : Nat) (rest : List Nat) (hv : ∀ c ∈ rest, valid c)
    (hlo : isHigh lo = false) : unitsToBytes (lo :: cstr rest) = utf8 lo ++ jstr rest := by
  simp only [unitsToBytes]
  rw [unitsToCps_cons_nonhigh _ _ hlo, unitsToCps_cstr rest hv]
  simp [jstr]

/-- Dropping `j` units of a valid text leaves at most `bytes - j` bytes (a cut surrogate pair: the
lone low surrogate is 3 bytes of the pair's 4). -/
theorem unitsToBytes_drop_le (cs : List Nat) (hv : ∀ c ∈ cs, valid c) (j : Nat) :
    (unitsToBytes ((cstr cs).drop j)).length + j ≤ (jstr cs).length ∨ (cstr cs).length < j := by
  induction cs generalizing j with
  | nil => cases j <;> simp [cstr, jstr, unitsToBytes, unitsToCps]
  | cons c rest ih =>
    have hc := hv c (by simp)
    have hr : ∀ x ∈ rest, valid x := fun x hx => hv x (by simp [hx])
    have hge := (utf8_ge_utf16 c).1
    rw [cstr_cons, jstr_cons, List.length_append, List.length_append]
    by_cases hj : (utf16 c).length ≤ j
    · rw [drop_append_ge _ _ _ hj]
      rcases ih hr (j - (utf16 c).length) with h | h
      · left; omega
      · right; omega
    · by_cases hj0 : j = 0
      · subst hj0; left
        simp only [List.drop_zero, Nat.add_zero]
        rw [← cstr_cons, unitsToBytes_cstr (c :: rest) hv, jstr_cons, List.length_append]
        exact Nat.le_refl _
      · have hsupp : 0x10000 ≤ c := by
          rw [utf16_length] at hj; split at hj <;> omega
        obtain ⟨hi, lo, he, _, _, hlo, _, l1, l2⟩ := utf16_supp c hsupp hc.1
        rw [he] at hj ⊢
        have : j = 1 := by simp at hj; omega
        subst this
        left
        simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append]
        rw [unitsToBytes_low_cons lo rest hr hlo, List.length_append]
        have e1 : (utf8 lo).length = 3 := by
          rw [utf8_length]
          simp only [show ¬ lo < 0x80 by omega, show ¬ lo < 0x800 by omega, show lo < 0x10000 by omega,
            ↓reduceIte]
        have e2 : (utf8 c).length = 4 := by
          rw [utf8_length]
          simp only [show ¬ c < 0x80 by omega, show ¬ c < 0x800 by omega, show ¬ c < 0x10000 by omega,
            ↓reduceIte]
        omega

/-- The byte after the lead of a 4-byte character is a continuation byte, never 0xED (the lead of
a lone surrogate's 3-byte form). -/
theorem utf8_supp_second_ne (c : Nat) (h : 0x10000 ≤ c) :
    ∃ b x rest2, utf8 c = b :: x :: rest2 ∧ x ≠ 0xED := by
  have hlt : (c >>> 12) &&& 0x3F < 64 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have key : ∀ y, y < 64 → (0x80 ||| y).toUInt8 ≠ (0xED : UInt8) := by decide
  simp only [utf8, show ¬ c < 0x80 by omega, show ¬ c < 0x800 by omega, show ¬ c < 0x10000 by omega,
    ↓reduceIte]
  exact ⟨_, _, _, rfl, key _ hlt⟩

theorem utf8_low_head (lo : Nat) (h1 : 0xDC00 ≤ lo) (h2 : lo ≤ 0xDFFF) :
    ∃ rest, utf8 lo = 0xED :: rest := by
  have : lo >>> 12 = 13 := by rw [Nat.shiftRight_eq_div_pow]; omega
  simp only [utf8, show ¬ lo < 0x80 by omega, show ¬ lo < 0x800 by omega, show lo < 0x10000 by omega,
    ↓reduceIte, this]
  exact ⟨_, rfl⟩

/-! ## `(subs s i)`: jank's equals Clojure's iff the cut is within the ASCII prefix -/

/-- `(subs s i)` as both sides compute it (core.jank `subs` 2-arity → `substring(start)` =
`substring(start, size)`; Clojure `String.substring(start)`). -/
def jSubs1 (cps : List Nat) (i : Int) : R := jSubs (jstr cps) i (jstr cps).length
def cSubs1 (cps : List Nat) (i : Int) : R := cSubs (cstr cps) i (cstr cps).length

theorem takeWhile_split (cps : List Nat) :
    ∃ a rest, cps = a ++ rest ∧ a.length = asciiPrefix cps ∧ (∀ c ∈ a, c < 0x80) ∧
      (∀ c, rest.head? = some c → 0x80 ≤ c) := by
  induction cps with
  | nil => exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | cons c rest ih =>
    by_cases hc : c < 0x80
    · obtain ⟨a, r, h1, h2, h3, h4⟩ := ih
      refine ⟨c :: a, r, by simp [h1], ?_, ?_, h4⟩
      · simp only [asciiPrefix] at h2 ⊢
        simp [List.takeWhile_cons, hc, h2]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hc
        · exact h3 x hx
    · refine ⟨[], c :: rest, rfl, ?_, by simp, ?_⟩
      · simp [asciiPrefix, List.takeWhile_cons, hc]
      · intro x hx; simp at hx; omega

theorem agrees_str (a b : List UInt8) : (R.str a).agrees (R.str b) = true ↔ a = b := by
  simp [R.agrees]

/-- ★ For every valid text and every `i`: jank's `(subs s i)` agrees with Clojure's exactly when
`i < 0`, `i ≤ asciiPrefix s`, or `i` is past jank's byte count. -/
theorem subs1_agrees_iff (cps : List Nat) (hv : ∀ c ∈ cps, valid c) (i : Int) :
    (jSubs1 cps i).agrees (cSubs1 cps i) = true ↔
      (i < 0 ∨ i ≤ asciiPrefix cps ∨ (jstr cps).length < i) := by
  obtain ⟨a, rest, hsplit, hlen, ha, hr⟩ := takeWhile_split cps
  have hvr : ∀ c ∈ rest, valid c := fun c hc => hv c (by rw [hsplit]; simp [hc])
  have hUB := units_le_bytes cps
  unfold jSubs1 cSubs1 jSubs cSubs
  by_cases hneg : i < 0
  · simp [hneg, R.agrees]
  by_cases hbig : ((jstr cps).length : Int) < i
  · have hc : ((cstr cps).length : Int) < i := by omega
    simp [hneg, hbig, hc, R.agrees]
  obtain ⟨n, rfl⟩ : ∃ n : Nat, i = n := ⟨i.toNat, by omega⟩
  have e0 : ((n : Int)).toNat = n := by omega
  have ej1 : (((jstr cps).length : Int) - n).toNat = (jstr cps).length - n := by omega
  rw [if_neg hneg, if_neg hbig, if_neg (by omega), e0, ej1,
    List.take_of_length_le (by simp)]
  by_cases hp : (n : Int) ≤ asciiPrefix cps
  · -- inside the ASCII prefix: both drop n code points
    apply iff_of_true _ (Or.inr (Or.inl hp))
    have hn : n ≤ a.length := by omega
    have ec1 : (((cstr cps).length : Int) - n).toNat = (cstr cps).length - n := by omega
    have hcl : (cstr cps).length ≥ a.length := by
      rw [hsplit, cstr_append, List.length_append, cstr_ascii_length a ha]; omega
    rw [if_neg (by omega), ec1, List.take_of_length_le (by simp)]
    have hsplit2 : cps = a.take n ++ (a.drop n ++ rest) := by
      rw [hsplit, ← List.append_assoc, List.take_append_drop]
    have ha1 : ∀ c ∈ a.take n, c < 0x80 := fun c hc => ha c (List.mem_of_mem_take hc)
    have hl1 : (a.take n).length = n := by simp; omega
    have hv2 : ∀ c ∈ a.drop n ++ rest, valid c := fun c hc => hv c (by rw [hsplit2]; simp [hc])
    have ej : (jstr cps).drop n = jstr (a.drop n ++ rest) := by
      have h := drop_jstr_ascii (a.take n) (a.drop n ++ rest) ha1
      rw [hl1, ← hsplit2] at h; exact h
    have ec : (cstr cps).drop n = cstr (a.drop n ++ rest) := by
      have h := drop_cstr_ascii (a.take n) (a.drop n ++ rest) ha1
      rw [hl1, ← hsplit2] at h; exact h
    rw [ej, ec, unitsToBytes_cstr _ hv2]
    simp [R.agrees]
  · -- past the ASCII prefix: the first non-ASCII character is cut or passed
    apply iff_of_false _ (by omega)
    have hna : a.length < n := by omega
    cases hrest : rest with
    | nil =>
      exfalso
      have : (jstr cps).length = a.length := by
        rw [hsplit, hrest, List.append_nil, jstr_ascii_length a ha]
      omega
    | cons c rs =>
      have hc80 : 0x80 ≤ c := hr c (by simp [hrest])
      have hvc : valid c := hvr c (by simp [hrest])
      have hvrs : ∀ x ∈ rs, valid x := fun x hx => hvr x (by simp [hrest, hx])
      have hcps : cps = a ++ c :: rs := by rw [hsplit, hrest]
      have eJ : (jstr cps).drop n = (utf8 c ++ jstr rs).drop (n - a.length) := by
        rw [hcps, jstr_append, jstr_cons, drop_append_ge _ _ _ (by rw [jstr_ascii_length a ha]; omega),
          jstr_ascii_length a ha]
      have eC : (cstr cps).drop n = (utf16 c ++ cstr rs).drop (n - a.length) := by
        rw [hcps, cstr_append, cstr_cons, drop_append_ge _ _ _ (by rw [cstr_ascii_length a ha]; omega),
          cstr_ascii_length a ha]
      have lenC : (cstr cps).length = a.length + (utf16 c).length + (cstr rs).length := by
        rw [hcps, cstr_append, cstr_cons, List.length_append, List.length_append, cstr_ascii_length a ha]
        omega
      have hgt := utf8_gt_utf16 c hc80
      have hUBrs := units_le_bytes rs
      by_cases hcl : ((cstr cps).length : Int) < n
      · rw [if_pos (Or.inr (Or.inl hcl))]
        simp [R.agrees]
      have ec1 : (((cstr cps).length : Int) - n).toNat = (cstr cps).length - n := by omega
      rw [if_neg (by omega), ec1, List.take_of_length_le (by simp), agrees_str, eJ, eC]
      by_cases hku : (utf16 c).length ≤ n - a.length
      · -- a whole first non-ASCII character is passed: jank keeps more bytes than Clojure
        rw [drop_append_ge _ _ _ hku]
        intro heq
        have hl := congrArg List.length heq
        rw [List.length_drop, List.length_append] at hl
        rcases unitsToBytes_drop_le rs hvrs (n - a.length - (utf16 c).length) with h | h
        · omega
        · omega
      · -- the cut falls inside a surrogate pair: jank's text starts with a continuation byte
        have hsupp : 0x10000 ≤ c := by rw [utf16_length] at hku; split at hku <;> omega
        obtain ⟨hi, lo, he, _, _, hlo, _, l1, l2⟩ := utf16_supp c hsupp hvc.1
        have hk1 : n - a.length = 1 := by rw [he] at hku; simp at hku; omega
        rw [hk1, he]
        simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append]
        rw [unitsToBytes_low_cons lo rs hvrs hlo]
        obtain ⟨b, x, rest2, hu, hx⟩ := utf8_supp_second_ne c hsupp
        obtain ⟨lrest, hl⟩ := utf8_low_head lo l1 l2
        rw [hu, hl]
        simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.cons.injEq]
        intro ⟨h1, _⟩
        exact hx h1

/-- LG3 is the case `i = 2 > asciiPrefix "é-è" = 0`, and round 2's model gives jank's "-è". -/
theorem lg3_model : jSubs1 [0xE9, 0x2D, 0xE8] 2 = .str (jstr [0x2D, 0xE8]) ∧
    cSubs1 [0xE9, 0x2D, 0xE8] 2 = .str (jstr [0xE8]) := by
  refine ⟨by decide, ?_⟩
  have h1 : cSubs1 [0xE9, 0x2D, 0xE8] 2 = .str (unitsToBytes (cstr [0xE8])) := rfl
  rw [h1, unitsToBytes_cstr _ (by simp [valid])]

/-! ## The smallest design change: code-point indexing -/

/-- Code-point `count`, `nth` and `subs` (what persistent_string.cpp `count`/`nth`/`substring`
and string_native.cpp `index_of`/`last_index_of` would compute if they walked `jtl::utf8`
characters, as persistent_string_sequence already does). -/
def cpCount (cps : List Nat) : R := .int cps.length
def cpNth (cps : List Nat) (i : Int) : R :=
  if i < 0 ∨ cps.length ≤ i.toNat then .err "index out of bounds" else .chr (utf8 (cps.getD i.toNat 0))
def cpSubs (cps : List Nat) (start stop : Int) : R :=
  if start < 0 ∨ stop < start ∨ stop.toNat > cps.length then .err "out of bounds"
  else .str (jstr ((cps.drop start.toNat).take (stop - start).toNat))

theorem cstr_bmp (cps : List Nat) (h : ∀ c ∈ cps, c < 0x10000) : cstr cps = cps := by
  induction cps with
  | nil => rfl
  | cons c rest ih =>
    rw [cstr_cons, utf16_bmp c (h c (by simp)), ih (fun x hx => h x (by simp [hx]))]; rfl

/-- ★ The code-point design gives Clojure's `count`, `nth` and `subs` on every valid text without
a supplementary character (every index, every pair of indices). -/
theorem cp_design_agrees_bmp (cps : List Nat) (hv : ∀ c ∈ cps, valid c) (hb : ∀ c ∈ cps, c < 0x10000)
    (i j : Int) :
    cpCount cps = cCount (cstr cps) ∧ (cpNth cps i).agrees (cNth (cstr cps) i) = true ∧
      (cpSubs cps i j).agrees (cSubs (cstr cps) i j) = true := by
  rw [cstr_bmp cps hb]
  refine ⟨rfl, ?_, ?_⟩
  · unfold cpNth cNth
    by_cases hcond : i < 0 ∨ cps.length ≤ i.toNat
    · rw [if_pos hcond, if_pos hcond]; rfl
    · rw [if_neg hcond, if_neg hcond]
      have hlt : i.toNat < cps.length := Nat.lt_of_not_le (not_or.mp hcond).2
      have hm : cps.getD i.toNat 0 ∈ cps := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem _
      have h1 := unitsToBytes_cstr [cps.getD i.toNat 0] (by simpa using hv _ hm)
      rw [cstr_bmp _ (by simpa using hb _ hm)] at h1
      rw [h1]; simp [jstr, R.agrees]
  · unfold cpSubs cSubs
    by_cases hcond : i < 0 ∨ j < i ∨ j.toNat > cps.length
    · rw [if_pos hcond, if_pos hcond]; rfl
    · rw [if_neg hcond, if_neg hcond]
      have hsub : ∀ c ∈ (cps.drop i.toNat).take (j - i).toNat, valid c ∧ c < 0x10000 :=
        fun c hc => ⟨hv c (List.mem_of_mem_drop (List.mem_of_mem_take hc)),
          hb c (List.mem_of_mem_drop (List.mem_of_mem_take hc))⟩
      have h1 := unitsToBytes_cstr _ (fun c hc => (hsub c hc).1)
      rw [cstr_bmp _ (fun c hc => (hsub c hc).2)] at h1
      rw [h1]; simp [R.agrees]

/-- … and still differs from Clojure on a supplementary character: `(count "😀")` is 1 vs 2. -/
theorem cp_design_supplementary : cpCount [0x1F600] ≠ cCount (cstr [0x1F600]) := by decide

/-- jank's byte design is coherent with itself: `(subs s (count s))` is "" for every string … -/
theorem byte_subs_count_coherent (s : List UInt8) : jSubs s s.length s.length = .str [] := by
  simp [jSubs]

/-- … while a code-point `subs` beside the byte `count` is not: `(subs "é" (count "é"))` throws. -/
theorem mixed_design_incoherent :
    cpSubs [0xE9] (jstr [0xE9]).length (jstr [0xE9]).length = .err "out of bounds" := by decide

end Jank.R6.Str

import Jank.R6.Str.Proofs

/-!
# Round 6, strings: `(count (seq s))` for every text (R53, made exact)

Round 2's `jSeqCount` replicates persistent_string_sequence.cpp `count` 78–88 (a walk by
`jtl::next_char_size`, utf8.cpp 13–36); `jCount` replicates persistent_string.cpp `count` 179–182
(`data.size()`). For every valid text:

- `seqCount_jstr` ★: jank's `(count (seq s))` is the number of code points;
- `seqCount_eq_count_iff` ★ (R53): it equals jank's own `(count s)` exactly when the text is ASCII;
- `seqCount_eq_clojure_iff` ★: it equals Clojure's `(count (seq s))` exactly when the text has no
  supplementary character (the code-point-character design choice, alone).
-/

namespace Jank.R6.Str

open Jank.Str

theorem getD_mid (pre tl post : List UInt8) (b : UInt8) :
    (pre ++ (b :: tl) ++ post).getD pre.length 0 = b := by
  rw [List.append_assoc, List.cons_append, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem lead1 : ∀ c, c < 128 → (c.toUInt8).toNat ≤ 0x7f := by decide
theorem lead2 : ∀ y, y < 32 →
    ¬ ((0xC0 ||| y).toUInt8.toNat ≤ 0x7f) ∧ ((0xC0 ||| y).toUInt8.toNat &&& 0xE0 == 0xC0) = true := by decide
theorem lead3 : ∀ y, y < 16 →
    ¬ ((0xE0 ||| y).toUInt8.toNat ≤ 0x7f) ∧ ((0xE0 ||| y).toUInt8.toNat &&& 0xE0 == 0xC0) = false ∧
      ((0xE0 ||| y).toUInt8.toNat &&& 0xF0 == 0xE0) = true := by decide
theorem lead4 : ∀ y, y < 5 →
    ¬ ((0xF0 ||| y).toUInt8.toNat ≤ 0x7f) ∧ ((0xF0 ||| y).toUInt8.toNat &&& 0xE0 == 0xC0) = false ∧
      ((0xF0 ||| y).toUInt8.toNat &&& 0xF0 == 0xE0) = false ∧
      ((0xF0 ||| y).toUInt8.toNat &&& 0xF8 == 0xF0) = true := by decide

/-- `next_char_size` at the start of a valid character gives its UTF-8 length. -/
theorem nextCharSize_utf8 (pre post : List UInt8) (c : Nat) (hc : c < 0x110000) :
    nextCharSize (pre ++ utf8 c ++ post) pre.length = .ok (utf8 c).length := by
  have hsh : ∀ k, c >>> k = c / 2 ^ k := fun k => Nat.shiftRight_eq_div_pow c k
  by_cases h1 : c < 0x80
  · have e : utf8 c = [c.toUInt8] := by simp [utf8, h1]
    rw [e]
    simp only [nextCharSize, getD_mid, List.length_singleton]
    rw [if_pos (lead1 c h1)]
  by_cases h2 : c < 0x800
  · have e : utf8 c = [(0xC0 ||| (c >>> 6)).toUInt8, (0x80 ||| (c &&& 0x3F)).toUInt8] := by
      simp [utf8, h1, h2]
    obtain ⟨a, b⟩ := lead2 (c >>> 6) (by rw [hsh]; omega)
    rw [e]
    simp only [nextCharSize, getD_mid, List.length_cons, List.length_nil]
    rw [if_neg a, if_pos b]
  by_cases h3 : c < 0x10000
  · have e : utf8 c = [(0xE0 ||| (c >>> 12)).toUInt8, (0x80 ||| ((c >>> 6) &&& 0x3F)).toUInt8,
        (0x80 ||| (c &&& 0x3F)).toUInt8] := by simp [utf8, h1, h2, h3]
    obtain ⟨a, b, d⟩ := lead3 (c >>> 12) (by rw [hsh]; omega)
    rw [e]
    simp only [nextCharSize, getD_mid, List.length_cons, List.length_nil]
    rw [if_neg a, if_neg (by rw [b]; exact Bool.false_ne_true), if_pos d]
  · have e : utf8 c = [(0xF0 ||| (c >>> 18)).toUInt8, (0x80 ||| ((c >>> 12) &&& 0x3F)).toUInt8,
        (0x80 ||| ((c >>> 6) &&& 0x3F)).toUInt8, (0x80 ||| (c &&& 0x3F)).toUInt8] := by
      simp [utf8, h1, h2, h3]
    obtain ⟨a, b, d, f⟩ := lead4 (c >>> 18) (by rw [hsh]; omega)
    rw [e]
    simp only [nextCharSize, getD_mid, List.length_cons, List.length_nil]
    rw [if_neg a, if_neg (by rw [b]; exact Bool.false_ne_true), if_neg (by rw [d]; exact Bool.false_ne_true), if_pos f]

theorem utf8_ne_nil (c : Nat) : utf8 c ≠ [] := by
  intro h; have := utf8_length_pos' c; rw [h] at this; simp at this
where
  utf8_length_pos' (c : Nat) : 1 ≤ (utf8 c).length := by
    rw [utf8_length]; split <;> (try split) <;> (try split) <;> omega

theorem seqCount_go (cps : List Nat) (hv : ∀ c ∈ cps, valid c) :
    ∀ (s pre : List UInt8) (n fuel : Nat), s = pre ++ jstr cps → cps.length < fuel →
      jSeqCount.go s fuel pre.length n = .int (n + cps.length) := by
  induction cps with
  | nil =>
    intro s pre n fuel hs hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp only [jSeqCount.go]
    rw [if_pos (by rw [hs]; simp [jstr])]
    simp
  | cons c rest ih =>
    intro s pre n fuel hs hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hc := hv c (by simp)
    have hlen : ¬ s.length ≤ pre.length := by
      rw [hs, jstr_cons, List.length_append, List.length_append]
      have := utf8_ne_nil c
      have : 0 < (utf8 c).length := List.length_pos_iff.mpr this
      omega
    have hs' : s = pre ++ utf8 c ++ jstr rest := by rw [hs, jstr_cons, List.append_assoc]
    simp only [jSeqCount.go]
    rw [if_neg hlen, hs', nextCharSize_utf8 pre (jstr rest) c hc.1]
    simp only
    have := ih (fun x hx => hv x (by simp [hx])) (pre ++ utf8 c ++ jstr rest) (pre ++ utf8 c) (n + 1) f
      (by rw [List.append_assoc]) (by simp at hf; omega)
    rw [List.length_append] at this
    rw [this]
    simp; omega

theorem length_le_jstr (cps : List Nat) : cps.length ≤ (jstr cps).length := by
  induction cps with
  | nil => simp [jstr]
  | cons c rest ih =>
    rw [jstr_cons, List.length_append, List.length_cons]
    have := List.length_pos_iff.mpr (utf8_ne_nil c); omega

/-- ★ jank's `(count (seq s))` is the number of code points of every valid text. -/
theorem seqCount_jstr (cps : List Nat) (hv : ∀ c ∈ cps, valid c) : jSeqCount (jstr cps) = .int cps.length := by
  unfold jSeqCount
  cases cps with
  | nil => simp [jstr]
  | cons c rest =>
    have hne : (jstr (c :: rest)).isEmpty = false := by
      rw [jstr_cons]; cases h : utf8 c with
      | nil => exact absurd h (utf8_ne_nil c)
      | cons b bs => simp
    rw [if_neg (by simp [hne])]
    have := seqCount_go (c :: rest) hv (jstr (c :: rest)) [] 0 ((jstr (c :: rest)).length + 1) (by simp)
      (by have := length_le_jstr (c :: rest); omega)
    simpa using this

theorem length_le_cstr (cps : List Nat) : cps.length ≤ (cstr cps).length := by
  induction cps with
  | nil => simp [cstr]
  | cons c rest ih => rw [cstr_cons, List.length_append, List.length_cons, utf16_length]; split <;> omega

theorem jstr_length_eq_iff (cps : List Nat) : (jstr cps).length = cps.length ↔ ∀ c ∈ cps, c < 0x80 := by
  constructor
  · intro h
    have h1 := count_ge cps
    have h2 := length_le_cstr cps
    exact (count_eq_iff cps).mp (by omega)
  · exact jstr_ascii_length cps

theorem cstr_length_eq_iff (cps : List Nat) : (cstr cps).length = cps.length ↔ ∀ c ∈ cps, c < 0x10000 := by
  induction cps with
  | nil => simp [cstr]
  | cons c rest ih =>
    rw [cstr_cons, List.length_append, List.length_cons, utf16_length]
    have hr := length_le_cstr rest
    simp only [List.mem_cons, forall_eq_or_imp]
    split
    · rename_i h; constructor
      · intro e; exact ⟨h, ih.mp (by omega)⟩
      · intro ⟨_, e⟩; have := ih.mpr e; omega
    · rename_i h; constructor
      · intro e; omega
      · intro ⟨e, _⟩; exact absurd e h

/-- ★ R53 exactly: jank's `(count (seq s))` equals its own `(count s)` iff the text is ASCII. -/
theorem seqCount_eq_count_iff (cps : List Nat) (hv : ∀ c ∈ cps, valid c) :
    jSeqCount (jstr cps) = jCount (jstr cps) ↔ ∀ c ∈ cps, c < 0x80 := by
  rw [seqCount_jstr cps hv, jCount, ← jstr_length_eq_iff]
  constructor
  · intro h; have := R.int.inj h; omega
  · intro h; rw [h]

/-- ★ … and Clojure's `(count (seq s))` iff no character is supplementary. -/
theorem seqCount_eq_clojure_iff (cps : List Nat) (hv : ∀ c ∈ cps, valid c) :
    jSeqCount (jstr cps) = cSeqCount (cstr cps) ↔ ∀ c ∈ cps, c < 0x10000 := by
  rw [seqCount_jstr cps hv, cSeqCount, ← cstr_length_eq_iff]
  constructor
  · intro h; have := R.int.inj h; omega
  · intro h; rw [h]

end Jank.R6.Str

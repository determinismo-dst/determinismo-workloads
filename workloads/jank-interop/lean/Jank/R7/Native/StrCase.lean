import Jank.StrModel
import Jank.R6.Str.Cut

/-!
# Round 7, strings: R60, the JDK's full case mapping beside jank's one-code-point mapping

**Clojure** (string.clj `upper-case`/`lower-case`/`capitalize`): `String.toUpperCase()` /
`toLowerCase()` in the default locale (en_CA on the JVM that ran Clojure 1.12.3; the root locale
gives the same answers for every code point, checked). They apply Unicode's SpecialCasing:
- upper: 102 code points map to two or three code points. The table below was derived on JDK 23
  (Unicode 15.1) by comparing `String.valueOf(Character.toChars(c)).toUpperCase(Locale.ROOT)`
  with `Character.toUpperCase(c)` for every scalar value c (`.r7-scratch/native/probe1.clj`):
  ß ŉ ǰ ΐ ΰ և ẖ ẗ ẘ ẙ ẚ, the Greek breathings ὐ ὒ ὔ ὖ, the 48 ypogegrammeni/prosgegrammeni
  forms ᾀ–ᾯ ᾲ–ᾷ ᾼ ῂ–ῇ ῌ ῒ ΐ ῖ ῗ ῢ ΰ ῤ ῦ ῧ ῲ–ῷ ῼ, the Latin ligatures ﬀ ﬁ ﬂ ﬃ ﬄ ﬅ ﬆ and the Armenian
  ﬓ–ﬗ;
- lower: one code point, İ (U+0130) → i + U+0307, plus the conditional Final_Sigma: Σ is ς at the
  end of a word (run: "ΣΑΣ" → "σας", "ΑΣ Α" → "ας α", "ΑΣ." → "ας.", "Σ" → "σ").
- capitalize: `(str (.toUpperCase (subs s 0 1)) (.toLowerCase (subs s 1)))`: "ßa" → "SSa".

**jank** (util/string.cpp `to_uppercase` 26-36, `to_lowercase` 14-24): `wstring_convert<
codecvt_utf8<wchar_t>>::from_bytes`, then `std::use_facet<std::ctype<wchar_t>>(std::locale(""))
.toupper(begin, end)` in place: one `wchar_t` in, one out (libstdc++'s `ctype<wchar_t>::do_toupper`
→ glibc `towupper_l`, a simple one-to-one mapping), then `to_bytes`. No code point can become two,
and no context is looked at. capitalize (string.jank 156-164 → util/string.cpp `capitalize` 54-70)
lower-cases, then `std::toupper` of the first byte only (R61).

So R60 holds for every text holding one of the 103 code points, or a final Σ, whatever glibc's
simple tables say (theorem `upper_count_differs`, for every simple mapping).
-/

namespace Jank.R7.Native.StrCase

open Jank.Str Jank.R6.Str

/-- JDK 23's unconditional special upper-case mappings (complete: 102 entries). -/
def jdkSpecialUpper : List (Nat × List Nat) :=
  [(0x00DF, [0x0053, 0x0053]), (0x0149, [0x02BC, 0x004E]), (0x01F0, [0x004A, 0x030C]), (0x0390, [0x0399, 0x0308, 0x0301]),
   (0x03B0, [0x03A5, 0x0308, 0x0301]), (0x0587, [0x0535, 0x0552]), (0x1E96, [0x0048, 0x0331]), (0x1E97, [0x0054, 0x0308]),
   (0x1E98, [0x0057, 0x030A]), (0x1E99, [0x0059, 0x030A]), (0x1E9A, [0x0041, 0x02BE]), (0x1F50, [0x03A5, 0x0313]),
   (0x1F52, [0x03A5, 0x0313, 0x0300]), (0x1F54, [0x03A5, 0x0313, 0x0301]), (0x1F56, [0x03A5, 0x0313, 0x0342]), (0x1F80, [0x1F08, 0x0399]),
   (0x1F81, [0x1F09, 0x0399]), (0x1F82, [0x1F0A, 0x0399]), (0x1F83, [0x1F0B, 0x0399]), (0x1F84, [0x1F0C, 0x0399]),
   (0x1F85, [0x1F0D, 0x0399]), (0x1F86, [0x1F0E, 0x0399]), (0x1F87, [0x1F0F, 0x0399]), (0x1F88, [0x1F08, 0x0399]),
   (0x1F89, [0x1F09, 0x0399]), (0x1F8A, [0x1F0A, 0x0399]), (0x1F8B, [0x1F0B, 0x0399]), (0x1F8C, [0x1F0C, 0x0399]),
   (0x1F8D, [0x1F0D, 0x0399]), (0x1F8E, [0x1F0E, 0x0399]), (0x1F8F, [0x1F0F, 0x0399]), (0x1F90, [0x1F28, 0x0399]),
   (0x1F91, [0x1F29, 0x0399]), (0x1F92, [0x1F2A, 0x0399]), (0x1F93, [0x1F2B, 0x0399]), (0x1F94, [0x1F2C, 0x0399]),
   (0x1F95, [0x1F2D, 0x0399]), (0x1F96, [0x1F2E, 0x0399]), (0x1F97, [0x1F2F, 0x0399]), (0x1F98, [0x1F28, 0x0399]),
   (0x1F99, [0x1F29, 0x0399]), (0x1F9A, [0x1F2A, 0x0399]), (0x1F9B, [0x1F2B, 0x0399]), (0x1F9C, [0x1F2C, 0x0399]),
   (0x1F9D, [0x1F2D, 0x0399]), (0x1F9E, [0x1F2E, 0x0399]), (0x1F9F, [0x1F2F, 0x0399]), (0x1FA0, [0x1F68, 0x0399]),
   (0x1FA1, [0x1F69, 0x0399]), (0x1FA2, [0x1F6A, 0x0399]), (0x1FA3, [0x1F6B, 0x0399]), (0x1FA4, [0x1F6C, 0x0399]),
   (0x1FA5, [0x1F6D, 0x0399]), (0x1FA6, [0x1F6E, 0x0399]), (0x1FA7, [0x1F6F, 0x0399]), (0x1FA8, [0x1F68, 0x0399]),
   (0x1FA9, [0x1F69, 0x0399]), (0x1FAA, [0x1F6A, 0x0399]), (0x1FAB, [0x1F6B, 0x0399]), (0x1FAC, [0x1F6C, 0x0399]),
   (0x1FAD, [0x1F6D, 0x0399]), (0x1FAE, [0x1F6E, 0x0399]), (0x1FAF, [0x1F6F, 0x0399]), (0x1FB2, [0x1FBA, 0x0399]),
   (0x1FB3, [0x0391, 0x0399]), (0x1FB4, [0x0386, 0x0399]), (0x1FB6, [0x0391, 0x0342]), (0x1FB7, [0x0391, 0x0342, 0x0399]),
   (0x1FBC, [0x0391, 0x0399]), (0x1FC2, [0x1FCA, 0x0399]), (0x1FC3, [0x0397, 0x0399]), (0x1FC4, [0x0389, 0x0399]),
   (0x1FC6, [0x0397, 0x0342]), (0x1FC7, [0x0397, 0x0342, 0x0399]), (0x1FCC, [0x0397, 0x0399]), (0x1FD2, [0x0399, 0x0308, 0x0300]),
   (0x1FD3, [0x0399, 0x0308, 0x0301]), (0x1FD6, [0x0399, 0x0342]), (0x1FD7, [0x0399, 0x0308, 0x0342]), (0x1FE2, [0x03A5, 0x0308, 0x0300]),
   (0x1FE3, [0x03A5, 0x0308, 0x0301]), (0x1FE4, [0x03A1, 0x0313]), (0x1FE6, [0x03A5, 0x0342]), (0x1FE7, [0x03A5, 0x0308, 0x0342]),
   (0x1FF2, [0x1FFA, 0x0399]), (0x1FF3, [0x03A9, 0x0399]), (0x1FF4, [0x038F, 0x0399]), (0x1FF6, [0x03A9, 0x0342]),
   (0x1FF7, [0x03A9, 0x0342, 0x0399]), (0x1FFC, [0x03A9, 0x0399]), (0xFB00, [0x0046, 0x0046]), (0xFB01, [0x0046, 0x0049]),
   (0xFB02, [0x0046, 0x004C]), (0xFB03, [0x0046, 0x0046, 0x0049]), (0xFB04, [0x0046, 0x0046, 0x004C]), (0xFB05, [0x0053, 0x0054]),
   (0xFB06, [0x0053, 0x0054]), (0xFB13, [0x0544, 0x0546]), (0xFB14, [0x0544, 0x0535]), (0xFB15, [0x0544, 0x053B]),
   (0xFB16, [0x054E, 0x0546]), (0xFB17, [0x0544, 0x053D])]

/-- JDK 23's unconditional special lower-case mappings (complete: 1 entry). -/
def jdkSpecialLower : List (Nat × List Nat) := [(0x0130, [0x0069, 0x0307])]

def special (tbl : List (Nat × List Nat)) (c : Nat) : Option (List Nat) :=
  (tbl.find? (·.1 == c)).map (·.2)

/-- Java's full mapping of a text (code points): a special entry, else the simple mapping `g`. -/
def javaMap (tbl : List (Nat × List Nat)) (g : Nat → Nat) : List Nat → List Nat
  | [] => []
  | c :: rest => (special tbl c).getD [g c] ++ javaMap tbl g rest

/-- jank's mapping of a text: `ctype<wchar_t>::toupper`, one code point per code point, whatever
the simple mapping `f` (glibc's) is. -/
def jankMap (f : Nat → Nat) (cps : List Nat) : List Nat := cps.map f

theorem special_upper_long : ∀ p ∈ jdkSpecialUpper, 2 ≤ p.2.length := by decide
theorem special_lower_long : ∀ p ∈ jdkSpecialLower, 2 ≤ p.2.length := by decide
theorem special_upper_count : jdkSpecialUpper.length = 102 := by decide

theorem special_long {tbl : List (Nat × List Nat)} (h : ∀ p ∈ tbl, 2 ≤ p.2.length) {c : Nat}
    {us : List Nat} (hs : special tbl c = some us) : 2 ≤ us.length := by
  unfold special at hs
  cases hf : tbl.find? (·.1 == c) with
  | none => simp [hf] at hs
  | some p =>
    simp [hf] at hs
    subst hs
    exact h p (List.mem_of_find?_eq_some hf)

theorem getD_len {tbl : List (Nat × List Nat)} (h : ∀ p ∈ tbl, 2 ≤ p.2.length) (g : Nat → Nat)
    (c : Nat) : 1 ≤ ((special tbl c).getD [g c]).length := by
  cases hs : special tbl c with
  | none => simp
  | some us => have := special_long h hs; simp; omega

theorem javaMap_len_ge {tbl : List (Nat × List Nat)} (h : ∀ p ∈ tbl, 2 ≤ p.2.length)
    (g : Nat → Nat) (cps : List Nat) : cps.length ≤ (javaMap tbl g cps).length := by
  induction cps with
  | nil => simp [javaMap]
  | cons c rest ih =>
    simp only [javaMap, List.length_append, List.length_cons]
    have := getD_len h g c
    omega

/-- ★ For every text holding a code point of the table, and for every pair of simple mappings
(jank's glibc `towupper`, Java's `Character.toUpperCase`), Java's result has more code points
than jank's: the results differ. -/
theorem count_differs {tbl : List (Nat × List Nat)} (h : ∀ p ∈ tbl, 2 ≤ p.2.length)
    (f g : Nat → Nat) (cps : List Nat) (hc : ∃ c ∈ cps, (special tbl c).isSome) :
    (jankMap f cps).length < (javaMap tbl g cps).length := by
  simp only [jankMap, List.length_map]
  induction cps with
  | nil => simp at hc
  | cons c rest ih =>
    simp only [javaMap, List.length_append, List.length_cons]
    cases hs : special tbl c with
    | some us =>
      have h2 := special_long h hs
      have := javaMap_len_ge h g rest
      simp only [Option.getD_some]
      omega
    | none =>
      have hrest : ∃ c ∈ rest, (special tbl c).isSome := by
        obtain ⟨d, hd, hds⟩ := hc
        rcases List.mem_cons.mp hd with rfl | hd'
        · simp [hs] at hds
        · exact ⟨d, hd', hds⟩
      have := ih hrest
      simp only [Option.getD_none, List.length_singleton]
      omega

/-- ★ R60 for upper-case: every text with one of JDK 23's 102 special code points. -/
theorem upper_count_differs (f g : Nat → Nat) (cps : List Nat)
    (hc : ∃ c ∈ cps, (special jdkSpecialUpper c).isSome) :
    (jankMap f cps).length < (javaMap jdkSpecialUpper g cps).length :=
  count_differs special_upper_long f g cps hc

/-- ★ R60 for lower-case: every text with İ. -/
theorem lower_count_differs (f g : Nat → Nat) (cps : List Nat)
    (hc : ∃ c ∈ cps, (special jdkSpecialLower c).isSome) :
    (jankMap f cps).length < (javaMap jdkSpecialLower g cps).length :=
  count_differs special_lower_long f g cps hc

/-! ## The tests' values

glibc's simple mappings for the code points the tests use (UnicodeData.txt's simple fields, which
glibc's locale data follows: assumption WA7-1): ß ŉ ǰ ﬁ have no simple upper case; ᾳ (U+1FB3) →
ᾼ (U+1FBC); İ → i (U+0069); Σ → σ. -/

def towupper7 (c : Nat) : Nat :=
  if c == 0x1FB3 then 0x1FBC else towupper .utf8 c

def towlower7 (c : Nat) : Nat :=
  if c == 0x130 then 0x69 else if c == 0x391 then 0x3B1 else towlower .utf8 c

/-- jank's `upper-case` / `lower-case` of a valid text (with the corrected decoder). -/
def jUpper (s : List UInt8) : R := match fromBytes s with
  | .ok cps => .str ((jankMap towupper7 cps).flatMap utf8) | .error _ => .err "wstring_convert::from_bytes"
def jLower (s : List UInt8) : R := match fromBytes s with
  | .ok cps => .str ((jankMap towlower7 cps).flatMap utf8) | .error _ => .err "wstring_convert::from_bytes"

/-- Java's `toUpperCase` with the table (simple mapping as glibc's for these code points). -/
def cUpper (cps : List Nat) : R := .str ((javaMap jdkSpecialUpper towupper7 cps).flatMap utf8)

theorem upper_values :
    jUpper (jstr [0xDF]) = .str (jstr [0xDF]) ∧ cUpper [0xDF] = .str (jstr [0x53, 0x53]) ∧
    jUpper (jstr [0x149]) = .str (jstr [0x149]) ∧ cUpper [0x149] = .str (jstr [0x2BC, 0x4E]) ∧
    jUpper (jstr [0x1F0]) = .str (jstr [0x1F0]) ∧ cUpper [0x1F0] = .str (jstr [0x4A, 0x30C]) ∧
    jUpper (jstr [0xFB01]) = .str (jstr [0xFB01]) ∧ cUpper [0xFB01] = .str (jstr [0x46, 0x49]) ∧
    jUpper (jstr [0x1FB3]) = .str (jstr [0x1FBC]) ∧ cUpper [0x1FB3] = .str (jstr [0x391, 0x399]) := by
  decide

/-- İ and final sigma: jank "i" and "σασ"; Clojure "i̇" (2 code points) and "σας". -/
theorem lower_values :
    jLower (jstr [0x130]) = .str (jstr [0x69]) ∧
    jLower (jstr [0x3A3, 0x391, 0x3A3]) = .str (jstr [0x3C3, 0x3B1, 0x3C3]) := by
  decide

/-- capitalize "ßa": jank lower-cases ("ßa") and upper-cases the first byte 0xC3, which no locale
changes (R61): "ßa"; Clojure "SSa". -/
def jCapitalize7 (s : List UInt8) : R :=
  match jLower s with
  | .str (b :: rest) => .str ((if 0x61 ≤ b && b ≤ 0x7A then b - 32 else b) :: rest)
  | r => r

theorem capitalize_value : jCapitalize7 (jstr [0xDF, 0x61]) = .str (jstr [0xDF, 0x61]) := by
  decide

end Jank.R7.Native.StrCase

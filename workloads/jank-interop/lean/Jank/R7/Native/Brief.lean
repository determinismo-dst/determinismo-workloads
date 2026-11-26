import Jank.StrModel
import Jank.R6.Str.Cut
import Jank.R6.Str.Fixes

/-!
# Round 7, brief check: the real jank's string observations put to round 6's string model

The coordinator ran round 6's tests on jank main 7135b7708 (Linux x86-64) and observed:

1. `(clojure.string/index-of "a" "a" -1)` is nil (Clojure 0): V74.
2. `(clojure.string/index-of "a" "" 5)` is nil (Clojure 1): V74.
3. `(clojure.string/last-index-of "aa" "a" -1)` is 1 (Clojure nil): V74.
4. `(clojure.string/upper-case (subs "é" 1))` throws "wstring_convert::from_bytes": V67.
5. `(clojure.string/split "aéb" #"")` splits é into its two bytes: V75 (round 3's regex replica,
   evaluated by the driver: `jank7-native brief`).

Each is stated below on round 6's functions (`Jank.Str.jIndexOf`, `jLastIndexOf`, `jSubs`,
`Jank.R6.Str.jUpper6`) beside Clojure's (`cIndexOf'`, `cLastIndexOf'`, `cSubs`, `cUpper`).

**One model refinement (round 6's `fromBytes`).** Round 6 labelled the decoder's failure
"range_error". libstdc++ 15.3.0 throws `std::range_error` with the text
"wstring_convert::from_bytes" (deps/libstdcxx-15.3.0-codecvt/locale_conv.h 346:
`__throw_range_error("wstring_convert::from_bytes")`); jank's runner prints that `what()`.
`jUpper7` below is `jUpper6` with the exact text; nothing else in round 6 depended on the label
(`w4_values` states the old label and still holds for `jUpper6`).
-/

namespace Jank.R7.Native.Brief

open Jank.Str Jank.R6.Str

/-- `to_uppercase` (util/string.cpp 26-36) with libstdc++'s exact exception text. Extends round 6's
`jUpper6`, whose error label was not the `what()` string. -/
def jUpper7 (loc : Locale) (s : List UInt8) : R :=
  match fromBytes s with
  | .ok cps => .str (cps.flatMap fun c => utf8 (towupper loc c))
  | .error _ => .err "wstring_convert::from_bytes"

def jLower7 (loc : Locale) (s : List UInt8) : R :=
  match fromBytes s with
  | .ok cps => .str (cps.flatMap fun c => utf8 (towlower loc c))
  | .error _ => .err "wstring_convert::from_bytes"

/-- Observations 1-3: round 6's `jIndexOf`/`jLastIndexOf` give exactly the real jank's values,
and Clojure's are 0, 1 and nil. -/
theorem brief_index_of :
    jIndexOf [0x61] [0x61] (-1) = .nil ∧ cIndexOf' [0x61] [0x61] (-1) = .int 0 ∧
    jIndexOf [0x61] [] 5 = .nil ∧ cIndexOf' [0x61] [] 5 = .int 1 ∧
    jLastIndexOf [0x61, 0x61] [0x61] (-1) = .int 1 ∧ cLastIndexOf' [0x61, 0x61] [0x61] (-1) = .nil := by
  decide

/-- Observation 4: `(subs "é" 1)` is the byte 0xA9 in jank and "" in Clojure; round 6's
`jUpper6` throws (`std::range_error`), and with libstdc++'s text the error is exactly the one the
real jank printed. Clojure gives "" (`(subs "é" 1)` is "" in UTF-16 units, run on 1.12.3). -/
theorem brief_upper_of_cut :
    jSubs (jstr [0xE9]) 1 2 = .str [0xA9] ∧
    jUpper6 .utf8 [0xA9] = .err "range_error" ∧
    jUpper7 .utf8 [0xA9] = .err "wstring_convert::from_bytes" ∧
    jUpper7 .c [0xA9] = .err "wstring_convert::from_bytes" := by
  decide

/-- The refinement changes no value: `jUpper7` and `jUpper6` agree on every byte string except
for the error's text. -/
theorem jUpper7_agrees_jUpper6 (loc : Locale) (s : List UInt8) :
    (∀ b, jUpper6 loc s = .str b ↔ jUpper7 loc s = .str b) ∧
    ((∃ w, jUpper6 loc s = .err w) ↔ (∃ w, jUpper7 loc s = .err w)) := by
  unfold jUpper6 jUpper7
  cases fromBytes s <;> simp

end Jank.R7.Native.Brief

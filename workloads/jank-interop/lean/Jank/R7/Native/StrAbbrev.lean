import Jank.StrModel

/-!
# Round 7, strings: the nREPL's `abbreviate` (src/jank/jank/nrepl/server/util.jank 4-11)

    (defn abbreviate [form n]
      (letfn [(inner [x] (if (and (string? x) (>= (count x) n)) (str (subs x 0 n) "…") x))]
        (postwalk inner form)))

- Its only callers are the two `log` lines of nrepl/server/core.jank `handle-client` 86 and 89:
  `(log "<-" (pr-str (abbreviate req 20)))` before each request is handled and
  `(log "->" (pr-str (abbreviate resp 20)))` before each response is written. `log` (29-31) is a
  defn, so its arguments are evaluated for every message, verbose or not; it prints only under `-v`.
- What a client receives: nothing from `abbreviate`. `write-message` (73-78) bencodes the original
  `resp`; the abbreviated copy goes only to the server's own stdout, and only in verbose mode.
- Does anything throw: no. `(count x)` and `subs` both count bytes (persistent_string.cpp count
  179, substring 133-155), so `(subs x 0 n)` with `n ≤ (count x)` is always in range
  (`subs_in_range`), and `pr-str` escapes byte by byte (util/escape.cpp `escape` 147-198), which
  never decodes UTF-8.
- Invalid UTF-8: yes, in the log. When byte n = 20 falls inside a multi-byte character, the logged
  string keeps that character's first bytes and then "…" (E2 80 A6): e.g. "a" followed by ten é
  (21 bytes) is logged as "a" + nine é + 0xC3 + "…" (`log_example`). The walk in the driver
  (`jank7-native abbrev`) gives the exact rule: the output is valid exactly when the input is
  shorter than n bytes or byte n starts a character.
- Clojure has no `abbreviate`; under Clojure's `count`/`subs` (UTF-16 units) the same function
  would cut at 20 units (only a surrogate pair could be split). jank's function is its own: noted,
  not a deviation from Clojure.
-/

namespace Jank.R7.Native.StrAbbrev

open Jank.Str

def ellipsis : List UInt8 := utf8 0x2026

/-- `inner` on one string, as jank computes it (bytes). -/
def jAbbrev (n : Nat) (s : List UInt8) : List UInt8 :=
  if n ≤ s.length then s.take n ++ ellipsis else s

/-- The same code under Clojure's `count`/`subs` (UTF-16 units). -/
def cAbbrev (n : Nat) (s : List Nat) : List Nat :=
  if n ≤ s.length then s.take n ++ [0x2026] else s

/-- ★ `abbreviate` never throws: for every string and every n, the `subs` it calls is in range
(round 2's `jSubs`, persistent_string.cpp substring 133-155). -/
theorem subs_in_range (s : List UInt8) (n : Nat) (h : n ≤ s.length) :
    jSubs s 0 n = .str (s.take n) := by
  have h1 : ¬ ((n : Int) < 0) := by omega
  have h3 : ¬ s.length < n := by omega
  simp [jSubs, h1, h3]

/-- A start of a character: not a continuation byte (or the end). -/
def boundary (s : List UInt8) (n : Nat) : Bool := n ≥ s.length || (s.getD n 0).toNat &&& 0xC0 != 0x80

/-- The log line of a 21-byte value, "a" and ten é: a cut é (its lead byte 0xC3 followed by
"…"'s 0xE2, not a continuation byte): invalid UTF-8 (the driver's walk decodes it). -/
theorem log_example :
    jAbbrev 20 (jstr (0x61 :: List.replicate 10 0xE9)) =
      jstr (0x61 :: List.replicate 9 0xE9) ++ [0xC3] ++ ellipsis ∧
    boundary (jstr (0x61 :: List.replicate 10 0xE9)) 20 = false := by
  decide

/-- Ten é (20 bytes) are logged whole with "…" appended; Clojure's units (10) would leave the
string alone. -/
theorem ten_e_acute :
    jAbbrev 20 (jstr (List.replicate 10 0xE9)) = jstr (List.replicate 10 0xE9) ++ ellipsis ∧
    cAbbrev 20 (cstr (List.replicate 10 0xE9)) = cstr (List.replicate 10 0xE9) := by
  decide

end Jank.R7.Native.StrAbbrev

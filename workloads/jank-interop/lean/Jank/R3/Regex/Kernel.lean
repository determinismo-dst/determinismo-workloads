import Jank.R3.Regex.JankFns

/-!
# Concrete programs checked by the kernel

Each statement runs the replica (scanner, compiler and, from `e_acute_star_needs_lead_byte` on,
the DFS executor) in the kernel with `decide +kernel`. Patterns and inputs are UTF-8 bytes.
-/

namespace Jank.R3.Regex

def compiles (p : List Nat) : Bool :=
  match compile .utf8 p with
  | .ok _ => true
  | .error _ => false

def errCode (p : List Nat) : Option ErrCode :=
  match compile .utf8 p with
  | .ok _ => none
  | .error e => some e.code

/-- RX: `#"[a-é]"` is a read error (`error_range`): 'a' > (char)0xC3. -/
theorem read_error_range_a_to_e_acute : errCode [0x5B, 0x61, 0x2D, 0xC3, 0xA9, 0x5D] = some .range := by
  decide +kernel

/-- RX: `#"^*a"` is a read error: `_M_term` takes no quantifier after an assertion, and the
`*` left over fails the end-of-pattern check (`error_paren`). -/
theorem read_error_quantified_caret : errCode [0x5E, 0x2A, 0x61] = some .paren := by
  decide +kernel

/-- R18 corrected: `#"a*+"` compiles (a greedy repeat of `a*`), it is not a read error. -/
theorem possessive_compiles : compiles [0x61, 0x2A, 0x2B] = true := by
  decide +kernel

def V.isNil : V → Bool
  | .nil => true
  | _ => false

def V.asStr? : V → Option (List Nat)
  | .str b => some b
  | _ => none

def V.asVec? : V → Option (List (Option (List Nat)))
  | .vec xs => some xs
  | _ => none

/-- `re-matches` on a compiled pattern, run in the kernel. -/
def kMatches (p s : List Nat) : V :=
  match compile .utf8 p with
  | .ok nfa => jReMatches nfa s { budget := 1000, fuel := 100 }
  | .error e => .err e.what

def kFind (p s : List Nat) : V :=
  match compile .utf8 p with
  | .ok nfa => jReFind nfa s { budget := 1000, fuel := 100 }
  | .error e => .err e.what

/-- RX (R78): `(re-matches #"é*" "")` is nil: the `*` repeats only the byte 0xA9, after a
required 0xC3 (Clojure: ""). -/
theorem e_acute_star_needs_lead_byte : (kMatches [0xC3, 0xA9, 0x2A] []).isNil = true := by
  decide +kernel

/-- RX: `(re-find #"a(?=\b)" "ab")` is "a": the lookahead's sub-executor starts at 1 as if it
were the start of the input, so `\b` sees no character before it (Clojure: nil). -/
theorem lookahead_boundary_example :
    (kFind [0x61, 0x28, 0x3F, 0x3D, 0x5C, 0x62, 0x29] [0x61, 0x62]).asStr? = some [0x61] := by
  decide +kernel

/-- RX: `(re-find #"a++a" "aaa")` is "aaa": `a++` is `(a+)+`, not possessive (Clojure: nil). -/
theorem possessive_backtracks : (kFind [0x61, 0x2B, 0x2B, 0x61] [0x61, 0x61, 0x61]).asStr? = some [0x61, 0x61, 0x61] := by
  decide +kernel

/-- RX: `(re-find #"\u0141" "A")` is "A": the code point is cut to its low byte (Clojure: nil). -/
theorem u_escape_low_byte : (kFind [0x5C, 0x75, 0x30, 0x31, 0x34, 0x31] [0x41]).asStr? = some [0x41] := by
  decide +kernel

/-- RX: `(re-find #"[[:alpha:]]" "x")` is "x": a POSIX class, where Java reads a nested class of
`:alph` (Clojure: nil). -/
theorem posix_bracket_example :
    (kFind [0x5B, 0x5B, 0x3A, 0x61, 0x6C, 0x70, 0x68, 0x61, 0x3A, 0x5D, 0x5D] [0x78]).asStr? = some [0x78] := by
  decide +kernel

/-- R80: `(re-find #"(a)?b" "b")` is `["b" ""]` (Clojure: `["b" nil]`). -/
theorem unmatched_group_example :
    (kFind [0x28, 0x61, 0x29, 0x3F, 0x62] [0x62]).asVec? = some [some [0x62], some []] := by
  decide +kernel

/-- R82: `(re-matches #"a|ab" "ab")` is nil (Clojure: "ab"). -/
theorem re_matches_first_alternative : (kMatches [0x61, 0x7C, 0x61, 0x62] [0x61, 0x62]).isNil = true := by
  decide +kernel

end Jank.R3.Regex

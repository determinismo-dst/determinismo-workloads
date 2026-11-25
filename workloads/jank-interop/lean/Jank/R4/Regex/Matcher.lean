-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (with round 3's regex replica; see README.md)
import Jank.R4.Regex.Compare4

/-!
# `re-matcher` objects: `re-find`, `re-groups`, `nth`, printing a pattern

jank (7135b7708):
- `re_matcher` (obj/re_matcher.hpp; re_matcher.cpp 8–23) holds `match_input` and `groups`, the
  object the last `re_find` returned (core.cpp 972–988: `smatch_to_vector`, nil after a failed
  search); it is `indexable`, and its `nth` is `runtime::nth(groups, index[, fallback])`
  (re_matcher.cpp 14–22).
- `clojure.core/nth` → core/seq.cpp `nth` 648 (an index below 0 throws, a nil collection gives
  nil, an indexable object answers) and the 3-argument `nth` 698 (an index below 0 or nil gives the
  fallback). On the `groups` object: nil gives nil (or the fallback); a string (a pattern without
  groups) gives a character from its bytes (persistent_string.cpp `nth` 107–126); a vector gives
  its element ("" for a group that did not take part, R80).
- `re-groups` (core.cpp 990): nil throws "No match was found…", else `groups`.
- `print` (core.cpp `print` 141) writes `to_string`, which for a pattern is its text
  (re_pattern.cpp 17–25); `pr` writes `to_code_string`, `#"…"`.

Clojure 1.12 (clojure-ref RT.java `nthFrom` 920–953 and 963–1012, core.clj `re-groups` 4911;
core_print.clj prints a `Pattern` as `#"…"` through `print-method`, which ignores
`*print-readably*`):
- `(nth m n)` is `m.group(n)`: `IllegalStateException` without a current match,
  `IndexOutOfBoundsException` for `n < 0` or `n > groupCount`, nil for a group that did not take
  part, else the group's text;
- `(nth m n nf)`: `nf` for `n < 0`; when the pattern has groups and `n ≤ groupCount`,
  `m.group(n)` (so it throws without a current match); else `nf`.
-/

namespace Jank.R4.Regex

open Jank.R3.Regex

/-- What a matcher operation returns. -/
inductive MV where
  | nil
  | str (b : List Nat)
  /-- A character: jank's `nth` on a string yields one byte. -/
  | ch (b : Nat)
  | vec (xs : List (Option (List Nat)))
  | notFound
  | err (what : String)
  | skip
  deriving BEq, Repr, Inhabited

def MV.show : MV → String
  | .nil => "nil"
  | .str b => showB b
  | .ch b => s!"\\{Char.ofNat b}"
  | .vec xs => "[" ++ " ".intercalate (xs.map fun o => match o with | some b => showB b | none => "nil") ++ "]"
  | .notFound => ":nf"
  | .err w => s!"throws ({w})"
  | .skip => "<not decided>"

/-- One operation on a matcher. -/
inductive MOp where
  | find
  | groups
  | nth (n : Int)
  | nthNf (n : Int)
  deriving BEq, Repr, Inhabited

def MOp.show : MOp → String
  | .find => "(re-find m)"
  | .groups => "(re-groups m)"
  | .nth n => s!"(nth m {n})"
  | .nthNf n => s!"(nth m {n} :nf)"

def ofV : V → MV
  | .nil => .nil
  | .str b => .str b
  | .vec xs => .vec xs
  | .err w => .err w
  | _ => .skip

/-- jank: `runtime::nth` on the matcher, which forwards to its `groups` object. -/
def jNth (groups : V) (n : Int) (nf : Option Unit) : MV :=
  match nf with
  | none =>
    if n < 0 then .err "index out of bounds"
    else match groups with
      | .nil => .nil
      | .str b => match b[n.toNat]? with
        | some x => .ch x
        | none => .err "index out of bounds for this persistent_string"
      | .vec xs => match xs[n.toNat]? with
        | some (some b) => .str b
        | some none => .nil
        | none => .err "index out of bounds"
      | _ => .skip
  | some _ =>
    if n < 0 then .notFound
    else match groups with
      | .nil => .notFound
      | .str b => match b[n.toNat]? with
        | some x => .ch x
        | none => .notFound
      | .vec xs => match xs[n.toNat]? with
        | some (some b) => .str b
        | some none => .nil
        | none => .notFound
      | _ => .skip

/-- jank: a script of operations on `(re-matcher re s)`. -/
def jankScript (loc : Loc) (pat inp : List Nat) (ops : List MOp) (lim : Lim := {}) : List MV :=
  match compile loc (utf8s (pat.takeWhile (· != 0))) with
  | .error e => [.err e.what]
  | .ok nfa => Id.run do
    let mut mt : JMatcher := { input := cstr (utf8s inp) }
    let mut out : List MV := []
    for op in ops do
      match op with
      | .find =>
        match jReFindM nfa mt lim with
        | .error _ => out := out ++ [.skip]
        | .ok (v, mt', _) => mt := mt'; out := out ++ [ofV v]
      | .groups => out := out ++ [if mt.groups == .nil then .err "No match was found" else ofV mt.groups]
      | .nth n => out := out ++ [jNth mt.groups n none]
      | .nthNf n => out := out ++ [jNth mt.groups n (some ())]
    return out

/-- Clojure: the same script on a `java.util.regex.Matcher`. -/
def cljScript (pat inp : List Nat) (ops : List MOp) (lim : J.Lim := {}) : List MV :=
  match JM.compile pat with
  | .error (.syntax e) => [.err e]
  | .ok p =>
    if p.node.unsupportedIn.isSome then [.skip] else Id.run do
    let a := J.units inp
    let mut ms : J.MState := {}
    let mut cur : Option (Nat × Nat × JM.Groups) := none
    let mut out : List MV := []
    let grp (c : Option (Nat × Nat × JM.Groups)) (n : Nat) : MV :=
      match c with
      | none => .err "No match found"
      | some (s, e, gs) =>
        if n == 0 then .str (J.sub a s e)
        else match gs.getD n none with
          | some (x, y) => .str (J.sub a x y)
          | none => .nil
    for op in ops do
      match op with
      | .find =>
        match JM.find p a ms lim 0 {} with
        | .error _ => out := out ++ [.skip]
        | .ok (r, ms', _) =>
          ms := ms'
          cur := r
          match r with
          | none => out := out ++ [.nil]
          | some (s, e, gs) =>
            out := out ++ [match JM.reGroups p a s e gs with
              | .str b => .str b
              | .vec xs => .vec xs
              | _ => .skip]
      | .groups =>
        match cur with
        | none => out := out ++ [.err "No match found"]
        | some (s, e, gs) =>
          out := out ++ [match JM.reGroups p a s e gs with
            | .str b => .str b
            | .vec xs => .vec xs
            | _ => .skip]
      | .nth n =>
        if n < 0 || n.toNat > p.groups then
          out := out ++ [if cur.isNone && n ≥ 0 && n.toNat ≤ p.groups then .err "No match found" else .err "IndexOutOfBoundsException"]
        else out := out ++ [grp cur n.toNat]
      | .nthNf n =>
        if n < 0 then out := out ++ [.notFound]
        else if p.groups > 0 && n.toNat ≤ p.groups then out := out ++ [grp cur n.toNat]
        else out := out ++ [.notFound]
    return out

/-- Two answers agree (errors agree with errors; undecided ones are not compared). -/
def MV.agree : MV → MV → Bool
  | .err _, .err _ => true
  | .skip, _ | _, .skip => true
  | a, b => a == b

def scriptProgram (pat inp : List Nat) (ops : List MOp) : String :=
  let r := if pat.contains 0 then s!"(re-pattern {Jank.Str.lit pat})" else patLit pat
  s!"(let [m (re-matcher {r} {Jank.Str.lit inp})] {" ".intercalate (ops.map MOp.show)})"

/-! ## Printing a pattern -/

/-- Clojure's `print-method` for a `Pattern` (core_print.clj): `#"`, the pattern with `"` written
`\"` (inside `\Q…\E` as `\E\"\Q`), `"`. Printing with `print` uses it too. -/
def cljPrintPattern (p : List Nat) : List Nat :=
  let rec go : Nat → List Nat → Bool → List Nat
    | 0, _, _ => []
    | _ + 1, [], _ => []
    | f + 1, c :: rest, qmode =>
      if c == 0x5C then
        match rest with
        | c2 :: r2 => [0x5C, c2] ++ go f r2 (if qmode then c2 != 0x45 else c2 == 0x51)
        | [] => [0x5C]
      else if c == 0x22 then
        -- `\E\"\Q` inside `\Q…\E`, else `\"`
        (if qmode then [0x5C, 0x45, 0x5C, 0x22, 0x5C, 0x51] else [0x5C, 0x22]) ++ go f rest qmode
      else c :: go f rest qmode
  [0x23, 0x22] ++ go (p.length + 1) p false ++ [0x22]

/-- jank's `print` of a pattern: `to_string`, the pattern's text. -/
def jankPrintPattern (p : List Nat) : List Nat := p

end Jank.R4.Regex

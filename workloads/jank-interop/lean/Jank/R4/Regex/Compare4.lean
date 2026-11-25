-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (with round 3's regex replica; see README.md)
import Jank.R3.Regex.Search
import Jank.R4.Regex.JavaM

/-!
# Round 4 questions: the replica against the round-4 spec

- jank's side is round 3's replica (`jankEval`) with one correction: `re-pattern` builds its
  `std::regex` from `s.c_str()` (re_pattern.cpp 9, `regex{ s.c_str(), ECMAScript }`), so a
  pattern string is cut at its first NUL. Round 3's `jRePattern`/`jankEval` compiled the whole
  string; no round-3 alphabet put a NUL in a pattern, so no round-3 count changes.
- Clojure's side is `JavaM` (captures kept as Java keeps them, lookbehind, flags, named groups).
  Nothing is left "not compared" because of a capture inside a lookahead (round 3's RXJ4).
- Classification: the first toggle that removes the deviation, in order: the pattern NUL cut,
  round 3's jank toggles (`fixOrder`), then a spec-side toggle that clears the groups before every
  start position (what libstdc++ does: `_M_main_dispatch` sets `_M_cur_results = _M_results` at
  each start, executor.tcc 91).
-/

namespace Jank.R4.Regex

open Jank.R3.Regex

structure Fix4 where
  base : Fix := {}
  /-- The spec side reads the pattern only up to its first NUL, as jank's `c_str()` does (the
  toggle that classifies a deviation as the pattern cut). -/
  javaPatCut : Bool := false
  jfix : JM.JFix := {}
  deriving BEq, Repr, Inhabited

def liftFix (p : String × (Fix → Fix)) : String × (Fix4 → Fix4) :=
  (p.1, fun (f : Fix4) => { f with base := p.2 f.base })

def fixOrder4 : List (String × (Fix4 → Fix4)) :=
  [("pattern-cut-at-nul (new)", fun (f : Fix4) => { f with javaPatCut := true })] ++
  fixOrder.map liftFix ++
  [("lookahead-capture-from-an-earlier-start (new)", fun (f : Fix4) => { f with jfix := { resetPerStart := true } })]

/-- jank's answer (round 3's replica, with the `c_str` cut of the pattern). -/
def jankEval4 (loc : Loc) (fx : Fix4) (q : Q) (lim : Lim := {}) : V :=
  jankEval loc fx.base { q with pat := q.pat.takeWhile (· != 0) } lim

def jankAccepts4 (loc : Loc) (pat : List Nat) : Bool :=
  jankAccepts loc (pat.takeWhile (· != 0))

def javaAccepts4 (pat : List Nat) : Bool :=
  match JM.compile pat with
  | .ok _ => true
  | .error _ => false

/-- Clojure's answer on the round-4 spec. -/
def cljEval4 (q : Q) (jfx : JM.JFix := {}) (lim : J.Lim := {}) : J.CV :=
  match JM.compile q.pat with
  | .error (.syntax e) => .err e
  | .ok p =>
    match p.node.unsupportedIn with
    | some w => .unknown w
    | none =>
    match q.api with
    | .find => JM.reFind p q.inp lim jfx
    | .seq => JM.reSeq p q.inp lim jfx
    | .matches => JM.reMatches p q.inp lim
    | .replace t => JM.replace p q.inp (.inl t) false lim jfx
    | .replaceFirst t => JM.replace p q.inp (.inl t) true lim jfx
    | .replaceFn => JM.replace p q.inp (.inr renderArgC) false lim jfx
    | .replaceFirstFn => JM.replace p q.inp (.inr renderArgC) true lim jfx
    | .split l => JM.split p q.inp l lim jfx

def verdict4 (loc : Loc) (fx : Fix4) (q : Q) : Verdict × V × J.CV :=
  let qc := if fx.javaPatCut then { q with pat := q.pat.takeWhile (· != 0) } else q
  let c := cljEval4 qc fx.jfix
  let ja := jankAccepts4 loc q.pat
  let ca := javaAccepts4 qc.pat
  let j := jankEval4 loc fx q
  if !ja && ca then (.rejects (match j with | .err w => w | _ => "?"), j, c)
  else if ja && !ca then (.acceptsInvalid (match c with | .err w => w | _ => "?"), j, c)
  else match j, c with
    | .abort w, _ => (.skip s!"jank {w}", j, c)
    | _, .unknown w => (.skip s!"spec {w}", j, c)
    | _, _ => if agreeV j c then (.agree, j, c) else (.differ, j, c)

def classify4 (loc : Loc) (q : Q) : Option String :=
  let rec go : List (String × (Fix4 → Fix4)) → Fix4 → Option String
    | [], _ => none
    | (name, g) :: rest, fx =>
      let fx' := g fx
      match verdict4 loc fx' q with
      | (.agree, _, _) => some name
      | _ => go rest fx'
  go fixOrder4 {}

/-- Whether the pattern opens an inline flag group: `(?` then a flag letter, `-`, `)` or `:`-less
flag list. -/
def flagGroup (pat : List Nat) : Bool :=
  (List.range pat.length).any fun i =>
    pat.getD i 0 == 0x28 && pat.getD (i + 1) 0 == 0x3F &&
      (cpsOf "idmsuxUc-)").contains (pat.getD (i + 2) 0) &&
      !(i > 0 && pat.getD (i - 1) 0 == 0x5C)

/-- The class of a pattern jank rejects and Java compiles (round 3's shapes, on the round-4 tree). -/
def rejectShape4 (pat : List Nat) (jankErr : String) : String :=
  let has (s : String) := subList pat (cpsOf s)
  if has "(?<=" || has "(?<!" then "lookbehind (R18)"
  else if has "(?<" then "named group (R18)"
  else if has "(?>" then "atomic group (R18)"
  else if flagGroup pat then "inline flags (R18)"
  else if has "\\k<" then "named backreference (R18)"
  else rejectShape pat jankErr

def showQ4 (loc : Loc) (q : Q) : String :=
  let (_, j, c) := verdict4 loc {} q
  let prog := if q.pat.contains 0 then
      (q.program.replace (patLit q.pat) s!"(re-pattern {Jank.Str.lit q.pat})")
    else q.program
  s!"{prog}: Clojure {CV.show c}, jank {V.show j}"

/-- Census of a list of questions (round 3's tally, round 4's verdict and classes). -/
def census4 (loc : Loc) (fx : Fix4) (qs : List Q) (classifyOn : Bool := true) : Tally := Id.run do
  let mut t : Tally := {}
  for q in qs do
    t := { t with total := t.total + 1 }
    let (v, _, _) := verdict4 loc fx q
    match v with
    | .agree => t := { t with agree := t.agree + 1 }
    | .skip w => t := { t with skipped := t.skipped + 1, skipReasons := bumpN t.skipReasons w }
    | .rejects w => t := { t with rejects := bump t.rejects (rejectShape4 q.pat w) q }
    | .acceptsInvalid w => t := { t with acceptsInvalid := bump t.acceptsInvalid w q }
    | .differ =>
      let cls := if classifyOn then (classify4 loc q).getD (trigger q) else trigger q
      t := { t with differ := bump t.differ cls q }
  return t

def printTally4 (loc : Loc) (name : String) (t : Tally) : IO Unit := do
  let nd := t.differ.foldl (fun a (_, n, _) => a + n) 0
  let nr := t.rejects.foldl (fun a (_, n, _) => a + n) 0
  let na := t.acceptsInvalid.foldl (fun a (_, n, _) => a + n) 0
  IO.println s!"  {name}: {t.total} questions: {t.agree} agree, {nd} differ, {nr} jank rejects a valid pattern, {na} jank accepts an invalid one, {t.skipped} not compared"
  for (k, n) in t.skipReasons do IO.println s!"    not compared ({k}): {n}"
  for (k, n, qs) in t.differ do
    IO.println s!"    differ [{k}]: {n}"
    for q in qs do IO.println s!"      {showQ4 loc q}"
  for (k, n, qs) in t.rejects do
    IO.println s!"    jank rejects [{k}]: {n}"
    for q in qs.take 2 do IO.println s!"      {showQ4 loc q}"
  for (k, n, qs) in t.acceptsInvalid do
    IO.println s!"    jank accepts, Java rejects [{k}]: {n}"
    for q in qs.take 2 do IO.println s!"      {showQ4 loc q}"

/-! ## The spec on a JVM: questions with the model's answer, one EDN vector per line -/

def ednNats (xs : List Nat) : String := "[" ++ " ".intercalate (xs.map toString) ++ "]"

partial def ednCV : J.CV → String
  | .nil => "nil"
  | .str b => s!"[:s {ednNats b}]"
  | .vec xs => "[:v [" ++ " ".intercalate (xs.map fun o => match o with | some b => ednNats b | none => "nil") ++ "]]"
  | .list xs => "[:l [" ++ " ".intercalate (xs.map ednCV) ++ "]]"
  | .err _ => "[:e]"
  | .unknown w => s!"[:u {repr w}]"

def ednApi : Api → String
  | .find => "[:find]" | .seq => "[:seq]" | .matches => "[:matches]"
  | .replace t => s!"[:replace {ednNats t}]" | .replaceFirst t => s!"[:replace-first {ednNats t}]"
  | .replaceFn => "[:replace-fn]" | .replaceFirstFn => "[:replace-first-fn]"
  | .split l => s!"[:split {l}]"

/-- `[id api pattern input expected]` (code points; strings expected as UTF-8 bytes). -/
def ednLine (id : Nat) (q : Q) (jfx : JM.JFix := {}) : String :=
  s!"[{id} {ednApi q.api} {ednNats q.pat} {ednNats q.inp} {ednCV (cljEval4 q jfx)}]"

end Jank.R4.Regex

-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (with round 3's regex replica; see README.md)
import Jank.R4.Regex.Compare4
import Jank.R5.Regex.JavaM5

/-!
# Round 5 questions: the replica against the round-5 spec (Java's Unicode rules)

- jank's side is round 4's (`jankEval4`: round 3's libstdc++ replica with the `c_str()` cut).
- Clojure's side is `JavaM5` (round 4's model with `Bound`'s non-spacing-mark rule, `(?U)`'s
  `WORD()`, and `\p{…}` with `UNICODE_CHARACTER_CLASS`).
- Classification: round 4's toggles (`fixOrder4`, each removing one known deviation), then two
  spec-side toggles: `Bound` without the non-spacing-mark rule, and `.`/`$` with only `\n`/`\r` as
  line terminators. A deviation no toggle removes is classified by its trigger (round 3's
  `trigger`: a construct whose syntax differs, else non-ASCII text, R78).
-/

namespace Jank.R5.Regex

open Jank.R3.Regex Jank.R4.Regex

structure Fix5 where
  f4 : Fix4 := {}
  noMn : Bool := false
  asciiTerm : Bool := false
  deriving BEq, Repr, Inhabited

def Fix5.jfix (fx : Fix5) : JM5.JFix := { resetPerStart := fx.f4.jfix.resetPerStart }

def javaAccepts5 (pat : List Nat) : Bool :=
  match JM5.compile pat with
  | .ok _ => true
  | .error _ => false

/-- Clojure's answer on the round-5 spec. -/
def cljEval5 (q : Q) (fx : Fix5 := {}) (lim : J.Lim := {}) : J.CV :=
  match JM5.compile q.pat fx.noMn fx.asciiTerm with
  | .error (.syntax e) => .err e
  | .ok p =>
    match p.node.unsupportedIn with
    | some w => .unknown w
    | none =>
    let jfx := fx.jfix
    match q.api with
    | .find => JM5.reFind p q.inp lim jfx
    | .seq => JM5.reSeq p q.inp lim jfx
    | .matches => JM5.reMatches p q.inp lim
    | .replace t => JM5.replace p q.inp (.inl t) false lim jfx
    | .replaceFirst t => JM5.replace p q.inp (.inl t) true lim jfx
    | .replaceFn => JM5.replace p q.inp (.inr renderArgC) false lim jfx
    | .replaceFirstFn => JM5.replace p q.inp (.inr renderArgC) true lim jfx
    | .split l => JM5.split p q.inp l lim jfx

def verdict5 (loc : Loc) (fx : Fix5) (q : Q) : Verdict × V × J.CV :=
  let qc := if fx.f4.javaPatCut then { q with pat := q.pat.takeWhile (· != 0) } else q
  let c := cljEval5 qc fx
  let ja := jankAccepts4 loc q.pat
  let ca := javaAccepts5 qc.pat
  let j := jankEval4 loc fx.f4 q
  if !ja && ca then (.rejects (match j with | .err w => w | _ => "?"), j, c)
  else if ja && !ca then (.acceptsInvalid (match c with | .err w => w | _ => "?"), j, c)
  else match j, c with
    | .abort w, _ => (.skip s!"jank {w}", j, c)
    | _, .unknown w => (.skip s!"spec {w}", j, c)
    | _, _ => if agreeV j c then (.agree, j, c) else (.differ, j, c)

def fixOrder5 : List (String × (Fix5 → Fix5)) :=
  fixOrder4.map (fun (n, g) => (n, fun (f : Fix5) => { f with f4 := g f.f4 })) ++
  [("non-spacing mark after a letter is a word character for \\b (new)", fun (f : Fix5) => { f with noMn := true }),
   ("Unicode line terminators U+0085/U+2028/U+2029 in . and $ (R78/R79 refinement)",
     fun (f : Fix5) => { f with asciiTerm := true })]

def classify5 (loc : Loc) (q : Q) : Option String :=
  let rec go : List (String × (Fix5 → Fix5)) → Fix5 → Option String
    | [], _ => none
    | (name, g) :: rest, fx =>
      let fx' := g fx
      match verdict5 loc fx' q with
      | (.agree, _, _) => some name
      | _ => go rest fx'
  go fixOrder5 {}

/-- The class of a pattern jank rejects and Java compiles: round 4's shapes, and `\p`/`\P`. -/
def rejectShape5 (pat : List Nat) (jankErr : String) : String :=
  let has (s : String) := subList pat (cpsOf s)
  if flagGroup pat then "inline flags (R18)"
  else if has "\\p" || has "\\P" then "property escape \\p{…} (S31)"
  else rejectShape4 pat jankErr

def showQ5 (loc : Loc) (q : Q) : String :=
  let (_, j, c) := verdict5 loc {} q
  s!"{q.program}: Clojure {CV.show c}, jank {V.show j}"

def census5 (loc : Loc) (qs : List Q) : Tally := Id.run do
  let mut t : Tally := {}
  for q in qs do
    t := { t with total := t.total + 1 }
    let (v, _, _) := verdict5 loc {} q
    match v with
    | .agree => t := { t with agree := t.agree + 1 }
    | .skip w => t := { t with skipped := t.skipped + 1, skipReasons := bumpN t.skipReasons w }
    | .rejects w => t := { t with rejects := bump t.rejects (rejectShape5 q.pat w) q }
    | .acceptsInvalid w => t := { t with acceptsInvalid := bump t.acceptsInvalid w q }
    | .differ =>
      let cls := (classify5 loc q).getD (trigger q)
      t := { t with differ := bump t.differ cls q }
  return t

def printTally5 (loc : Loc) (name : String) (t : Tally) : IO Unit := do
  let nd := t.differ.foldl (fun a (_, n, _) => a + n) 0
  let nr := t.rejects.foldl (fun a (_, n, _) => a + n) 0
  let na := t.acceptsInvalid.foldl (fun a (_, n, _) => a + n) 0
  IO.println s!"  {name}: {t.total} questions: {t.agree} agree, {nd} differ, {nr} jank rejects a valid pattern, {na} jank accepts an invalid one, {t.skipped} not compared"
  for (k, n) in t.skipReasons do IO.println s!"    not compared ({k}): {n}"
  for (k, n, qs) in t.differ do
    IO.println s!"    differ [{k}]: {n}"
    for q in qs do IO.println s!"      {showQ5 loc q}"
  for (k, n, qs) in t.rejects do
    IO.println s!"    jank rejects [{k}]: {n}"
    for q in qs.take 2 do IO.println s!"      {showQ5 loc q}"
  for (k, n, qs) in t.acceptsInvalid do
    IO.println s!"    jank accepts, Java rejects [{k}]: {n}"
    for q in qs.take 2 do IO.println s!"      {showQ5 loc q}"

/-- `[id api pattern input expected]`, or `[id :compile-error pattern]` (round 4's format, read by
`.r5-scratch/regex/clj/validate.clj`). -/
def ednLine5 (id : Nat) (q : Q) : String :=
  if javaAccepts5 q.pat then
    s!"[{id} {ednApi q.api} {ednNats q.pat} {ednNats q.inp} {ednCV (cljEval5 q)}]"
  else s!"[{id} :compile-error {ednNats q.pat}]"

end Jank.R5.Regex

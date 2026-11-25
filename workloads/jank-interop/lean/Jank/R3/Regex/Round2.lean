import Jank.R3.Regex.Search
import Jank.RegexModel

/-!
# Round 2's regex tables on the replica

Round 2 (`Jank/RegexModel.lean`, read-only here) asked 117,936 `re-find`/`re-seq`/`re-matches`
questions (`allCases`) and 66,300 `replace`/`split` questions (`iterCases`) of its own
backtracking model of `std::regex` (jank) and of java.util.regex (Clojure). Each question is asked
again of the libstdc++ replica and of this round's Java model; the per-entry changes are counted:
the jank answer, the Clojure answer and the verdict, each round-2 vs round-3.
-/

namespace Jank.R3.Regex.R2

open Jank.Regex (G Grp Case IterCase)

def grpV : Grp → V
  | .str b => .str (b.map (·.toNat))
  | .vec xs => .vec (xs.map fun o => o.map fun b => b.map (·.toNat))

def gV : G → V
  | .nil => .nil
  | .one g => grpV g
  | .many gs => .list (gs.map grpV)
  | .infinite p => .infinite (p.map grpV)
  | .err w => .err w

/-- Round 2's Clojure value in round 3's spec type (for the spec-side comparison). -/
def gCV : G → J.CV
  | .nil => .nil
  | .one (.str b) => .str (b.map (·.toNat))
  | .one (.vec xs) => .vec (xs.map fun o => o.map fun b => b.map (·.toNat))
  | .many gs => .list (gs.map fun g => match g with
      | .str b => J.CV.str (b.map (·.toNat))
      | .vec xs => J.CV.vec (xs.map fun o => o.map fun b => b.map (·.toNat)))
  | .infinite _ => .unknown "infinite"
  | .err w => .err w

/-- Equality of two jank answers (infinite seqs by their first two elements). -/
partial def sameV : V → V → Bool
  | .infinite a, .infinite b => a.take 2 == b.take 2
  | .list a, .list b => a.length == b.length && (a.zip b).all fun (x, y) => sameV x y
  | a, b => a == b

partial def sameCV : J.CV → J.CV → Bool
  | .list a, .list b => a.length == b.length && (a.zip b).all fun (x, y) => sameCV x y
  | .err _, .err _ => true
  | a, b => a == b

def caseQ (c : Case) : Q :=
  { api := match c.api with | .find => .find | .seq => .seq | .matches => .matches,
    pat := cpsOf c.re.src, inp := c.input }

def iterQ (c : IterCase) : Q :=
  { api := match c.api with
      | .replace t => .replace (cpsOf t)
      | .split l => .split l,
    pat := cpsOf c.re.src, inp := c.input }

structure Row where
  name : String
  total : Nat := 0
  r2differ : Nat := 0
  r3differ : Nat := 0
  r3skip : Nat := 0
  /-- deviating in round 2, agreeing now (round-2 predictions retracted) -/
  retracted : Nat := 0
  /-- agreeing in round 2, deviating now (new) -/
  added : Nat := 0
  /-- deviating in both, with another jank answer now -/
  changedJank : Nat := 0
  /-- round 2's jank model and the replica give different answers -/
  jankModelWrong : Nat := 0
  /-- round 2's Java model and this round's give different answers -/
  specChanged : Nat := 0
  exRetracted : List String := []
  exAdded : List String := []
  exJank : List String := []
  exSpec : List String := []
  deriving Inhabited

def addEx (xs : List String) (s : String) : List String := if xs.length < 4 then xs ++ [s] else xs

def step (loc : Loc) (r : Row) (q : Q) (j2 c2 : G) : Row := Id.run do
  let mut r := { r with total := r.total + 1 }
  let r2d := !(j2.agrees c2)
  let (v, j3, c3) := verdict loc {} q
  let r3d := match v with | .differ | .rejects _ => true | _ => false
  if r2d then r := { r with r2differ := r.r2differ + 1 }
  if r3d then r := { r with r3differ := r.r3differ + 1 }
  if let .skip _ := v then r := { r with r3skip := r.r3skip + 1 }
  let line := s!"{q.program}: Clojure {CV.show c3}, jank {V.show j3} (round 2: Clojure {CV.show (gCV c2)}, jank {V.show (gV j2)})"
  if r2d && !r3d then r := { r with retracted := r.retracted + 1, exRetracted := addEx r.exRetracted line }
  if !r2d && r3d then r := { r with added := r.added + 1, exAdded := addEx r.exAdded line }
  if r2d && r3d && !sameV (gV j2) j3 then r := { r with changedJank := r.changedJank + 1 }
  if !sameV (gV j2) j3 then r := { r with jankModelWrong := r.jankModelWrong + 1, exJank := addEx r.exJank line }
  if !sameCV (gCV c2) c3 then r := { r with specChanged := r.specChanged + 1, exSpec := addEx r.exSpec line }
  return r

def printRow (r : Row) : IO Unit := do
  IO.println s!"  {r.name}: {r.total} questions; deviate: round 2 {r.r2differ}, round 3 {r.r3differ} (not compared now: {r.r3skip})"
  IO.println s!"    retracted (deviated, now agree): {r.retracted}; added (agreed, now deviate): {r.added}; deviate in both with another jank answer: {r.changedJank}"
  IO.println s!"    round 2's jank model differs from the replica on {r.jankModelWrong}; round 2's Java model differs from round 3's on {r.specChanged}"
  for e in r.exRetracted do IO.println s!"      retracted: {e}"
  for e in r.exAdded do IO.println s!"      added: {e}"
  for e in r.exJank do IO.println s!"      jank model vs replica: {e}"
  for e in r.exSpec do IO.println s!"      spec change: {e}"

def rerun (loc : Loc) : IO Unit := do
  IO.println s!"== round 2's regex tables on the replica (locale {loc.name})"
  for api in [Jank.Regex.Api.find, .seq, .matches] do
    let mut r : Row := { name := api.name }
    for c in Jank.Regex.allCases.filter (·.api == api) do
      let (j2, c2) := c.eval
      r := step loc r (caseQ c) j2 c2
    printRow r
  for (nm, sel) in [("replace \"-\"", fun (c : IterCase) => match c.api with | .replace _ => true | _ => false),
                    ("split", fun (c : IterCase) => match c.api with | .split _ => true | _ => false)] do
    let mut r : Row := { name := nm }
    for c in Jank.Regex.iterCases.filter sel do
      let (j2, c2) := c.eval
      r := step loc r (iterQ c) j2 c2
    printRow r

end Jank.R3.Regex.R2

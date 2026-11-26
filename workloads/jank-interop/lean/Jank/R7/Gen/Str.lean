import Jank.StrModel
import Jank.R6.Str.Fixes
import Jank.R7.Gen.Core

/-!
# Round 7, area G: draws from the string models (round 2's `Jank.StrModel`, round 6's `Jank.R6.Str`)

Universe: every text of at most 3 code points over a, -, é (2 bytes), € (3 bytes), 😀 (4 bytes, a
surrogate pair) (`compare`: every pair of texts of at most 2); indices from -1 to one past jank's
byte count; `index-of`/`last-index-of` needles "", a, é, 😀, - with no start or starts -5, -1, 0, 1,
2, 3, 4, 6, 9. The operations and their models: `count` (`jCount`/`cCount`), `nth`, `get`,
`contains?`, `subs` (2 and 3 arguments: `jSubs`/`cSubs`), `index-of` (`jIndexOf`/`cIndexOf'`),
`last-index-of` (`jLastIndexOf`/`cLastIndexOf'`), and `compare` with round 6's exact values
(`jankCompare` under StrA6-1, Java's `javaCompare`): round 2's `jCompare`/`cCompare` keep only the
sign, which round 6 replaced.

Paths: the models do not distinguish them (REPORT-6 3.3: the inlined `nth`, `get`, `contains?`,
`count` and the fn bodies reach the same C++), so every path is predicted alike; the draws are
emitted on [literals], [let] and [fn] to check exactly that.

Exceptions: jank's `nth` out of range throws a `std::runtime_error` (persistent_string.cpp `nth`
112–117, seq.cpp `nth` 656–661 for a negative index) and `subs` an `error_ref` (persistent_string.cpp
`substring` 139–155 returns an error, core.cpp `subs` 408/421 `.expect_ok()`, jtl/result.hpp
`assert_ok` 148–156 → `panic` 41–68 → error.cpp `throw_result_failure` 775–780): neither is an
object, so where Clojure also throws, `thrown?` misses jank's (verdict throws, V7's class).
Draws whose Clojure result holds a lone surrogate are left out (jank's reader turns a lone
`\uD83D` escape into "?", V76, so the expected value could not be written).
-/

namespace Jank.R7.Gen.Str

open Jank.R7.Gen Jank.Str Jank.R6.Str

def alpha : List Nat := [0x61, 0x2D, 0xE9, 0x20AC, 0x1F600]

def textsUpTo : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
    let shorter := textsUpTo n
    shorter ++ ((shorter.filter (·.length == n)).flatMap fun s => alpha.map (s ++ [·]))

inductive SOp where
  | count
  | nth (i : Int)
  | get (i : Int)
  | contains (i : Int)
  | subs1 (i : Int)
  | subs2 (i j : Int)
  | indexOf (n : List Nat) (f : Option Int)
  | lastIndexOf (n : List Nat) (f : Option Int)
  | compare (t : List Nat)
  deriving Inhabited

def SOp.slug : SOp → String
  | .count => "count" | .nth _ => "nth" | .get _ => "get" | .contains _ => "contains"
  | .subs1 _ => "subs" | .subs2 .. => "subs3" | .indexOf .. => "index-of"
  | .lastIndexOf .. => "last-index-of" | .compare _ => "compare"

/-- The clojure.core or clojure.string function, and its arguments after the text. -/
def SOp.fnName : SOp → String
  | .count => "count" | .nth _ => "nth" | .get _ => "get" | .contains _ => "contains?"
  | .subs1 _ | .subs2 .. => "subs" | .indexOf .. => "string/index-of"
  | .lastIndexOf .. => "string/last-index-of" | .compare _ => "compare"

def SOp.wrapper : SOp → String
  | .count => "g-count" | .nth _ => "g-nth" | .get _ => "g-get" | .contains _ => "g-contains"
  | .subs1 _ | .subs2 .. => "g-subs" | .indexOf .. => "g-index-of"
  | .lastIndexOf .. => "g-last-index-of" | .compare _ => "g-compare"

def SOp.args : SOp → List String
  | .count => []
  | .nth i | .get i | .contains i | .subs1 i => [toString i]
  | .subs2 i j => [toString i, toString j]
  | .indexOf n f | .lastIndexOf n f => [strLit n] ++ (match f with | some v => [toString v] | none => [])
  | .compare t => [strLit t]

/-- jank's and Clojure's results (round 2's replicas; round 6's exact compare). -/
def eval (s : List Nat) : SOp → R × R
  | .count => (jCount (jstr s), cCount (cstr s))
  | .nth i => (jNth (jstr s) i, cNth (cstr s) i)
  | .get i => (jGet (jstr s) i, cGet (cstr s) i)
  | .contains i => (jContains (jstr s) i, cContains (cstr s) i)
  | .subs1 i => (jSubs (jstr s) i (jstr s).length, cSubs (cstr s) i (cstr s).length)
  | .subs2 i j => (jSubs (jstr s) i j, cSubs (cstr s) i j)
  | .indexOf n f => (jIndexOf (jstr s) (jstr n) (f.getD 0), cIndexOf' (cstr s) (cstr n) (f.getD 0))
  | .lastIndexOf n f =>
    (jLastIndexOf (jstr s) (jstr n) (f.getD (jstr s).length),
     cLastIndexOf' (cstr s) (cstr n) (f.getD (cstr s).length))
  | .compare t => (.int (jankCompare (jstr s) (jstr t)), .int (javaCompare (cstr s) (cstr t)))

/-- Code points of result bytes, `none` when not valid UTF-8 or holding a surrogate. -/
def cleanCps (b : List UInt8) : Option (List Nat) :=
  match decodeUtf8 b with
  | some cps => if cps.any (fun c => 0xD800 ≤ c && c ≤ 0xDFFF) then none else some cps
  | none => none

def showBytesA (b : List UInt8) : String :=
  match decodeUtf8 b with
  | some cps => strLit cps
  | none => "\"" ++ String.join (b.map fun x =>
      if x.toNat < 0x80 then String.singleton (Char.ofNat x.toNat) else "\\x" ++ Jank.Str.hex2 x.toNat) ++ "\" (invalid UTF-8)"

def showR (r : R) : String :=
  match r with
  | .nil => "nil" | .bool b => toString b | .int v => toString v
  | .str b => showBytesA b
  | .chr b => "char " ++ showBytesA b
  | .chars cs => "(" ++ " ".intercalate (cs.map showBytesA) ++ ")"
  | .err w => s!"throws ({w})"
  | .ub w => s!"undefined behavior ({w})"

/-- The one assertion on Clojure's result; `none` when it cannot be written (a lone surrogate). -/
def assertion (c : R) (e : String) : Option String :=
  match c with
  | .nil => some s!"(nil? {e})"
  | .bool true => some s!"(true? {e})"
  | .bool false => some s!"(false? {e})"
  | .int v => some s!"(= {v} {e})"
  | .str b => (cleanCps b).map fun cps => s!"(= {strLit cps} {e})"
  | .chr b => (cleanCps b).map fun cps => s!"(= {strLit cps} (str {e}))"
  | .err _ => some s!"(thrown? {e})"
  | _ => none

/-- What that assertion gives on jank's result: `=` of strings compares bytes, `str` of a
character is its bytes; jank's exceptions here are never objects. -/
def verdictOf (j c : R) : Option Jank.R7.Gen.Verdict :=
  match j, c with
  | .ub _, _ => none
  | .err _, _ => some .throws
  | _, .err _ => some .fail
  | a, b => some (if a == b then .pass else .fail)

/-- The deviation that explains a disagreement (REPORT-6 3.3). -/
def explain (s : List Nat) (op : SOp) (j c : R) : String :=
  match j, c with
  | .err _, .err _ => "V7"
  | _, _ =>
  match op with
  | .count => "R52"
  | .nth _ => "V65"
  | .get _ | .contains _ => "V66"
  | .subs1 _ | .subs2 .. => "LG3"
  | .compare _ => "V72"
  | .indexOf n f =>
    let fixed := jIndexOfFixed (jstr s) (jstr n) (f.getD 0)
    let ids := (if !(fixed == j) then ["V74"] else []) ++ (if !(fixed == c) then ["R58"] else [])
    if ids.isEmpty then "?" else "+".intercalate ids
  | .lastIndexOf n f =>
    let fixed := jLastIndexOfFixed (jstr s) (jstr n) (f.getD (jstr s).length)
    let ids := (if !(fixed == j) then ["V74"] else []) ++ (if !(fixed == c) then ["R58"] else [])
    if ids.isEmpty then "?" else "+".intercalate ids

def form (s : List Nat) (op : SOp) (via : Via) : Path → String
  | .literals => "(" ++ " ".intercalate ([op.fnName, strLit s] ++ op.args) ++ ")"
  | .letp =>
    let names := (List.range op.args.length).map fun k => s!"x{k}"
    let binds := " ".intercalate (["s", strLit s] ++ (names.zip op.args).flatMap fun (n, a) => [n, a])
    s!"(let [{binds}] (" ++ " ".intercalate ([op.fnName, "s"] ++ names) ++ "))"
  | _ =>
    let argv := [strLit s] ++ op.args
    match via with
    | .defn => "(" ++ " ".intercalate ([op.wrapper] ++ argv) ++ ")"
    | .lam =>
      let names := (List.range argv.length).map fun k => s!"x{k}"
      s!"((fn [{" ".intercalate names}] (" ++ " ".intercalate ([op.fnName] ++ names) ++ ")) " ++ " ".intercalate argv ++ ")"
    | .app => s!"(apply {op.fnName} [" ++ " ".intercalate argv ++ "])"

def item (group : String) (s : List Nat) (op : SOp) (via : Via) (p : Path) : Option Item := do
  let (j, c) := eval s op
  let e := form s op via p
  let a ← assertion c e
  let v ← verdictOf j c
  pure { group, op := op.slug, path := p, detail := (if p == .fn then via.slug else p.slug), form := e,
         assertion := a, clj := showR c, jank := showR j, verdict := v,
         id := if v == .pass then "" else explain s op j c }

def strPaths : List Path := [.literals, .letp, .fn]

def mkDraws (group : String) (cases : List (List Nat × SOp)) (paths : List Path := strPaths) : Array Draw := Id.run do
  let mut out := #[]
  let mut n := 0
  for (s, op) in cases do
    let via := viaOf n
    n := n + 1
    let items := paths.filterMap (item group s op via)
    if items.length == paths.length then
      out := out.push { key := form s op .defn .literals, items := items.toArray }
  return out

def idx (s : List Nat) : List Int := (List.range ((jstr s).length + 3)).map fun (k : Nat) => (k : Int) - 1

def needles : List (List Nat) := [[], [0x61], [0xE9], [0x1F600], [0x2D]]
def froms : List (Option Int) := [none, some (-5), some (-1), some 0, some 1, some 2, some 3, some 4, some 6, some 9]

def texts3 : List (List Nat) := textsUpTo 3
def texts2 : List (List Nat) := textsUpTo 2

def casesOf (slug : String) : List (List Nat × SOp) :=
  match slug with
  | "count" => texts3.map fun s => (s, .count)
  | "nth" => texts3.flatMap fun s => (idx s).map fun i => (s, .nth i)
  | "get" => texts3.flatMap fun s => (idx s).map fun i => (s, .get i)
  | "contains" => texts3.flatMap fun s => (idx s).map fun i => (s, .contains i)
  | "subs" => texts3.flatMap fun s => (idx s).map fun i => (s, .subs1 i)
  | "subs3" => texts3.flatMap fun s => (idx s).flatMap fun i => (idx s).map fun j => (s, .subs2 i j)
  | "index-of" => texts3.flatMap fun s => needles.flatMap fun n => froms.map fun f => (s, .indexOf n f)
  | "last-index-of" => texts3.flatMap fun s => needles.flatMap fun n => froms.map fun f => (s, .lastIndexOf n f)
  | _ => texts2.flatMap fun s => texts2.map fun t => (s, .compare t)

def slugs : List String := ["count", "nth", "get", "contains", "subs", "subs3", "index-of", "last-index-of", "compare"]

/-- The brief's classes: `index-of` with a negative start or one past the end (the real jank: nil
where Clojure gives 0 and 1), `last-index-of` with a negative start (jank 1, Clojure nil). -/
def briefIndexOf : List (List Nat × SOp) :=
  texts3.flatMap fun s =>
    let len : Int := (cstr s).length
    needles.flatMap fun n =>
      ([-5, -2, -1, len, len + 1, len + 3].map fun f => (s, SOp.indexOf n (some f)))

def briefLastIndexOf : List (List Nat × SOp) :=
  texts3.flatMap fun s => needles.flatMap fun n => ([-1, -2].map fun f => (s, SOp.lastIndexOf n (some f)))

end Jank.R7.Gen.Str

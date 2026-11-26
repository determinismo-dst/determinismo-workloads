import Jank.R6.Num.Search
import Jank.R7.Gen.Core

/-!
# Round 7, area G: draws from round 6's integer model (`Jank.R6.Num.Int`, `Jank.R6.Num.Search`)

Universe: `Jank.R6.Num.Search.ints` (23 integers, each boundary that changes a C++ type or a
check), every operator of `Search.ops`, and per operand the sources of `Search.srcs`: a literal on
the [literals] and [let] paths (`Src.lit`: jank keeps the literal's `int`/`long` type in a let,
analyze/processor.cpp `analyze_let` 2370–2421), and on the [fn] side a literal through a parameter
(`Src.fnLit`) or a computed value (`Src.fnVal`, `(identity v)`, `(dec' -9223372036854775807)` for
Long/MIN_VALUE so the reader's R5 does not apply).

The model's answer is `Search.answer`, unchanged, with one correction (`excIsObject`): R6's `jRem`
returns `.error` for a zero divisor like every other operation, but math.cpp `rem` throws a
`std::runtime_error` there (upstream-r5/compiler+runtime/src/cpp/jank/runtime/core/math.cpp
299–302 for longs, 288–291 for BigInts), which no object catch, and so no `thrown?`, sees (V7's
class); `quot` throws a boxed string (`make_box("Division by zero is not permitted.")`, 331–335)
and `inc`/`dec` a boxed string too (math.hpp `inc` 1194–1199), which `thrown?` catches.
-/

namespace Jank.R7.Gen.Num

open Jank.R7.Gen Jank.R6.Num Jank.R6.Num.Search Jank.Numbers

def slug : IOp → String
  | .bin .add => "add" | .bin .sub => "sub" | .bin .mul => "mul"
  | .binP .add => "addp" | .binP .sub => "subp" | .binP .mul => "mulp"
  | .neg => "neg" | .inc => "inc" | .dec => "dec" | .incP => "incp" | .decP => "decp"
  | .abs => "abs" | .quot => "quot" | .rem => "rem"

def wrapper (op : IOp) : String := "g-" ++ slug op

/-- Whether jank's exception for this operation is an object (`thrown?` sees it). -/
def excIsObject (op : IOp) : Bool := op != .rem

/-- One draw: the operands, their [fn]-side sources, which operand is the parameter on [mixed],
and how [fn] reaches the operation. -/
structure T where
  op : IOp
  x : CInt
  y : CInt
  fx : Src
  fy : Src
  leftParam : Bool
  via : Via

def call (op : IOp) (a b : String) : String :=
  if op.unary then s!"({op.name} {a})" else s!"({op.name} {a} {b})"

def T.paths (t : T) : List Path := if t.op.unary then [.literals, .letp, .fn] else Path.all

/-- The sources each operand has on a path. -/
def T.srcs (t : T) : Path → Src × Src
  | .literals | .letp => (.lit, .lit)
  | .fn => (t.fx, t.fy)
  | .mixed => if t.leftParam then (t.fx, .lit) else (.lit, t.fy)

def T.form (t : T) : Path → String
  | .literals => call t.op t.x.text t.y.text
  | .letp =>
    if t.op.unary then s!"(let [a {t.x.text}] {call t.op "a" ""})"
    else s!"(let [a {t.x.text} b {t.y.text}] {call t.op "a" "b"})"
  | .fn =>
    let ax := argText t.x t.fx
    let ay := argText t.y t.fy
    match t.via, t.op.unary with
    | .defn, true => s!"({wrapper t.op} {ax})"
    | .defn, false => s!"({wrapper t.op} {ax} {ay})"
    | .lam, true => s!"((fn [a] {call t.op "a" ""}) {ax})"
    | .lam, false => s!"((fn [a b] {call t.op "a" "b"}) {ax} {ay})"
    | .app, true => s!"(apply {t.op.name} [{ax}])"
    | .app, false => s!"(apply {t.op.name} [{ax} {ay}])"
  | .mixed =>
    if t.leftParam then s!"((fn [a] {call t.op "a" t.y.text}) {argText t.x t.fx})"
    else s!"((fn [b] {call t.op t.x.text "b"}) {argText t.y t.fy})"

def T.detail (t : T) : Path → String
  | .fn => t.via.slug
  | p => p.slug

/-- The test's one assertion on Clojure's outcome. -/
def assertion (c : Out) (e : String) : String :=
  match c with
  | .error _ => s!"(thrown? {e})"
  | .ok r => s!"(= \"{showR r}\" (pr-str {e}))"

/-- What that assertion gives on jank's outcome. -/
def verdictOf (op : IOp) (j c : Out) : Jank.R7.Gen.Verdict :=
  match c, j with
  | .error _, .error _ => if excIsObject op then .pass else .throws
  | .error _, .ok _ => .fail
  | .ok _, .error _ => .throws
  | .ok a, .ok b => if showR a == showR b then .pass else .fail

def jankText (op : IOp) (j : Out) : String :=
  match j with
  | .error e => if excIsObject op then s!"throws {e} (an object)" else s!"throws {e} (a std::runtime_error, not an object)"
  | .ok r => showR r

def isMinLit (x : CInt) (s : Src) : Bool :=
  match x, jRep x s with
  | .long _, .big _ => true
  | _, _ => false

/-- The deviation that explains a disagreement (REPORT-6 sections 2–3 and earlier rounds). -/
def explain (t : T) (p : Path) (j c : Out) : String :=
  let (sx, sy) := t.srcs p
  let r5 := isMinLit t.x sx || (!t.op.unary && isMinLit t.y sy)
  match c, j with
  | .error _, .error _ => "V7"
  | _, _ =>
  -- `quot` goes through doubles and always returns a long (D4), whatever the reader made of the
  -- literal Long/MIN_VALUE (a BigInt and a long convert to the same double)
  if t.op == .quot then "D4" else
  if r5 then "R5" else
  match t.op with
  | .bin o =>
    let rx := jRep t.x sx
    let ry := jRep t.y sy
    match c with
    | .error _ =>
      if o == .sub && t.y == .long i64minI && !(staticPath t.x t.y sx sy) && inI64 (t.x.val - t.y.val)
      then "V55" else "LG2"
    | .ok _ =>
      match rx, ry with
      | .i32 _, .i32 _ => match p with
        | .literals => "R25" | .letp => "V53" | _ => "D1"
      | _, _ => "LG2"
  | .binP .sub =>
    if t.y == .long i64minI && !(staticPath t.x t.y sx sy) then "V55" else "V54"
  | .neg =>
    match jRep t.x sx with
    | .i32 _ => "D1"
    | _ => "LG2"
  | .quot => "D4"
  | _ => "R5"

def item (t : T) (p : Path) : Option Item :=
  let (sx, sy) := t.srcs p
  if !admissible t.x sx || (!t.op.unary && !admissible t.y sy) then none else
  let (j, c) := if t.op.unary then answer t.op t.x t.x sx sx else answer t.op t.x t.y sx sy
  let e := t.form p
  let v := verdictOf t.op j c
  some { group := "num", op := slug t.op, path := p, detail := t.detail p, form := e,
         assertion := assertion c e, clj := showOut c, jank := jankText t.op j, verdict := v,
         id := if v == .pass then "" else explain t p j c }

def fnSrcs (x : CInt) : List Src := [Src.fnLit, Src.fnVal].filter (admissible x ·)

/-- Every draw of one operator. -/
def draws (op : IOp) : Array Draw := Id.run do
  let mut out := #[]
  let mut k := 0
  for x in ints do
    for fx in fnSrcs x do
      if op.unary then
        let t : T := { op, x, y := x, fx, fy := fx, leftParam := true, via := viaOf k }
        k := k + 1
        let items := t.paths.filterMap (item t)
        if items.length == t.paths.length then
          out := out.push { key := t.form .literals ++ "|" ++ t.form .fn, items := items.toArray }
      else
        for y in ints do
          for fy in fnSrcs y do
            for lp in [true, false] do
              let t : T := { op, x, y, fx, fy, leftParam := lp, via := viaOf k }
              k := k + 1
              let items := t.paths.filterMap (item t)
              if items.length == t.paths.length then
                out := out.push { key := t.form .literals ++ "|" ++ t.form .fn ++ "|" ++ t.form .mixed,
                                  items := items.toArray }
  return out

end Jank.R7.Gen.Num

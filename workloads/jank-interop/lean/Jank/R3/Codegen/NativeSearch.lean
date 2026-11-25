import Jank.R3.Codegen.NativeSpec
import Determinismo

/-!
# Searching the native world

Programs are drawn by decisions: native literals (ints around the i32 and i64 edges, doubles
around the int/long range, `##Inf`, `##NaN`, booleans), `+ - * / <`, `int`, `if`, `let`, `log`
(an output), loops counted or bounded by a value, `(loop [] (if c (recur) v))` on a parameter,
and fns with object or native-typed parameters, called once, with or without fn-level `recur`.

Two properties, each per optimization level and target:
1. jank means what Clojure means (`agreeCJ`);
2. an optimized build means what `-O0` means (`agreeJJ`): no undefined behavior on the path.

A deviation's class comes from what the jank run went through (its events) and the two outcomes;
`known` classes are set aside (the residual search).
-/

namespace Jank.R3.Codegen.NativeSearch

open Determinismo Jank.R3.Codegen

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev G := EStateM Determinismo.Stop W

def d (name : String) (n : Nat) : G Nat := Determinismo.decide (σ := W) name n
def pk {α : Type} [Inhabited α] (name : String) (xs : List α) : G α := do
  pure ((← Determinismo.pick (σ := W) name xs).getD default)

def intPool : List Int :=
  [0, 1, -1, 2, 10, 2147483647, -2147483648, -2147483647, 2147483648, 65536, 4294967296,
   9223372036854775807, -9223372036854775807, 3]
def dblPool : List Float :=
  [0.5, 1.5, -0.5, 1e10, 1e20, -1e20, (1.0 / 0.0), (0.0 / 0.0), 0.0, 3e9, 2147483647.5, -2147483648.5]

def ops : List AOp := [.add, .sub, .mul, .div, .lt]

/-- The pools of the exhaustive walks (fewer values, the same edges). -/
def intPoolSmall : List Int := [0, 1, 2147483647, -2147483648, 4294967296]
def dblPoolSmall : List Float := [0.5, 1e10, (0.0 / 0.0)]

/-- A numeric (or boolean) expression over `locals`. -/
partial def genNum (small : Bool) (depth : Nat) (locals : List String) : G NF := do
  let leaf : G NF := do
    match ← d "num.leaf" (if locals.isEmpty then 4 else 5) with
    | 0 => pure (.int (← pk "num.int" (if small then intPoolSmall else intPool)))
    | 1 => pure (.dbl (← pk "num.dbl" (if small then dblPoolSmall else dblPool)))
    | 2 => pure (.bool ((← d "num.bool" 2) == 1))
    | 3 => pure (← pk "num.obj" [NF.kw "k", .nil])
    | _ => pure (.sym (← pk "num.local" locals))
  if depth == 0 then return ← leaf
  match ← d "num.kind" 7 with
  | 0 => leaf
  | 1 | 2 => pure (.op (← pk "num.op" ops) (← genNum small (depth - 1) locals) (← genNum small (depth - 1) locals))
  | 3 => pure (.toInt (← genNum small (depth - 1) locals))
  | 4 => pure (.if_ (← genNum small (depth - 1) locals) (← genNum small (depth - 1) locals) (← genNum small (depth - 1) locals))
  | 5 =>
    let x := (← pk "let.name" ["a", "b"])
    pure (.let_ x (← genNum small (depth - 1) locals) (← genNum small (depth - 1) (x :: locals)))
  | _ => pure (.log (← genNum small (depth - 1) locals))

/-- Loops: bounded by the local itself, or counted. -/
partial def genLoop (small : Bool) (depth : Nat) (locals : List String) : G NF := do
  match ← d "loop.shape" 3 with
  | 0 =>
    -- (loop [x init] (if (< x bound) (recur (op x step)) result))
    let init ← genNum small (depth - 1) locals
    let bound ← genNum small 0 locals
    let step ← genNum small 0 locals
    let o ← pk "loop.op" [AOp.add, .mul, .sub]
    let res ← genNum small (depth - 1) ("x" :: locals)
    pure (.loop [("x", init)] (.if_ (.op .lt (.sym "x") bound) (.recur [.op o (.sym "x") step]) res))
  | 1 =>
    -- (loop [x init n 0] (if (< n 2) (recur e (+ n 1)) x))
    let init ← genNum small (depth - 1) locals
    let e ← genNum small (depth - 1) ("x" :: "n" :: locals)
    pure (.loop [("x", init), ("n", .int 0)]
      (.if_ (.op .lt (.sym "n") (.int 2)) (.recur [e, .op .add (.sym "n") (.int 1)]) (.sym "x")))
  | _ =>
    -- ((fn [p] (loop [] (if p (recur) v))) arg)
    let arg ← genNum small (depth - 1) locals
    let v ← genNum small 0 ("p" :: locals)
    pure (.call (.fn_ [("p", .obj)] (.loop [] (.if_ (.sym "p") (.recur []) v))) [arg])

def ptys : List PTy := [.obj, .long, .double, .int]

/-- A fn called once: a plain body, or fn-level `recur`. -/
partial def genFn (small : Bool) (depth : Nat) (locals : List String) : G NF := do
  let t ← pk "fn.ptype" ptys
  let arg ← genNum small (depth - 1) locals
  match ← d "fn.shape" 2 with
  | 0 =>
    let body ← genNum small (depth - 1) ("p" :: locals)
    pure (.call (.fn_ [("p", t)] body) [arg])
  | _ =>
    let bound ← genNum small 0 locals
    let step ← genNum small 0 locals
    let o ← pk "fn.op" [AOp.add, .mul, .sub]
    pure (.call (.fn_ [("p", t)] (.if_ (.op .lt (.sym "p") bound) (.recur [.op o (.sym "p") step]) (.sym "p"))) [arg])

partial def genProg (small : Bool) (depth : Nat) : G NF := do
  match ← d "prog.kind" 5 with
  | 0 => genNum small depth []
  | 1 => genLoop small (max depth 1) []
  | 2 => genFn small (max depth 1) []
  | 3 => pure (.let_ "u" (.int 0) (← genNum small depth ["u"]))
  | _ =>
    -- a closure capturing a native local
    let u ← genNum small (depth - 1) []
    pure (.let_ "u" u (← genFn small (max depth 1) ["u"]))

/-! ## Classes -/

def hasE (evs : List String) (e : String) : Bool := evs.contains e

partial def _root_.Jank.R3.Codegen.NF.hasToInt : NF → Bool
  | .toInt _ => true
  | .op _ a b => a.hasToInt || b.hasToInt
  | .if_ c t e => c.hasToInt || t.hasToInt || e.hasToInt
  | .let_ _ v b => v.hasToInt || b.hasToInt
  | .loop bs b => bs.any (·.2.hasToInt) || b.hasToInt
  | .recur as => as.any NF.hasToInt
  | .fn_ _ b => b.hasToInt
  | .call f as => f.hasToInt || as.any NF.hasToInt
  | .log a => a.hasToInt
  | _ => false

partial def _root_.Jank.R3.Codegen.NF.hasTyped (t : PTy) : NF → Bool
  | .fn_ ps b => ps.any (·.2 == t) || b.hasTyped t
  | .op _ a b => a.hasTyped t || b.hasTyped t
  | .if_ c x e => c.hasTyped t || x.hasTyped t || e.hasTyped t
  | .let_ _ v b => v.hasTyped t || b.hasTyped t
  | .loop bs b => bs.any (·.2.hasTyped t) || b.hasTyped t
  | .call f as => f.hasTyped t || as.any (NF.hasTyped t)
  | .log a | .toInt a => a.hasTyped t
  | .recur as => as.any (NF.hasTyped t)
  | _ => false

def isRatio : Val → Bool | .ratio .. | .big _ => true | _ => false

/-- The class of a Clojure/jank disagreement (most specific cause first). -/
def classCJ (f : NF) (c : COut) (j : JRun) : String :=
  let ev := j.events
  match c, j.out with
  | _, .compileError m =>
    if hasE ev "typed param fn recur" then "CG5 typed parameter + fn-level recur: invalid C++"
    else "compile error: " ++ String.ofList (m.toList.take 50)
  | .compileError _, _ => "Clojure rejects (recur to a primitive parameter with another type)"
  | _, .ub k _ _ =>
    if k.startsWith "forward progress" then "CG1 forward progress"
    else if k.startsWith "double out of" then "CG2 float-to-integer conversion out of range"
    else if k == "integer division by zero" then "documented: integer division by zero is UB (book)"
    else if k == "integer division overflow" then "D2 (round 1): INT_MIN / -1"
    else "UB: " ++ k
  | _, _ =>
    if hasE ev "double out of int range" || hasE ev "double out of long range" then "CG2 float-to-integer conversion out of range"
    else if hasE ev "runtime static_cast<i64> out of range" then "CG2 float-to-integer conversion out of range"
    else if hasE ev "integer division by zero" then "documented: integer division by zero is UB (book)"
    else if hasE ev "integer division overflow" then "D2 (round 1): INT_MIN / -1"
    else if hasE ev "side-effect-free loop never ends" && hasE ev "recur/cast changes the value" then "R24 loop local keeps the literal's type"
    else if hasE ev "recur/cast changes the value" || hasE ev "from_object of a non-number" then "R24 loop local keeps the literal's type"
    else if hasE ev "bool as number" || j.notes.contains "bool-arith" then "R33 booleans are numbers"
    else if j.notes.contains "R36" then "R36 object loop local, native recur value"
    else if hasE ev "if merges branch types" then "R23 if merges branch types"
    else if hasE ev "int arithmetic wraps (32-bit)" || hasE ev "narrowed to the analyzer's type when boxed" then "R25 32-bit literal arithmetic"
    else if hasE ev "object arithmetic wraps (32-bit)" then "D1 (round 1): small integers wrap at 32 bits"
    else if hasE ev "long arithmetic wraps" then "D1 (round 1): long overflow wraps (documented)"
    else if hasE ev "integer division truncates" then "D2 (round 1): integer / is C++ division"
    else if (match c with | .value v _ => isRatio v | _ => false) then "D2 (round 1): integer / is C++ division"
    else if (match c with | .value _ o | .threw _ o => o.any (fun x => x.contains '/' || x.endsWith "N") | _ => false) then
      "D2 (round 1): integer / is C++ division"
    else if (match c with | .threw m _ => m.startsWith "ArithmeticException: Divide" | _ => false) then "D2 (round 1): integer / is C++ division"
    else if f.hasToInt && (match c with | .threw m _ => (m.splitOn "out of range for int").length > 1 | _ => false) then
      "CG2b int does not check the int range"
    else if f.hasTyped .int then "jank ^cpp/int parameter (no Clojure counterpart)"

    else "other"

def classJJ (j0 jl : JRun) : String :=
  match jl.out with
  | .ub k _ _ =>
    if k.startsWith "forward progress" then "CG1 forward progress"
    else if k.startsWith "double out of" then "CG2 float-to-integer conversion out of range"
    else if k == "integer division by zero" then "documented: integer division by zero is UB (book)"
    else if k == "integer division overflow" then "D2 (round 1): INT_MIN / -1"
    else "UB: " ++ k
  | _ => "-O differs: " ++ j0.out.show.take 30 ++ " / " ++ jl.out.show.take 30

/-- One timeline: a program, Clojure vs jank at `lvl` (property 1), and jank at `lvl` vs `-O0`
(property 2). -/
def body (lvl : Lvl) (tgt : Target) (depth : Nat) (known : List String) (prop : Nat := 0) (small : Bool := false) : G Unit := do
  let f ← genProg small depth
  let c := runClojure f
  let j := runJank lvl tgt f
  if prop != 2 then
   match agreeCJ c j.out with
   | some false =>
    let k := classCJ f c j
    if !known.contains k then
      Determinismo.violate (σ := W) s!"jank means what Clojure means [{k}]" s!"{f.code}: Clojure {c.show}, jank -O{lvl.n} {j.out.show}"
   | _ => pure ()
  if prop != 1 && lvl.optimizes then
    let j0 := runJank .o0 tgt f
    match agreeJJ j0.out j.out with
    | some false =>
      let k := classJJ j0 j
      if !known.contains k then
        Determinismo.violate (σ := W) s!"-O{lvl.n} means what -O0 means [{k}]" s!"{f.code}: -O0 {j0.out.show}, -O{lvl.n} {j.out.show}"
    | _ => pure ()

def run (lvl : Lvl) (tgt : Target) (depth : Nat) (known : List String) (prop : Nat) (source : Source) (small : Bool := false) : Ended :=
  match (body lvl tgt depth known prop small).run { decisions := { source, limit := 200 } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p dd) w => { taken := w.decisions.taken, violation := some (p, dd) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R3.Codegen.NativeSearch

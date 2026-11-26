import Jank.R6.Native.Math

/-!
# The analyzer's typing of native branches: `if` and `case` (R23, R26), with every native type

analyze/cpp_util.cpp `find_branch_common_type` 1907-1995: two branches of different native
arithmetic types are "compatible" (`Cpp::GetCommonType` is the type of `c ? a : b`, the usual
arithmetic conversions), neither is boxed (`then_needs_conversion` is false when the other branch
is native and compatible), and the `if` takes the common type (1970-1974): the chosen branch is
converted into it (ir/processor.cpp 659 assigns each branch to one typed local). `analyze_case`
(processor.cpp 1386-1581) runs it per branch against the default and keeps the LAST branch's type
(`chosen_type = branch_common_type.type`, 1521); without a boxing need nothing is converted, so
each branch is assigned to the last type by C++'s implicit conversion.

Round 2 found R23 and R26 with `int`, `long`, `double` and `bool`. With every native type of this
round, a new value change appears where the common type is `unsigned int`: `(if c (hash 1) -1)`
gives 4294967295 for the `-1` branch.

Switches: `r23` (fixes/R23.diff: two different native number types are boxed, each branch keeps
its value) and `r26` (fixes/R26.diff: a `case` whose branches do not all have the default's type
is boxed).
-/

namespace Jank.R6.Native.Typing

open Jank.R6.Native

/-- The native operands of the walk (every source whose jank operand is a primitive). -/
def natives : List Src :=
  sources.filter fun s => match s.jank {} with | .prim _ => true | _ => false

def primOf (s : Src) (sw : Sw := {}) : NV := match s.jank sw with | .prim n => n | _ => .i .int 0

/-- The source switches (P6, R122, P7), to separate their value changes from the typing's. -/
def srcSw : Sw := { hashSigned := true, bytesSigned := true, floatF32 := true }

/-- The value an `if` with branches `a`, `b` gives when it takes `a` (`takeThen`) or `b`. -/
def ifJank (r23 : Bool) (a b : Src) (takeThen : Bool) (sw : Sw := {}) : CR :=
  let na := primOf a sw
  let nb := primOf b sw
  let chosen := if takeThen then na else nb
  if na.ty == nb.ty || r23 then (JR.prim chosen).seen
  else
    match chosen.conv (commonType na.ty nb.ty) with
    | .ok v => (JR.prim v).seen
    | .ub m => .threw s!"undefined behavior: {m}"

def ifClj (a b : Src) (takeThen : Bool) : CR := .val (if takeThen then a.clj else b.clj)

/-- A `case` with branches `bs` and default `d`, taking branch `k` (`bs.length` = the default). -/
def caseJank (r26 : Bool) (bs : List Src) (d : Src) (k : Nat) (sw : Sw := {}) : CR :=
  let nd := primOf d sw
  let nbs := bs.map (primOf · sw)
  let chosen := if k < nbs.length then nbs[k]! else nd
  let allSame := nbs.all (·.ty == nd.ty)
  if allSame || r26 then (JR.prim chosen).seen
  else
    -- the last branch's common type with the default; nothing boxed (all native, compatible)
    let last := nbs.getLast!
    match chosen.conv (commonType last.ty nd.ty) with
    | .ok v => (JR.prim v).seen
    | .ub m => .threw s!"undefined behavior: {m}"

def caseClj (bs : List Src) (d : Src) (k : Nat) : CR :=
  .val (if k < bs.length then bs[k]!.clj else d.clj)

def isUnsignedNarrow (t : NT) : Bool := t == .uint || t == .ushort || t == .uchar

def run : IO Unit := do
  -- `if`: every pair of native sources, both branches taken
  let mut n := 0
  let mut dev := 0
  let mut devNew := 0
  let mut afterFix := 0
  let mut afterAll := 0
  let mut ex : Array String := #[]
  for a in natives do
    for b in natives do
      for t in [true, false] do
        n := n + 1
        let j := ifJank false a b t
        let c := ifClj a b t
        if !agrees j c then
          dev := dev + 1
          let ct := commonType (primOf a).ty (primOf b).ty
          if !ct.signed && ct.isIntegral && ct != .ullong && ct != .bool then
            devNew := devNew + 1
            if ex.size < 6 then
              ex := ex.push s!"((fn [c] (if c {a.code} {b.code})) {t}): Clojure {c.show}, jank {j.show} (common type {ct.name})"
        if !agrees (ifJank true a b t) c then afterFix := afterFix + 1
        if !agrees (ifJank true a b t srcSw) c then afterAll := afterAll + 1
  IO.println s!"if: {natives.length} native sources, {n} (then, else, taken) cases, complete"
  IO.println s!"  differ: {dev}; of them with an unsigned common type narrower than usize (new): {devNew}; with R23.diff: {afterFix}; with R23.diff and the source switches (P6, R122, P7): {afterAll}"
  for e in ex do IO.println s!"    e.g. {e}"
  -- `case`: two branches and a default from a smaller set, every branch taken
  let small : List Src := [.lit (-1), .lit 7, .dlit 1.5, .count 1, .hash 1, .pred true, .int_ (-1)]
  let mut cn := 0
  let mut cdev := 0
  let mut cfix := 0
  let mut cex : Array String := #[]
  for b1 in small do
    for b2 in small do
      for d in small do
        for k in [0, 1, 2] do
          cn := cn + 1
          let j := caseJank false [b1, b2] d k
          let c := caseClj [b1, b2] d k
          if !agrees j c then
            cdev := cdev + 1
            if cex.size < 4 then
              cex := cex.push s!"((fn [k] (case k 0 {b1.code} 1 {b2.code} {d.code})) {k}): Clojure {c.show}, jank {j.show}"
          if !agrees (caseJank true [b1, b2] d k srcSw) c then cfix := cfix + 1
  IO.println s!"case: 2 branches and a default over {small.length} native sources, each taken: {cn} cases, complete"
  IO.println s!"  differ: {cdev}; with R26.diff and the source switches: {cfix}"
  for e in cex do IO.println s!"    e.g. {e}"

end Jank.R6.Native.Typing

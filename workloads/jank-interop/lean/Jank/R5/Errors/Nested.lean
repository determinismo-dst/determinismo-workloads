import Jank.R5.Errors.World

/-!
# Round 5, errors: errors raised through nested contexts

An inner error (`Inner`, or a `require` of a missing lib) is raised inside up to two wrapping
contexts, innermost first: a delay (one deref), a future (deref), a module's top level (required),
a macro's body (the macro used through `eval`), a top-level def's value (through `eval`). Each
context is one function per side, from `Model.lean`; the world composes them and compares what the
outermost caller sees: which handler catches it, and the root data. Classes as in `World.lean`;
`unexplained` would be an interaction no single mechanism explains.
-/

namespace Jank.R5.Errors.Nested

open Determinismo Jank.R5.Errors Jank.R5.Errors.World

inductive Base where
  | inner (i : Inner)
  | requireMissing
  deriving Repr, BEq, Inhabited

def Base.show : Base → String
  | .inner i => i.show
  | .requireMissing => "(require 'missing)"

def Base.all : List Base := Inner.all.map .inner ++ [.requireMissing]

inductive Ctx where
  | delay
  | future
  | module
  | macro
  | topDef
  deriving Repr, BEq, Inhabited, DecidableEq

def Ctx.all : List Ctx := [.delay, .future, .module, .macro, .topDef]

def Ctx.wrap : Ctx → String → String
  | .delay, s => s!"@(delay {s})"
  | .future, s => s!"@(future {s})"
  | .module, s => s!"(require 'm) where m runs {s}"
  | .macro, s => s!"(eval '(m)) where macro m runs {s}"
  | .topDef, s => s!"(eval '(def x {s}))"

def jBase : Base → JRes
  | .inner i => .thrown (jInner i)
  | .requireMissing => jRequireMissing

def cBase : Base → CRes
  | .inner i => .thrown (cInner i)
  | .requireMissing => cRequireMissing

/-- jank: one context around what its body gave. -/
def jWrap : Ctx → JRes → JRes
  | .delay, r => (jDelayDeref r {}).1
  | .future, r => jFuture r
  | .module, r => match r with
    | .thrown t => .thrown (jLoadModuleConvert t)
    | .terminated w => .terminated w
    | .ok _ => .ok .nil
  | .macro, r => match r with
    | .thrown t => .thrown (jMacroConvert t)
    | r => r
  | .topDef, r => r

def isCompiler (e : CEx) : Bool :=
  match e with
  | l :: _ => l.cls == .compilerException
  | [] => false

/-- Clojure: one context around what its body gave. -/
def cWrap : Ctx → CRes → CRes
  | .delay, r => r
  | .future, r => cFuture r
  | .module, r => match r with
    | .thrown e => .thrown (if isCompiler e then e else cCompiler "execution" :: e)
    | .ok _ => .ok .nil
  | .macro, r => match r with
    | .thrown e =>
      if isCompiler e then .thrown e
      else match e with
        | l :: _ => if l.cls == .exceptionInfo || l.cls == .illegalArgument
                    then .thrown (cCompiler "macro-syntax-check" :: e)
                    else .thrown (cCompiler "macroexpansion" :: e)
        | [] => .thrown e
    | r => r
  | .topDef, r => match r with
    | .thrown e => .thrown (if isCompiler e then e else cCompiler "execution" :: e)
    | r => r

def jRun (b : Base) (cs : List Ctx) : JRes := cs.foldl (fun r c => jWrap c r) (jBase b)
def cRun (b : Base) (cs : List Ctx) : CRes := cs.foldl (fun r c => cWrap c r) (cBase b)

def showProg (b : Base) (cs : List Ctx) : String := cs.foldl (fun s c => c.wrap s) b.show

/-- Whether a context that turns an object into an error_ref (a module, a macro) is on the way
out from the base. -/
def converts (cs : List Ctx) : Bool := cs.any (fun c => c == .module || c == .macro)

def program : WM Unit := do
  let b ← pickFrom "nested.base" Base.all
  let depth ← decide (σ := W) "nested.depth" 3
  let mut cs : List Ctx := []
  for _ in [0:depth] do
    cs := cs ++ [← pickFrom "nested.ctx" Ctx.all]
  let jr := jRun b cs
  let cr := cRun b cs
  let p := showProg b cs
  match jr with
  | .terminated _ =>
    violate (σ := W) "B6: a future whose body raises an error_ref ends the process"
      s!"{p}: Clojure {(cOutcome cr).show}, jank the process ends"
  | _ =>
    let jk := jOutcome jr
    let ck := cOutcome cr
    if jk != ck then
      let cls := match jk with
        | .error => "B1: an error_ref (read, analysis, load error) escapes the object catch"
        | .native => "known: a std::exception escapes the object catch (book native-exceptions.md; R26, U79)"
        | _ => "unexplained"
      violate (σ := W) cls s!"{p}: Clojure {ck.show}, jank {jk.show}"
    if b == .inner .exInfo then
      let jd := (jRootData jr).isSome
      let cd := (cRootData cr).isSome
      if jd != cd then
        let cls := if converts cs then "B3: an ex-info raised under the compiler or the loader loses its data"
                   else "unexplained"
        violate (σ := W) cls s!"{p}: the ex-info's data reachable: Clojure {cd}, jank {jd}"

def run : Source → Ended := runW program

end Jank.R5.Errors.Nested

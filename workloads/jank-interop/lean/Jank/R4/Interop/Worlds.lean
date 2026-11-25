import Jank.R4.Interop.TopLevel
import Jank.R4.Interop.Operators
import Jank.R4.Interop.Templates
import Jank.R4.Interop.Deferred

/-!
# Round 4 interop worlds: decision bodies for `explore`/`exhaust`, and `cpp/delete`

Each body draws one case with named decisions and breaks the property with the case's class when
jank (the replica) and the spec disagree; `Worlds.residual` (round 3) sets each found class aside
and searches again until a complete run finds nothing.
-/

namespace Jank.R4.Interop.Worlds4

open Determinismo
open Jank.Interop
open Jank.Interop.Search (W runW pickW)

/-! ## XVI′: `if` with native branches, at the top level and inside a fn -/

/-- R23 (round 2) covers an `if` whose two branches are literals; S57 (round 3) one whose branch
is a reference (a `cpp/` global). Inside a compiled fn both convert the chosen branch; at the top
level neither does. -/
def ctxClass (c : TopLevel.CtxCase) (cls : String) : String :=
  if cls == "compiled-if-converts" then
    if c.a.1.startsWith "cpp/" || c.b.1.startsWith "cpp/" then "S57-compiled" else "R23-compiled"
  else cls

def ctxBody (skip : List String) : EStateM Stop W Unit := do
  let c ← pickW "r4.branch.case" TopLevel.allCtx
  if let some (cls, d) := TopLevel.ctxJudge x86_64 c then
    let cls := ctxClass c cls
    if !skip.contains cls then violate (σ := W) s!"if-context:{cls}" d

/-! ## XVIII: operators with `GetOperator`'s lookup -/

def opBody (skip : List String) : EStateM Stop W Unit := do
  let c ← pickW "r4.operator.case" Operators.allCases
  if let some (cls, d) := Operators.judge x86_64 c then
    if !skip.contains cls then violate (σ := W) s!"operator:{cls}" (d.take 400 |>.toString)

/-! ## XIX: class template constructor calls -/

def tBody (skip : List String) : EStateM Stop W Unit := do
  let c ← pickW "r4.template.case" Templates.allTCases
  if let some (cls, d) := Templates.tJudge x86_64 c then
    if !skip.contains cls then violate (σ := W) s!"class-template:{cls}" d

/-! ## XXI: `cpp/delete` by pointer origin -/

/-- Where a pointer comes from. -/
inductive Origin where
  /-- `(cpp/new T …)`: `new (UseGC) T{ … }` (cpp_processor.cpp 1866-1891), the collector's heap. -/
  | cppNewForm
  /-- `new T(…)` inside `cpp/raw` code: `::operator new`, malloc (jank links bdwgc's `gc` and
  `gctba`, not `gccpp`, CMakeLists.txt 446/677; gc_badalc.cc defines only `GC_throw_bad_alloc`). -/
  | cxxNew
  /-- `(cpp/& cpp/g)` of a global: static storage. -/
  | staticObject
  deriving Repr, BEq, Inhabited

/-- What `(cpp/delete p)` does: `p->~T()` when not trivially destructible, then `GC_free(p)`
(cpp_processor.cpp 1894-1919). bdwgc's `GC_free` (malloc.c 824-849) takes `HDR(p)`, which is null
outside the collector's heap (gc_hdrs.h 155-200: the bottom index `GC_all_nils`), and
`GC_free_internal` (766-771) reads `hhdr->hb_sz` first. -/
def jankDelete : Origin → String
  | .cppNewForm => "destroyed and freed"
  | .cxxNew => "destructor runs, then GC_free dereferences a null header: SIGSEGV"
  | .staticObject => "destructor runs, then GC_free dereferences a null header: SIGSEGV"

/-- C++ `delete p` ([expr.delete]/2: the pointer must come from a non-array new-expression). -/
def cppDelete : Origin → String
  | .cppNewForm => "undefined (placement `new (UseGC)` memory)"
  | .cxxNew => "destroyed and freed"
  | .staticObject => "undefined"

def deleteRows : List (Origin × String × String) :=
  [.cppNewForm, .cxxNew, .staticObject].map fun o => (o, jankDelete o, cppDelete o)

theorem delete_cxx_new_crashes : jankDelete .cxxNew ≠ cppDelete .cxxNew := by decide

end Jank.R4.Interop.Worlds4

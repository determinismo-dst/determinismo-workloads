import Jank.R9.Err.Catch

/-!
# Round 9, area E: the paths the fixes change, beyond the catch

- **Reporting.** util/try.cpp `print_exception` 209–255: an error_ref prints `error::report(e)`; an
  exception_info prints its `to_code_string()` (`#error {…}`); a string or a std::exception the
  "uncaught exception" report of its text. A34/V7a: an exception_info carrying an error prints
  that error's report.
- **load_module** (context.cpp 324–354): an error_ref from the module is returned as is; an object
  becomes `runtime_unable_to_load_module(e.to_code_string())`; A34/V7a: an exception_info carrying
  an error is that error; V9: the object stays with the error (`base::thrown`).
- **nth** (core/seq.cpp `nth` 648–695; persistent_vector.cpp `nth` 321–339; persistent_string.cpp
  `nth` 105–121): stock throws std::runtime_errors; X20 made the string's own check an object;
  X20b makes seq.cpp's and the vectors' checks objects.
- **The error ctor** `exception_info(error_ref)` (exception_info.cpp 23–27; `*e` in safe_eval
  evaluate.cpp 750, and A34's converter): V9's cause, V18's CompilerException shape.
-/

namespace Jank.R9.Err

open Jank.R5.Errors

/-! ## Reporting -/

/-- What the CLI prints for what escaped to `jank_init`'s handlers. -/
inductive Printed where
  | report (e : JErr)
  | codeString (x : JEx)
  | uncaught (text : String)
  | unknown
  deriving Repr, BEq, Inhabited

def jvalText : JVal → String
  | .str s => s
  | _ => "object"

def printStock : Thrown → Printed
  | .err e => .report e
  | .obj (.ex x) => .codeString x
  | .obj o => .uncaught (jvalText o)
  | .std _ w => .uncaught w
  | _ => .unknown

def printFixed : Thrown → Printed
  | .obj (.ex x) => match x.error with
    | some e => .report e
    | none => .codeString x
  | t => printStock t

/-- A program catch of object_ref that rethrows what it bound (core.jank load-lib 4860–4865:
`(catch cpp/jank.runtime.object_ref e (when undefined-on-entry? (remove-ns lib)) (throw e))`),
under a variant's code: what leaves it. -/
def rethrowLayer (c : Conv) (t : Thrown) : Thrown :=
  match fixedTry c [.object] t with
  | .handled _ v => v
  | .escapes t => t

def layers (c : Conv) : Nat → Thrown → Thrown
  | 0, t => t
  | n + 1, t => layers c n (rethrowLayer c t)

theorem rethrow_err (c : Conv) (hc : c.err = true) (e : JErr) :
    rethrowLayer c (.err e) = .obj (convErr e) := by
  simp [rethrowLayer, fixedTry, objIdx, inner, convertible, hc, convert, stockTry, catches]

theorem rethrow_obj (c : Conv) (o : JVal) : rethrowLayer c (.obj o) = .obj o := by
  simp [rethrowLayer, fixedTry, objIdx, inner, stockTry, catches]

theorem layers_obj (c : Conv) (o : JVal) : ∀ n, layers c n (.obj o) = .obj o := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp [layers, rethrow_obj, ih]

/-- ★ jank's own report is kept: an error that crosses any number n ≥ 0 of program catches that
rethrow (load-lib's, at each nested require) prints, under A34 or V7a, exactly what the stock CLI
prints for the bare error. -/
theorem report_preserved (c : Conv) (hc : c.err = true) (e : JErr) :
    ∀ n, printFixed (layers c n (.err e)) = printStock (.err e) := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [layers, rethrow_err c hc, layers_obj]
    simp [printFixed, convErr, printStock]

/-- Stock: the same crossing prints the error when nothing converts (the catches don't see it). -/
theorem report_stock (e : JErr) : ∀ n, printStock (layers .stock n (.err e)) = printStock (.err e) := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    have : rethrowLayer .stock (.err e) = .err e := by
      simp [rethrowLayer, fixedTry, objIdx, inner, convertible, Conv.stock, stockTry, catches,
        Res.shift]
    simp [layers, this, ih]

/-- What V7r (round 8) throws for a read error: `make_box<exception_info>(e->message, nil)` with
the error attached. The CLI prints it as `#error {…}` on stock's print_exception, and as the
error's report with A34/V7a's. -/
def v7rObj (e : JErr) : Thrown := .obj (.ex { message := e.message, data := .nil, error := some e })

theorem v7r_report (e : JErr) : printFixed (v7rObj e) = .report e ∧
    printStock (v7rObj e) ≠ .report e := by
  simp [v7rObj, printFixed, printStock]

/-! ## load_module -/

/-- context.cpp 342–353 (round 5's `jLoadModuleConvert`, on R9's thrown values). -/
def loadModuleStock : Thrown → Thrown
  | .std _ w => .err { kind := .runtimeUnableToLoadModule, message := w }
  | .obj o => .err { kind := .runtimeUnableToLoadModule,
                     message := match o with | .ex e => s!"#error {e.message}" | _ => "object" }
  | t => t

def loadModuleFixed : Thrown → Thrown
  | .obj (.ex x) => match x.error with
    | some e => .err e
    | none => loadModuleStock (.obj (.ex x))
  | t => loadModuleStock t

/-- ★ A nested require's failure keeps its error: what a module's load-lib made an object and
rethrew is, at the enclosing load_module, the same error the stock code returns for the bare
error. -/
theorem load_module_unwrap (c : Conv) (hc : c.err = true) (e : JErr) :
    loadModuleFixed (rethrowLayer c (.err e)) = loadModuleStock (.err e) := by
  rw [rethrow_err c hc]; simp [loadModuleFixed, convErr, loadModuleStock]

/-! ## V9 and V18: the error ctor

An error with V9's `thrown` and V18's phase. The phase is by kind group (lex/parse → read-source,
macro expansion → macro-syntax-check, other analysis → compile-syntax-check, else none). -/

inductive Phase where
  | readSource
  | macroSyntax
  | compileSyntax
  deriving Repr, BEq, DecidableEq, Inhabited

structure Err9 where
  base : JErr
  phase : Option Phase
  thrown : Option JVal := none
  deriving Repr, BEq, Inhabited

def kindPhase : ErrKind → Option Phase
  | .parseUnterminatedList | .parseUnexpectedClosing => some .readSource
  | .analyzeMacroExpansionException => some .macroSyntax
  | .analyzeUnresolvedSymbol => some .compileSyntax
  | .runtimeModuleNotFound | .runtimeUnableToLoadModule => none

def mkErr9 (e : JErr) (thrown : Option JVal := none) : Err9 :=
  { base := e, phase := kindPhase e.kind, thrown }

/-- The thrown ex-info's link (message, data) and its own causes. -/
def thrownLinks : Option JVal → List (String × Data)
  | some (.ex x) => (x.message, x.data) :: x.causes
  | _ => []

/-- `exception_info(error_ref)` with V9 and V18 (the merged fixes): for a phase, the message
"Syntax error … at (…)." (abstracted), the :clojure.error/* data, and the cause chain
[error's message, then the thrown ex-info's links]; without, the error's message (U44 or A34's
converter), nil data, the thrown ex-info's links as causes. -/
def ctorFixed (e : Err9) : JEx :=
  match e.phase with
  | some _ => { message := "Syntax error", data := compilerData,
                causes := (e.base.message, .nil) :: thrownLinks e.thrown, error := some e.base }
  | none => { message := e.base.message, data := .nil, causes := thrownLinks e.thrown,
              error := some e.base }

/-- Stock `exception_info(error_ref)`: only `error` (message "", nil data, no cause). -/
def ctorStock (e : Err9) : JEx := { message := "", data := .nil, error := some e.base }

/-- ★ V18: `*e` (and a program's catch, through A34) of every read, analysis or macro error has
ex-data and an ex-cause, as nREPL over Clojure gives (CompilerException); stock has neither. -/
theorem v18_star_e (e : Err9) (h : e.phase.isSome) :
    (ctorFixed e).data ≠ .nil ∧ (ctorFixed e).causes ≠ [] ∧
    (ctorStock e).data = .nil ∧ (ctorStock e).causes = [] := by
  cases hp : e.phase with
  | none => simp [hp] at h
  | some p => simp [ctorFixed, ctorStock, hp, compilerData]

theorem data_has_nil (k : String) : Data.nil.has k = false := rfl

/-- ★ V9: for every ex-info a module's top level or a macro's body throws, with every data map,
the converted error keeps the data reachable through ex-cause (round 5's `jDataWith`), whatever the
error's phase; stock loses it. -/
theorem v9_data_kept (e : JErr) (x : JEx) (k : String) (hk : x.data.has k = true)
    (hnot : compilerData.has k = false) :
    jDataWith (ctorFixed (mkErr9 e (some (.ex x)))) k = some x.data ∧
    jDataWith (ctorStock (mkErr9 e (some (.ex x)))) k = none := by
  constructor
  · unfold ctorFixed mkErr9
    cases kindPhase e.kind <;>
      simp [jDataWith, thrownLinks, hk, hnot, data_has_nil, List.find?_cons]
  · simp [ctorStock, jDataWith, data_has_nil]

/-! ## nth (X20b) -/

/-- The collection `nth` is given. -/
inductive Coll where
  | nil
  | str (n : Nat)
  | vec (n : Nat)
  | seq (n : Nat)
  | kw
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What `(nth coll i)` does: a value, a throw (object or std, with the site), in jank. -/
inductive NthR where
  | val
  | nilv
  | objThrow (site : String)
  | stdThrow (site : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- seq.cpp `nth` 648–695 (2-arity): nil → nil; a negative index throws first (656–660); an
indexable value's own `nth` (string: persistent_string.cpp 105–121, an object with X20; vector:
persistent_vector.cpp 321–339); a sequential seq walked (673–688); else "not indexable" (690–692).
`x20` and `x20b` select the fixes. -/
def thrw (site : String) (obj : Bool) : NthR := if obj then .objThrow site else .stdThrow site

def jNth (x20 x20b : Bool) (c : Coll) (i : Int) : NthR :=
  match c with
  | .nil => .nilv
  | .str n => if i < 0 then thrw "seq.cpp nth: negative index" x20b
              else if i < n then .val else thrw "persistent_string::nth" x20
  | .vec n => if i < 0 then thrw "seq.cpp nth: negative index" x20b
              else if i < n then .val else thrw "persistent_vector::nth" x20b
  | .seq n => if i < 0 then thrw "seq.cpp nth: negative index" x20b
              else if i < n then .val else thrw "seq.cpp nth: walk" x20b
  | .kw => if i < 0 then thrw "seq.cpp nth: negative index" x20b
           else thrw "seq.cpp nth: not indexable" x20b

/-- Clojure's RT.nth (RT.java 893–950): nil → nil; out of range or negative throws
(StringIndexOutOfBounds / IndexOutOfBounds); a keyword throws UnsupportedOperationException. -/
def cNth (c : Coll) (i : Int) : NthR :=
  match c with
  | .nil => .nilv
  | .str n | .vec n | .seq n => if 0 ≤ i ∧ i < n then .val else .objThrow "Clojure"
  | .kw => .objThrow "Clojure"

def NthR.kindEq : NthR → NthR → Bool
  | .val, .val | .nilv, .nilv | .objThrow _, .objThrow _ | .stdThrow _, .stdThrow _ => true
  | _, _ => false

/-- ★ With X20 and X20b, `nth` agrees with Clojure for every collection and index: a value, nil,
or a throw a program's catch sees (an object). -/
theorem nth_fixed_eq_clj (c : Coll) (i : Int) : (jNth true true c i).kindEq (cNth c i) = true := by
  cases c with
  | nil => rfl
  | kw => by_cases h1 : i < 0 <;> simp [jNth, cNth, thrw, NthR.kindEq, h1]
  | str n | vec n | seq n =>
    by_cases h1 : i < 0
    · have h0 : ¬ (0 ≤ i) := by omega
      simp [jNth, cNth, thrw, NthR.kindEq, h1, h0]
    · have h0 : 0 ≤ i := by omega
      by_cases h2 : i < (n : Int) <;> simp [jNth, cNth, thrw, NthR.kindEq, h1, h0, h2]

/-- ★ X20's miss, for every string and negative index: with X20 alone, `(nth s i)` for i < 0
still throws a std::runtime_error (seq.cpp 656–660), which `thrown?` doesn't see (g480–g482). -/
theorem x20_miss (n : Nat) (i : Int) (h : i < 0) :
    jNth true false (.str n) i = .stdThrow "seq.cpp nth: negative index" := by
  simp [jNth, thrw, h]

/-- ★ Stock: every throw of `nth` is a std::runtime_error. -/
theorem nth_stock_std (c : Coll) (i : Int) :
    ∀ s, jNth false false c i ≠ .objThrow s := by
  intro s
  cases c <;> simp only [jNth, thrw] <;> (try split) <;> (try split) <;> simp_all

end Jank.R9.Err

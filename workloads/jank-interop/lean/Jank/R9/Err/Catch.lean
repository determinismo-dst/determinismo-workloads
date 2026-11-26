import Jank.R5.Errors.Model

/-!
# Round 9, area E: what a jank `catch` sees, stock and with A34 / V7a

Every jank path is under `upstream-r5/compiler+runtime/` (94d32623).

**What is thrown** (round 5's `JThrown`, refined): an `object_ref` (jank's `throw`, codegen
`gen(throw)` cpp_processor.cpp 1022–1051, which `static_cast`s every object to `object_ref`); a
`jank::error_ref` (`jtl::ref<error::base>`, error.hpp 293; `jtl::result::expect_ok`'s `panic`
throws it, jtl/result.hpp 41–68); a `std::exception` of some class (the runtime's checks, the
`invalid_arity` of object.cpp, libstdc++'s `regex_error` and `filesystem_error`); a C++ `int`
(cpp/raw code, a native `(throw 1)`); anything else.

**What a handler is** (analyze_try processor.cpp 2925–3150; gen(catch) cpp_processor.cpp
1105–1123): `catch(T &e)` for the analyzed type T (class types are made lvalue references,
3049–3053), and `:default` is `catch(...)`. C++ picks the first handler whose type catches the
thrown value's type ([except.handle]/3): `object_ref` only an object_ref, `std::X&` a class
derived from X, `error_ref` an error_ref, `int` an int, `catch(...)` anything.

**Stock** `gen(try)` (cpp_processor.cpp 1054–1100) emits `try { body } catch(h₁)… catch(hₙ)` in the
program's order. **A34** (fixes/A34.diff) adds, when some hₖ is `object_ref`, an inner try around
the body: `catch(h₁) { throw; } … catch(hₖ₋₁) { throw; }` (the handlers before the object one get
what they match, unchanged), `catch(object_ref const &) { throw; }`, then
`catch(error_ref const &) { throw to_exception_object(e); }` and
`catch(std::exception const &) { throw to_exception_object(e); }`. **V7a** has only the error_ref
converter. `to_exception_object` (A34's exception_info.cpp) builds an ex-info: an error's message,
nil data, the error attached; a std::exception's `what()`, nil data.

Clojure: every exception is a Throwable, and `(catch Throwable e …)` is the handler jank programs
write as `(catch cpp/jank.runtime.object_ref e …)` (round 4's NA9 mapping, round 5's errA5-1).
-/

namespace Jank.R9.Err

open Jank.R5.Errors

/-- std::exception classes met on these paths. `invalidArity` is object.cpp's `invalid_arity<N>`,
a `std::runtime_error` (object.hpp); `regexError` is libstdc++'s `std::regex_error` (a
runtime_error); `fsError` is `std::filesystem::filesystem_error` (system_error, a runtime_error). -/
inductive StdCls where
  | runtimeError
  | invalidArity
  | regexError
  | fsError
  | logicError
  | badCast
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The class a `std::` handler names. -/
inductive StdH where
  | exception
  | runtimeError
  | logicError
  | badCast
  | invalidArity
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Whether a thrown std class derives from the handler's class. -/
def StdCls.sub : StdCls → StdH → Bool
  | _, .exception => true
  | .runtimeError, .runtimeError => true
  | .invalidArity, .runtimeError => true
  | .regexError, .runtimeError => true
  | .fsError, .runtimeError => true
  | .logicError, .logicError => true
  | .badCast, .badCast => true
  | .invalidArity, .invalidArity => true
  | _, _ => false

/-- What a C++ `throw` carries on these paths. -/
inductive Thrown where
  | obj (o : JVal)
  | err (e : JErr)
  | std (c : StdCls) (what : String)
  | int (n : Int)
  | foreign
  deriving Repr, BEq, Inhabited

/-- A handler: `catch(object_ref &)`, `catch(jank::error_ref &)`, `catch(std::X &)`, `catch(int)`,
`catch(...)` (`:default`). -/
inductive H where
  | object
  | errorRef
  | std (c : StdH)
  | int
  | default_
  deriving Repr, BEq, DecidableEq, Inhabited

/-- [except.handle]/3 on these types. -/
def catches : H → Thrown → Bool
  | .object, .obj _ => true
  | .errorRef, .err _ => true
  | .std h, .std c _ => c.sub h
  | .int, .int _ => true
  | .default_, _ => true
  | _, _ => false

/-- A try's outcome: handler `i` (0-based, in the program's order) ran with `v` bound (for
`:default`, jank binds a nil object_ref, gen(catch) 1111–1113; the model keeps what was thrown and
the observers below ignore a default's binding), or `t` left the try. -/
inductive Res where
  | handled (i : Nat) (v : Thrown)
  | escapes (t : Thrown)
  deriving Repr, BEq, Inhabited

def Res.shift : Res → Res
  | .handled i v => .handled (i + 1) v
  | r => r

/-- Stock `gen(try)`: the program's handlers, in order. -/
def stockTry : List H → Thrown → Res
  | [], t => .escapes t
  | h :: hs, t => if catches h t then .handled 0 t else (stockTry hs t).shift

/-! ## to_exception_object (A34: exception_info.cpp, appended) -/

/-- `to_exception_object(error_ref)`: `make_box<exception_info>(e)` (exception_info.cpp 23–27: only
`error` set), then the message from the error, nil data, and the error's `cause` chain as
ex-causes (each converted the same way: message, nil data). -/
def convErr (e : JErr) : JVal :=
  .ex { message := e.message, data := .nil, causes := e.causes.map (fun (_, m) => (m, .nil)),
        error := some e }

/-- `to_exception_object(std::exception)`: `make_box<exception_info>(what(), jank_nil)`. -/
def convStd (w : String) : JVal := .ex { message := w, data := .nil }

/-- Which kinds the generated inner try converts: A34 both, V7a error_refs only, stock none. -/
structure Conv where
  err : Bool
  std : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

def Conv.stock : Conv := ⟨false, false⟩
def Conv.v7a : Conv := ⟨true, false⟩
def Conv.a34 : Conv := ⟨true, true⟩

/-- Whether a thrown value is one the converters take. -/
def convertible (c : Conv) : Thrown → Bool
  | .err _ => c.err
  | .std _ _ => c.std
  | _ => false

def convert : Thrown → Thrown
  | .err e => .obj (convErr e)
  | .std _ w => .obj (convStd w)
  | t => t

/-! ## The generated code, literally -/

/-- What leaves A34's inner try: a value a handler before the object handler catches is rethrown
unchanged (`catch(hᵢ) { throw; }`); an object passes (`catch(object_ref const &) { throw; }`); an
error_ref or a std::exception is converted when the variant converts it; anything else no inner
handler catches, so it propagates as it was. -/
def inner (pre : List H) (c : Conv) (t : Thrown) : Thrown :=
  if pre.any (fun h => catches h t) then t
  else match t with
    | .obj _ => t
    | _ => if convertible c t then convert t else t

/-- The index of the first `object_ref` handler. -/
def objIdx : List H → Option Nat
  | [] => none
  | .object :: _ => some 0
  | _ :: hs => (objIdx hs).map (· + 1)

/-- A34's / V7a's `gen(try)`: no object handler, the stock code; else the inner try, then the
program's handlers in order. -/
def fixedTry (c : Conv) (hs : List H) (t : Thrown) : Res :=
  match objIdx hs with
  | none => stockTry hs t
  | some k => stockTry hs (inner (hs.take k) c t)

/-! ## The specification: an object handler is Clojure's catch of Throwable -/

def isObj : H → Bool
  | .object => true
  | _ => false

/-- The first handler that catches natively, or the first object handler for a value the
variant converts, binding the converted object. -/
def specTry (c : Conv) : List H → Thrown → Res
  | [], t => .escapes t
  | h :: hs, t =>
    if catches h t then .handled 0 t
    else if isObj h && convertible c t then .handled 0 (convert t)
    else (specTry c hs t).shift

/-! ## Theorems -/

theorem convertible_not_obj {c : Conv} {t : Thrown} (h : convertible c t = true) :
    ∀ o, t ≠ .obj o := by
  intro o ho; subst ho; simp [convertible] at h

theorem matches_object_iff (t : Thrown) : catches .object t = true ↔ ∃ o, t = .obj o := by
  cases t <;> simp [catches]

/-- Without an object handler, the spec is the stock code. -/
theorem spec_eq_stock_of_none (c : Conv) :
    ∀ hs t, objIdx hs = none → specTry c hs t = stockTry hs t := by
  intro hs t
  induction hs with
  | nil => intro _; rfl
  | cons h hs ih =>
    intro hn
    cases h with
    | object => simp [objIdx] at hn
    | errorRef =>
      simp only [objIdx, Option.map_eq_none_iff] at hn
      simp [specTry, stockTry, isObj, ih hn]
    | std x =>
      simp only [objIdx, Option.map_eq_none_iff] at hn
      simp [specTry, stockTry, isObj, ih hn]
    | int =>
      simp only [objIdx, Option.map_eq_none_iff] at hn
      simp [specTry, stockTry, isObj, ih hn]
    | default_ =>
      simp only [objIdx, Option.map_eq_none_iff] at hn
      simp [specTry, stockTry, isObj, ih hn]

/-- For a value the variant doesn't convert, the spec is the stock code. -/
theorem spec_eq_stock_of_not_conv (c : Conv) (t : Thrown) (hc : convertible c t = false) :
    ∀ hs, specTry c hs t = stockTry hs t := by
  intro hs
  induction hs with
  | nil => rfl
  | cons h hs ih => simp [specTry, stockTry, hc, ih]

/-- A converted value is an object. -/
theorem convert_obj {c : Conv} {t : Thrown} (h : convertible c t = true) :
    ∃ o, convert t = .obj o := by
  cases t <;> simp [convertible, convert] at h ⊢

/-- What leaves the inner try with no handler before the object one. -/
theorem inner_nil (c : Conv) (t : Thrown) :
    inner [] c t = if convertible c t then convert t else t := by
  cases t <;> simp [inner, convertible]

/-- A handler other than `object_ref` that doesn't match `t` doesn't match what the inner try
lets out either: that is `t`, or an object, which only `object_ref` and `catch(...)` match, and
`catch(...)` would have matched `t`. -/
theorem nomatch_inner (h : H) (hne : h ≠ .object) (pre : List H) (c : Conv) (t : Thrown)
    (hm : catches h t = false) : catches h (inner pre c t) = false := by
  unfold inner
  split
  · exact hm
  · split
    · exact hm
    · split
      · obtain ⟨o, ho⟩ : ∃ o, convert t = .obj o := convert_obj (by assumption)
        rw [ho]
        cases h with
        | object => exact absurd rfl hne
        | default_ => simp [catches] at hm
        | _ => rfl
      · exact hm

theorem inner_cons_nomatch (h : H) (pre : List H) (c : Conv) (t : Thrown)
    (hm : catches h t = false) : inner (h :: pre) c t = inner pre c t := by
  simp [inner, hm]

/-- ★ A34's (and V7a's) generated try is the specification, for every handler list and every
thrown value: the first handler matching natively wins as before, and the first object handler
also takes what the variant converts, bound as the converted object. -/
theorem fixed_eq_spec (c : Conv) : ∀ hs t, fixedTry c hs t = specTry c hs t := by
  intro hs t
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    unfold fixedTry at ih ⊢
    cases h with
    | object =>
      simp only [objIdx, List.take_zero]
      rw [inner_nil]
      by_cases hc : convertible c t = true
      · obtain ⟨o, ho⟩ := convert_obj hc
        have hnm : catches .object t = false := by
          cases t <;> simp_all [convertible, catches]
        rw [if_pos hc]
        have h1 : catches .object (convert t) = true := by rw [ho]; rfl
        simp only [stockTry, specTry, h1, hnm, hc, isObj, Bool.and_self, ite_true,
          Bool.false_eq_true, ite_false]
      · have hc' : convertible c t = false := by simpa using hc
        rw [if_neg (by simp [hc'])]
        simp [stockTry, specTry, hc', isObj, spec_eq_stock_of_not_conv c t hc']
    | errorRef => exact step H.errorRef (by decide) hs t ih
    | std x => exact step (H.std x) (by simp) hs t ih
    | int => exact step H.int (by decide) hs t ih
    | default_ => exact step H.default_ (by decide) hs t ih
where
  step (h : H) (hne : h ≠ .object) (hs : List H) (t : Thrown)
      (ih : (match objIdx hs with
            | none => stockTry hs t
            | some k => stockTry hs (inner (hs.take k) c t)) = specTry c hs t) :
      (match objIdx (h :: hs) with
        | none => stockTry (h :: hs) t
        | some k => stockTry (h :: hs) (inner ((h :: hs).take k) c t)) = specTry c (h :: hs) t := by
    have hidx : objIdx (h :: hs) = (objIdx hs).map (· + 1) := by
      cases h <;> first | exact absurd rfl hne | rfl
    have hbeq : isObj h = false := by
      cases h <;> first | exact absurd rfl hne | rfl
    rw [hidx]
    cases hk : objIdx hs with
    | none =>
      simp only [Option.map_none]
      rw [spec_eq_stock_of_none c (h :: hs) t (by rw [hidx, hk]; rfl)]
    | some k =>
      simp only [Option.map_some, List.take_succ_cons]
      rw [hk] at ih
      simp only at ih
      by_cases hm : catches h t = true
      · have : inner (h :: hs.take k) c t = t := by simp [inner, hm]
        simp [stockTry, specTry, this, hm]
      · have hm' : catches h t = false := by simpa using hm
        rw [inner_cons_nomatch h _ c t hm']
        simp [stockTry, specTry, nomatch_inner h hne _ c t hm', hm', hbeq, ih]

/-- ★ With no conversion the generated code is the stock code (A34 only adds the inner try when
an object handler exists, and it then changes nothing the stock code does with what it doesn't
convert). -/
theorem fixed_stock_eq (hs : List H) (t : Thrown) : fixedTry .stock hs t = stockTry hs t := by
  rw [fixed_eq_spec]; exact spec_eq_stock_of_not_conv _ t (by cases t <;> rfl) hs

/-- ★ No regression: for every value the variant doesn't convert (objects, C++ ints, foreign
values), A34's code does what the stock code does. -/
theorem fixed_eq_stock_of_not_conv (c : Conv) (hs : List H) (t : Thrown)
    (hc : convertible c t = false) : fixedTry c hs t = stockTry hs t := by
  rw [fixed_eq_spec]; exact spec_eq_stock_of_not_conv c t hc hs

/-- ★ No regression: when a handler before every object handler catches the value natively
(jank's suite: cpp/try/pass-catch-mixed.jank's `std.runtime_error` before `object_ref`), the
stock and the fixed code both give it that handler, unconverted. -/
theorem fixed_eq_stock_of_earlier (c : Conv) :
    ∀ (pre : List H) (h : H) (rest : List H) (t : Thrown),
      (∀ x ∈ pre, x ≠ .object) → h ≠ .object → catches h t = true →
      fixedTry c (pre ++ h :: rest) t = stockTry (pre ++ h :: rest) t := by
  intro pre h rest t hpre hne hm
  rw [fixed_eq_spec]
  induction pre with
  | nil => simp [specTry, stockTry, hm]
  | cons x xs ih =>
    have hx : x ≠ .object := hpre x (by simp)
    have hbeq : isObj x = false := by cases x <;> first | exact absurd rfl hx | rfl
    simp only [List.cons_append, specTry, stockTry, hbeq, Bool.false_and, ite_false,
      Bool.false_eq_true]
    rw [ih (fun y hy => hpre y (by simp [hy]))]

/-- ★ An object handler sees everything A34 converts: if no handler before the first object
handler catches `t`, and `t` is an error_ref or a std::exception, A34's code runs that object
handler with the converted object. -/
theorem a34_object_sees (pre rest : List H) (t : Thrown)
    (hpre : ∀ x ∈ pre, x ≠ .object ∧ catches x t = false)
    (hc : convertible .a34 t = true) :
    fixedTry .a34 (pre ++ .object :: rest) t = .handled pre.length (convert t) := by
  rw [fixed_eq_spec]
  induction pre with
  | nil =>
    have hnm : catches .object t = false := by
      cases t <;> simp_all [convertible, catches]
    simp [specTry, hnm, hc, isObj]
  | cons x xs ih =>
    obtain ⟨hx, hxm⟩ := hpre x (by simp)
    have hbeq : isObj x = false := by cases x <;> first | exact absurd rfl hx | rfl
    simp only [List.cons_append, specTry, hxm, hbeq, Bool.false_and, ite_false,
      Bool.false_eq_true, List.length_cons]
    rw [ih (fun y hy => hpre y (by simp [hy]))]
    rfl

/-- ★ What the object handler gets from a jank error has the error's message as ex-message and
nil ex-data (round 5's `jExMessage`/`jExData`), and the error attached. -/
theorem convErr_observed (e : JErr) :
    jExMessage (convErr e) = .ok (.str e.message) ∧ jExData (convErr e) = .ok .nil ∧
    (match convErr e with | .ex x => x.error = some e | _ => False) := by
  simp [convErr, jExMessage, jExData]

/-- ★ … and from a std::exception: its `what()` as ex-message, nil ex-data (Clojure: ex-data of an
exception that isn't an ExceptionInfo is nil). -/
theorem convStd_observed (w : String) :
    jExMessage (convStd w) = .ok (.str w) ∧ jExData (convStd w) = .ok .nil := by
  simp [convStd, jExMessage, jExData]

/-! ## The tests' observer -/

/-- `vb-outcome`'s try: `(catch object_ref e [:object e]) (catch std.exception _ [:native])
(catch jank.error_ref _ [:error])`. -/
def vbHandlers : List H := [.object, .std .exception, .errorRef]

def kindOf : Res → Kind
  | .handled 0 _ => .object
  | .handled 1 _ => .native
  | .handled 2 _ => .error
  | .handled _ _ => .uncaught
  | .escapes _ => .uncaught

/-- `thrown?` (clojure/test.jank 493–504) and `is`'s try-expr (525–532): one object handler. -/
def thrownHandlers : List H := [.object]

/-- ★ With A34, `vb-outcome` answers `:object` for every error_ref and every std::exception, as
Clojure's `(catch Throwable …)` does; stock answers `:error` and `:native`. -/
theorem vb_outcome_a34 (t : Thrown) (h : convertible .a34 t = true) :
    kindOf (fixedTry .a34 vbHandlers t) = .object := by
  cases t <;> simp_all [convertible, fixedTry, vbHandlers, objIdx, inner, stockTry, catches,
    convert, kindOf]

theorem vb_outcome_stock_err (e : JErr) :
    kindOf (stockTry vbHandlers (.err e)) = .error := by
  simp [stockTry, vbHandlers, catches, kindOf, Res.shift]

theorem vb_outcome_stock_std (c : StdCls) (w : String) :
    kindOf (stockTry vbHandlers (.std c w)) = .native := by
  simp [stockTry, vbHandlers, catches, kindOf, Res.shift, StdCls.sub]

/-- ★ `thrown?` passes, with A34, for every error_ref and std::exception (stock: it escapes). -/
theorem thrown_a34 (t : Thrown) (h : convertible .a34 t = true) :
    ∃ v, fixedTry .a34 thrownHandlers t = .handled 0 v := by
  cases t <;> simp_all [convertible, fixedTry, thrownHandlers, objIdx, inner, stockTry, catches,
    convert]

theorem thrown_stock (t : Thrown) (h : convertible .a34 t = true) :
    stockTry thrownHandlers t = .escapes t := by
  cases t <;> simp_all [convertible, thrownHandlers, stockTry, catches, Res.shift]

end Jank.R9.Err

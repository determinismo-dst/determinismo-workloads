import Jank.R5.Errors.Model

/-!
# Round 5, errors: theorems

★ marks a statement over every input of its domain (every thrown value, every count of derefs,
every module, every namespace state), not one example.
-/

namespace Jank.R5.Errors.Theorems

open Jank.R5.Errors

/-! ## Catching -/

/-- ★ jank's object handler never matches an error_ref, nor a `std::exception` (gen(catch)
1117: `catch(object_ref e)`). -/
theorem object_catch_misses_error_ref (e : JErr) : jMatches .object (.err e) = false := rfl

theorem object_catch_misses_std (w : String) : jMatches .object (.std w) = false := rfl

/-- ★ What `(catch :default e …)` binds is nil, whatever was thrown. -/
theorem default_catch_binds_nil (t : JThrown) : jDefaultBinding t = .nil := rfl

/-! ## read-string -/

/-- ★ For every text, core.jank's 1-arity `read-string` never throws an object: it returns, or
throws an error_ref (a read error), so an object catch never sees what it raises. -/
theorem jank_read_string_never_object (t : Text) : jOutcome (jReadString1 t) ≠ .object := by
  cases t <;> simp [jReadString1, jReadString, jOutcome, jMatches]

/-- ★ For every text, Clojure's `read-string` throws exactly when the text holds no complete
form, and a `(catch Throwable …)` sees it. -/
theorem clj_read_string_throws_iff (t : Text) :
    cOutcome (cReadString1 t) = .object ↔ (∀ v, t ≠ .form v) := by
  cases t <;> simp [cReadString1, cReadString, cOutcome]

/-- A text without a form: jank returns nil, Clojure throws "EOF while reading". -/
theorem read_empty_differs :
    jReadString1 .empty = .ok .nil ∧
    cReadString1 .empty = .thrown [{ cls := .runtimeException, message := some "EOF while reading" }] :=
  ⟨rfl, rfl⟩

/-! ## A failed require -/

/-- `jLoad` for any raised value (the general form of the module's failure). -/
def jLoadT (lib : String) (raised : Option JThrown) (s : NsState) : JRes × NsState :=
  let s1 := { s with nss := if s.nss.contains lib then s.nss else s.nss ++ [lib],
                     loaded := if s.loaded.contains lib then s.loaded else s.loaded ++ [lib] }
  match raised with
  | none => (.ok .nil, s1)
  | some t => (.thrown (jLoadModuleConvert t), s1)

def jLoadLibT (lib : String) (raised : Option JThrown) (s : NsState) : JRes × NsState :=
  let undefinedOnEntry := !s.nss.contains lib
  let (r, s') := jLoadT lib raised s
  match r with
  | .thrown t =>
    if jMatches .object t then
      (.thrown t, if undefinedOnEntry then { s' with nss := s'.nss.filter (· != lib) } else s')
    else (.thrown t, s')
  | r => (r, s')

/-- ★ `context::load_module` turns every object, `std::exception` and error_ref the module raised
into an error_ref. -/
theorem load_module_converts (t : JThrown) (h : t ≠ .foreign) :
    ∃ e, jLoadModuleConvert t = .err e := by
  cases t with
  | obj o => exact ⟨_, rfl⟩
  | std w => exact ⟨_, rfl⟩
  | err e => exact ⟨e, rfl⟩
  | foreign => exact absurd rfl h

theorem contains_after_add (l : List String) (x : String) :
    (if l.contains x then l else l ++ [x]).contains x = true := by
  by_cases h : x ∈ l <;> simp [h]

/-- ★ For every namespace state and every value a module raises after its `ns` form (but a
foreign native one), jank's `load-lib` leaves the module's namespace defined. -/
theorem jank_failed_require_keeps_ns (lib : String) (t : JThrown) (h : t ≠ .foreign) (s : NsState) :
    (jLoadLibT lib (some t) s).2.nss.contains lib = true := by
  obtain ⟨e, he⟩ := load_module_converts t h
  simp only [jLoadLibT, jLoadT, he, jMatches]
  exact contains_after_add s.nss lib

/-- The Clojure side for any raised Throwable (Compiler.load wraps it; load-lib's
`catch Exception` sees the wrapper). -/
def cLoadLibT (lib : String) (raised : Option CEx) (s : NsState) : CRes × NsState :=
  let undefinedOnEntry := !s.nss.contains lib
  let s1 := { s with nss := if s.nss.contains lib then s.nss else s.nss ++ [lib],
                     loaded := if s.loaded.contains lib then s.loaded else s.loaded ++ [lib] }
  match raised with
  | none => (.ok .nil, s1)
  | some e =>
    (.thrown (cCompiler "execution" :: e),
     if undefinedOnEntry then { s1 with nss := s1.nss.filter (· != lib) } else s1)

/-- ★ For every namespace state where the lib was undefined on entry and every Throwable its top
level raises, Clojure's `load-lib` removes the namespace. -/
theorem clj_failed_require_removes_ns (lib : String) (e : CEx) (s : NsState)
    (hundef : s.nss.contains lib = false) :
    (cLoadLibT lib (some e) s).2.nss.contains lib = false := by
  have h : lib ∉ s.nss := by simpa using hundef
  simp [cLoadLibT, h]

/-- The replica's module paths are instances of the general ones. -/
theorem jLoadLib_instance (m : Module) (s : NsState) :
    jLoadLib m s = jLoadLibT m.lib (m.raises.map jInner) s := by
  unfold jLoadLib jLoadLibT jLoad jLoadT
  cases m.raises <;> rfl

/-! ## delay -/

/-- ★ For every message, a delay whose body throws a `std::exception`: the first deref throws the
native exception, the second throws a string object holding its message. -/
theorem jank_delay_native_then_string (w : String) :
    (jDelayDerefs (.thrown (.std w)) 2 {}).1 = [.thrown (.std w), .thrown (.obj (.str w))] := by
  simp [jDelayDerefs, jDelayDeref]

/-- A delay whose body raises an error_ref keeps neither a value nor an error. -/
theorem jank_delay_err_step (e : JErr) (d : JDelay) (hv : d.val = none) (he : d.error = none) :
    jDelayDeref (.thrown (.err e)) d = (.thrown (.err e), { d with runs := d.runs + 1 }) := by
  simp [jDelayDeref, hv, he]

/-- ★ For every error_ref and every number of derefs n, the body runs n times. -/
theorem jank_delay_err_runs (e : JErr) (n : Nat) : ∀ d : JDelay, d.val = none → d.error = none →
    (jDelayDerefs (.thrown (.err e)) n d).2.runs = d.runs + n := by
  induction n with
  | zero => intro d _ _; simp [jDelayDerefs]
  | succ k ih =>
    intro d hv he
    simp only [jDelayDerefs, jank_delay_err_step e d hv he]
    rw [ih { d with runs := d.runs + 1 } hv he]
    simp; omega

/-- ★ Clojure: for every body outcome and every n ≥ 1 derefs, the body runs once and every deref
gives the body's first outcome (the same exception object, Delay.java 28–58). -/
theorem clj_delay_once_after (b : CRes) (n : Nat) :
    ∀ d : CDelay, d.done = true → d.result = some b →
      cDelayDerefs b n d = (List.replicate n b, d) := by
  induction n with
  | zero => intro d _ _; rfl
  | succ k ih =>
    intro d hd hr
    simp only [cDelayDerefs, cDelayDeref, hd, hr, ite_true, Option.getD_some]
    rw [ih d hd hr]
    rfl

theorem clj_delay_once (b : CRes) (n : Nat) :
    (cDelayDerefs b (n + 1) {}).2.runs = 1 ∧ (cDelayDerefs b (n + 1) {}).1 = List.replicate (n + 1) b := by
  have h := clj_delay_once_after b n { done := true, result := some b, runs := 1 } rfl rfl
  simp only [cDelayDerefs, cDelayDeref]
  simp only [Bool.false_eq_true, ite_false]
  rw [h]
  exact ⟨rfl, rfl⟩

/-! ## future -/

/-- ★ For every thrown value that is neither an object nor a `std::exception` (an error_ref, a
foreign native value), a jank future ends the process. -/
theorem jank_future_terminates (t : JThrown) (h1 : ∀ o, t ≠ .obj o) (h2 : ∀ w, t ≠ .std w) :
    ∃ why, jFuture (.thrown t) = .terminated why := by
  cases t with
  | obj o => exact absurd rfl (h1 o)
  | std w => exact absurd rfl (h2 w)
  | err e => exact ⟨_, rfl⟩
  | foreign => exact ⟨_, rfl⟩

/-- ★ For every message, a jank future whose body throws a `std::exception` rethrows a string. -/
theorem jank_future_native_string (w : String) : jFuture (.thrown (.std w)) = .thrown (.obj (.str w)) := rfl

/-- ★ Clojure: for every Throwable, deref throws an ExecutionException whose cause chain is the
body's. -/
theorem clj_future_wraps (e : CEx) :
    ∃ l, cFuture (.thrown e) = .thrown (l :: e) ∧ l.cls = .executionException := ⟨_, rfl, rfl⟩

/-! ## A top-level def whose value raises -/

/-- ★ For every metadata, dynamic flag and value outcome, jank's var carries the def's metadata. -/
theorem jank_def_meta_always (ks : List String) (dyn : Bool) (v : Option Inner) :
    (jTopDef ks dyn v).2.metaKeys = ks ++ (if dyn then ["dynamic"] else []) := by
  cases v <;> rfl

/-- ★ Clojure's var carries none of it when the value raised. -/
theorem clj_def_meta_none_on_raise (ks : List String) (dyn : Bool) (i : Inner) :
    (cTopDef ks dyn (some i)).2.metaKeys = [] := by
  cases i <;> rfl

/-! ## ex-info -/

/-- A nil message: jank throws a native error, Clojure makes an exception with a nil message. -/
theorem ex_info_nil_message :
    jOutcome (jExInfo .nil (.keys [])) = .native ∧
    cExInfo .nil (.keys []) = .ok (.ex [{ cls := .exceptionInfo, message := none, data := some (.keys []) }]) :=
  ⟨rfl, rfl⟩

/-- ★ For every message string, jank's and Clojure's `ex-info` with nil data differ in `ex-data`:
nil against `{}`. -/
theorem ex_data_of_nil_data (m : String) :
    (match jExInfo (.str m) .nil with | .ok v => jExData v | r => r) = .ok .nil ∧
    (match cExInfo (.str m) .nil with | .ok v => cExData v | _ => none) = some (.keys []) := by
  constructor <;> rfl

/-! ## The nREPL's *e -/

/-- ★ For every error_ref, `*e` has an empty message, nil data and no cause chain, so neither
`ex-data` nor `ex-cause` reaches anything (U44's constructor). -/
theorem star_e_of_error_ref (e : JErr) :
    (jStarE (.err e)).message = "" ∧ (jStarE (.err e)).data = .nil ∧ (jStarE (.err e)).causes = [] :=
  ⟨rfl, rfl, rfl⟩

end Jank.R5.Errors.Theorems

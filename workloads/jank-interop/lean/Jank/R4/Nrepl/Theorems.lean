import Jank.R4.Nrepl.Hand

/-!
# Round 4, nREPL: theorems

- `try_agree_unless_terminate` (for every outcome of a body, a handler and a finally): jank's `try`
  (cpp_processor.cpp gen(try)/gen(catch)/gen(finally), as `JEval.evalE`'s `.try_` arm runs it)
  and Clojure's (`TryExpr`, as `CEval`'s `spec-try` runs it) give the same outcome, except when
  the handler throws and the finally throws: jank calls `std::terminate` (REPORT D24).
- `binding_frames_restored` (for every thread state and bindings): `push-thread-bindings` then
  `pop-thread-bindings` leave the thread's binding frames as they were (context.cpp 706–760).
- `completions_ns_is_searched` (for every namespace, prefix and process): every var candidate's
  `:ns` is the namespace searched, never the var's own (E2).
-/

namespace Jank.R4.Nrepl
open Jank.R3.Nrepl
open Jank.Analyzer

/-! ## `try` -/

/-- What a piece of code does: a value, or an exception (a thrown object `t`, or another kind
`o`, e.g. a `std::exception` that `catch(object_ref)` does not catch). -/
inductive Out where
  | val (v : Nat)
  | thrown (e : Nat)
  | other (e : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What the process does: an outcome, or the process ends (`std::terminate`). -/
inductive Res where
  | out (o : Out)
  | terminate
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A `try` with one `catch(object_ref e)` handler (or none) and a finally (or none). `handler e`
is what the handler does with the thrown object; `fin` what the finally does. -/
structure TryCase where
  body : Out
  handler : Option (Nat → Out)
  fin : Option Out

/-- jank (the `.try_` arm of `JEval.evalE`): `try { body } catch(object_ref e) { handler }
catch(...) { guard.release(); fin(); throw; } guard.release(); fin();` with the guard armed while a
handler's exception unwinds. -/
def jankTry (c : TryCase) : Res :=
  let runFin (after : Out) : Res := match c.fin with
    | none => .out after
    | some (.val _) => .out after
    | some f => .out f
  match c.body with
  | .val v => runFin (.val v)
  | .other e => runFin (.other e)
  | .thrown e =>
    match c.handler with
    | none => runFin (.thrown e)
    | some h =>
      match h e with
      | .val v => runFin (.val v)
      | x =>
        -- the handler's exception unwinds through the armed scope_exit
        match c.fin with
        | none => .out x
        | some (.val _) => .out x
        | some _ => .terminate

/-- Clojure (`CEval`'s `spec-try`, Compiler `TryExpr`): finally always runs; an exception from it
replaces the one in flight. -/
def cljTry (c : TryCase) : Res :=
  let runFin (after : Out) : Res := match c.fin with
    | none => .out after
    | some (.val _) => .out after
    | some f => .out f
  match c.body with
  | .val v => runFin (.val v)
  | .other e => runFin (.other e)
  | .thrown e =>
    match c.handler with
    | none => runFin (.thrown e)
    | some h => runFin (h e)

/-- The only disagreement is D24: a handler that throws, then a finally that throws. -/
theorem try_agree_unless_terminate (c : TryCase) :
    jankTry c = cljTry c ∨
      (∃ e h f, c.body = .thrown e ∧ c.handler = some h ∧ (∀ v, h e ≠ .val v) ∧ c.fin = some f ∧
        (∀ v, f ≠ .val v) ∧ jankTry c = .terminate) := by
  rcases c with ⟨body, handler, fin⟩
  cases body with
  | val v => left; cases fin <;> rfl
  | other e => left; cases fin <;> rfl
  | thrown e =>
    cases handler with
    | none => left; cases fin <;> rfl
    | some h =>
      cases hh : h e with
      | val v =>
        left
        cases fin with
        | none => simp [jankTry, cljTry, hh]
        | some f => cases f <;> simp [jankTry, cljTry, hh]
      | thrown x =>
        cases fin with
        | none => left; simp [jankTry, cljTry, hh]
        | some f =>
          cases f with
          | val w => left; simp [jankTry, cljTry, hh]
          | thrown y => right; exact ⟨e, h, .thrown y, rfl, rfl, by simp [hh], rfl, by simp, by simp [jankTry, hh]⟩
          | other y => right; exact ⟨e, h, .other y, rfl, rfl, by simp [hh], rfl, by simp, by simp [jankTry, hh]⟩
      | other x =>
        cases fin with
        | none => left; simp [jankTry, cljTry, hh]
        | some f =>
          cases f with
          | val w => left; simp [jankTry, cljTry, hh]
          | thrown y => right; exact ⟨e, h, .thrown y, rfl, rfl, by simp [hh], rfl, by simp, by simp [jankTry, hh]⟩
          | other y => right; exact ⟨e, h, .other y, rfl, rfl, by simp [hh], rfl, by simp, by simp [jankTry, hh]⟩

/-! ## `binding` -/

/-- `push_thread_bindings` then `pop_thread_bindings`: the frames are the ones before, for every
thread state and every bindings (the boxes array only grew). -/
theorem binding_frames_restored (tb : TB) (bs : List (VarRef × Obj)) :
    (tb.push bs).pop.frames = tb.frames := rfl

/-! ## completions -/

/-- Every var candidate a `completions` reply lists carries `:ns` = the namespace searched (E2),
for every process, request, namespace and prefix. -/
theorem completions_ns_is_searched (n : NsCell) (pfx : String) (w : JW) :
    ∀ c ∈ n.mappings.filterMap (fun (k, r) =>
        if k.startsWith pfx then
          let m := (w.slots.get r).md
          let ty := if (metaGet m "macro").truthy then "macro" else if (metaGet m "arglists").truthy then "function" else "var"
          some (Jank.NreplServer.kmap [("ns", Jank.NreplServer.JVal.s n.name), ("type", Jank.NreplServer.JVal.k ty),
            ("candidate", Jank.NreplServer.JVal.s k)])
        else none),
      ∃ ty k, c = Jank.NreplServer.kmap [("ns", Jank.NreplServer.JVal.s n.name), ("type", Jank.NreplServer.JVal.k ty),
            ("candidate", Jank.NreplServer.JVal.s k)] := by
  intro c hc
  rw [List.mem_filterMap] at hc
  obtain ⟨⟨k, r⟩, _, hk⟩ := hc
  by_cases hp : k.startsWith pfx
  · simp only [hp, if_true, Option.some.injEq] at hk
    exact ⟨_, k, hk.symm⟩
  · simp [hp] at hk

end Jank.R4.Nrepl

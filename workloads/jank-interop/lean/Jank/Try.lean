import Determinismo

/-!
# try / catch / finally: the C++ jank generates, beside the JVM's semantics

Checked against jank 7135b7708 (unchanged from f3d82d654; paths under
`upstream-main/compiler+runtime/src/cpp/jank/`): codegen/cpp_processor.cpp 1054-1103
`gen(ir::inst::try_ref)`, 1105-1127 `gen(ir::inst::catch_ref)`, 1129-1139 `gen(ir::inst::finally_ref)`;
ir/processor.cpp 727-796 `gen(expr::try_ref)` (one line lower than in f3d82d654);
util/scope_exit.cpp 19-29 `~scope_exit`.

codegen/cpp_processor.cpp `gen(ir::inst::try_ref)`, `gen(ir::inst::catch_ref)`,
`gen(ir::inst::finally_ref)` emit, for `(try body (catch T e handler) (finally fin))`:

    {
      auto const G_fn{ [&](){ fin } };
      jank::util::scope_exit G{ G_fn, true };
      try { body }
      catch(T e) { handler }
      catch(...) { G.release(); G_fn(); throw; }
      G.release(); G_fn();
    }

util/scope_exit.cpp: `scope_exit::~scope_exit()` calls `func()` when still `active` and
`should_propagate_exceptions` is true. The destructor is not declared `noexcept(false)`, so it is
`noexcept` ([except.spec]): an exception leaving it calls `std::terminate`.

When the handler throws, the exception leaves the `try` statement: the sibling `catch(...)` does
not see it ([except.handle]), `G` is still active, and its destructor runs `fin` during the
unwinding. If `fin` throws too, the process terminates. On the JVM (Clojure's `try`), the
finally's exception replaces the handler's and propagates to the enclosing `catch`.
-/

namespace Jank.Try

open Determinismo

/-- An exception, by name. -/
abbrev Exn := String

inductive Outcome where
  | value (v : String)
  | throws (e : Exn)
  /-- `std::terminate`: the process ends (no enclosing catch runs). -/
  | terminate
  deriving Repr, BEq, Inhabited

/-- One piece of code: returns a value or throws. -/
inductive Code where
  | ok (v : String)
  | throw (e : Exn)
  deriving Repr, BEq, Inhabited

def Code.run : Code → Outcome
  | .ok v => .value v
  | .throw e => .throws e

/-- A `try` form: its body, one `catch` (the type it catches and its handler), an optional
`finally`. -/
structure Form where
  body : Code
  catches : Exn
  handler : Code
  fin : Option Code
  deriving Repr, Inhabited

def Form.program (f : Form) : String :=
  let code : Code → String := fun c => match c with
    | .ok v => v
    | .throw e => s!"(throw (ex-info \"{e}\" \{}))"
  let finPart := match f.fin with | some c => s!" (finally {code c})" | none => ""
  s!"(try {code f.body} (catch {f.catches} e {code f.handler}){finPart})"

/-- The generated C++ (above), executed. -/
def jank (f : Form) : Outcome :=
  let fin? := f.fin
  -- `G.release(); G_fn();` on the normal path and in `catch(...)`: fin runs as ordinary code.
  let finNormally (after : Outcome) : Outcome :=
    match fin? with
    | none => after
    | some c => match c.run with
      | .throws e => .throws e
      | _ => after
  -- The guard's destructor during unwinding: fin runs inside a noexcept destructor.
  let finInDestructor (propagating : Exn) : Outcome :=
    match fin? with
    | none => .throws propagating
    | some c => match c.run with
      | .throws _ => .terminate
      | _ => .throws propagating
  match f.body.run with
  | .value v => finNormally (.value v)
  | .terminate => .terminate
  | .throws e =>
    if e == f.catches then
      -- catch(T e) { handler }: the guard still active.
      match f.handler.run with
      | .value h => finNormally (.value h)          -- falls through to `G.release(); G_fn();`
      | .throws e2 => finInDestructor e2             -- leaves the block: ~scope_exit runs fin
      | .terminate => .terminate
    else
      -- catch(...) { G.release(); G_fn(); throw; } (only emitted with a finally)
      match fin? with
      | none => .throws e
      | some _ => finNormally (.throws e)

/-- Clojure (the JVM's try/catch/finally): finally runs on every exit; its exception, if any,
replaces the one in flight. -/
def clojure (f : Form) : Outcome :=
  let fin (after : Outcome) : Outcome :=
    match f.fin with
    | none => after
    | some c => match c.run with
      | .throws e => .throws e
      | _ => after
  match f.body.run with
  | .value v => fin (.value v)
  | .terminate => .terminate
  | .throws e =>
    if e == f.catches then fin f.handler.run else fin (.throws e)

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def drawCode (name : String) (thrown : Exn) : EStateM Stop World Code := do
  if (← decide (σ := World) name 2) == 0 then pure (.ok ":ok") else pure (.throw thrown)

def body : EStateM Stop World Unit := do
  let b ← drawCode "try.body_throws" "a"
  let catches := if (← decide (σ := World) "try.catch_matches" 2) == 0 then "a" else "other"
  let h ← drawCode "try.handler_throws" "b"
  let fin ← match ← decide (σ := World) "try.finally" 3 with
    | 0 => pure none
    | 1 => pure (some (.ok ":fin"))
    | _ => pure (some (.throw "c"))
  let f : Form := { body := b, catches, handler := h, fin }
  let j := jank f
  let c := clojure f
  if j != c then
    violate (σ := World) "try/catch/finally as on the JVM"
      s!"{f.program}: Clojure {reprStr c}, jank {reprStr j}"

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- The only disagreement: the handler throws and the finally throws. -/
theorem only_handler_and_finally_throwing (f : Form) :
    jank f ≠ clojure f →
    f.body = .throw f.catches ∧ (∃ e, f.handler = .throw e) ∧ (∃ e, f.fin = some (.throw e)) := by
  intro h
  rcases f with ⟨b, catches, handler, fin⟩
  cases b <;> cases handler <;> (try cases fin) <;>
    (try rename_i c; cases c) <;> simp_all [jank, clojure, Code.run] <;>
    (try split at h) <;> simp_all

end Jank.Try

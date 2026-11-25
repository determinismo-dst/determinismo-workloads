import Jank.R4.Core.Value

/-!
# Round 4: `ex-info`, `ex-message`, `ex-data`, `ex-cause`, `Throwable->map` and printing

**jank** at 7135b7708:
- core.jank 113–150: `ex-message`, `ex-data`, `ex-cause`, `ex-map` call core.cpp `ex_message`
  1338, `ex_data` 1343, `ex_cause` 1348, `ex_map` 1353. Each is
  `try_object<obj::exception_info>(o)->…`: anything but an `exception_info` throws (a native
  `std::runtime_error`). jank's own docstrings say "Otherwise returns nil".
- `ex_info` 1327: the cause must be an `exception_info` (`try_object`), data is unchecked.
- `Throwable->map` is `ex-map` (core.jank 150) → exception_info.cpp `to_map` 116–148:
  `:cause` is the exception's *own* message, `:data` its own data, `:via` one
  `cause_to_via` per link (131–135), and `cause_to_via` (38–54) has `:message`, `:data`, `:at`
  but no `:type`.
- `pr-str`/`str` (exception_info.cpp `to_code_string` 70–101): `:cause` and `:data` are the
  exception's own; the `:via` loop (80–83) iterates `cause_it` but prints `cause_to_via(cause)`,
  the *first* cause, at every step.

**Clojure** 1.12: `ex-message`/`ex-cause` return nil unless a Throwable, `ex-data` nil unless an
IExceptionInfo (core.clj 4841–4863). `Throwable->map` (core_print.clj 473–507): `:cause` is the
root cause's message, `:data` the root's ex-data, `:via` one entry per link with `:type`;
`print-throwable` (509) prints `:via` from it.
-/

namespace Jank.R4.Core.Exceptions

open Jank.R4.Core

/-- An exception chain, outermost first: each link's message and data. -/
abbrev Chain := List (String × V)

/-- What a `catch` gets: an ex-info chain or any other thrown object (jank throws strings,
keywords, … as objects; a Clojure program only throws Throwables, so on the Clojure side the
non-exception values are passed to `ex-message` directly, not caught). -/
inductive Thrown where
  | ex (c : Chain)
  | obj (v : V)
  deriving Inhabited

/-- A result or a thrown error (by its message). -/
inductive R (α : Type) where
  | ok (a : α)
  | err (msg : String)
  deriving Inhabited

/-- core.cpp `ex_message` 1338: `try_object<exception_info>(o)->message`. -/
def jankExMessage : Thrown → R (Option String)
  | .ex ((m, _) :: _) => .ok (some m)
  | .ex [] => .ok none
  | .obj _ => .err "An object of type `exception_info` was expected here"

def jankExData : Thrown → R V
  | .ex ((_, d) :: _) => .ok d
  | .ex [] => .ok .nil
  | .obj _ => .err "An object of type `exception_info` was expected here"

/-- Clojure's `ex-message`: `(when (instance? Throwable ex) (.getMessage ^Throwable ex))`. -/
def cljExMessage : Thrown → R (Option String)
  | .ex ((m, _) :: _) => .ok (some m)
  | .ex [] => .ok none
  | .obj _ => .ok none

def cljExData : Thrown → R V
  | .ex ((_, d) :: _) => .ok d
  | .ex [] => .ok .nil
  | .obj _ => .ok .nil

/-- The fields of `Throwable->map` that this replica compares. -/
structure TMap where
  cause : Option String
  data : V
  viaMessages : List String
  viaHasType : Bool
  deriving Inhabited

/-- exception_info.cpp `to_map` 116–148. -/
def jankThrowableMap (c : Chain) : TMap :=
  { cause := c.head?.map (·.1)
    data := (c.head?.map (·.2)).getD .nil
    viaMessages := c.map (·.1)
    viaHasType := false }

/-- core_print.clj `Throwable->map` 473–507: root = the last link. -/
def cljThrowableMap (c : Chain) : TMap :=
  { cause := c.getLast?.map (·.1)
    data := (c.getLast?.map (·.2)).getD .nil
    viaMessages := c.map (·.1)
    viaHasType := true }

/-- exception_info.cpp `to_code_string` 70–101: the messages its `:via` prints. The loop runs
`cause_it` over the causes but prints `cause_to_via(cause)`, the first cause, each time. -/
def jankPrintedVia (c : Chain) : List String :=
  match c with
  | [] => []
  | (m, _) :: rest =>
    let first := rest.head?.map (·.1)
    m :: (rest.map fun _ => first.getD "")

/-- exception_info.cpp `to_code_string`: the `:cause` it prints (the exception's own). -/
def jankPrintedCause (c : Chain) : Option String := c.head?.map (·.1)

/-- core_print.clj `print-throwable` 509: `:cause` of `Throwable->map`, `:via` each link. -/
def cljPrintedVia (c : Chain) : List String := c.map (·.1)
def cljPrintedCause (c : Chain) : Option String := c.getLast?.map (·.1)

/-- For every chain of three or more links, jank's printed `:via` differs from the chain. -/
theorem jank_printed_via_wrong (m0 m1 m2 : String) (d0 d1 d2 : V) (rest : Chain)
    (h : m2 ≠ m1) :
    jankPrintedVia ((m0, d0) :: (m1, d1) :: (m2, d2) :: rest) ≠
      cljPrintedVia ((m0, d0) :: (m1, d1) :: (m2, d2) :: rest) := by
  simp only [jankPrintedVia, cljPrintedVia, List.map_cons, List.head?_cons, Option.map_some,
    Option.getD_some]
  intro heq
  have := congrArg (fun l => l[2]?) heq
  simp at this
  exact h this.symm

/-- For every chain of two or more links with distinct outer and root messages,
`Throwable->map`'s `:cause` differs. -/
theorem jank_cause_not_root (c : Chain) (m : String) (d : V) (hne : c ≠ [])
    (h : ∀ x ∈ c.getLast?, x.1 ≠ m) :
    (jankThrowableMap ((m, d) :: c)).cause ≠ (cljThrowableMap ((m, d) :: c)).cause := by
  simp only [jankThrowableMap, cljThrowableMap, List.head?_cons, Option.map_some]
  cases hl : c.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
  | some x =>
    have hx := h x (by simp [hl])
    have : ((m, d) :: c).getLast? = some x := by
      rw [List.getLast?_cons, hl]; rfl
    simp [this]
    exact fun e => hx e.symm

end Jank.R4.Core.Exceptions

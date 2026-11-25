/-
  Theorems about the pipeline replica (Pipeline.lean).  No `sorry`, no axioms
  beyond propext, Classical.choice and Quot.sound.
-/
import FlecsLean.Pipeline

namespace Flecs.Pipe

/-- An empty write state reports no staged write for any id. -/
theorem getWS_empty (id : Id) : getWS {} id = false := by
  simp [getWS]

/-- A term checked against an empty write state never asks for a merge. -/
theorem checkTerm_empty (t : Term) (a : Bool) : (checkTerm t a {}).1 = false := by
  obtain ⟨id, src, oper, io⟩ := t
  cases src <;> cases oper <;> cases io <;> cases a <;>
    simp (config := { decide := true }) [checkTerm, getWS_empty, isThis, hasSelf]

/-- So a system with one term never trips the assert of pipeline.c 354
    (the re-check after a merge starts from an empty write state). -/
theorem single_term_no_assert (t : Term) : (checkTerms [t] true {}).1 = false := by
  unfold checkTerms
  by_cases h : isThis t.src <;> simp [h, checkTerm_empty]

/-- F15: two terms, the first marking Position written ([out] C0()), the
    second reading it ([in] C0()), ask for a merge even from an empty write
    state, which is the assert's condition. -/
theorem write_then_read_asks_merge :
    (checkTerms [{ id := C0, src := .zero, inout := .out }, { id := C0, src := .zero, inout := .in_ }]
      true {}).1 = true := by decide

/-- F16: a write recorded for (R, *) is not seen by a read of (*, T1), though
    both match (R, T1); likewise a write of (R, T1) and a read of (R, _). -/
theorem wildcard_write_missed :
    getWS (setWS {} (mkPair R EcsWildcard)) (mkPair EcsWildcard T1) = false ∧
    semMatch (mkPair R T1) (mkPair R EcsWildcard) = true ∧
    semMatch (mkPair R T1) (mkPair EcsWildcard T1) = true := by decide

theorem any_read_missed :
    getWS (setWS {} (mkPair R T1)) (mkPair R EcsAny) = false ∧
    semMatch (mkPair R T1) (mkPair R EcsAny) = true := by decide

end Flecs.Pipe

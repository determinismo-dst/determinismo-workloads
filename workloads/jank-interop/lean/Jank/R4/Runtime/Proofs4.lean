import Jank.R4.Runtime.Gc4
import Jank.R4.Runtime.Bindings4

/-!
# Round 4, Runtime: for-every-input proofs of components that came back quiet

## `swap-vals!` and `reset-vals!` (obj/atom.cpp 65-78, 146-230)

```cpp
persistent_vector_ref atom::swap_vals(object_ref const fn)
{ while(true) { auto v(val.load()); auto const next(fn.call(v)); validate(next);
    if(val.compare_exchange_weak(v, next.raw()))
    { notify_watches(…); return make_box<persistent_vector>(std::in_place, v, next); } } }
persistent_vector_ref atom::reset_vals(object_ref const o)
{ validate(o); while(true) { auto v(val.load());
    if(val.compare_exchange_weak(v, o.raw())) { notify_watches(…); return […](v, o); } } }
```

Abstracted: threads interleave `load` and `cas` events on one word; a thread's `cas` succeeds when
the word still holds what it loaded (identity, as `compare_exchange_weak` compares raw words), and
may also fail spuriously (`compare_exchange_weak` on LL/SC machines, round 1's D17); a failure
retries from the load. The function a thread applies is arbitrary (`fn` of its value, or the
constant of `reset-vals!`). Proved for every interleaving, every number of threads, every
function: the `[old new]` pairs the successful operations return, in the order of their CAS, form
a sequential history (each `old` is the previous `new`, the first the initial value) and the atom
ends at the last `new`. That is linearizability to Clojure's sequential `swap-vals!` (Atom.java
`swapVals`: the same CAS loop), the linearization point being the successful CAS.

## The printed form of an unbound root, and thread bindings (statements over every input)
-/

namespace Jank.R4.Runtime.Proofs4

/-! ### swap-vals! / reset-vals! -/

inductive Ev where
  | load (t : Nat)
  | cas (t : Nat)
  /-- a spurious failure of compare_exchange_weak -/
  | casFail (t : Nat)
  deriving Repr

structure TS where
  shared : Nat
  loaded : Nat → Option Nat
  /-- successful operations in CAS order: (thread, old, new) -/
  out : List (Nat × Nat × Nat)

def upd (g : Nat → Option Nat) (t : Nat) (x : Option Nat) : Nat → Option Nat :=
  fun u => if u = t then x else g u

/-- One event. `f t v` is what thread t's operation computes from v. -/
def stepEv (f : Nat → Nat → Nat) (s : TS) : Ev → TS
  | .load t => { s with loaded := upd s.loaded t (some s.shared) }
  | .cas t =>
    match s.loaded t with
    | some v =>
      if v = s.shared then
        { shared := f t v, loaded := upd s.loaded t none, out := s.out ++ [(t, v, f t v)] }
      else { s with loaded := upd s.loaded t none }
    | none => s
  | .casFail t => { s with loaded := upd s.loaded t none }

def runEvs (f : Nat → Nat → Nat) (s : TS) : List Ev → TS
  | [] => s
  | e :: es => runEvs f (stepEv f s e) es

/-- The pairs form a sequential history from `v`: each old is the previous new. -/
def Chain (f : Nat → Nat → Nat) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | v, (t, o, n) :: rest => o = v ∧ n = f t o ∧ Chain f n rest

def lastNew (v : Nat) : List (Nat × Nat × Nat) → Nat
  | [] => v
  | (_, _, n) :: rest => lastNew n rest

theorem chain_append (f : Nat → Nat → Nat) (v : Nat) (xs : List (Nat × Nat × Nat)) (t o : Nat)
    (h : Chain f v xs) (ho : o = lastNew v xs) :
    Chain f v (xs ++ [(t, o, f t o)]) ∧ lastNew v (xs ++ [(t, o, f t o)]) = f t o := by
  induction xs generalizing v with
  | nil => simp [Chain, lastNew, ho]
  | cons x rest ih =>
    obtain ⟨t', o', n'⟩ := x
    simp only [Chain] at h
    obtain ⟨h1, h2, h3⟩ := h
    have := ih n' h3 (by simpa [lastNew] using ho)
    simp only [List.cons_append, Chain, lastNew]
    exact ⟨⟨h1, h2, this.1⟩, this.2⟩

/-- For every interleaving: the successful operations' `[old new]` pairs chain from the initial
value, and the atom holds the last new value. -/
theorem swapVals_linearizable (f : Nat → Nat → Nat) (v0 : Nat) (evs : List Ev) :
    let s := runEvs f { shared := v0, loaded := fun _ => none, out := [] } evs
    Chain f v0 s.out ∧ s.shared = lastNew v0 s.out := by
  suffices h : ∀ (s : TS), Chain f v0 s.out → s.shared = lastNew v0 s.out →
      Chain f v0 (runEvs f s evs).out ∧ (runEvs f s evs).shared = lastNew v0 (runEvs f s evs).out by
    exact h _ trivial rfl
  induction evs with
  | nil => intro s h1 h2; exact ⟨h1, h2⟩
  | cons e es ih =>
    intro s h1 h2
    apply ih
    · cases e with
      | load t => exact h1
      | casFail t => exact h1
      | cas t =>
        simp only [stepEv]
        cases hl : s.loaded t with
        | none => exact h1
        | some v =>
          simp only
          split
          · rename_i hv
            exact (chain_append f v0 s.out t v h1 (hv.trans h2)).1
          · exact h1
    · cases e with
      | load t => exact h2
      | casFail t => exact h2
      | cas t =>
        simp only [stepEv]
        cases hl : s.loaded t with
        | none => exact h2
        | some v =>
          simp only
          split
          · rename_i hv
            exact (chain_append f v0 s.out t v h1 (hv.trans h2)).2.symm
          · exact h2

/-! ### The unbound root's printed form -/

/-- jank's text and Clojure's differ for every address and every var (they differ at the first
character: `u` against `U`). -/
theorem unbound_str_differs (addr v : String) :
    Gc4.jankUnboundStr addr v ≠ Gc4.cljUnboundStr v := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [Gc4.jankUnboundStr, Gc4.cljUnboundStr] at this

/-! ### Binding conveyance (core.cpp 1093, 1126 / binding-conveyor-fn): a future's thread sees
its creator's bindings, in jank and Clojure alike, for every creator binding. -/

theorem future_conveys (cr : Option Nat) :
    (Bindings4.stepJ (Bindings4.startJ true cr) .deref).1
      = (Bindings4.stepC (Bindings4.startC true cr) .deref).1 := by
  simp [Bindings4.stepJ, Bindings4.stepC, Bindings4.startJ, Bindings4.startC, Bindings4.bound]

end Jank.R4.Runtime.Proofs4

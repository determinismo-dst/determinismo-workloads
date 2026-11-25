import Jank.R3.Proofs.AtomStep

/-!
# Atoms: every interleaving's history is linearizable (round 3, proofs)

The theorems over the replica `Jank.Atom` (atom.cpp `swap`, `compare_and_set`, `reset`,
`deref`, `add_watch`, `notify_watches` as `Threads` steps), for every scenario of the fragment
`AtomLin.COp` (any number of threads and operations), every source of decisions and every
`maxSteps`:

- `linearizable_x86`: on x86-64 (strong CAS: `llsc = false`) and in the Clojure mode, the history is
  linearizable against the replica's register `applyOp`;
- `linearizable_llsc_weak`: on LL/SC, against the register whose compare-and-set may answer false
  without effect (and no stronger: `llsc_cas_not_linearizable`);
- `linearizable_llsc_no_cas`: on LL/SC without `compare-and-set!`, against the strong register:
  spurious failures only make `swap!` retry.
-/

namespace Jank.R3.Proofs.AtomLin

open Determinismo Jank.Atom Jank.R3.Proofs Jank.R3.Proofs.Lin

/-! ## The start -/

theorem nodup_flatMap_inj {α β : Type} (f : α → List β) (d : α) :
    ∀ (ts : List α), (ts.flatMap f).Nodup → ∀ i j x, x ∈ f (ts.getD i d) → x ∈ f (ts.getD j d) →
      (∀ y, y ∉ f d) → i = j
  | [], _, i, j, x, hi, _, hd => by simp at hi; exact absurd hi (hd x)
  | a :: as, hN, i, j, x, hi, hj, hd => by
    rw [List.flatMap_cons, List.nodup_append] at hN
    obtain ⟨h1, h2, h3⟩ := hN
    have mem_of : ∀ k, k ≠ 0 → x ∈ f ((a :: as).getD k d) → x ∈ as.flatMap f := by
      intro k hk hx
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [List.getD_cons_succ] at hx
      rw [List.getD_eq_getElem?_getD] at hx
      cases hg : as[k']? with
      | none => rw [hg] at hx; simp at hx; exact absurd hx (hd x)
      | some b => rw [hg] at hx; simp at hx; exact List.mem_flatMap.mpr ⟨b, List.mem_of_getElem? hg, hx⟩
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getD_cons_zero] at hi
        exact absurd rfl (h3 x hi x (mem_of (j + 1) (by omega) hj))
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getD_cons_zero] at hj
        exact absurd rfl (h3 x hj x (mem_of (i + 1) (by omega) hi))
      | succ j =>
        simp only [List.getD_cons_succ] at hi hj
        rw [nodup_flatMap_inj f d as h2 i j x hi hj hd]

theorem flatMap_getD_sub {α β : Type} (f : α → List β) (ts : List α) (i : Nat) (d : α) (hd : f d = []) :
    (f (ts.getD i d)).Sublist (ts.flatMap f) := by
  rw [List.getD_eq_getElem?_getD]
  cases hg : ts[i]? with
  | none => simp [hd]
  | some b =>
    simp only [Option.getD_some]
    obtain ⟨l1, l2, hl⟩ := List.append_of_mem (List.mem_of_getElem? hg)
    rw [hl, List.flatMap_append, List.flatMap_cons]
    exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)

/-- The process `runProcess` starts from (`Jank.Atom.start`, with the source's decisions). -/
def startP (name : String) (ts : List (List COp)) (v0 : Nat) (llsc clj : Bool) (source : Source)
    (limit : Nat) : Process Mem Loc :=
  { start (ofThreads name ts v0) llsc clj with decisions := { source, limit } }

theorem start_getD (name : String) (ts : List (List COp)) (v0 : Nat) (llsc clj : Bool) (source : Source)
    (limit : Nat) (t : Nat) :
    (startP name ts v0 llsc clj source limit).threads.getD t none =
      if t < ts.length then some { instrs := restInstrs (ts.getD t []) } else none := by
  simp only [startP, start, ofThreads, Array.getD, List.size_toArray, List.length_map]
  by_cases h : t < ts.length
  · have h' : t < (List.map (fun ops => some ({ instrs := flatten ops } : Loc))
        (List.map (fun x => List.map COp.entry x) ts)).toArray.size := by simpa using h
    simp only [h, h', ↓reduceIte, dite_true, Array.getInternal_eq_getElem, List.getElem_toArray, List.getElem_map]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  · simp [h]

theorem init_ginv (spec : Spec Nat Op Res) (name : String) (ts : List (List COp)) (v0 : Nat) (llsc clj nc : Bool)
    (source : Source) (limit : Nat) (hN : (allIds ts).Nodup) (h1000 : 1000 ∉ allIds ts)
    (hnc : nc = true → ∀ ops ∈ ts, ∀ c ∈ ops, c.noCas = true) :
    let p := startP name ts v0 llsc clj source limit
    GInv spec v0 nc p.memory p.threads p.steps [] (fun t => (.idle, ts.getD t [])) where
  hNodup := by simp [startP, start]
  linNodup := by simp
  linRec := by simp
  linOrder := List.Pairwise.nil
  answered := by simp [startP, start]
  runs := rfl
  invokeLt := by simp [startP, start]
  lpLt := by simp
  watchesRecord := by simp [startP, start]
  threadOK := by
    intro t
    rw [start_getD]
    split
    · rename_i ht
      refine ⟨by simp [Ph.instrs], trivial, ?_, ?_, ?_⟩
      · intro _ _ h; cases h
      · intro _ _ h; cases h
      · intro h
        refine ⟨rfl, fun c hc => hnc h _ ?_ c hc⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
        exact List.getElem_mem ht
    · rename_i ht
      refine ⟨rfl, ?_⟩
      simp only
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  disjoint := by
    intro t1 t2 x h1 h2
    simp only [tids, Ph.ids, List.nil_append] at h1 h2
    exact nodup_flatMap_inj (fun ops : List COp => ops.flatMap COp.ids) [] ts hN t1 t2 x h1 h2 (by simp)
  nodup := by
    intro t
    simp only [tids, Ph.ids, List.nil_append]
    exact (flatMap_getD_sub (fun ops : List COp => ops.flatMap COp.ids) ts t [] rfl).nodup hN
  restFresh := by simp [startP, start]
  not1000 := by
    intro t h
    simp only [tids, Ph.ids, List.nil_append] at h
    exact h1000 ((flatMap_getD_sub (fun ops : List COp => ops.flatMap COp.ids) ts t [] rfl).subset h)

theorem init_minv (name : String) (ts : List (List COp)) (v0 : Nat) (llsc clj : Bool) (source : Source)
    (limit : Nat) (phs : Nat → Ph × List COp) :
    MInv (startP name ts v0 llsc clj source limit).memory phs where
  vW := rfl
  vQ := rfl
  clj := fun _ => ⟨rfl, rfl, rfl⟩
  wW := by intro w h; cases h
  wQ := by intro w h; cases h
  wQN := List.nodup_nil
  wR := by intro w h; cases h
  wRN := List.nodup_nil

theorem init_inv (spec : Spec Nat Op Res) (name : String) (ts : List (List COp)) (v0 : Nat) (llsc clj nc : Bool)
    (source : Source) (limit : Nat) (hN : (allIds ts).Nodup) (h1000 : 1000 ∉ allIds ts)
    (hnc : nc = true → ∀ ops ∈ ts, ∀ c ∈ ops, c.noCas = true) :
    InvF spec v0 nc llsc clj (startP name ts v0 llsc clj source limit) :=
  ⟨rfl, rfl, [], _, init_ginv spec name ts v0 llsc clj nc source limit hN h1000 hnc, init_minv _ _ _ _ _ _ _ _⟩

/-! ## The theorem -/

/-- The history of every timeline of every scenario of the fragment is linearizable against
`spec`, given that `spec` allows each step's answer. -/
theorem history_linearizable (spec : Spec Nat Op Res) (hs : SpecOK spec) (name : String)
    (ts : List (List COp)) (v0 : Nat) (llsc clj nc : Bool)
    (hN : (allIds ts).Nodup) (h1000 : 1000 ∉ allIds ts)
    (hnc : nc = true → ∀ ops ∈ ts, ∀ c ∈ ops, c.noCas = true)
    (hspur : llsc = true → clj = false → nc = false → ∀ v o n, spec v (.cas o n) v (.bool false))
    (source : Source) (maxSteps limit : Nat) :
    Linearizable spec v0
      (runProcess (start (ofThreads name ts v0) llsc clj) (interleave prog maxSteps) source limit).2.memory.history.toList := by
  rw [runProcess_snd]
  have hinit := init_inv spec name ts v0 llsc clj nc source limit hN h1000 hnc
  have hend := interleave_inv prog maxSteps (fun _ => some "every live thread blocked")
    (InvF spec v0 nc llsc clj) (fun p d h => h) (stepKeeps hs hspur) _ hinit
  obtain ⟨_, _, lin, phs, g, _⟩ := hend
  exact linearizable_of_witness spec v0 _ lin
    { hNodup := g.hNodup, linNodup := g.linNodup, linRec := g.linRec, linOrder := g.linOrder,
      answered := g.answered, runs := ⟨_, g.runs⟩ }

/-! ## The specifications satisfy the steps -/

theorem strong_ok : SpecOK strong where
  swap v := rfl
  deref v := rfl
  reset v x := rfl
  casT v n := by simp [strong, applyOp]
  casF v o n h := by simp [strong, applyOp, h]

theorem weak_ok : SpecOK weak where
  swap v := Or.inl rfl
  deref v := Or.inl rfl
  reset v x := Or.inl rfl
  casT v n := Or.inl (by simp [applyOp])
  casF v o n h := Or.inl (by simp [applyOp, h])

/-! ## The results -/

/-- x86-64 (`compare_exchange_weak` is a `lock cmpxchg`: no spurious failure), jank's code or
the Clojure mode: every timeline's history is linearizable against the register. -/
theorem linearizable_x86 (name : String) (ts : List (List COp)) (v0 : Nat) (clj : Bool)
    (hN : (allIds ts).Nodup) (h1000 : 1000 ∉ allIds ts) (source : Source) (maxSteps limit : Nat) :
    Linearizable strong v0
      (runProcess (start (ofThreads name ts v0) false clj) (interleave prog maxSteps) source limit).2.memory.history.toList :=
  history_linearizable strong strong_ok name ts v0 false clj false hN h1000 (by simp) (by simp) source maxSteps limit

/-- The Clojure mode (strong `compareAndSet`) on either platform. -/
theorem linearizable_clojure (name : String) (ts : List (List COp)) (v0 : Nat) (llsc : Bool)
    (hN : (allIds ts).Nodup) (h1000 : 1000 ∉ allIds ts) (source : Source) (maxSteps limit : Nat) :
    Linearizable strong v0
      (runProcess (start (ofThreads name ts v0) llsc true) (interleave prog maxSteps) source limit).2.memory.history.toList :=
  history_linearizable strong strong_ok name ts v0 llsc true false hN h1000 (by simp) (by simp) source maxSteps limit

/-- LL/SC (AArch64 without LSE), jank's code: linearizable against the register whose
compare-and-set may answer false without effect. -/
theorem linearizable_llsc_weak (name : String) (ts : List (List COp)) (v0 : Nat) (clj : Bool)
    (hN : (allIds ts).Nodup) (h1000 : 1000 ∉ allIds ts) (source : Source) (maxSteps limit : Nat) :
    Linearizable weak v0
      (runProcess (start (ofThreads name ts v0) true clj) (interleave prog maxSteps) source limit).2.memory.history.toList :=
  history_linearizable weak weak_ok name ts v0 true clj false hN h1000 (by simp)
    (fun _ _ _ v o n => Or.inr ⟨o, n, rfl, rfl, rfl⟩) source maxSteps limit

/-- LL/SC without `compare-and-set!`: the spurious failures only make `swap!` loop, and the history
is linearizable against the strong register. -/
theorem linearizable_llsc_no_cas (name : String) (ts : List (List COp)) (v0 : Nat) (clj : Bool)
    (hN : (allIds ts).Nodup) (h1000 : 1000 ∉ allIds ts) (hc : ∀ ops ∈ ts, ∀ c ∈ ops, c.noCas = true)
    (source : Source) (maxSteps limit : Nat) :
    Linearizable strong v0
      (runProcess (start (ofThreads name ts v0) true clj) (interleave prog maxSteps) source limit).2.memory.history.toList :=
  history_linearizable strong strong_ok name ts v0 true clj true hN h1000 (fun _ => hc)
    (fun _ _ h => absurd h (by simp)) source maxSteps limit

end Jank.R3.Proofs.AtomLin

import Jank.R3.Proofs.AtomMain

/-!
# Atoms with recording watches never deadlock (round 3, proofs)

Round 1's D16: a watch that adds or removes watches, or `swap!`s the atom beside an `add-watch`,
deadlocks on folly's write-priority `SharedMutex`. Its searches judged every timeline for a
deadlock too (`Threads.interleave` reports one when every live thread is blocked); for the
scenarios without such watches they found none within their bounds. Here: for every scenario of
the fragment `AtomLin.COp` (any threads, any `swap!`, `@`, `compare-and-set!`, `reset!`,
`add-watch` with watches that only record), every source of decisions and every `maxSteps`, the
run never reports a deadlock; it ends normally or at the decision limit.

The argument: the validator lock is never taken exclusively; a thread holding the watches lock
exclusively, or shared, can always step; a thread waiting for it exclusively can take it once
the shared holders are gone; and with nobody holding or waiting, every lock is free.
-/

namespace Jank.R3.Proofs.AtomLin

open Determinismo Jank.Atom Jank.R3.Proofs Jank.R3.Proofs.Lin Jank.Sync

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

syntax "astepAt" "[" Lean.Parser.Tactic.simpLemma,* "]" ident : tactic
macro_rules
  | `(tactic| astepAt [$hs,*] $h:ident) => `(tactic| simp [prog, stepLogged, step, $hs,*, bind, EStateM.bind, mem,
      get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet, setMem, Jank.Atom.invoke, answer, stamp] at $h:ident)

/-- What can block: the three lock acquisitions, when the lock is not free for the thread. -/
def ABlocks (m : Mem) (t : Nat) (l : Loc) : Prop :=
  match l.instrs with
  | .validateLock :: _ => m.validatorMutex.lockShared t = none
  | .notifyLock _ _ :: _ => m.clojure = false ∧ m.watchesMutex.lockShared t = none
  | .watchLock :: _ => m.clojure = false ∧ m.watchesMutex.lock t = none
  | _ => False

def Blocks (p : Process Mem Loc) (t : Nat) : Prop :=
  ∃ l, p.threads.getD t none = some l ∧ ABlocks p.memory t l

theorem spurious_err (p : Process Mem Loc) (e : Stop) (s : Process Mem Loc) (h : spurious p = .error e s) :
    e = .limit := by
  by_cases hc : (p.memory.llsc && !p.memory.clojure) = true
  · cases hn : (Chaotic.decisions p).next "cpu.cas_spurious" [7, 1] with
    | ok vd =>
      obtain ⟨v, d⟩ := vd
      simp [spurious, hc, decideWeighted, hn, bind, EStateM.bind, mem, get, getThe, MonadStateOf.get, EStateM.get,
          pure, EStateM.pure, set, EStateM.set, Chaotic.setDecisions, Functor.map, EStateM.map] at h
    | error e' =>
      simp [spurious, hc, decideWeighted, hn, bind, EStateM.bind, mem, get, getThe,
        MonadStateOf.get, EStateM.get, pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
      obtain ⟨rfl, _⟩ := h
      exact next_error hn
  · simp only [Bool.not_eq_true] at hc
    simp [spurious, hc, bind, EStateM.bind, mem, get, getThe, MonadStateOf.get, EStateM.get, pure,
      EStateM.pure] at h

/-- A step that blocks changed nothing but the log, and its instruction was a lock not free. -/
theorem step_blocked (t : Nat) (l : Loc) (p p' : Process Mem Loc) (h : stepLogged t l p = .ok .blocked p') :
    ABlocks p.memory t l ∧ p'.memory = p.memory ∧ p'.threads = p.threads := by
  cases hi : l.instrs with
  | nil => astepAt [hi] h
  | cons i rest =>
    cases i with
    | validateLock =>
      cases hlk : p.memory.validatorMutex.lockShared t with
      | some vm => astepAt [hi, hlk] h
      | none =>
        astepAt [hi, hlk] h
        subst h
        exact ⟨by simp [ABlocks, hi, hlk], rfl, rfl⟩
    | notifyLock o n =>
      cases hcl : p.memory.clojure with
      | true => astepAt [hi, hcl] h
      | false =>
        cases hlk : p.memory.watchesMutex.lockShared t with
        | some vm => astepAt [hi, hcl, hlk] h
        | none =>
          astepAt [hi, hcl, hlk] h
          subst h
          exact ⟨by simp [ABlocks, hi, hlk, hcl], rfl, rfl⟩
    | watchLock =>
      cases hcl : p.memory.clojure with
      | true => astepAt [hi, hcl] h
      | false =>
        cases hlk : p.memory.watchesMutex.lock t with
        | some vm => astepAt [hi, hcl, hlk] h
        | none =>
          astepAt [hi, hcl, hlk] h
          subst h
          exact ⟨by simp [ABlocks, hi, hlk, hcl], rfl, rfl⟩
    | swapCas op =>
      rcases spurious_eq p with ⟨b, d, hsp, _⟩ | ⟨e, hsp⟩
      · by_cases hc : p.memory.val = l.v ∧ b = false
        · astepAt [hi, hsp, hc] h
        · astepAt [hi, hsp, hc] h
      · astepAt [hi, hsp] h
    | casOnce op o n =>
      rcases spurious_eq p with ⟨b, d, hsp, _⟩ | ⟨e, hsp⟩
      · by_cases hc : p.memory.val = o ∧ b = false
        · astepAt [hi, hsp, hc] h
        · astepAt [hi, hsp, hc] h
      · astepAt [hi, hsp] h
    | watchAnnounce => cases hcl : p.memory.clojure <;> astepAt [hi, hcl] h
    | watchUnlock => cases hcl : p.memory.clojure <;> astepAt [hi, hcl] h
    | _ => astepAt [hi] h

/-- A step throws only at the decision limit. -/
theorem step_err (t : Nat) (l : Loc) (p p' : Process Mem Loc) (e : Stop) (h : stepLogged t l p = .error e p') :
    e = .limit := by
  cases hi : l.instrs with
  | nil => astepAt [hi] h
  | cons i rest =>
    cases i with
    | validateLock => cases hlk : p.memory.validatorMutex.lockShared t <;> astepAt [hi, hlk] h
    | notifyLock o n =>
      cases hcl : p.memory.clojure with
      | true => astepAt [hi, hcl] h
      | false => cases hlk : p.memory.watchesMutex.lockShared t <;> astepAt [hi, hcl, hlk] h
    | watchLock =>
      cases hcl : p.memory.clojure with
      | true => astepAt [hi, hcl] h
      | false => cases hlk : p.memory.watchesMutex.lock t <;> astepAt [hi, hcl, hlk] h
    | swapCas op =>
      rcases spurious_eq p with ⟨b, d, hsp, _⟩ | ⟨e', hsp⟩
      · by_cases hc : p.memory.val = l.v ∧ b = false
        · astepAt [hi, hsp, hc] h
        · astepAt [hi, hsp, hc] h
      · astepAt [hi, hsp] h
        obtain ⟨rfl, _⟩ := h
        exact spurious_err p e' p hsp
    | casOnce op o n =>
      rcases spurious_eq p with ⟨b, d, hsp, _⟩ | ⟨e', hsp⟩
      · by_cases hc : p.memory.val = o ∧ b = false
        · astepAt [hi, hsp, hc] h
        · astepAt [hi, hsp, hc] h
      · astepAt [hi, hsp] h
        obtain ⟨rfl, _⟩ := h
        exact spurious_err p e' p hsp
    | watchAnnounce => cases hcl : p.memory.clojure <;> astepAt [hi, hcl] h
    | watchUnlock => cases hcl : p.memory.clojure <;> astepAt [hi, hcl] h
    | _ => astepAt [hi] h

/-- The head instruction of a phase that never blocks. -/
theorem notBlocks_of_head (m : Mem) (t : Nat) (l : Loc) (i : Instr) (rest : List Instr) (hl : l.instrs = i :: rest)
    (hi : match i with | .validateLock | .notifyLock _ _ | .watchLock => False | _ => True) : ¬ ABlocks m t l := by
  unfold ABlocks; rw [hl]; cases i <;> simp_all

/-- Some live thread can always step. -/
theorem live_step {spec : Spec Nat Op Res} {v0 : Nat} {nc llsc clj : Bool} (p : Process Mem Loc)
    (hI : InvF spec v0 nc llsc clj p) (t : Nat) (ht : (p.threads.getD t none).isSome = true) :
    ∃ u, (p.threads.getD u none).isSome = true ∧ ¬ Blocks p u := by
  obtain ⟨_, _, lin, phs, g, hM⟩ := hI
  -- a thread in phase `ph` is live, and its head instruction is the phase's first
  have liveOf : ∀ u, (phs u).1 ≠ .idle → ∃ l, p.threads.getD u none = some l ∧
      l.instrs = (phs u).1.instrs ++ restInstrs (phs u).2 := by
    intro u hu
    have := g.threadOK u
    cases hg : p.threads.getD u none with
    | none => rw [hg] at this; exact absurd this.1 hu
    | some l => rw [hg] at this; exact ⟨l, rfl, this.1⟩
  by_cases hw : ∃ w, p.memory.watchesMutex.writer = some w
  · obtain ⟨w, hw⟩ := hw
    have hiw := hM.wW w hw
    have hne : (phs w).1 ≠ .idle := by intro h; rw [h] at hiw; cases hiw
    obtain ⟨l, hl, hins⟩ := liveOf w hne
    refine ⟨w, by rw [hl]; rfl, ?_⟩
    rintro ⟨l', hl', hb⟩
    rw [hl] at hl'; injection hl' with hl'; subst hl'
    unfold ABlocks at hb; rw [hins] at hb
    cases hp : (phs w).1 <;> rw [hp] at hiw <;> simp [Ph.isW] at hiw <;> simp [hp, Ph.instrs] at hb
  · have hw' : p.memory.watchesMutex.writer = none := by
      cases h : p.memory.watchesMutex.writer with
      | none => rfl
      | some w => exact absurd ⟨w, h⟩ hw
    by_cases hr : p.memory.watchesMutex.readers = []
    · by_cases hq : p.memory.watchesMutex.waiting = []
      · -- every lock free: the given thread itself
        refine ⟨t, ht, ?_⟩
        rintro ⟨l, hl, hb⟩
        unfold ABlocks at hb
        split at hb
        · simp [SharedMutex.lockShared, hM.vW, hM.vQ] at hb
        · simp [SharedMutex.lockShared, hw', hq] at hb
        · simp [SharedMutex.lock, hw', hr] at hb
        · exact hb
      · obtain ⟨w, hwq⟩ : ∃ w, w ∈ p.memory.watchesMutex.waiting := by
          cases h : p.memory.watchesMutex.waiting with
          | nil => exact absurd h hq
          | cons w _ => exact ⟨w, by simp⟩
        have hiw := hM.wQ w hwq
        have hne : (phs w).1 ≠ .idle := by intro h; rw [h] at hiw; cases hiw
        obtain ⟨l, hl, hins⟩ := liveOf w hne
        refine ⟨w, by rw [hl]; rfl, ?_⟩
        rintro ⟨l', hl', hb⟩
        rw [hl] at hl'; injection hl' with hl'; subst hl'
        unfold ABlocks at hb; rw [hins] at hb
        cases hp : (phs w).1 <;> rw [hp] at hiw <;> simp [Ph.isL] at hiw <;>
          simp [hp, Ph.instrs, SharedMutex.lock, hw', hr] at hb
    · obtain ⟨r, hrr⟩ : ∃ r, r ∈ p.memory.watchesMutex.readers := by
        cases h : p.memory.watchesMutex.readers with
        | nil => exact absurd h hr
        | cons r _ => exact ⟨r, by simp⟩
      have hir := hM.wR r hrr
      have hne : (phs r).1 ≠ .idle := by intro h; rw [h] at hir; cases hir
      obtain ⟨l, hl, hins⟩ := liveOf r hne
      refine ⟨r, by rw [hl]; rfl, ?_⟩
      rintro ⟨l', hl', hb⟩
      rw [hl] at hl'; injection hl' with hl'; subst hl'
      unfold ABlocks at hb; rw [hins] at hb
      cases hp : (phs r).1 <;> rw [hp] at hir <;> simp [Ph.isR] at hir
      rename_i x res o n ks u
      cases u
      · simp [Ph.isR] at hir
      · cases ks <;> simp [hp, Ph.instrs] at hb

/-- The run of every scenario of the fragment never reports a deadlock: it ends normally or at
the decision limit. -/
theorem no_deadlock (name : String) (ts : List (List COp)) (v0 : Nat) (llsc clj : Bool)
    (hN : (allIds ts).Nodup) (h1000 : 1000 ∉ allIds ts) (source : Source) (maxSteps limit : Nat) :
    ∀ e, (runProcess (start (ofThreads name ts v0) llsc clj) (interleave prog maxSteps) source limit).1 = .error e →
      e = .limit := by
  intro e he
  simp only [runProcess, EStateM.run] at he
  split at he
  · cases he
  · rename_i e' s hres
    injection he with he; subst he
    exact interleave_no_deadlock prog maxSteps _ (InvF weak v0 false llsc clj) Blocks
      (fun p d h => h) (fun p d t h => h) (stepKeeps weak_ok (fun _ _ _ v o n => Or.inr ⟨o, n, rfl, rfl, rfl⟩))
      (by
        intro p t l p' _ hl hst
        obtain ⟨hb, hm, hth⟩ := step_blocked t l p p' hst
        refine ⟨⟨l, ?_, ?_⟩, ?_⟩
        · rw [hth]; exact hl
        · rw [hm]; exact hb
        · rintro u ⟨lu, hlu, hbu⟩; exact ⟨lu, by rw [hth]; exact hlu, by rw [hm]; exact hbu⟩)
      (fun p t l e p' _ _ h => step_err t l p p' e h)
      (fun p hp t ht => live_step p hp t ht)
      _ (init_inv weak name ts v0 llsc clj false source limit hN h1000 (by simp)) e' s hres

end Jank.R3.Proofs.AtomLin

/-! ## Round 1's scenarios, and the LL/SC counterexample -/

namespace Jank.R3.Proofs.AtomLin

open Determinismo Jank.Atom Jank.R3.Proofs Jank.R3.Proofs.Lin

/-- Round 1's scenarios are scenarios of the fragment. -/
theorem counter_eq : counter = ofThreads counter.name [[.watch 9, .swap 0], [.swap 1], [.deref 2]] := rfl
theorem counter2_eq : counter2 = ofThreads counter2.name [[.swap 0], [.swap 1]] := rfl
theorem casRace_eq : casRace = ofThreads casRace.name [[.cas 0 0 1], [.cas 1 0 2]] := rfl
theorem casFresh_eq : casFresh = ofThreads casFresh.name [[.cas 0 0 1]] := rfl

/-- Two `swap! inc` and a `deref` beside a recording watch (round 1: jank on x86-64, jank on
LL/SC and the Clojure mode each stopped at 500,000 timelines with nothing): for every timeline,
on either platform and in either mode, the history is linearizable against the register and the
run never deadlocks. -/
theorem counter_linearizable (llsc clj : Bool) (source : Source) (maxSteps limit : Nat) :
    Linearizable strong 0
      (runProcess (start counter llsc clj) (interleave prog maxSteps) source limit).2.memory.history.toList ∧
    ∀ e, (runProcess (start counter llsc clj) (interleave prog maxSteps) source limit).1 = .error e →
      e = .limit := by
  rw [counter_eq]
  refine ⟨?_, no_deadlock _ _ 0 llsc clj (by decide) (by decide) source maxSteps limit⟩
  cases clj with
  | true => exact linearizable_clojure _ _ 0 llsc (by decide) (by decide) source maxSteps limit
  | false =>
    cases llsc with
    | false => exact linearizable_x86 _ _ 0 false (by decide) (by decide) source maxSteps limit
    | true => exact linearizable_llsc_no_cas _ _ 0 false (by decide) (by decide) (by decide) source maxSteps limit

/-- Two `swap! inc` (round 1: x86-64 complete over 217,500 timelines; LL/SC stopped at 500,000). -/
theorem counter2_linearizable (llsc clj : Bool) (source : Source) (maxSteps limit : Nat) :
    Linearizable strong 0
      (runProcess (start counter2 llsc clj) (interleave prog maxSteps) source limit).2.memory.history.toList := by
  rw [counter2_eq]
  cases llsc with
  | false => exact linearizable_x86 _ _ 0 clj (by decide) (by decide) source maxSteps limit
  | true => exact linearizable_llsc_no_cas _ _ 0 clj (by decide) (by decide) (by decide) source maxSteps limit

/-- Two racing `compare-and-set!` from 0 on x86-64 (round 1: complete over 4,228 timelines). -/
theorem casRace_linearizable_x86 (clj : Bool) (source : Source) (maxSteps limit : Nat) :
    Linearizable strong 0
      (runProcess (start casRace false clj) (interleave prog maxSteps) source limit).2.memory.history.toList := by
  rw [casRace_eq]
  exact linearizable_x86 _ _ 0 clj (by decide) (by decide) source maxSteps limit

/-- The timeline of round 1's tape `{"name":"cpu.cas_spurious","options":2,"value":1}` on
`(compare-and-set! (atom 0) 0 1)`, LL/SC, jank's code. -/
def llscRun : List (OpRec Op Res) :=
  (runProcess (start casFresh true false) (interleave prog 200) (Source.path #[1])).2.memory.history.toList

def recCode (h : OpRec Op Res) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (h.id, h.invoke, h.ret.getD 999,
   (match h.op with | .cas o n => 1000 * o + n | _ => 999999),
   (match h.outcome with | some (.ok (.bool true)) => 1 | some (.ok (.bool false)) => 0 | _ => 2),
   (match h.op with | .cas .. => 1 | _ => 0))

theorem llscRun_code : llscRun.map recCode = [(0, 0, 4, 1, 0, 1)] := by decide +kernel

/-- That history is not linearizable against the strong register: `compare-and-set!` answered
false on an atom holding the expected value, with nothing concurrent (D17). -/
theorem llsc_cas_not_linearizable : ¬ Linearizable strong 0 llscRun := by
  have hc := llscRun_code
  rcases hrun : llscRun with _ | ⟨o, rest⟩
  · rw [hrun] at hc; cases hc
  rw [hrun] at hc
  rcases rest with _ | ⟨o2, rest⟩
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc
    simp only [recCode, Prod.mk.injEq] at hc
    obtain ⟨_, _, hret, hop, hout, _⟩ := hc
    have hop' : o.op = .cas 0 1 := by
      revert hop; cases o.op <;> simp <;> omega
    have hout' : o.outcome = some (.ok (.bool false)) := by
      revert hout; rcases o.outcome with _ | (_ | _) | _ <;> simp
      rename_i r; cases r <;> simp
    rintro ⟨order, hsub, _, hans, _, _, hlegal⟩
    have hin : o ∈ order := hans o List.mem_cons_self (by
      cases h : o.ret with
      | none => simp [h] at hret
      | some _ => rfl) (by rw [hout']; simp)
    cases order with
    | nil => cases hin
    | cons a as =>
      have ha : a = o := by have := hsub a List.mem_cons_self; simpa using this
      subst ha
      obtain ⟨s', r, hs, hr, _⟩ := hlegal
      rw [hop'] at hs
      simp [strong, applyOp] at hs
      obtain ⟨_, rfl⟩ := hs
      have := hr _ hout'
      cases this
  · simp at hc

/-- And it is linearizable against the weak register (`linearizable_llsc_weak`). -/
theorem llscRun_weak : Linearizable weak 0 llscRun := by
  unfold llscRun
  rw [casFresh_eq]
  exact linearizable_llsc_weak _ _ 0 false (by decide) (by decide) (Source.path #[1]) 200 100000

end Jank.R3.Proofs.AtomLin

import Jank.Delay
import Jank.R3.Proofs.Threads

/-!
# delay and promise, for every interleaving (round 3, proofs)

Round 1 searched `Jank.Delay` (delay.cpp `deref`/`is_realized`, promise.cpp `call` at
7135b7708) with `exhaust`: a delay whose body returns a value was complete with nothing found,
the Clojure mode complete (168 timelines); `deliver` after the D20 fix complete over 40
timelines. Here, for any number of threads, any number of derefs or delivers each, every source
of decisions and every `maxSteps`:

- `delay_value_runs_once`: jank's `delay` with a body returning a value runs the body at most once,
  and `realized?` after a deref is true;
- `delay_clojure_runs_once`: the Clojure mode (Delay.java), whatever the body does;
- `deliver_once`: at most one `deliver` returns the promise, and once every thread has ended,
  exactly one did (when there was one).
-/

namespace Jank.R3.Proofs.Delay

open Determinismo Jank.Delay Jank.R3.Proofs

/-! ## delay -/

/-- What `realized?` reads: jank `val.is_some()`, Clojure `lock == null`. -/
def realized (m : DelayMem) : Bool := if m.clojure then m.realized else m.val.isSome

/-- The invariant: `D` derefs per thread. -/
structure DInv (D : Nat) (clj : Bool) (p : Process DelayMem DLoc) : Prop where
  mode : p.memory.clojure = clj
  body : clj = false → p.memory.body = .returnsValue
  noError : p.memory.error = false
  runs : p.memory.runs = if realized p.memory then 1 else 0
  after : ∀ b ∈ p.memory.realizedAfter, b = true
  threads : ∀ t l, p.threads.getD t none = some l →
    l.pc ≤ 3 ∧ l.derefsLeft ≤ D ∧ ((l.pc = 1 ∨ l.pc = 2) → 1 ≤ l.derefsLeft) ∧ (l.pc = 3 → l.derefsLeft = 0) ∧
    (l.pc = 2 ∨ l.derefsLeft < D → realized p.memory = true)

theorem delay_step (D : Nat) (hD : 1 ≤ D) (clj : Bool) : StepKeeps { step := delayStep } (DInv D clj) := by
  intro p t l h hl
  have ht : t < p.threads.size := getD_some_lt _ _ _ hl
  obtain ⟨hpc, hdl, h12, h3, hreal⟩ := h.threads t l hl
  have upd : ∀ (m : DelayMem) (l' : Option DLoc),
      m.clojure = clj → (clj = false → m.body = .returnsValue) → m.error = false →
      m.runs = (if realized m then 1 else 0) → (∀ b ∈ m.realizedAfter, b = true) →
      (realized p.memory = true → realized m = true) →
      (∀ l'', l' = some l'' → l''.pc ≤ 3 ∧ l''.derefsLeft ≤ D ∧ ((l''.pc = 1 ∨ l''.pc = 2) → 1 ≤ l''.derefsLeft) ∧
        (l''.pc = 3 → l''.derefsLeft = 0) ∧ (l''.pc = 2 ∨ l''.derefsLeft < D → realized m = true)) →
      ∀ (dec : Decisions) (lg : Array String),
        DInv D clj ⟨dec, m, p.threads.set! t l', p.steps + 1, lg⟩ := by
    intro m l' h1 h2 h3' h4 h5 hmono hl' dec lg
    refine ⟨h1, h2, h3', h4, h5, ?_⟩
    intro u lu hu
    simp only at hu
    rw [getD_set _ _ _ _ ht] at hu
    simp only
    by_cases e : u = t
    · subst e
      rcases l' with _ | l'
      · simp at hu
      · simp at hu; subst hu; exact hl' _ rfl
    · simp only [e, ↓reduceIte] at hu
      obtain ⟨a, b, c, d, f⟩ := h.threads u lu hu
      exact ⟨a, b, c, d, fun x => hmono (f x)⟩
  obtain ⟨pc, dl⟩ := l
  simp only at hpc hdl h12 h3 hreal
  rcases pc with _ | _ | _ | _ | pc
  · -- pc 0: a deref begins (lock), or the thread asks `realized?`
    by_cases hz : dl = 0
    · subst hz
      simp [delayStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
      exact upd p.memory (some { pc := 3, derefsLeft := 0 }) h.mode h.body h.noError h.runs h.after id
        (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simp, by simp, by simp, fun _ => rfl, fun _ => hreal (Or.inr (by omega))⟩)
        _ _
    · cases hlk : p.memory.mutex.lock t with
      | some mx =>
        simp [delayStep, hz, hlk, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
          modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        exact upd { p.memory with mutex := mx } (some { pc := 1, derefsLeft := dl }) h.mode h.body h.noError h.runs
          h.after id
          (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simp, hdl, fun _ => by simp; omega, by simp, fun h' => by
                rcases h' with h' | h'; · simp at h'
                exact hreal (Or.inr h')⟩)
          _ _
      | none =>
        simp [delayStep, hz, hlk, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
        exact h
  · -- pc 1: the check and the body
    have hd1 : 1 ≤ dl := h12 (Or.inl rfl)
    by_cases hcl : p.memory.clojure = true
    · by_cases hr : p.memory.realized = true
      · simp only [delayStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        rw [if_pos hcl, if_neg (by simp [hr])]
        simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        have hre : realized p.memory = true := by simp [realized, hcl, hr]
        exact upd p.memory (some { pc := 2, derefsLeft := dl }) h.mode h.body h.noError h.runs h.after id
          (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simp, hdl, fun _ => by simp; omega,
            by simp, fun _ => hre⟩) _ _
      · simp only [delayStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        rw [if_pos hcl, if_pos (by simp [hr])]
        simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        have hre0 : realized p.memory = false := by simp [realized, hcl, hr]
        have hruns : p.memory.runs = 0 := by have := h.runs; rw [hre0] at this; simpa using this
        exact upd { p.memory with runs := p.memory.runs + 1, realized := true } (some { pc := 2, derefsLeft := dl })
          h.mode h.body h.noError (by simp [realized, hcl, hruns]) h.after
          (fun _ => by simp [realized, hcl])
          (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simp, hdl, fun _ => by simp; omega,
            by simp, fun _ => by simp [realized, hcl]⟩) _ _
    · have hcl' : p.memory.clojure = false := by simpa using hcl
      have hclj : clj = false := by rw [← h.mode, hcl']
      cases hv : p.memory.val with
      | some v =>
        simp only [delayStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        rw [if_neg hcl, if_pos (by simp [hv])]
        simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        have hre : realized p.memory = true := by simp [realized, hcl', hv]
        exact upd p.memory (some { pc := 2, derefsLeft := dl }) h.mode h.body h.noError h.runs h.after id
          (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simp, hdl, fun _ => by simp; omega,
            by simp, fun _ => hre⟩) _ _
      | none =>
        have he := h.noError
        have hb := h.body hclj
        simp only [delayStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        rw [if_neg hcl, if_neg (by simp [hv]), if_neg (by simp [he])]
        simp only [hb, bodyResult, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        have hre0 : realized p.memory = false := by simp [realized, hcl', hv]
        have hruns : p.memory.runs = 0 := by have := h.runs; rw [hre0] at this; simpa using this
        exact upd { p.memory with runs := p.memory.runs + 1, val := some 7, error := false, body := .returnsValue }
          (some { pc := 2, derefsLeft := dl })
          h.mode (fun _ => rfl) rfl (by simp [realized, hcl', hruns]) h.after
          (fun _ => by simp [realized, hcl'])
          (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simp, hdl, fun _ => by simp; omega,
            by simp, fun _ => by simp [realized, hcl']⟩) _ _
  · -- pc 2: unlock, the deref returns
    have hd1 : 1 ≤ dl := h12 (Or.inr rfl)
    have hre : realized p.memory = true := hreal (Or.inl rfl)
    simp [delayStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    exact upd { p.memory with mutex := p.memory.mutex.unlock } (some { pc := 0, derefsLeft := dl - 1 })
      h.mode h.body h.noError h.runs h.after id
      (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simp, by simp; omega, by simp,
        by simp, fun _ => hre⟩) _ _
  · -- pc 3: `realized?`
    have hd0 : dl = 0 := h3 rfl
    have hre : realized p.memory = true := hreal (Or.inr (by omega))
    simp [delayStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    exact upd { p.memory with realizedAfter := p.memory.realizedAfter ++ [realized p.memory] } none
      h.mode h.body h.noError h.runs
      (by intro b hb; simp at hb; rcases hb with hb | hb; exact h.after b hb; rw [hb]; exact hre)
      id (by intro l'' hl''; cases hl'') _ _
  · omega

theorem getD_replicate {α : Type} (n t : Nat) (x : α) (l : α)
    (h : (List.replicate n (some x)).toArray.getD t none = some l) : l = x := by
  simp only [Array.getD, List.size_toArray, List.length_replicate] at h
  split at h
  · simp at h; exact h.symm
  · cases h

/-- The process `runDelay` runs (`threads` threads, `derefs` derefs each). -/
def delayStart (body : Body) (clojure : Bool) (threads derefs : Nat) : Process DelayMem DLoc :=
  { memory := { body, clojure }, threads := (List.replicate threads (some { derefsLeft := derefs })).toArray }

theorem delay_init (body : Body) (clj : Bool) (hb : clj = false → body = .returnsValue) (threads D : Nat)
    (source : Source) (limit : Nat) :
    DInv D clj { delayStart body clj threads D with decisions := { source, limit } } where
  mode := rfl
  body := hb
  noError := rfl
  runs := by cases clj <;> simp [realized, delayStart]
  after := by simp [delayStart]
  threads := by
    intro t l hl
    have := getD_replicate _ _ _ _ hl
    subst this
    simp

theorem delay_end (body : Body) (clj : Bool) (hb : clj = false → body = .returnsValue) (threads D : Nat)
    (hD : 1 ≤ D) (source : Source) (maxSteps limit : Nat) :
    let p := (runProcess (delayStart body clj threads D) (interleave { step := delayStep } maxSteps) source limit).2
    p.memory.runs ≤ 1 ∧ ∀ b ∈ p.memory.realizedAfter, b = true := by
  simp only
  rw [runProcess_snd]
  have h := interleave_inv { step := delayStep } maxSteps (fun _ => some "every live thread blocked") (DInv D clj)
    (fun p d h => ⟨h.mode, h.body, h.noError, h.runs, h.after, h.threads⟩) (delay_step D hD clj) _
    (delay_init body clj hb threads D source limit)
  refine ⟨?_, h.after⟩
  rw [h.runs]; split <;> omega

/-- jank's `delay` with a body returning a value (delay.cpp `deref`): for any number of threads
and derefs, every interleaving, the body runs at most once and `realized?` after a deref is true
(round 1: `exhaust` complete within its bounds). -/
theorem delay_value_runs_once (threads derefs : Nat) (hD : 1 ≤ derefs) (source : Source) (maxSteps limit : Nat) :
    let p := (runProcess (delayStart .returnsValue false threads derefs) (interleave { step := delayStep } maxSteps)
      source limit).2
    p.memory.runs ≤ 1 ∧ ∀ b ∈ p.memory.realizedAfter, b = true :=
  delay_end .returnsValue false (fun _ => rfl) threads derefs hD source maxSteps limit

/-- The Clojure mode (Delay.java `deref`/`isRealized`), whatever the body does: the specification
the jank model is judged against holds for every interleaving. -/
theorem delay_clojure_runs_once (body : Body) (threads derefs : Nat) (hD : 1 ≤ derefs) (source : Source)
    (maxSteps limit : Nat) :
    let p := (runProcess (delayStart body true threads derefs) (interleave { step := delayStep } maxSteps)
      source limit).2
    p.memory.runs ≤ 1 ∧ ∀ b ∈ p.memory.realizedAfter, b = true :=
  delay_end body true (fun h => by cases h) threads derefs hD source maxSteps limit

theorem delayStart_eq (body : Body) (clojure : Bool) (threads derefs : Nat) :
    delayStart body clojure threads derefs =
      { memory := { body, clojure }, threads := (List.replicate threads (some { derefsLeft := derefs })).toArray } := rfl

/-! ## promise: `deliver` -/

/-- The invariant of `runPromise`'s process, with `n` deliver threads first. -/
structure PInv (n sz : Nat) (p : Process PromiseMem PLoc) : Prop where
  size : p.threads.size = sz
  count : (p.memory.returns.filter id).length = if p.memory.ready then 1 else 0
  kind : ∀ t l, p.threads.getD t none = some l → (l.delivers = true ↔ t < n)
  past : ∀ t l, p.threads.getD t none = some l → l.delivers = true → 2 ≤ l.pc → p.memory.ready = true
  ended : ∀ t, t < n → t < p.threads.size → p.threads.getD t none = none → p.memory.ready = true

theorem filter_id_append (l : List Bool) (b : Bool) :
    ((l ++ [b]).filter id).length = (l.filter id).length + (if b then 1 else 0) := by
  cases b <;> simp

theorem promise_step (n sz : Nat) : StepKeeps { step := promiseStep } (PInv n sz) := by
  intro p t l h hl
  have ht : t < p.threads.size := getD_some_lt _ _ _ hl
  have hkind := h.kind t l hl
  have hpast := h.past t l hl
  -- the frame: memory changes keeping `ready` monotone, the thread's new locals
  have upd : ∀ (m : PromiseMem) (l' : Option PLoc),
      (m.returns.filter id).length = (if m.ready then 1 else 0) →
      (p.memory.ready = true → m.ready = true) →
      (∀ l'', l' = some l'' → (l''.delivers = true ↔ t < n) ∧ (l''.delivers = true → 2 ≤ l''.pc → m.ready = true)) →
      (l' = none → t < n → m.ready = true) →
      ∀ (dec : Decisions) (lg : Array String),
        PInv n sz ⟨dec, m, p.threads.set! t l', p.steps + 1, lg⟩ := by
    intro m l' hc hmono hl' hnone dec lg
    refine ⟨by simp [size_set, h.size], hc, ?_, ?_, ?_⟩
    · intro u lu hu
      simp only at hu
      rw [getD_set _ _ _ _ ht] at hu
      by_cases e : u = t
      · subst e; simp only [↓reduceIte] at hu; exact (hl' lu hu).1
      · simp only [e, ↓reduceIte] at hu; exact h.kind u lu hu
    · intro u lu hu hd hpc
      simp only at hu
      rw [getD_set _ _ _ _ ht] at hu
      simp only
      by_cases e : u = t
      · subst e; simp only [↓reduceIte] at hu; exact (hl' lu hu).2 hd hpc
      · simp only [e, ↓reduceIte] at hu; exact hmono (h.past u lu hu hd hpc)
    · intro u hu hus hnu
      simp only [size_set] at hus hnu
      rw [getD_set _ _ _ _ ht] at hnu
      simp only
      by_cases e : u = t
      · subst e; simp only [↓reduceIte] at hnu; exact hnone hnu hu
      · simp only [e, ↓reduceIte] at hnu; exact hmono (h.ended u hu hus hnu)
  obtain ⟨pc, x, dv⟩ := l
  simp only at hkind hpast
  cases dv with
  | false =>
    -- a timed deref: one step, done
    cases hcl : p.memory.clojure with
    | true =>
      cases hd : (Chaotic.decisions p).next "time.within_timeout" [1, 1] with
      | ok vd =>
        obtain ⟨v, d⟩ := vd
        simp [promiseStep, hcl, Determinismo.decide, decideWeighted, hd, set, EStateM.set, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        exact upd _ none (by simp [h.count]) (fun hh => by simpa using hh) (by intro _ h'; cases h')
          (by intro _ htn; simp at hkind; omega) _ _
      | error e =>
        simp [promiseStep, hcl, Determinismo.decide, decideWeighted, hd, throw, throwThe, MonadExceptOf.throw,
          EStateM.throw, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        exact h
    | false =>
      simp [promiseStep, hcl, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
      exact upd _ none (by simp [h.count]) (fun hh => by simpa using hh) (by intro _ h'; cases h')
        (by intro _ htn; simp at hkind; omega) _ _
  | true =>
    rcases pc with _ | _ | _ | pc
    · cases hlk : (p.memory.state.announce t).lock t with
      | some st =>
        simp [promiseStep, hlk, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        exact upd { p.memory with state := st } (some { pc := 1, x, delivers := true }) h.count id
          (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simpa using hkind, by simp⟩)
          (by intro h'; cases h') _ _
      | none =>
        simp [promiseStep, hlk, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        exact ⟨h.size, h.count, h.kind, h.past, h.ended⟩
    · by_cases hr : p.memory.ready = true
      · simp only [promiseStep, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        rw [if_neg (by simp [hr])]
        simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        exact upd { p.memory with returns := p.memory.returns ++ [false] }
          (some { pc := 2, x, delivers := true })
          (by simp [filter_id_append, h.count, hr]) id
          (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simpa using hkind, fun _ _ => hr⟩)
          (by intro h'; cases h') _ _
      · have hr' : p.memory.ready = false := by simpa using hr
        simp only [promiseStep, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        rw [if_pos (by simp [hr'])]
        simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
        exact upd { p.memory with ready := true, val := x, returns := p.memory.returns ++ [true] }
          (some { pc := 2, x, delivers := true })
          (by simp [filter_id_append, h.count, hr']) (fun _ => rfl)
          (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simpa using hkind, fun _ _ => rfl⟩)
          (by intro h'; cases h') _ _
    · have hrd : p.memory.ready = true := hpast rfl (by decide)
      simp [promiseStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
      exact upd { p.memory with state := p.memory.state.unlock } (some { pc := 3, x, delivers := true }) h.count id
        (by intro l'' hl''; obtain rfl := Option.some.inj hl''; exact ⟨by simpa using hkind, fun _ _ => hrd⟩)
        (by intro h'; cases h') _ _
    · have hrd : p.memory.ready = true := hpast rfl (by omega)
      simp [promiseStep, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
      exact upd p.memory none h.count id (by intro _ h'; cases h') (fun _ _ => hrd) _ _

/-- The process `runPromise` runs: `delivers` threads delivering `1, 2, …`, then the timed
derefs. -/
def promiseStart (clojure : Bool) (delivers timeoutDerefs : Nat) : Process PromiseMem PLoc :=
  let threads := (List.range delivers).map (fun i => some ({ x := i + 1, delivers := true } : PLoc))
    ++ List.replicate timeoutDerefs (some ({ x := 0, delivers := false } : PLoc))
  { memory := { clojure }, threads := threads.toArray }

theorem promise_thread (n k t : Nat) (l : PLoc)
    (h : ((List.range n).map (fun i => some ({ x := i + 1, delivers := true } : PLoc)) ++
          List.replicate k (some ({ x := 0, delivers := false } : PLoc))).toArray.getD t none = some l) :
    (t < n ∧ l.delivers = true ∧ l.pc = 0) ∨ (n ≤ t ∧ l.delivers = false ∧ l.pc = 0) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray] at h
  by_cases htn : t < n
  · rw [List.getElem?_append_left (by simpa using htn)] at h
    simp [htn] at h
    left; subst h; exact ⟨htn, rfl, rfl⟩
  · rw [List.getElem?_append_right (by simp; omega)] at h
    simp only [List.length_map, List.length_range, List.getElem?_replicate] at h
    by_cases hk : t - n < k
    · simp [hk] at h; right; subst h; exact ⟨by omega, rfl, rfl⟩
    · simp [hk] at h

theorem promise_some (n k t : Nat) (ht : t < n) :
    ((List.range n).map (fun i => some ({ x := i + 1, delivers := true } : PLoc)) ++
      List.replicate k (some ({ x := 0, delivers := false } : PLoc))).toArray.getD t none ≠ none := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_append_left (by simpa using ht)]
  simp [ht]

theorem promise_init (clojure : Bool) (n k : Nat) (source : Source) (limit : Nat) :
    PInv n (n + k) { promiseStart clojure n k with decisions := { source, limit } } where
  size := by simp [promiseStart]
  count := by simp [promiseStart]
  kind := by
    intro t l hl
    simp only [promiseStart] at hl
    rcases promise_thread n k t l hl with ⟨htn, hd, _⟩ | ⟨htn, hd, _⟩
    · simp [hd, htn]
    · simp [hd]; omega
  past := by
    intro t l hl hd hpc
    simp only [promiseStart] at hl
    rcases promise_thread n k t l hl with ⟨_, _, hp⟩ | ⟨_, hd', _⟩
    · omega
    · rw [hd] at hd'; cases hd'
  ended := by
    intro t ht _ hn
    simp only [promiseStart] at hn
    exact absurd hn (promise_some n k t ht)

/-- `deliver` (promise.cpp `call`, 7135b7708): for any number of delivering threads and timed
derefs, every interleaving and every `maxSteps`, at most one `deliver` returns the promise; once
every thread has ended, exactly one did (when there was a deliver). Round 1: `exhaust` complete
over 40 timelines (2 delivers). -/
theorem deliver_once (clojure : Bool) (n k : Nat) (source : Source) (maxSteps limit : Nat) :
    let p := (runProcess (promiseStart clojure n k) (interleave { step := promiseStep } maxSteps) source limit).2
    (p.memory.returns.filter id).length ≤ 1 ∧
    (0 < n → (∀ t, p.threads.getD t none = none) → (p.memory.returns.filter id).length = 1) := by
  simp only
  rw [runProcess_snd]
  have h := interleave_inv { step := promiseStep } maxSteps (fun _ => some "every live thread blocked")
    (PInv n (n + k))
    (fun p d h => ⟨h.size, h.count, h.kind, h.past, h.ended⟩)
    (promise_step n (n + k)) _ (promise_init clojure n k source limit)
  have hsize := h.size
  refine ⟨by rw [h.count]; split <;> omega, ?_⟩
  intro hn hall
  rw [h.count, h.ended 0 hn (by rw [hsize]; omega) (hall 0)]
  rfl

end Jank.R3.Proofs.Delay

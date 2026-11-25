import Jank.Atom
import Jank.R3.Proofs.Lin
import Jank.R3.Proofs.Threads

/-!
# `swap!` and friends are linearizable, for every interleaving (round 3, proofs)

Round 1 searched `Jank.Atom` (atom.cpp as `Threads` steps): two `swap! inc` complete over 217,500
timelines on x86-64; two `swap! inc` plus a `deref` (and a recording watch) stopped at 500,000;
the LL/SC variant stopped at 500,000. Here the property is proved for every input of a fragment:

- any number of threads, each running any list of client operations among `(swap! a inc)`,
  `@a`, `(compare-and-set! a old new)`, `(reset! a x)` and `(add-watch a k f)` with a watch that
  only records (the watch bodies that call back into the atom are D16's area);
- every source of decisions (every interleaving, every spurious-failure pattern), every
  `maxSteps`, either platform (`llsc`), jank's code or the Clojure mode, any initial value.

The histories are judged against the replica's own sequential model `Jank.Atom.applyOp` (a
register; `swap! inc` returns the new value) through `Lin.Linearizable`, the relational
definition (`Determinismo.linearizable` is `partial`, so it cannot be reasoned about).

The proof is by linearization points: `swapCas` (when it succeeds), `casOnce`, `resetStore` and
`deref` each take effect in one step. The invariant `GInv` keeps, beside the replica's state, the
points taken so far (`lin`) and each thread's position in its program (`phs`).
-/

namespace Jank.R3.Proofs.AtomLin

open Determinismo Jank.Atom Jank.R3.Proofs Jank.R3.Proofs.Lin

/-! ## The fragment -/

/-- A client operation: its history id first. `watch k` is `(add-watch a k (fn [k r o n] ...))`
with a body that touches nothing (`WatchFn.record`). -/
inductive COp where
  | swap (x : Nat)
  | deref (x : Nat)
  | cas (x old new : Nat)
  | reset (x v : Nat)
  | watch (k : Nat)
  deriving Repr, BEq, DecidableEq

/-- The replica's own scenario entries (`Jank.Atom.swapInc`, `derefOp`, `casOp`, `resetTo`,
`addWatch`). -/
def COp.entry : COp → Option (Nat × Op) × List Instr
  | .swap x => (some (x, .swapInc), swapInc x)
  | .deref x => (some (x, .deref), derefOp x)
  | .cas x o n => (some (x, .cas o n), casOp x o n)
  | .reset x v => (some (x, .reset v), resetTo x v)
  | .watch k => (none, addWatch k .record)

def COp.ids : COp → List Nat
  | .swap x | .deref x | .cas x _ _ | .reset x _ => [x]
  | .watch _ => []

def COp.noCas : COp → Bool
  | .cas .. => false
  | _ => true

/-- A scenario of the fragment, built with the replica's `Scenario`. -/
def ofThreads (name : String) (ts : List (List COp)) (initial : Nat := 0) : Scenario :=
  { name, threads := ts.map (·.map COp.entry), initial }

/-- Every history id of a scenario (they must be distinct, and not 1000, the id the replica
gives a watch's nested `swap!`). -/
def allIds (ts : List (List COp)) : List Nat := ts.flatMap (·.flatMap COp.ids)

/-- The instructions of the operations not yet started. -/
def restInstrs (rest : List COp) : List Instr := flatten (rest.map COp.entry)

theorem restInstrs_nil : restInstrs [] = [] := rfl

/-- An operation's instructions, its `invoke` first. -/
def COp.instrs : COp → List Instr
  | .swap x => .invoke x .swapInc :: swapInc x
  | .deref x => .invoke x .deref :: derefOp x
  | .cas x o n => .invoke x (.cas o n) :: casOp x o n
  | .reset x v => .invoke x (.reset v) :: resetTo x v
  | .watch k => addWatch k .record

theorem restInstrs_cons (c : COp) (cs : List COp) :
    restInstrs (c :: cs) = c.instrs ++ restInstrs cs := by
  cases c <;> simp [restInstrs, flatten, List.flatMap_cons, COp.entry, COp.instrs]

/-! ## A thread's position: the phase of its current operation -/

inductive Ph where
  | idle
  | swL (x : Nat) | swV (x : Nat) | swU (x : Nat) | swC (x : Nat)
  | casV (x o n : Nat) | casU (x o n : Nat) | casC (x o n : Nat)
  | rsV (x v : Nat) | rsU (x v : Nat) | rsL (x v : Nat) | rsS (x v : Nat)
  | drD (x : Nat)
  /-- After its point: the notification, then the answer `r`. -/
  | nfL (x : Nat) (r : Res) (o n : Nat)
  /-- The watch calls left, the unlock (jank) and the answer. -/
  | nfC (x : Nat) (r : Res) (o n : Nat) (ks : List Nat) (u : Bool)
  | wL (k : Nat) | wD (k : Nat) | wU

def Ph.instrs : Ph → List Instr
  | .idle => []
  | .swL x => [.loadInc x, .validateLock, .validateUnlock, .swapCas x]
  | .swV x => [.validateLock, .validateUnlock, .swapCas x]
  | .swU x => [.validateUnlock, .swapCas x]
  | .swC x => [.swapCas x]
  | .casV x o n => [.validateLock, .validateUnlock, .casOnce x o n]
  | .casU x o n => [.validateUnlock, .casOnce x o n]
  | .casC x o n => [.casOnce x o n]
  | .rsV x v => [.validateLock, .validateUnlock, .resetLoad x v, .resetStore x v]
  | .rsU x v => [.validateUnlock, .resetLoad x v, .resetStore x v]
  | .rsL x v => [.resetLoad x v, .resetStore x v]
  | .rsS x v => [.resetStore x v]
  | .drD x => [.deref x]
  | .nfL x r o n => [.notifyLock o n, .ret x r]
  | .nfC x r o n ks u => ks.map (fun k => .callWatch k .record o n) ++ (if u then [.notifyUnlock] else []) ++ [.ret x r]
  | .wL k => [.watchLock, .watchAdd k .record, .watchUnlock]
  | .wD k => [.watchAdd k .record, .watchUnlock]
  | .wU => [.watchUnlock]

def Ph.ids : Ph → List Nat
  | .idle | .wL _ | .wD _ | .wU => []
  | .swL x | .swV x | .swU x | .swC x | .casV x .. | .casU x .. | .casC x ..
  | .rsV x _ | .rsU x _ | .rsL x _ | .rsS x _ | .drD x | .nfL x .. | .nfC x .. => [x]

/-- Before its linearization point: the operation's id and op. -/
def Ph.pending : Ph → Option (Nat × Op)
  | .swL x | .swV x | .swU x | .swC x => some (x, .swapInc)
  | .casV x o n | .casU x o n | .casC x o n => some (x, .cas o n)
  | .rsV x v | .rsU x v | .rsL x v | .rsS x v => some (x, .reset v)
  | .drD x => some (x, .deref)
  | _ => none

/-- After its point: the id and the result it answers. -/
def Ph.post : Ph → Option (Nat × Res)
  | .nfL x r .. | .nfC x r .. => some (x, r)
  | _ => none

def Ph.noCas : Ph → Bool
  | .casV .. | .casU .. | .casC .. => false
  | _ => true

/-- The first phase of an operation (after its `invoke`). -/
def COp.first : COp → Ph
  | .swap x => .swL x
  | .deref x => .drD x
  | .cas x o n => .casV x o n
  | .reset x v => .rsV x v
  | .watch k => .wL k

def tids (s : Ph × List COp) : List Nat := s.1.ids ++ s.2.flatMap COp.ids

/-! ## The invariant -/

abbrev Hist := List (OpRec Op Res)
abbrev LE := LinE Op Res

def Pend (H : Hist) (lin : List LE) (x : Nat) (o : Op) : Prop :=
  (∃ h ∈ H, h.id = x ∧ h.ret = none ∧ h.op = o) ∧ x ∉ lin.map (·.id)

def Post (H : Hist) (lin : List LE) (x : Nat) (r : Res) : Prop :=
  (∃ h ∈ H, h.id = x ∧ h.ret = none) ∧ ∃ e ∈ lin, e.id = x ∧ e.res = r

def LocOK (ph : Ph) (l : Loc) : Prop :=
  match ph with
  | .swV _ | .swU _ | .swC _ => l.next = l.v + 1
  | _ => True

def ThreadOK (noCas : Bool) (H : Hist) (lin : List LE) (s : Ph × List COp) : Option Loc → Prop
  | none => s.1 = .idle ∧ s.2 = []
  | some l => l.instrs = s.1.instrs ++ restInstrs s.2 ∧ LocOK s.1 l ∧
      (∀ x o, s.1.pending = some (x, o) → Pend H lin x o) ∧
      (∀ x r, s.1.post = some (x, r) → Post H lin x r) ∧
      (noCas = true → s.1.noCas = true ∧ ∀ c ∈ s.2, c.noCas = true)

/-- The invariant: the replica's memory, threads and step count, with the linearization points
taken so far and each thread's phase. -/
structure GInv (spec : Spec Nat Op Res) (v0 : Nat) (noCas : Bool) (m : Mem) (threads : Array (Option Loc))
    (steps : Nat) (lin : List LE) (phs : Nat → Ph × List COp) : Prop where
  hNodup : (m.history.toList.map (·.id)).Nodup
  linNodup : (lin.map (·.id)).Nodup
  linRec : ∀ e ∈ lin, ∃ h ∈ m.history.toList, h.id = e.id ∧ h.op = e.op ∧ h.invoke < e.lp
  linOrder : lin.Pairwise (fun a b => a.lp < b.lp)
  answered : ∀ h ∈ m.history.toList, (h.ret = none ∧ h.outcome = none) ∨
    (∃ rt, ∃ e ∈ lin, h.ret = some rt ∧ e.id = h.id ∧ h.outcome = some (.ok e.res) ∧ e.lp < rt)
  runs : RunsTo spec v0 lin m.val
  invokeLt : ∀ h ∈ m.history.toList, h.invoke < steps
  lpLt : ∀ e ∈ lin, e.lp < steps
  watchesRecord : ∀ w ∈ m.watches, w.2 = .record
  threadOK : ∀ t, ThreadOK noCas m.history.toList lin (phs t) (threads.getD t none)
  disjoint : ∀ t1 t2 x, x ∈ tids (phs t1) → x ∈ tids (phs t2) → t1 = t2
  nodup : ∀ t, (tids (phs t)).Nodup
  restFresh : ∀ t, ∀ x ∈ (phs t).2.flatMap COp.ids, x ∉ m.history.toList.map (·.id)
  not1000 : ∀ t, 1000 ∉ tids (phs t)

def Inv (spec : Spec Nat Op Res) (v0 : Nat) (noCas : Bool) (p : Process Mem Loc) : Prop :=
  ∃ lin phs, GInv spec v0 noCas p.memory p.threads p.steps lin phs

/-! ## The specifications -/

/-- The replica's register (`Jank.Atom.applyOp`). -/
def strong : Spec Nat Op Res := fun v op v' r => applyOp v op = (v', r)

/-- The register with a weak compare-and-set: besides the strong answer, a `compare-and-set!` may
answer false without effect (C++ `compare_exchange_weak`: "may fail spuriously"). -/
def weak : Spec Nat Op Res := fun v op v' r =>
  applyOp v op = (v', r) ∨ (∃ o n, op = .cas o n ∧ v' = v ∧ r = .bool false)

/-! ## Keeping the invariant: the frame -/

theorem pending_mem_ids {ph : Ph} {x : Nat} {o : Op} (h : ph.pending = some (x, o)) : x ∈ ph.ids := by
  cases ph <;> simp_all [Ph.pending, Ph.ids]

theorem post_mem_ids {ph : Ph} {x : Nat} {r : Res} (h : ph.post = some (x, r)) : x ∈ ph.ids := by
  cases ph <;> simp_all [Ph.post, Ph.ids]

theorem ThreadOK.transfer {nc : Bool} {H H' : Hist} {lin lin' : List LE} {s : Ph × List COp} {ol : Option Loc}
    (h : ThreadOK nc H lin s ol)
    (hy : ∀ y ∈ tids s, (∀ o, Pend H lin y o → Pend H' lin' y o) ∧ (∀ r, Post H lin y r → Post H' lin' y r)) :
    ThreadOK nc H' lin' s ol := by
  cases ol with
  | none => exact h
  | some l =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨h1, h2, ?_, ?_, h5⟩
    · intro x o hp
      exact (hy x (List.mem_append_left _ (pending_mem_ids hp))).1 o (h3 x o hp)
    · intro x r hp
      exact (hy x (List.mem_append_left _ (post_mem_ids hp))).2 r (h4 x r hp)

theorem GInv.step {spec : Spec Nat Op Res} {v0 : Nat} {nc : Bool} {m : Mem} {threads : Array (Option Loc)}
    {steps : Nat} {lin : List LE} {phs : Nat → Ph × List COp}
    (g : GInv spec v0 nc m threads steps lin phs)
    {t : Nat} (ht : t < threads.size) {m' : Mem} {lin' : List LE} {s' : Ph × List COp} {ol' : Option Loc}
    (hN : (m'.history.toList.map (·.id)).Nodup)
    (hlinN : (lin'.map (·.id)).Nodup)
    (hlinRec : ∀ e ∈ lin', ∃ h ∈ m'.history.toList, h.id = e.id ∧ h.op = e.op ∧ h.invoke < e.lp)
    (hord : lin'.Pairwise (fun a b => a.lp < b.lp))
    (hans : ∀ h ∈ m'.history.toList, (h.ret = none ∧ h.outcome = none) ∨
      (∃ rt, ∃ e ∈ lin', h.ret = some rt ∧ e.id = h.id ∧ h.outcome = some (.ok e.res) ∧ e.lp < rt))
    (hruns : RunsTo spec v0 lin' m'.val)
    (hinv : ∀ h ∈ m'.history.toList, h.invoke < steps + 1)
    (hlp : ∀ e ∈ lin', e.lp < steps + 1)
    (hw : ∀ w ∈ m'.watches, w.2 = .record)
    (hT : ThreadOK nc m'.history.toList lin' s' ol')
    (hother : ∀ y, (∃ i, i ≠ t ∧ y ∈ tids (phs i)) →
      (∀ o, Pend m.history.toList lin y o → Pend m'.history.toList lin' y o) ∧
      (∀ r, Post m.history.toList lin y r → Post m'.history.toList lin' y r))
    (hsub : ∀ y ∈ tids s', y ∈ tids (phs t))
    (hnd : (tids s').Nodup)
    (hfresh : ∀ i, ∀ y ∈ (if i = t then s' else phs i).2.flatMap COp.ids, y ∉ m'.history.toList.map (·.id)) :
    GInv spec v0 nc m' (threads.set! t ol') (steps + 1) lin' (fun i => if i = t then s' else phs i) where
  hNodup := hN
  linNodup := hlinN
  linRec := hlinRec
  linOrder := hord
  answered := hans
  runs := hruns
  invokeLt := hinv
  lpLt := hlp
  watchesRecord := hw
  threadOK := by
    intro i
    rw [getD_set _ _ _ _ ht]
    by_cases hi : i = t
    · simp only [hi, ↓reduceIte]; exact hT
    · simp only [hi, ↓reduceIte]
      exact ThreadOK.transfer (g.threadOK i) (fun y hy => hother y ⟨i, hi, hy⟩)
  disjoint := by
    intro t1 t2 x h1 h2
    have h1' : x ∈ tids (phs t1) := by
      by_cases e : t1 = t
      · simp only [e, ↓reduceIte] at h1; rw [e]; exact hsub x h1
      · simpa [e] using h1
    have h2' : x ∈ tids (phs t2) := by
      by_cases e : t2 = t
      · simp only [e, ↓reduceIte] at h2; rw [e]; exact hsub x h2
      · simpa [e] using h2
    exact g.disjoint t1 t2 x h1' h2'
  nodup := by
    intro i
    by_cases e : i = t
    · simp only [e, ↓reduceIte]; exact hnd
    · simp only [e, ↓reduceIte]; exact g.nodup i
  restFresh := hfresh
  not1000 := by
    intro i
    by_cases e : i = t
    · simp only [e, ↓reduceIte]; intro hc; exact g.not1000 t (hsub _ hc)
    · simp only [e, ↓reduceIte]; exact g.not1000 i

/-! ## The five kinds of steps -/

variable {spec : Spec Nat Op Res} {v0 : Nat} {nc : Bool} {m : Mem} {threads : Array (Option Loc)}
    {steps : Nat} {lin : List LE} {phs : Nat → Ph × List COp} {t : Nat}

theorem tids_eq {s s' : Ph × List COp} (h1 : s'.1.ids = s.1.ids)
    (h2 : s'.2.flatMap COp.ids = s.2.flatMap COp.ids) : tids s' = tids s := by
  simp [tids, h1, h2]

/-- Ids of another thread are not this thread's. -/
theorem GInv.other_ne (g : GInv spec v0 nc m threads steps lin phs) {x y : Nat} {i : Nat}
    (hx : x ∈ tids (phs t)) (hi : i ≠ t) (hy : y ∈ tids (phs i)) : y ≠ x := by
  intro e; subst e; exact hi (g.disjoint i t y hy hx)

/-- A step that changes neither the history, the value nor the points (locks, loads, watch calls,
the failed CAS of a `swap!` that retries). -/
theorem GInv.neutral (g : GInv spec v0 nc m threads steps lin phs) (ht : t < threads.size)
    {m' : Mem} (hm : m'.history = m.history) (hv : m'.val = m.val) (hw : ∀ w ∈ m'.watches, w.2 = .record)
    {s' : Ph × List COp} {l' : Loc}
    (hT : ThreadOK nc m.history.toList lin s' (some l'))
    (h1 : s'.1.ids = (phs t).1.ids) (h2 : s'.2.flatMap COp.ids = (phs t).2.flatMap COp.ids) :
    GInv spec v0 nc m' (threads.set! t (some l')) (steps + 1) lin (fun i => if i = t then s' else phs i) := by
  have hte := tids_eq h1 h2
  refine g.step ht ?_ g.linNodup ?_ g.linOrder ?_ ?_ ?_ ?_ hw ?_ ?_ ?_ ?_ ?_
  · rw [hm]; exact g.hNodup
  · rw [hm]; exact g.linRec
  · rw [hm]; exact g.answered
  · rw [hv]; exact g.runs
  · rw [hm]; intro h hh; have := g.invokeLt h hh; omega
  · intro e he; have := g.lpLt e he; omega
  · rw [hm]; exact hT
  · intro y _; rw [hm]; exact ⟨fun _ h => h, fun _ h => h⟩
  · intro y hy; rw [← hte]; exact hy
  · rw [hte]; exact g.nodup t
  · intro i y hy
    rw [hm]
    by_cases e : i = t
    · simp only [e, ↓reduceIte] at hy; rw [h2] at hy; exact g.restFresh t y hy
    · simp only [e, ↓reduceIte] at hy; exact g.restFresh i y hy

/-- The `invoke` step of operation `x` (the head of the thread's program): its record is pushed. -/
theorem GInv.invoke (g : GInv spec v0 nc m threads steps lin phs) (ht : t < threads.size)
    {c : COp} {cs : List COp} (hph : phs t = (.idle, c :: cs)) {x : Nat} (hx : c.ids = [x]) (o : Op)
    (nd : Nat) {m' : Mem}
    (hm : m'.history = m.history.push { id := x, node := nd, op := o, invoke := steps })
    (hv : m'.val = m.val) (hw : m'.watches = m.watches)
    {l' : Loc}
    (hT : ThreadOK nc (m.history.toList ++ [{ id := x, node := nd, op := o, invoke := steps }]) lin
      (c.first, cs) (some l'))
    (hfirst : c.first.ids = [x]) :
    GInv spec v0 nc m' (threads.set! t (some l')) (steps + 1) lin (fun i => if i = t then (c.first, cs) else phs i) := by
  have hxt : x ∈ tids (phs t) := by rw [hph]; simp [tids, hx, Ph.ids]
  have hxfresh : x ∉ m.history.toList.map (·.id) := g.restFresh t x (by rw [hph]; simp [hx])
  have hHt : m'.history.toList = m.history.toList ++ [{ id := x, node := nd, op := o, invoke := steps }] := by
    rw [hm]; simp
  have hte : tids (c.first, cs) = tids (phs t) := by
    rw [hph]; simp only [tids, hfirst]; simp [hx, Ph.ids]
  refine g.step ht ?_ g.linNodup ?_ g.linOrder ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hHt, List.map_append, List.nodup_append]
    refine ⟨g.hNodup, by simp, ?_⟩
    intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hxfresh ha
  · rw [hHt]; intro e he
    obtain ⟨h, hh, h1, h2, h3⟩ := g.linRec e he
    exact ⟨h, List.mem_append_left _ hh, h1, h2, h3⟩
  · rw [hHt]; intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact g.answered h hh
    · simp at hh; subst hh; left; exact ⟨rfl, rfl⟩
  · rw [hv]; exact g.runs
  · rw [hHt]; intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · have := g.invokeLt h hh; omega
    · simp at hh; subst hh; simp
  · intro e he; have := g.lpLt e he; omega
  · rw [hw]; exact g.watchesRecord
  · rw [hHt]; exact hT
  · intro y _
    rw [hHt]
    refine ⟨fun o' ⟨⟨h, hh, h1⟩, h2⟩ => ⟨⟨h, List.mem_append_left _ hh, h1⟩, h2⟩,
      fun r ⟨⟨h, hh, h1⟩, h2⟩ => ⟨⟨h, List.mem_append_left _ hh, h1⟩, h2⟩⟩
  · intro y hy; rw [← hte]; exact hy
  · rw [hte]; exact g.nodup t
  · intro i y hy
    rw [hHt, List.map_append]
    simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or]
    by_cases e : i = t
    · simp only [e, ↓reduceIte] at hy
      have hy' : y ∈ (phs t).2.flatMap COp.ids := by rw [hph]; simp only [List.flatMap_cons, hx]; simp [hy]
      refine ⟨by simpa using g.restFresh t y hy', ?_⟩
      intro ⟨a, ha, hay⟩; subst ha; simp at hay
      -- y = x, but x is the head's id and the rest's ids are distinct from it
      have hnd : (x :: cs.flatMap COp.ids).Nodup := by
        have := g.nodup t; rw [hph] at this; simpa [tids, Ph.ids, hx] using this
      exact (List.nodup_cons.mp hnd).1 (by rw [hay]; exact hy)
    · simp only [e, ↓reduceIte] at hy
      refine ⟨by simpa using g.restFresh i y hy, ?_⟩
      intro ⟨a, ha, hay⟩; subst ha; simp at hay
      exact g.other_ne hxt e (List.mem_append_right _ hy) hay.symm

/-- The linearization point of the thread's pending operation `x`: the value moves by the
specification, the point is appended. -/
theorem GInv.lp (g : GInv spec v0 nc m threads steps lin phs) (ht : t < threads.size) {l : Loc}
    (hl : threads.getD t none = some l) {x : Nat} {o : Op} (hpre : (phs t).1.pending = some (x, o))
    {m' : Mem} (hm : m'.history = m.history) (hw : ∀ w ∈ m'.watches, w.2 = .record)
    {r : Res} (hspec : spec m.val o m'.val r)
    {s' : Ph × List COp} {l' : Loc}
    (hins : l'.instrs = s'.1.instrs ++ restInstrs s'.2) (hloc : LocOK s'.1 l')
    (hpost : s'.1.post = some (x, r)) (hpend : s'.1.pending = none)
    (hnc : nc = true → s'.1.noCas = true)
    (h1 : s'.1.ids = (phs t).1.ids) (h2 : s'.2 = (phs t).2) :
    GInv spec v0 nc m' (threads.set! t (some l')) (steps + 1) (lin ++ [⟨x, o, r, steps⟩])
      (fun i => if i = t then s' else phs i) := by
  have hT0 := g.threadOK t
  rw [hl] at hT0
  obtain ⟨_, _, hp, _, hnc0⟩ := hT0
  obtain ⟨⟨h0, hh0, hid0, hret0, hop0⟩, hxlin⟩ := hp x o hpre
  have hxt : x ∈ tids (phs t) := List.mem_append_left _ (pending_mem_ids hpre)
  have hte : tids s' = tids (phs t) := tids_eq h1 (by rw [h2])
  refine g.step ht ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hw ?_ ?_ ?_ ?_ ?_
  · rw [hm]; exact g.hNodup
  · rw [List.map_append, List.nodup_append]
    refine ⟨g.linNodup, by simp, ?_⟩
    intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hxlin ha
  · rw [hm]; intro e he
    rcases List.mem_append.mp he with he | he
    · exact g.linRec e he
    · simp at he; subst he
      exact ⟨h0, hh0, hid0, hop0, g.invokeLt h0 hh0⟩
  · rw [List.pairwise_append]
    refine ⟨g.linOrder, by simp, ?_⟩
    intro a ha b hb; simp at hb; subst hb; exact g.lpLt a ha
  · rw [hm]; intro h hh
    rcases g.answered h hh with h' | ⟨rt, e, he, h3⟩
    · exact Or.inl h'
    · exact Or.inr ⟨rt, e, List.mem_append_left _ he, h3⟩
  · exact RunsTo.append spec v0 lin m.val ⟨x, o, r, steps⟩ m'.val g.runs hspec
  · rw [hm]; intro h hh; have := g.invokeLt h hh; omega
  · intro e he
    rcases List.mem_append.mp he with he | he
    · have := g.lpLt e he; omega
    · simp at he; subst he; simp
  · rw [hm]
    refine ⟨hins, hloc, ?_, ?_, ?_⟩
    · intro x' o' h; rw [hpend] at h; cases h
    · intro x' r' h
      rw [hpost] at h
      injection h with h; injection h with hx hr; subst hx; subst hr
      exact ⟨⟨h0, hh0, hid0, hret0⟩, ⟨x, o, r, steps⟩, by simp, rfl, rfl⟩
    · intro hc; exact ⟨hnc hc, by rw [h2]; exact (hnc0 hc).2⟩
  · intro y ⟨i, hi, hy⟩
    have hyx : y ≠ x := g.other_ne hxt hi hy
    rw [hm]
    refine ⟨fun o' ⟨hr, hn⟩ => ⟨hr, ?_⟩, fun r' ⟨hr, e, he, h3⟩ => ⟨hr, e, List.mem_append_left _ he, h3⟩⟩
    simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton, not_or]
    exact ⟨hn, hyx⟩
  · intro y hy; rw [← hte]; exact hy
  · rw [hte]; exact g.nodup t
  · intro i y hy
    rw [hm]
    by_cases e : i = t
    · simp only [e, ↓reduceIte] at hy; rw [h2] at hy; exact g.restFresh t y hy
    · simp only [e, ↓reduceIte] at hy; exact g.restFresh i y hy

/-- The history's answer function (`Jank.Atom.answer`). -/
def ansF (x : Nat) (r : Res) (stamp : Nat) (h : OpRec Op Res) : OpRec Op Res :=
  if h.id == x && h.ret.isNone then { h with ret := some stamp, outcome := some (.ok r) } else h

theorem ansF_id (x : Nat) (r : Res) (st : Nat) (h : OpRec Op Res) : (ansF x r st h).id = h.id := by
  unfold ansF; split <;> rfl

theorem ansF_ne (x : Nat) (r : Res) (st : Nat) (h : OpRec Op Res) (hne : h.id ≠ x) : ansF x r st h = h := by
  unfold ansF; simp [hne]

theorem ansF_self (x : Nat) (r : Res) (st : Nat) (h : OpRec Op Res) (hc : ¬(h.id = x ∧ h.ret = none)) :
    ansF x r st h = h := by
  unfold ansF
  split
  · rename_i hh
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hh
    exact absurd hh hc
  · rfl

/-- The answer of the thread's operation `x` with `r`. -/
theorem GInv.ret (g : GInv spec v0 nc m threads steps lin phs) (ht : t < threads.size) {l : Loc}
    (hl : threads.getD t none = some l) {x : Nat} {r : Res} {o n : Nat} {rest : List COp}
    (hph : phs t = (.nfC x r o n [] false, rest))
    {m' : Mem} (hm : m'.history.toList = m.history.toList.map (ansF x r steps))
    (hv : m'.val = m.val) (hw : m'.watches = m.watches) {l' : Loc} (hins : l'.instrs = restInstrs rest) :
    GInv spec v0 nc m' (threads.set! t (some l')) (steps + 1) lin
      (fun i => if i = t then (.idle, rest) else phs i) := by
  have hT0 := g.threadOK t
  rw [hl, hph] at hT0
  obtain ⟨_, _, _, hpo, hnc0⟩ := hT0
  obtain ⟨⟨h0, hh0, hid0, hret0⟩, ⟨e0, he0, hide0, hres0⟩⟩ := hpo x r rfl
  have hxt : x ∈ tids (phs t) := by rw [hph]; simp [tids, Ph.ids]
  have hids : m'.history.toList.map (·.id) = m.history.toList.map (·.id) := by
    rw [hm, List.map_map]; congr 1; funext h; exact ansF_id x r steps h
  refine g.step ht ?_ g.linNodup ?_ g.linOrder ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hids]; exact g.hNodup
  · rw [hm]; intro e he
    obtain ⟨h, hh, h1, h2, h3⟩ := g.linRec e he
    refine ⟨ansF x r steps h, List.mem_map_of_mem hh, ?_, ?_, ?_⟩ <;> unfold ansF <;> split <;> simp_all
  · rw [hm]; intro h' hh'
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hh'
    by_cases hc : h.id = x ∧ h.ret = none
    · right
      refine ⟨steps, e0, he0, ?_, ?_, ?_, g.lpLt e0 he0⟩ <;> simp [ansF, hc, hide0, hres0]
    · rw [ansF_self x r steps h hc]; exact g.answered h hh
  · rw [hv]; exact g.runs
  · rw [hm]; intro h' hh'
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hh'
    have := g.invokeLt h hh
    unfold ansF; split <;> simp <;> omega
  · intro e he; have := g.lpLt e he; omega
  · rw [hw]; exact g.watchesRecord
  · refine ⟨by simp [Ph.instrs, hins], trivial, ?_, ?_, ?_⟩
    · intro _ _ h; cases h
    · intro _ _ h; cases h
    · intro hc; exact ⟨rfl, (hnc0 hc).2⟩
  · intro y ⟨i, hi, hy⟩
    have hyx : y ≠ x := g.other_ne hxt hi hy
    rw [hm]
    refine ⟨fun o' ⟨⟨h, hh, h1, h2, h3⟩, hn⟩ => ⟨⟨h, ?_, h1, h2, h3⟩, hn⟩,
      fun r' ⟨⟨h, hh, h1, h2⟩, h3⟩ => ⟨⟨h, ?_, h1, h2⟩, h3⟩⟩
    · rw [← ansF_ne x r steps h (h1 ▸ hyx)]; exact List.mem_map_of_mem hh
    · rw [← ansF_ne x r steps h (h1 ▸ hyx)]; exact List.mem_map_of_mem hh
  · intro y hy; rw [hph]; simp [tids, Ph.ids] at hy ⊢; exact Or.inr hy
  · have := g.nodup t; rw [hph] at this; simp [tids, Ph.ids] at this ⊢; exact this.2
  · intro i y hy
    rw [hids]
    by_cases e : i = t
    · simp only [e, ↓reduceIte] at hy
      exact g.restFresh t y (by rw [hph]; exact hy)
    · simp only [e, ↓reduceIte] at hy; exact g.restFresh i y hy

theorem Ph.instrs_ne_nil (ph : Ph) (h : ph ≠ .idle) : ph.instrs ≠ [] := by
  cases ph <;> simp_all [Ph.instrs]

theorem COp.instrs_ne_nil (c : COp) : c.instrs ≠ [] := by
  cases c <;> simp [COp.instrs, addWatch]

/-- A thread with nothing left ends. -/
theorem GInv.done (g : GInv spec v0 nc m threads steps lin phs) (ht : t < threads.size) {l : Loc}
    (hl : threads.getD t none = some l) (hnil : l.instrs = []) :
    GInv spec v0 nc m (threads.set! t none) (steps + 1) lin phs := by
  have hT0 := g.threadOK t
  rw [hl] at hT0
  obtain ⟨hi, _⟩ := hT0
  rw [hnil] at hi
  have hph : (phs t).1 = .idle := by
    have hnil2 : (phs t).1.instrs = [] := (List.append_eq_nil_iff.mp hi.symm).1
    cases hp : (phs t).1 <;> rw [hp] at hnil2 <;> simp [Ph.instrs] at hnil2 ⊢
  have hrest : (phs t).2 = [] := by
    rw [hph] at hi
    cases hh : (phs t).2 with
    | nil => rfl
    | cons c cs =>
      rw [hh, restInstrs_cons] at hi
      have := COp.instrs_ne_nil c
      cases hc : c.instrs with
      | nil => exact absurd hc this
      | cons a as => rw [hc] at hi; simp [Ph.instrs] at hi
  have hfun : (fun i => if i = t then phs t else phs i) = phs := by funext i; split <;> simp_all
  have := g.step (m' := m) (lin' := lin) (s' := phs t) (ol' := none) ht g.hNodup g.linNodup g.linRec g.linOrder
    g.answered g.runs (fun h hh => by have := g.invokeLt h hh; omega) (fun e he => by have := g.lpLt e he; omega)
    g.watchesRecord ⟨hph, hrest⟩ (fun y _ => ⟨fun _ h => h, fun _ h => h⟩) (fun y hy => hy) (g.nodup t)
    (fun i y hy => by
      by_cases e : i = t
      · simp only [e, ↓reduceIte] at hy; exact g.restFresh t y hy
      · simp only [e, ↓reduceIte] at hy; exact g.restFresh i y hy)
  rw [hfun] at this
  exact this

/-! ## The locks: who holds or waits for them (for deadlock freedom) -/

def Ph.isW : Ph → Bool
  | .wD _ | .wU => true
  | _ => false

def Ph.isL : Ph → Bool
  | .wL _ => true
  | _ => false

def Ph.isR : Ph → Bool
  | .nfC _ _ _ _ _ true => true
  | _ => false

open Jank.Sync in
/-- The validator lock is never taken exclusively; the watches lock is held exclusively by a
thread adding a watch, waited for by threads that announced themselves, and held shared by
threads calling the watches (jank). The Clojure mode never touches it. -/
structure MInv (m : Mem) (phs : Nat → Ph × List COp) : Prop where
  vW : m.validatorMutex.writer = none
  vQ : m.validatorMutex.waiting = []
  clj : m.clojure = true → m.watchesMutex.writer = none ∧ m.watchesMutex.waiting = [] ∧ m.watchesMutex.readers = []
  wW : ∀ w, m.watchesMutex.writer = some w → (phs w).1.isW = true
  wQ : ∀ w ∈ m.watchesMutex.waiting, (phs w).1.isL = true
  wQN : m.watchesMutex.waiting.Nodup
  wR : ∀ r ∈ m.watchesMutex.readers, (phs r).1.isR = true
  wRN : m.watchesMutex.readers.Nodup

open Jank.Sync

theorem lockShared_eq {mx vm : SharedMutex} {t : Nat} (h : mx.lockShared t = some vm) :
    vm = { mx with readers := t :: mx.readers } ∧ mx.writer = none ∧ mx.waiting = [] := by
  unfold SharedMutex.lockShared at h
  split at h
  · rename_i hc; injection h with h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at hc
    exact ⟨h.symm, hc.1, hc.2⟩
  · cases h

theorem lock_eq {mx vm : SharedMutex} {t : Nat} (h : mx.lock t = some vm) :
    vm = { mx with writer := some t, waiting := mx.waiting.erase t } ∧ mx.writer = none ∧ mx.readers = [] := by
  unfold SharedMutex.lock at h
  split at h
  · rename_i hc; injection h with h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff] at hc
    exact ⟨h.symm, hc.1, hc.2⟩
  · cases h

variable {m : Mem} {phs : Nat → Ph × List COp} {t : Nat}

/-- A step that leaves the watches lock alone. -/
theorem MInv.same (h : MInv m phs) {m' : Mem} (hv1 : m'.validatorMutex.writer = m.validatorMutex.writer)
    (hv2 : m'.validatorMutex.waiting = m.validatorMutex.waiting) (hw : m'.watchesMutex = m.watchesMutex)
    (hc : m'.clojure = m.clojure) {s' : Ph × List COp}
    (hW : (phs t).1.isW = true → s'.1.isW = true) (hL : (phs t).1.isL = true → s'.1.isL = true)
    (hR : (phs t).1.isR = true → s'.1.isR = true) :
    MInv m' (fun i => if i = t then s' else phs i) where
  vW := by rw [hv1]; exact h.vW
  vQ := by rw [hv2]; exact h.vQ
  clj := by rw [hw, hc]; exact h.clj
  wW := by
    intro w hw'; rw [hw] at hw'
    by_cases e : w = t
    · subst e; simp only [↓reduceIte]; exact hW (h.wW w hw')
    · simp only [e, ↓reduceIte]; exact h.wW w hw'
  wQ := by
    intro w hw'; rw [hw] at hw'
    by_cases e : w = t
    · subst e; simp only [↓reduceIte]; exact hL (h.wQ w hw')
    · simp only [e, ↓reduceIte]; exact h.wQ w hw'
  wQN := by rw [hw]; exact h.wQN
  wR := by
    intro w hw'; rw [hw] at hw'
    by_cases e : w = t
    · subst e; simp only [↓reduceIte]; exact hR (h.wR w hw')
    · simp only [e, ↓reduceIte]; exact h.wR w hw'
  wRN := by rw [hw]; exact h.wRN

/-- In the Clojure mode the watches lock stays free: any phases. -/
theorem MInv.cljMode (h : MInv m phs) (hcl : m.clojure = true) {m' : Mem}
    (hv1 : m'.validatorMutex.writer = m.validatorMutex.writer)
    (hv2 : m'.validatorMutex.waiting = m.validatorMutex.waiting) (hw : m'.watchesMutex = m.watchesMutex)
    (hc : m'.clojure = m.clojure) (phs' : Nat → Ph × List COp) : MInv m' phs' := by
  obtain ⟨h1, h2, h3⟩ := h.clj hcl
  refine ⟨by rw [hv1]; exact h.vW, by rw [hv2]; exact h.vQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; rw [hw]; exact ⟨h1, h2, h3⟩
  · intro w hw'; rw [hw, h1] at hw'; cases hw'
  · intro w hw'; rw [hw, h2] at hw'; cases hw'
  · rw [hw, h2]; exact List.nodup_nil
  · intro w hw'; rw [hw, h3] at hw'; cases hw'
  · rw [hw, h3]; exact List.nodup_nil

theorem MInv.notR (h : MInv m phs) (hr : (phs t).1.isR = false) : t ∉ m.watchesMutex.readers := by
  intro hc; have := h.wR t hc; rw [hr] at this; cases this

theorem MInv.notL (h : MInv m phs) (hr : (phs t).1.isL = false) : t ∉ m.watchesMutex.waiting := by
  intro hc; have := h.wQ t hc; rw [hr] at this; cases this

theorem MInv.notW (h : MInv m phs) (hr : (phs t).1.isW = false) : m.watchesMutex.writer ≠ some t := by
  intro hc; have := h.wW t hc; rw [hr] at this; cases this

/-- `notifyLock` (jank): the watches lock taken shared. -/
theorem MInv.lockShared (h : MInv m phs) {m' : Mem} {wm : SharedMutex}
    (hlk : m.watchesMutex.lockShared t = some wm) (hm : m'.watchesMutex = wm)
    (hv1 : m'.validatorMutex = m.validatorMutex) (hc : m'.clojure = m.clojure) (hcl0 : m.clojure = false)
    {s' : Ph × List COp}
    (hold : (phs t).1.isR = false ∧ (phs t).1.isW = false ∧ (phs t).1.isL = false) (hnew : s'.1.isR = true) :
    MInv m' (fun i => if i = t then s' else phs i) := by
  obtain ⟨hwm, hwr, hwq⟩ := lockShared_eq hlk
  subst hwm
  have htn := h.notR hold.1
  refine ⟨by rw [hv1]; exact h.vW, by rw [hv1]; exact h.vQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcl; rw [hc, hcl0] at hcl; cases hcl
  · intro w hw; rw [hm] at hw; simp [hwr] at hw
  · intro w hw; rw [hm] at hw; simp [hwq] at hw
  · rw [hm]; simp [hwq]
  · intro r hr; rw [hm] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · simp [hnew]
    · have hne : r ≠ t := fun e => htn (e ▸ hr)
      simp only [hne, ↓reduceIte]; exact h.wR r hr
  · rw [hm]; exact List.nodup_cons.mpr ⟨htn, h.wRN⟩

/-- `notifyUnlock`: the shared hold released. -/
theorem MInv.unlockShared (h : MInv m phs) {m' : Mem} (hm : m'.watchesMutex = m.watchesMutex.unlockShared t)
    (hv1 : m'.validatorMutex = m.validatorMutex) (hc : m'.clojure = m.clojure) {s' : Ph × List COp}
    (hold : (phs t).1.isW = false ∧ (phs t).1.isL = false) :
    MInv m' (fun i => if i = t then s' else phs i) := by
  have hnW := h.notW hold.1
  have hnL := h.notL hold.2
  refine ⟨by rw [hv1]; exact h.vW, by rw [hv1]; exact h.vQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcl; rw [hc] at hcl; obtain ⟨h1, h2, h3⟩ := h.clj hcl; rw [hm]; simp [SharedMutex.unlockShared, h1, h2, h3]
  · intro w hw; rw [hm] at hw
    simp only [SharedMutex.unlockShared] at hw
    have hne : w ≠ t := fun e => hnW (e ▸ hw)
    simp only [hne, ↓reduceIte]; exact h.wW w hw
  · intro w hw; rw [hm] at hw
    simp only [SharedMutex.unlockShared] at hw
    have hne : w ≠ t := fun e => hnL (e ▸ hw)
    simp only [hne, ↓reduceIte]; exact h.wQ w hw
  · rw [hm]; exact h.wQN
  · intro r hr; rw [hm] at hr
    simp only [SharedMutex.unlockShared] at hr
    have := (List.Nodup.mem_erase_iff h.wRN).mp hr
    simp only [this.1, ↓reduceIte]; exact h.wR r this.2
  · rw [hm]; exact h.wRN.erase t

/-- `watchAnnounce` (jank): the thread waits for the watches lock. -/
theorem MInv.announce (h : MInv m phs) {m' : Mem} (hm : m'.watchesMutex = m.watchesMutex.announce t)
    (hv1 : m'.validatorMutex = m.validatorMutex) (hc : m'.clojure = m.clojure) (hcl : m.clojure = false)
    {s' : Ph × List COp}
    (hold : (phs t).1.isR = false ∧ (phs t).1.isW = false ∧ (phs t).1.isL = false) (hnew : s'.1.isL = true) :
    MInv m' (fun i => if i = t then s' else phs i) := by
  have hnL := h.notL hold.2.2
  have hnW := h.notW hold.2.1
  have hnR := h.notR hold.1
  have hann : m.watchesMutex.announce t = { m.watchesMutex with waiting := m.watchesMutex.waiting ++ [t] } := by
    simp [SharedMutex.announce, hnL]
  rw [hann] at hm
  refine ⟨by rw [hv1]; exact h.vW, by rw [hv1]; exact h.vQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hc'; rw [hc, hcl] at hc'; cases hc'
  · intro w hw; rw [hm] at hw
    have hne : w ≠ t := fun e => hnW (e ▸ hw)
    simp only [hne, ↓reduceIte]; exact h.wW w hw
  · intro w hw; rw [hm] at hw
    rcases List.mem_append.mp hw with hw | hw
    · have hne : w ≠ t := fun e => hnL (e ▸ hw)
      simp only [hne, ↓reduceIte]; exact h.wQ w hw
    · simp at hw; subst hw; simp [hnew]
  · rw [hm, List.nodup_append]
    exact ⟨h.wQN, by simp, by intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hnL ha⟩
  · intro r hr; rw [hm] at hr
    have hne : r ≠ t := fun e => hnR (e ▸ hr)
    simp only [hne, ↓reduceIte]; exact h.wR r hr
  · rw [hm]; exact h.wRN

/-- `watchLock` (jank): the thread takes the watches lock. -/
theorem MInv.lock (h : MInv m phs) {m' : Mem} {wm : SharedMutex}
    (hlk : m.watchesMutex.lock t = some wm) (hm : m'.watchesMutex = wm)
    (hv1 : m'.validatorMutex = m.validatorMutex) (hc : m'.clojure = m.clojure) (hcl0 : m.clojure = false)
    {s' : Ph × List COp} (hnew : s'.1.isW = true) :
    MInv m' (fun i => if i = t then s' else phs i) := by
  obtain ⟨hwm, hwr, hrd⟩ := lock_eq hlk
  subst hwm
  refine ⟨by rw [hv1]; exact h.vW, by rw [hv1]; exact h.vQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcl; rw [hc, hcl0] at hcl; cases hcl
  · intro w hw; rw [hm] at hw; simp at hw; subst hw; simp [hnew]
  · intro w hw; rw [hm] at hw
    have := (List.Nodup.mem_erase_iff h.wQN).mp hw
    simp only [this.1, ↓reduceIte]; exact h.wQ w this.2
  · rw [hm]; exact h.wQN.erase t
  · intro r hr; rw [hm] at hr; simp [hrd] at hr
  · rw [hm]; simp [hrd]

/-- `watchUnlock` (jank): the watches lock released. -/
theorem MInv.unlock (h : MInv m phs) {m' : Mem} (hm : m'.watchesMutex = m.watchesMutex.unlock)
    (hv1 : m'.validatorMutex = m.validatorMutex) (hc : m'.clojure = m.clojure) {s' : Ph × List COp}
    (hold : (phs t).1.isR = false ∧ (phs t).1.isL = false) :
    MInv m' (fun i => if i = t then s' else phs i) := by
  have hnL := h.notL hold.2
  have hnR := h.notR hold.1
  refine ⟨by rw [hv1]; exact h.vW, by rw [hv1]; exact h.vQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcl; rw [hc] at hcl; obtain ⟨h1, h2, h3⟩ := h.clj hcl; rw [hm]; simp [SharedMutex.unlock, h2, h3]
  · intro w hw; rw [hm] at hw; simp [SharedMutex.unlock] at hw
  · intro w hw; rw [hm] at hw
    simp only [SharedMutex.unlock] at hw
    have hne : w ≠ t := fun e => hnL (e ▸ hw)
    simp only [hne, ↓reduceIte]; exact h.wQ w hw
  · rw [hm]; exact h.wQN
  · intro r hr; rw [hm] at hr
    simp only [SharedMutex.unlock] at hr
    have hne : r ≠ t := fun e => hnR (e ▸ hr)
    simp only [hne, ↓reduceIte]; exact h.wR r hr
  · rw [hm]; exact h.wRN

end Jank.R3.Proofs.AtomLin

-- SPDX-License-Identifier: GPL-3.0-or-later WITH GCC-exception-3.1 (with round 3's regex replica; see README.md)
import Jank.R3.Regex.Executor

/-!
# libstdc++'s DFS executor keeps `_M_results` until a solution (for every NFA and input)

Round 4 kept this proof aside unfinished (`.r4-scratch/regex/ExecInv.lean.unfinished`): a tactic
walk over the replica's `dfs` left goals. Here it is done by small combinators instead of one walk.

`_M_results` is written only by `_M_handle_accept` (regex_executor.tcc 429–) when it accepts, and
that sets `_M_has_sol`. Once a call into `_M_dfs` returns with `_M_has_sol` set, the handler it
returns to either returns too or checks `_M_has_sol` before exploring again
(`_M_handle_repeat` 233–, `_M_handle_alternative` 507–: "If it's DFS executor and already
accepted, we're done"); a lookahead's sub-executor (`_M_lookahead` 186) has its own results and
flag, and the caller keeps its own. So a run that starts without a solution and ends without one
leaves `_M_results` as it found it (`dfs_keeps_res`), and therefore a start position of `_M_search`
that fails leaves `_M_results` unchanged (`searchFromFirst_fail_keeps_res`): the next position's
`_M_main_dispatch` starts again from `_M_cur_results = _M_results` (executor.tcc 91), so nothing a
failed position's lookahead copied into `_M_cur_results` survives into a later position's match.
With `searchFromFirst_starts_clean` (round 4), this makes U35's mechanism a statement about every
NFA, input, flag set and fuel: `search_later_position_starts_from_initial_results`.

Three properties of a computation `x : EM α` at a state `st` (only runs that return `.ok` count;
an aborted run, `.error`, is not a result):
- `Kat st x`: `x` keeps `hasSol` and `res`;
- `Gat st x`: started without a solution, `x` ends without one only with `res` unchanged;
- `Hat st x`: `Gat`, and started with a solution, `x` ends with one.

`dfs` is `G` (every state); the handlers' code after a call into `dfs` is `H`; the code before
it is `K`.
-/

namespace Jank.R5.Regex

open Jank.R3.Regex

def Kat {α : Type} (st : ExSt) (x : EM α) : Prop :=
  ∀ a st', x.run st = .ok (a, st') → st'.hasSol = st.hasSol ∧ st'.res = st.res

def Gat {α : Type} (st : ExSt) (x : EM α) : Prop :=
  st.hasSol = false → ∀ a st', x.run st = .ok (a, st') → st'.hasSol = false → st'.res = st.res

def Hat {α : Type} (st : ExSt) (x : EM α) : Prop :=
  Gat st x ∧ (st.hasSol = true → ∀ a st', x.run st = .ok (a, st') → st'.hasSol = true)

/-! ## The run of a bind -/

theorem run_bind_ok {α β : Type} {x : EM α} {f : α → EM β} {st : ExSt} {b : β} {st' : ExSt}
    (h : (x >>= f).run st = .ok (b, st')) :
    ∃ a s1, x.run st = .ok (a, s1) ∧ (f a).run s1 = .ok (b, st') := by
  rw [StateT.run_bind] at h
  cases hx : x.run st with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1, p.2, rfl, h⟩

/-! ## Combinators -/

theorem Kat.toH {α : Type} {st : ExSt} {x : EM α} (h : Kat st x) : Hat st x := by
  refine ⟨?_, ?_⟩
  · intro h0 a st' hr hf
    exact (h a st' hr).2
  · intro h0 a st' hr
    rw [(h a st' hr).1]; exact h0

theorem Hat.toG {α : Type} {st : ExSt} {x : EM α} (h : Hat st x) : Gat st x := h.1

theorem Kat_bind {α β : Type} {st : ExSt} {x : EM α} {f : α → EM β} (hx : Kat st x)
    (hf : ∀ a s1, x.run st = .ok (a, s1) → Kat s1 (f a)) : Kat st (x >>= f) := by
  intro b st' hr
  obtain ⟨a, s1, h1, h2⟩ := run_bind_ok hr
  obtain ⟨e1, e2⟩ := hx a s1 h1
  obtain ⟨e3, e4⟩ := hf a s1 h1 b st' h2
  exact ⟨e3.trans e1, e4.trans e2⟩

theorem Gat_bind_K {α β : Type} {st : ExSt} {x : EM α} {f : α → EM β} (hx : Kat st x)
    (hf : ∀ a s1, x.run st = .ok (a, s1) → Gat s1 (f a)) : Gat st (x >>= f) := by
  intro h0 b st' hr hend
  obtain ⟨a, s1, h1, h2⟩ := run_bind_ok hr
  obtain ⟨e1, e2⟩ := hx a s1 h1
  rw [hf a s1 h1 (e1.trans h0) b st' h2 hend, e2]

theorem Gat_bind_H {α β : Type} {st : ExSt} {x : EM α} {f : α → EM β} (hx : Gat st x)
    (hf : ∀ a s1, x.run st = .ok (a, s1) → Hat s1 (f a)) : Gat st (x >>= f) := by
  intro h0 b st' hr hend
  obtain ⟨a, s1, h1, h2⟩ := run_bind_ok hr
  cases hs : s1.hasSol with
  | true =>
    have := (hf a s1 h1).2 hs b st' h2
    rw [this] at hend; cases hend
  | false =>
    rw [(hf a s1 h1).1 hs b st' h2 hend, hx h0 a s1 h1 hs]

theorem Hat_bind {α β : Type} {st : ExSt} {x : EM α} {f : α → EM β} (hx : Hat st x)
    (hf : ∀ a s1, x.run st = .ok (a, s1) → Hat s1 (f a)) : Hat st (x >>= f) := by
  refine ⟨Gat_bind_H hx.1 hf, ?_⟩
  intro h0 b st' hr
  obtain ⟨a, s1, h1, h2⟩ := run_bind_ok hr
  exact (hf a s1 h1).2 (hx.2 h0 a s1 h1) b st' h2

theorem Kat_pure {α : Type} (st : ExSt) (v : α) : Kat st (pure v : EM α) := by
  intro a st' h
  cases h
  exact ⟨rfl, rfl⟩

theorem Kat_get (st : ExSt) : Kat st (get : EM ExSt) := by
  intro a st' h
  cases h
  exact ⟨rfl, rfl⟩

theorem get_run (st : ExSt) {a : ExSt} {s1 : ExSt} (h : (get : EM ExSt).run st = .ok (a, s1)) :
    a = st ∧ s1 = st := by
  cases h
  exact ⟨rfl, rfl⟩

theorem Kat_set (st s : ExSt) (h1 : s.hasSol = st.hasSol) (h2 : s.res = st.res) :
    Kat st (set s : EM PUnit) := by
  intro a st' h
  cases h
  exact ⟨h1, h2⟩

theorem Kat_modify (st : ExSt) (g : ExSt → ExSt) (h1 : (g st).hasSol = st.hasSol)
    (h2 : (g st).res = st.res) : Kat st (modify g : EM PUnit) := by
  intro a st' h
  cases h
  exact ⟨h1, h2⟩

theorem Kat_ethrow {α : Type} (st : ExSt) (e : Abort) : Kat st (ethrow e : EM α) := by
  intro a st' h
  cases h

theorem Gat_ethrow {α : Type} (st : ExSt) (e : Abort) : Gat st (ethrow e : EM α) :=
  (Kat_ethrow st e).toH.toG

theorem pure_ok {α : Type} {v w : α} (h : (pure v : Except Abort α) = .ok w) : v = w :=
  Except.ok.inj h

theorem nosol_of {b : Bool} (h : (!b) = true) : b = false := by simpa using h

theorem sol_of {b : Bool} (h : ¬ (!b) = true) : b = true := by simpa using h

/-! ## Steps (each for `Kat`, `Gat` and `Hat`) -/

theorem get_bind_run {α : Type} (f : ExSt → EM α) (st : ExSt) :
    (get >>= f).run st = (f st).run st := by
  simp only [StateT.run_bind, StateT.run_get]; rfl

theorem set_bind_run {α : Type} (v : ExSt) (x : PUnit → EM α) (st : ExSt) :
    (set v >>= x).run st = (x PUnit.unit).run v := by
  simp only [StateT.run_bind, StateT.run_set]; rfl

theorem modify_bind_run {α : Type} (g : ExSt → ExSt) (x : PUnit → EM α) (st : ExSt) :
    (modify g >>= x).run st = (x PUnit.unit).run (g st) := by
  simp only [StateT.run_bind, StateT.run_modify]; rfl

theorem Gat_get {α : Type} {f : ExSt → EM α} {st : ExSt} (h : Gat st (f st)) : Gat st (get >>= f) := by
  intro h0 a st' hr; rw [get_bind_run] at hr; exact h h0 a st' hr

theorem Hat_get {α : Type} {f : ExSt → EM α} {st : ExSt} (h : Hat st (f st)) : Hat st (get >>= f) := by
  refine ⟨Gat_get h.1, ?_⟩
  intro h0 a st' hr; rw [get_bind_run] at hr; exact h.2 h0 a st' hr

theorem Gat_set {α : Type} {v st : ExSt} {x : PUnit → EM α} (h1 : v.hasSol = st.hasSol)
    (h2 : v.res = st.res) (h : Gat v (x PUnit.unit)) : Gat st (set v >>= x) := by
  intro h0 a st' hr hend; rw [set_bind_run] at hr
  rw [h (h1.trans h0) a st' hr hend, h2]

theorem Hat_set {α : Type} {v st : ExSt} {x : PUnit → EM α} (h1 : v.hasSol = st.hasSol)
    (h2 : v.res = st.res) (h : Hat v (x PUnit.unit)) : Hat st (set v >>= x) := by
  refine ⟨Gat_set h1 h2 h.1, ?_⟩
  intro h0 a st' hr; rw [set_bind_run] at hr; exact h.2 (h1.trans h0) a st' hr

theorem Gat_modify {α : Type} {g : ExSt → ExSt} {st : ExSt} {x : PUnit → EM α}
    (h1 : (g st).hasSol = st.hasSol) (h2 : (g st).res = st.res) (h : Gat (g st) (x PUnit.unit)) :
    Gat st (modify g >>= x) := by
  intro h0 a st' hr hend; rw [modify_bind_run] at hr
  rw [h (h1.trans h0) a st' hr hend, h2]

theorem Hat_modify {α : Type} {g : ExSt → ExSt} {st : ExSt} {x : PUnit → EM α}
    (h1 : (g st).hasSol = st.hasSol) (h2 : (g st).res = st.res) (h : Hat (g st) (x PUnit.unit)) :
    Hat st (modify g >>= x) := by
  refine ⟨Gat_modify h1 h2 h.1, ?_⟩
  intro h0 a st' hr; rw [modify_bind_run] at hr; exact h.2 (h1.trans h0) a st' hr

theorem Hat_modify_end {g : ExSt → ExSt} {st : ExSt} (h1 : (g st).hasSol = st.hasSol)
    (h2 : (g st).res = st.res) : Hat st (modify g : EM PUnit) := by
  refine Kat.toH ?_
  intro a st' hr
  simp only [StateT.run_modify] at hr
  have := pure_ok hr
  cases this
  exact ⟨h1, h2⟩

theorem Hat_pure {α : Type} (st : ExSt) (v : α) : Hat st (pure v : EM α) := (Kat_pure st v).toH

theorem Gat_ethrow_bind {α β : Type} (st : ExSt) (e : Abort) (f : α → EM β) :
    Gat st (ethrow e >>= f) := by
  intro h0 a st' hr
  obtain ⟨_, _, h1, _⟩ := run_bind_ok hr
  cases h1

/-- After a call into `dfs`: the rest must be `H` (from every state). -/
theorem Gat_call {α β : Type} {st : ExSt} {y : EM α} {f : α → EM β} (hy : Gat st y)
    (hf : ∀ a s1, Hat s1 (f a)) : Gat st (y >>= f) :=
  Gat_bind_H hy (fun a s1 _ => hf a s1)

/-- A call explored only when there is no solution yet. -/
theorem Hat_of_nosol {α : Type} {st : ExSt} {y : EM α} (h0 : st.hasSol = false) (hy : Gat st y) :
    Hat st y := by
  refine ⟨hy, ?_⟩
  intro h; rw [h0] at h; cases h

/-- `_M_lookahead`: the sub-executor's state replaces the caller's, and the caller's comes back
with only `curRes`, the counters and the step count taken from the sub-run. -/
theorem Gat_look {α : Type} {st : ExSt} {v : ExSt} {y : EM PUnit} {w : ExSt → ExSt}
    {k : ExSt → PUnit → EM α} (hw1 : ∀ s, (w s).hasSol = st.hasSol) (hw2 : ∀ s, (w s).res = st.res)
    (hk : ∀ s, Gat (w s) (k s PUnit.unit)) :
    Gat st (set v >>= fun _ => y >>= fun _ => get >>= fun sub => set (w sub) >>= k sub) := by
  intro h0 a st' hr hend
  rw [set_bind_run] at hr
  obtain ⟨_, s2, _, h3⟩ := run_bind_ok hr
  rw [get_bind_run, set_bind_run] at h3
  rw [hk s2 ((hw1 s2).trans h0) a st' h3 hend, hw2]

/-- `_M_handle_accept` with a solution: the flag is set, and nothing after it clears it. -/
theorem Gat_set_sol {α : Type} {v st : ExSt} {x : PUnit → EM α} (h1 : v.hasSol = true)
    (h : Hat v (x PUnit.unit)) : Gat st (set v >>= x) := by
  intro h0 a st' hr hend; rw [set_bind_run] at hr
  rw [h.2 h1 a st' hr] at hend; cases hend

/-- `_M_handle_accept` without a solution: the flag is cleared, the results are kept. -/
theorem Gat_set_nosol {α : Type} {v st : ExSt} {x : PUnit → EM α} (h1 : v.hasSol = false)
    (h2 : v.res = st.res) (h : Gat v (x PUnit.unit)) : Gat st (set v >>= x) := by
  intro h0 a st' hr hend; rw [set_bind_run] at hr
  rw [h h1 a st' hr hend, h2]

theorem Gat_assoc {α β γ : Type} {st : ExSt} {x : EM α} {f : α → EM β} {g : β → EM γ}
    (h : Gat st (x >>= fun a => f a >>= g)) : Gat st ((x >>= f) >>= g) := by
  rw [bind_assoc]; exact h

theorem Hat_assoc {α β γ : Type} {st : ExSt} {x : EM α} {f : α → EM β} {g : β → EM γ}
    (h : Hat st (x >>= fun a => f a >>= g)) : Hat st ((x >>= f) >>= g) := by
  rw [bind_assoc]; exact h

theorem Gat_pure_bind {α β : Type} {st : ExSt} {v : α} {g : α → EM β} (h : Gat st (g v)) :
    Gat st (pure v >>= g) := by
  rw [pure_bind]; exact h

theorem Hat_pure_bind {α β : Type} {st : ExSt} {v : α} {g : α → EM β} (h : Hat st (g v)) :
    Hat st (pure v >>= g) := by
  rw [pure_bind]; exact h

theorem Gat_ite {α : Type} {st : ExSt} {c : Prop} [Decidable c] {a b : EM α}
    (ha : c → Gat st a) (hb : ¬ c → Gat st b) : Gat st (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem Hat_ite {α : Type} {st : ExSt} {c : Prop} [Decidable c] {a b : EM α}
    (ha : c → Hat st a) (hb : ¬ c → Hat st b) : Hat st (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

theorem Gat_setCurRes {α : Type} {st : ExSt} {k : Nat} {v : Sub} {x : PUnit → EM α}
    (h : Gat { st with curRes := st.curRes.set! k v } (x PUnit.unit)) :
    Gat st (setCurRes k v >>= x) := by
  unfold setCurRes; exact Gat_modify rfl rfl h

theorem Hat_setCurRes {α : Type} {st : ExSt} {k : Nat} {v : Sub} {x : PUnit → EM α}
    (h : Hat { st with curRes := st.curRes.set! k v } (x PUnit.unit)) :
    Hat st (setCurRes k v >>= x) := by
  unfold setCurRes; exact Hat_modify rfl rfl h

set_option hygiene false in
/-- One step of the walk over a handler: state operations (`K`), a call into `dfs` (by the
induction hypothesis `ih`, then `H` for the rest), a guarded call, the lookahead's sub-executor,
`_M_handle_accept`, and case splits. -/
macro "walk1" : tactic => `(tactic| first
  | (with_reducible refine Gat_ite (fun _ => ?_) (fun _ => ?_))
  | (with_reducible refine Hat_ite (fun _ => ?_) (fun _ => ?_))
  | (with_reducible exact Gat_ethrow_bind _ _ _)
  | (with_reducible exact ih _ _ _ _)
  | ((with_reducible refine Gat_call (ih _ _ _ _) ?_); intro _ _)
  | (with_reducible refine Hat_of_nosol (nosol_of ‹_›) ?_)
  | (with_reducible refine Gat_set (by rfl) (by rfl) ?_)
  | (with_reducible refine Hat_set (by rfl) (by rfl) ?_)
  | (with_reducible refine Gat_set_sol (by rfl) ?_)
  | ((with_reducible refine Gat_look (fun _ => by rfl) (fun _ => by rfl) ?_); intro _)
  | (with_reducible refine Gat_set_nosol (by rfl) (by rfl) ?_)
  | (with_reducible refine Gat_setCurRes ?_)
  | (with_reducible refine Hat_setCurRes ?_)
  | (with_reducible refine Gat_modify (by rfl) (by rfl) ?_)
  | (with_reducible refine Hat_modify (by rfl) (by rfl) ?_)
  | (with_reducible refine Gat_pure_bind ?_)
  | (with_reducible refine Hat_pure_bind ?_)
  | (with_reducible refine Gat_assoc ?_)
  | (with_reducible refine Hat_assoc ?_)
  | (with_reducible exact Hat_modify_end (by rfl) (by rfl))
  | (with_reducible exact (Hat_modify_end (by rfl) (by rfl)).toG)
  | (with_reducible exact Hat_pure _ _)
  | (with_reducible exact (Hat_pure _ _).toG)
  | (with_reducible refine Gat_get ?_)
  | (with_reducible refine Hat_get ?_)
  | split)

-- `dfs` stays folded while the walk unifies (its unfolding is the whole executor).
attribute [local irreducible] dfs in
set_option maxHeartbeats 4000000 in
/-- ★ For every NFA, input, flag set, fuel and state: a run of `_M_dfs` that starts without a
solution and ends without one leaves `_M_results` (`res`) as it found it. -/
theorem dfs_keeps_res (c : Ctx) (f : Nat) : ∀ (mode : Mode) (i : Int) (tail : Bool) (st : ExSt),
    Gat st (dfs c f mode i tail) := by
  induction f with
  | zero =>
    intro mode i tail st
    rw [dfs.eq_1]
    exact (Kat_ethrow st .depth).toH.toG
  | succ f ih =>
    intro mode i tail st
    rw [dfs.eq_2]
    refine Gat_get ?_
    dsimp only
    repeat walk1

/-- ★ A start position of `_M_search` without a solution leaves `_M_results` as it was. -/
theorem searchFromFirst_fail_keeps_res (c : Ctx) (fuel : Nat) (mode : Mode) (st st' : ExSt)
    (h : (searchFromFirst c fuel mode).run st = .ok (false, st')) : st'.res = st.res := by
  simp only [searchFromFirst] at h
  rw [modify_bind_run] at h
  obtain ⟨_, s2, h2, h3⟩ := run_bind_ok h
  rw [get_bind_run] at h3
  simp only [StateT.run_pure] at h3
  have h4 := pure_ok h3
  simp only [Prod.mk.injEq] at h4
  obtain ⟨h5, h6⟩ := h4
  subst h6
  have hg := dfs_keeps_res c fuel mode 0 false _ (by rfl) _ _ h2 h5
  exact hg

theorem searchFromFirst_res_of_run (c : Ctx) (fuel : Nat) (mode : Mode) (st st' : ExSt) (b : Bool)
    (h : (searchFromFirst c fuel mode).run st = .ok (b, st')) : b = st'.hasSol := by
  simp only [searchFromFirst] at h
  rw [modify_bind_run] at h
  obtain ⟨_, s2, _, h3⟩ := run_bind_ok h
  rw [get_bind_run] at h3
  simp only [StateT.run_pure] at h3
  have h4 := pure_ok h3
  simp only [Prod.mk.injEq] at h4
  obtain ⟨h5, h6⟩ := h4
  subst h6; exact h5.symm

/-- The positions after the first: each found solution comes from one `_M_search_from_first`
run from a state whose `_M_results` are the loop's. -/
theorem loop_found (c : Ctx) (fuel : Nat) : ∀ (k : Nat) (st st' : ExSt),
    (searchAll.loop c fuel k).run st = .ok (true, st') →
    ∃ s, s.res = st.res ∧ (searchFromFirst c fuel .prefix_).run s = .ok (true, st') := by
  intro k
  induction k with
  | zero =>
    intro st st' h
    rw [searchAll.loop.eq_1] at h
    simp only [StateT.run_pure] at h
    have := pure_ok h
    simp at this
  | succ k ih =>
    intro st st' h
    rw [searchAll.loop.eq_2] at h
    rw [get_bind_run] at h
    split at h
    · simp only [StateT.run_pure] at h
      have := pure_ok h
      simp at this
    · rw [set_bind_run] at h
      obtain ⟨b, s2, h2, h3⟩ := run_bind_ok h
      cases b with
      | true =>
        simp only [ite_true, StateT.run_pure] at h3
        have := pure_ok h3
        simp only [Prod.mk.injEq] at this
        obtain ⟨-, rfl⟩ := this
        exact ⟨_, by rfl, h2⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false] at h3
        obtain ⟨s, hs, hrun⟩ := ih _ _ h3
        refine ⟨s, ?_, hrun⟩
        rw [hs, searchFromFirst_fail_keeps_res c fuel .prefix_ _ _ h2]

/-- ★ U35's mechanism for every NFA, input, flag set and fuel: when `regex_search` finds a match,
the match comes from a single `_M_search_from_first` run from a state whose `_M_results` are the
ones the search began with (`searchFromFirst_starts_clean`: that run starts with
`_M_cur_results = _M_results`). Whatever a failed earlier start position's lookahead copied into
`_M_cur_results` plays no part in it. -/
theorem search_found_from_initial_results (c : Ctx) (fuel : Nat) (st st' : ExSt)
    (h : (searchAll c fuel).run st = .ok (true, st')) :
    ∃ s, s.res = st.res ∧ (searchFromFirst c fuel .prefix_).run s = .ok (true, st') := by
  simp only [searchAll] at h
  obtain ⟨b, s1, h1, h2⟩ := run_bind_ok h
  cases b with
  | true =>
    refine ⟨st, rfl, ?_⟩
    simp only [ite_true, StateT.run_pure] at h2
    have := pure_ok h2
    simp only [Prod.mk.injEq] at this
    obtain ⟨-, rfl⟩ := this
    exact h1
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h2
    have hk := searchFromFirst_fail_keeps_res c fuel .prefix_ _ _ h1
    rw [get_bind_run] at h2
    split at h2
    · simp only [StateT.run_pure] at h2
      have := pure_ok h2
      simp at this
    · rw [modify_bind_run] at h2
      obtain ⟨s, hs, hrun⟩ := loop_found c fuel _ _ _ h2
      exact ⟨s, hs.trans hk, hrun⟩

/-- ★ A search that finds nothing leaves `_M_results` as it was. -/
theorem search_fail_keeps_res (c : Ctx) (fuel : Nat) (st st' : ExSt)
    (h : (searchAll c fuel).run st = .ok (false, st')) : st'.res = st.res := by
  simp only [searchAll] at h
  obtain ⟨b, s1, h1, h2⟩ := run_bind_ok h
  cases b with
  | true =>
    simp only [ite_true, StateT.run_pure] at h2
    have := pure_ok h2
    simp at this
  | false =>
    simp only [Bool.false_eq_true, ite_false] at h2
    have hk := searchFromFirst_fail_keeps_res c fuel .prefix_ _ _ h1
    rw [get_bind_run] at h2
    split at h2
    · simp only [StateT.run_pure] at h2
      have := pure_ok h2
      simp only [Prod.mk.injEq] at this
      obtain ⟨-, rfl⟩ := this
      exact hk
    · rw [modify_bind_run] at h2
      have key : ∀ (k : Nat) (s s' : ExSt), (searchAll.loop c fuel k).run s = .ok (false, s') →
          s'.res = s.res := by
        intro k
        induction k with
        | zero =>
          intro s s' h
          rw [searchAll.loop.eq_1] at h
          simp only [StateT.run_pure] at h
          have := pure_ok h
          simp only [Prod.mk.injEq] at this
          obtain ⟨-, rfl⟩ := this
          rfl
        | succ k ih =>
          intro s s' h
          rw [searchAll.loop.eq_2, get_bind_run] at h
          split at h
          · simp only [StateT.run_pure] at h
            have := pure_ok h
            simp only [Prod.mk.injEq] at this
            obtain ⟨-, rfl⟩ := this
            rfl
          · rw [set_bind_run] at h
            obtain ⟨b, s2, h3, h4⟩ := run_bind_ok h
            cases b with
            | true =>
              simp only [ite_true, StateT.run_pure] at h4
              have := pure_ok h4
              simp at this
            | false =>
              simp only [Bool.false_eq_true, ite_false] at h4
              rw [ih _ _ h4, searchFromFirst_fail_keeps_res c fuel .prefix_ _ _ h3]
      rw [key _ _ _ h2]
      exact hk

end Jank.R5.Regex

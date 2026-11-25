import Determinismo

/-!
# Invariants through `Determinismo.interleave` (round 3, proofs)

`Determinismo.Threads` runs a `Program` by `interleave`: a `for` loop over `maxSteps` turns, each
picking a thread (a decision) and running its step. The sdk has no way to prove that a property
holds after *every* interleaving: its searches enumerate timelines within bounds. This module
adds the induction principle:

- `interleave_inv`: an invariant of the process that is kept by decisions and by every step of
  every thread (whatever the step returns) holds when `interleave` ends, by its end or by an
  exception (a deadlock report or the decision limit), for every source of decisions and every
  `maxSteps`;
- `interleave_no_deadlock`: the same with the loop's `blocked` list: if every thread in it blocks,
  and some live thread can always step, the deadlock report never fires (the run ends normally or
  at the decision limit).

Also the monad facts they need: `forIn` over a list, `bind`, `pick`, and `Array.set!`/`getD`.
-/

namespace Jank.R3.Proofs

open Determinismo

/-- The state an `EStateM` run ends in, whether it returned or threw. -/
def resState {ε σ α : Type} : EStateM.Result ε σ α → σ
  | .ok _ s => s
  | .error _ s => s

theorem forIn_inv {σ ε β α : Type} (Inv : σ → Prop) (f : α → β → EStateM ε σ (ForInStep β))
    (hf : ∀ a b s, Inv s → Inv (resState (f a b s))) :
    ∀ (xs : List α) b s, Inv s → Inv (resState (forIn xs b f s)) := by
  intro xs
  induction xs with
  | nil => intro b s hs; simpa [resState, pure, EStateM.pure] using hs
  | cons a as ih =>
    intro b s hs
    simp only [List.forIn_cons]
    show Inv (resState (EStateM.bind (f a b) _ s))
    simp only [EStateM.bind]
    have := hf a b s hs
    revert this
    cases f a b s with
    | ok r s' =>
      intro h
      cases r with
      | done b' => simpa [resState, pure, EStateM.pure] using h
      | yield b' => exact ih b' s' h
    | error e s' => intro h; simpa [resState] using h

/-- The same, with an invariant on the loop's state as well. -/
theorem forIn_inv2 {σ ε β α : Type} (Inv : β → σ → Prop) (f : α → β → EStateM ε σ (ForInStep β))
    (hf : ∀ a b s, Inv b s → match f a b s with
      | .ok (.yield b') s' => Inv b' s'
      | .ok (.done b') s' => Inv b' s'
      | .error _ s' => ∃ b', Inv b' s') :
    ∀ (xs : List α) b s, Inv b s → match forIn xs b f s with
      | .ok b' s' => Inv b' s'
      | .error _ s' => ∃ b', Inv b' s' := by
  intro xs
  induction xs with
  | nil => intro b s hs; simpa [pure, EStateM.pure] using hs
  | cons a as ih =>
    intro b s hs
    simp only [List.forIn_cons]
    show match EStateM.bind (f a b) _ s with | .ok b' s' => Inv b' s' | .error _ s' => ∃ b', Inv b' s'
    simp only [EStateM.bind]
    have := hf a b s hs
    revert this
    cases f a b s with
    | ok r s' =>
      intro h
      cases r with
      | done b' => simpa [pure, EStateM.pure] using h
      | yield b' => exact ih b' s' h
    | error e s' => intro h; simpa using h

theorem bind_inv {σ ε α β : Type} (Inv : σ → Prop) (x : EStateM ε σ α) (f : α → EStateM ε σ β)
    (hx : ∀ s, Inv s → Inv (resState (x s))) (hf : ∀ a s, Inv s → Inv (resState (f a s))) :
    ∀ s, Inv s → Inv (resState ((x >>= f) s)) := by
  intro s hs
  show Inv (resState (EStateM.bind x f s))
  simp only [EStateM.bind]
  have := hx s hs
  revert this
  cases x s with
  | ok a s' => intro h; exact hf a s' h
  | error e s' => intro h; simpa [resState] using h

theorem getD_mem {α : Type} (l : List α) (d : α) (i : Nat) (h : d ∈ l) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simpa using h
  | some x => simpa using List.mem_of_getElem? hi

/-- `pick` changes only the decisions, and picks an element of the list. -/
theorem pick_res {M L α : Type} (name : String) (items : List α) (p : Process M L) :
    (∃ d v, (pick (σ := Process M L) name items) p = .ok v { p with decisions := d } ∧
       ∀ x, v = some x → x ∈ items) ∨
    (∃ e, (pick (σ := Process M L) name items) p = .error e p) := by
  cases items with
  | nil => left; exact ⟨p.decisions, none, rfl, by simp⟩
  | cons a as =>
    simp only [pick, Determinismo.decide, decideWeighted, bind, EStateM.bind, get, getThe, MonadStateOf.get,
      EStateM.get, pure, EStateM.pure, set, throw, throwThe, MonadExceptOf.throw]
    cases h : (Chaotic.decisions p).next name (List.replicate (a :: as).length 1) with
    | ok vd =>
      obtain ⟨v, d⟩ := vd
      left
      refine ⟨d, some ((a :: as).getD v a), ?_, ?_⟩
      · simp [EStateM.set, EStateM.bind, EStateM.pure, Chaotic.setDecisions]
      · intro x hx
        simp only [Option.some.injEq] at hx
        subst hx
        exact getD_mem _ _ _ List.mem_cons_self
    | error e =>
      right
      exact ⟨e, by simp [EStateM.throw]⟩

theorem getD_set {α : Type} (a : Array (Option α)) (t i : Nat) (v : Option α) (ht : t < a.size) :
    (a.set! t v).getD i none = if i = t then v else a.getD i none := by
  simp only [Array.set!, Array.getD, Array.size_setIfInBounds]
  by_cases hi : i < a.size
  · simp only [hi, dite_true, Array.getInternal_eq_getElem, Array.getElem_setIfInBounds]
    by_cases hit : i = t
    · subst hit; simp; intro h; omega
    · simp [hit, Ne.symm hit]
      intro h; omega
  · have : i ≠ t := by omega
    simp [hi, this]

theorem getD_some_lt {α : Type} (a : Array (Option α)) (t : Nat) (l : α) (h : a.getD t none = some l) :
    t < a.size := by
  simp only [Array.getD] at h
  split at h
  · assumption
  · simp at h

theorem size_set {α : Type} (a : Array α) (t : Nat) (v : α) : (a.set! t v).size = a.size := by
  simp [Array.set!]

/-- What a step must keep for `interleave_inv`. -/
def StepKeeps {M L : Type} (prog : Program M L) (Inv : Process M L → Prop) : Prop :=
  ∀ p t l, Inv p → p.threads.getD t none = some l →
    match prog.step t l p with
    | .ok (.ran l') p' => Inv { p' with threads := p'.threads.set! t (some l'), steps := p'.steps + 1 }
    | .ok .blocked p' => Inv p'
    | .ok .done p' => Inv { p' with threads := p'.threads.set! t none, steps := p'.steps + 1 }
    | .error _ p' => Inv p'

/-- An invariant kept by decisions and by every step holds after `interleave`, however it ended. -/
theorem interleave_inv {M L : Type} (prog : Program M L) (n : Nat)
    (stuck : Process M L → Option String) (Inv : Process M L → Prop)
    (hdec : ∀ p d, Inv p → Inv { p with decisions := d })
    (hstep : StepKeeps prog Inv)
    (p : Process M L) (hp : Inv p) : Inv (resState (interleave prog n stuck p)) := by
  unfold interleave
  refine bind_inv Inv _ _ ?_ ?_ p hp
  rotate_left
  · intro a s hs
    rcases a with ⟨_ | _, _⟩ <;> simpa [resState, pure, EStateM.pure] using hs
  apply forIn_inv Inv
  intro x b s hs
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  split
  · simpa [resState, pure, EStateM.pure] using hs
  split
  · cases stuck s <;> simpa [resState, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind, pure,
      EStateM.pure] using hs
  rcases pick_res (M := M) (L := L) "thread.next" (List.filter (fun x => !b.snd.contains x)
      (List.filter (fun i => (s.threads.getD i none).isSome) (List.range s.threads.size))) s with
    ⟨d, v, hv, _⟩ | ⟨e, he⟩
  · simp only [EStateM.bind, hv]
    rcases v with _ | t
    · simpa [resState, pure, EStateM.pure] using hdec s d hs
    simp only
    cases hl : s.threads.getD t none with
    | none => simpa [resState, pure, EStateM.pure] using hdec s d hs
    | some l =>
      simp only [EStateM.bind]
      have h1 := hstep _ t l (hdec s d hs) hl
      revert h1
      rcases h : prog.step t l { s with decisions := d } with ⟨r, s'⟩ | ⟨e, s'⟩
      · rcases r with l' | _ | _ <;>
          simp [resState, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
            EStateM.bind]
      · simp [resState]
  · simp only [EStateM.bind, he]
    simpa [resState] using hs

/-- What `runProcess` ends with: the body's final state. -/
theorem runProcess_snd {M L : Type} (start : Process M L) (body : ProcessM M L Unit) (source : Source)
    (limit : Nat) :
    (runProcess start body source limit).2 = resState (body { start with decisions := { source, limit } }) := by
  simp only [runProcess, EStateM.run]
  split <;> simp_all [resState]

/-! ## Deadlock freedom: the loop's `blocked` list -/

theorem forIn_inv3 {σ ε β α : Type} (Inv : β → σ → Prop) (E : ε → Prop) (f : α → β → EStateM ε σ (ForInStep β))
    (hf : ∀ a b s, Inv b s → match f a b s with
      | .ok (.yield b') s' => Inv b' s'
      | .ok (.done b') s' => Inv b' s'
      | .error e _ => E e) :
    ∀ (xs : List α) b s, Inv b s → match forIn xs b f s with
      | .ok b' s' => Inv b' s'
      | .error e _ => E e := by
  intro xs
  induction xs with
  | nil => intro b s hs; simpa [pure, EStateM.pure] using hs
  | cons a as ih =>
    intro b s hs
    simp only [List.forIn_cons]
    show match EStateM.bind (f a b) _ s with | .ok b' s' => Inv b' s' | .error e _ => E e
    simp only [EStateM.bind]
    have := hf a b s hs
    revert this
    cases f a b s with
    | ok r s' =>
      intro h
      cases r with
      | done b' => simpa [pure, EStateM.pure] using h
      | yield b' => exact ih b' s' h
    | error e s' => intro h; simpa using h

theorem next_error {d : Decisions} {name : String} {ws : List Nat} {e : Stop}
    (h : d.next name ws = .error e) : e = .limit := by
  simp only [Decisions.next] at h
  split at h
  · cases h
  · split at h
    · injection h with h; exact h.symm
    · cases h

theorem pick_res' {M L α : Type} (name : String) (items : List α) (p : Process M L) :
    (∃ d v, (pick (σ := Process M L) name items) p = .ok v { p with decisions := d } ∧
       ∀ x, v = some x → x ∈ items) ∨
    ((pick (σ := Process M L) name items) p = .error .limit p) := by
  cases items with
  | nil => left; exact ⟨p.decisions, none, rfl, by simp⟩
  | cons a as =>
    simp only [pick, Determinismo.decide, decideWeighted, bind, EStateM.bind, get, getThe, MonadStateOf.get,
      EStateM.get, pure, EStateM.pure, set, throw, throwThe, MonadExceptOf.throw]
    cases h : (Chaotic.decisions p).next name (List.replicate (a :: as).length 1) with
    | ok vd =>
      obtain ⟨v, d⟩ := vd
      left
      refine ⟨d, some ((a :: as).getD v a), ?_, ?_⟩
      · simp [EStateM.set, EStateM.bind, EStateM.pure, Chaotic.setDecisions]
      · intro x hx
        simp only [Option.some.injEq] at hx
        subst hx
        exact getD_mem _ _ _ List.mem_cons_self
    | error e =>
      right
      have := next_error h
      subst this
      simp [EStateM.throw]

theorem forIn_err {σ ε β α : Type} (Inv : β → σ → Prop) (E : ε → Prop) (f : α → β → EStateM ε σ (ForInStep β))
    (hf : ∀ a b s, Inv b s → match f a b s with
      | .ok (.yield b') s' => Inv b' s'
      | .ok (.done b') s' => Inv b' s'
      | .error e _ => E e)
    (xs : List α) (b : β) (s : σ) (hs : Inv b s) : ∀ e s', forIn xs b f s = .error e s' → E e := by
  intro e s' h
  have := forIn_inv3 Inv E f hf xs b s hs
  rw [h] at this
  exact this

theorem bind_err {σ ε α β : Type} (x : EStateM ε σ α) (f : α → EStateM ε σ β) (E : ε → Prop) (s : σ)
    (hx : ∀ e s', x s = .error e s' → E e) (hf : ∀ a s', ∀ e s'', f a s' = .error e s'' → E e) :
    ∀ e s', (x >>= f) s = .error e s' → E e := by
  intro e s' h
  change EStateM.bind x f s = _ at h
  simp only [EStateM.bind] at h
  revert h
  cases hx' : x s with
  | ok a s1 => intro h; exact hf a s1 e s' h
  | error e1 s1 => intro h; injection h with h1 h2; subst h1; exact hx e1 s1 hx'

theorem interleave_no_deadlock {M L : Type} (prog : Program M L) (n : Nat)
    (stuck : Process M L → Option String) (Inv : Process M L → Prop) (Blocks : Process M L → Nat → Prop)
    (hdec : ∀ p d, Inv p → Inv { p with decisions := d })
    (hdecB : ∀ p d t, Blocks p t → Blocks { p with decisions := d } t)
    (hstep : StepKeeps prog Inv)
    (hblocked : ∀ p t l p', Inv p → p.threads.getD t none = some l → prog.step t l p = .ok .blocked p' →
      Blocks p' t ∧ ∀ u, Blocks p u → Blocks p' u)
    (herr : ∀ p t l e p', Inv p → p.threads.getD t none = some l → prog.step t l p = .error e p' → e = .limit)
    (hlive : ∀ p, Inv p → ∀ t, (p.threads.getD t none).isSome →
      ∃ u, (p.threads.getD u none).isSome ∧ ¬ Blocks p u)
    (p : Process M L) (hp : Inv p) : ∀ e s, interleave prog n stuck p = .error e s → e = .limit := by
  intro e s hres
  unfold interleave at hres
  let I2 : Option Unit × List Nat → Process M L → Prop := fun b q => Inv q ∧ ∀ t ∈ b.2, Blocks q t
  refine bind_err _ _ (fun e => e = Stop.limit) p ?_ ?_ e s hres
  rotate_left
  · intro a s' e' s'' h; rcases a with ⟨_ | _, _⟩ <;> simp [pure, EStateM.pure] at h
  intro e' s' h'
  refine forIn_err I2 (fun e => e = Stop.limit) _ ?_ _ _ p ⟨hp, by simp⟩ e' s' h'
  intro x b q ⟨hq, hb⟩
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  by_cases h1 : (List.filter (fun i => (q.threads.getD i none).isSome) (List.range q.threads.size)).isEmpty = true
  · simp only [h1, ite_true, pure, EStateM.pure]; exact ⟨hq, hb⟩
  simp only [h1, Bool.false_eq_true, ite_false]
  by_cases h2 : (List.filter (fun x => !b.snd.contains x)
      (List.filter (fun i => (q.threads.getD i none).isSome) (List.range q.threads.size))).isEmpty = true
  · exfalso
    simp only [List.isEmpty_iff, List.filter_eq_nil_iff, List.mem_range] at h1 h2
    have : ∃ t, (q.threads.getD t none).isSome = true := by
      apply Classical.byContradiction
      intro hc
      apply h1
      intro t _ ht
      exact hc ⟨t, ht⟩
    obtain ⟨t, ht⟩ := this
    obtain ⟨u, hu, hnb⟩ := hlive q hq t ht
    have hus : u < q.threads.size := by
      cases hg : q.threads.getD u none with
      | none => rw [hg] at hu; cases hu
      | some lu => exact getD_some_lt _ _ _ hg
    have hin : b.snd.contains u = true := by
      have := h2 u (List.mem_filter.mpr ⟨List.mem_range.mpr hus, hu⟩)
      simpa using this
    exact hnb (hb u (by simpa using hin))
  simp only [h2, Bool.false_eq_true, ite_false]
  rcases pick_res' (M := M) (L := L) "thread.next" (List.filter (fun x => !b.snd.contains x)
      (List.filter (fun i => (q.threads.getD i none).isSome) (List.range q.threads.size))) q with
    ⟨d, v, hv, _⟩ | hv
  · simp only [EStateM.bind, hv]
    rcases v with _ | t
    · simp only [pure, EStateM.pure]
      exact ⟨hdec q d hq, fun u hu => hdecB q d u (hb u hu)⟩
    simp only
    cases hl : q.threads.getD t none with
    | none =>
      simp only [pure, EStateM.pure]
      exact ⟨hdec q d hq, fun u hu => hdecB q d u (hb u hu)⟩
    | some l =>
      simp only [EStateM.bind]
      have hq' := hdec q d hq
      have hst := hstep _ t l hq' hl
      have hbl := hblocked { q with decisions := d } t l
      have her := herr { q with decisions := d } t l
      revert hst hbl her
      rcases h : prog.step t l { q with decisions := d } with ⟨r, s'⟩ | ⟨e', s'⟩
      · rcases r with l' | _ | _
        · intro hst _ _
          simp [pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.bind]
          exact ⟨hst, fun _ h => by simp at h⟩
        · intro hst hbl _
          obtain ⟨hb1, hb2⟩ := hbl s' hq' hl rfl
          simp only [pure, EStateM.pure]
          refine ⟨hst, ?_⟩
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hb1
          · exact hb2 u (hdecB q d u (hb u hu))
        · intro hst _ _
          simp [pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, EStateM.bind]
          exact ⟨hst, fun _ h => by simp at h⟩
      · intro _ _ her
        exact her e' s' hq' hl rfl
  · simp only [EStateM.bind, hv]

end Jank.R3.Proofs

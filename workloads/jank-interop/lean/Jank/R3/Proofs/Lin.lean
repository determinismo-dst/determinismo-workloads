import Determinismo

/-!
# Linearizability as a relation (round 3, proofs)

`Determinismo.linearizable` (sdk/lean History.lean) is a `partial def`: a search that Lean
cannot unfold, so nothing can be proved about it. This module gives the definition it decides
(Herlihy and Wing's, with Jepsen's reading of unanswered operations) as a proposition, and the
standard way to establish it: linearization points.

A history `H` is linearizable against a sequential specification `spec` from `init` when some
order of a subset of its operations

- contains every answered operation (and no failed one),
- is legal: each operation has a transition of `spec`, answering exactly what was acknowledged
  (an unanswered operation may answer anything),
- respects real time: an operation answered before another was invoked comes first.

Unanswered operations that are left out never took effect; those kept took effect at some
moment after their invocation. The specification is a relation, so a weak compare-and-set
("may fail spuriously") is a specification too.
-/

namespace Jank.R3.Proofs.Lin

open Determinismo

/-- A sequential specification: from state `s`, operation `op` may go to `s'` answering `r`. -/
abbrev Spec (S Op Res : Type) := S → Op → S → Res → Prop

variable {S Op Res : Type}

/-- `order` runs legally from `s`. -/
def Legal (spec : Spec S Op Res) : S → List (OpRec Op Res) → Prop
  | _, [] => True
  | s, o :: os => ∃ s' r, spec s o.op s' r ∧ (∀ r', o.outcome = some (.ok r') → r' = r) ∧ Legal spec s' os

/-- Linearizable (relational). -/
def Linearizable (spec : Spec S Op Res) (init : S) (H : List (OpRec Op Res)) : Prop :=
  ∃ order : List (OpRec Op Res),
    (∀ o ∈ order, o ∈ H) ∧
    (order.map (·.id)).Nodup ∧
    (∀ o ∈ H, o.ret.isSome → o.outcome ≠ some .fail → o ∈ order) ∧
    (∀ o ∈ order, o.outcome ≠ some .fail) ∧
    order.Pairwise (fun a b => ∀ r, b.ret = some r → ¬ r < a.invoke) ∧
    Legal spec init order

/-- A linearization point: an operation (its id and op), the result it took and the step at
which it took effect. -/
structure LinE (Op Res : Type) where
  id : Nat
  op : Op
  res : Res
  lp : Nat

/-- The sequential run along linearization points: from `s` to `s'`. -/
def RunsTo (spec : Spec S Op Res) : S → List (LinE Op Res) → S → Prop
  | s, [], s' => s = s'
  | s, e :: es, s' => ∃ s1, spec s e.op s1 e.res ∧ RunsTo spec s1 es s'

theorem RunsTo.append (spec : Spec S Op Res) :
    ∀ (s : S) (l : List (LinE Op Res)) (s1 : S) (e : LinE Op Res) (s2 : S),
      RunsTo spec s l s1 → spec s1 e.op s2 e.res → RunsTo spec s (l ++ [e]) s2
  | s, [], s1, e, s2, h, h2 => by
    simp only [RunsTo] at h; subst h
    exact ⟨s2, h2, rfl⟩
  | s, e0 :: es, s1, e, s2, h, h2 => by
    obtain ⟨t, ht, hr⟩ := h
    exact ⟨t, ht, RunsTo.append spec t es s1 e s2 hr h2⟩

/-- What linearization points must satisfy for the history to be linearizable. -/
structure Witness (spec : Spec S Op Res) (init : S) (H : List (OpRec Op Res)) (lin : List (LinE Op Res)) : Prop where
  hNodup : (H.map (·.id)).Nodup
  linNodup : (lin.map (·.id)).Nodup
  /-- Each point belongs to an operation of the history, invoked before it. -/
  linRec : ∀ e ∈ lin, ∃ h ∈ H, h.id = e.id ∧ h.op = e.op ∧ h.invoke < e.lp
  /-- Points are in the order of their steps. -/
  linOrder : lin.Pairwise (fun a b => a.lp < b.lp)
  /-- Every operation is unanswered, or answered after its point with the point's result. -/
  answered : ∀ h ∈ H, (h.ret = none ∧ h.outcome = none) ∨
    (∃ rt, ∃ e ∈ lin, h.ret = some rt ∧ e.id = h.id ∧ h.outcome = some (.ok e.res) ∧ e.lp < rt)
  /-- The sequential run along the points ends somewhere. -/
  runs : ∃ s, RunsTo spec init lin s

theorem nodup_map_inj {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ a b, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, a, _, ha, _, _ => by simp at ha
  | x :: xs, hN, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons] at hN
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd (hab ▸ List.mem_map_of_mem hb') hN.1
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd (hab.symm ▸ List.mem_map_of_mem ha') hN.1
      · exact nodup_map_inj f xs hN.2 a b ha' hb' hab

/-- The record of `e` in `H`. -/
def recOf (H : List (OpRec Op Res)) (e : LinE Op Res) : Option (OpRec Op Res) := H.find? (·.id == e.id)

theorem recOf_spec {H : List (OpRec Op Res)} {e : LinE Op Res}
    (hN : (H.map (·.id)).Nodup) (h : OpRec Op Res) (hh : h ∈ H) (hid : h.id = e.id) :
    recOf H e = some h := by
  unfold recOf
  induction H with
  | nil => simp at hh
  | cons a as ih =>
    simp only [List.map_cons, List.nodup_cons] at hN
    simp only [List.find?_cons]
    rcases List.mem_cons.mp hh with rfl | hmem
    · simp [hid]
    · have hne : a.id ≠ e.id := by
        intro hc; apply hN.1; rw [hc, ← hid]; exact List.mem_map_of_mem hmem
      have hb : (a.id == e.id) = false := by simp [hne]
      simp only [hb]
      exact ih hN.2 hmem

theorem recOf_mem {H : List (OpRec Op Res)} {e : LinE Op Res} {h : OpRec Op Res}
    (hr : recOf H e = some h) : h ∈ H ∧ h.id = e.id := by
  unfold recOf at hr
  exact ⟨List.mem_of_find?_eq_some hr, by simpa using List.find?_some hr⟩

/-- Linearization points make a history linearizable. -/
theorem linearizable_of_witness (spec : Spec S Op Res) (init : S) (H : List (OpRec Op Res))
    (lin : List (LinE Op Res)) (w : Witness spec init H lin) : Linearizable spec init H := by
  -- The order: each point's record.
  refine ⟨lin.filterMap (recOf H), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho
    obtain ⟨e, _, he⟩ := List.mem_filterMap.mp ho
    exact (recOf_mem he).1
  · have hmap : (lin.filterMap (recOf H)).map (·.id) = lin.map (·.id) := by
      have : ∀ l : List (LinE Op Res), (∀ e ∈ l, e ∈ lin) →
          (l.filterMap (recOf H)).map (·.id) = l.map (·.id) := by
        intro l hl
        induction l with
        | nil => rfl
        | cons e es ih =>
          obtain ⟨h, hh, hid, _, _⟩ := w.linRec e (hl e (List.mem_cons_self))
          rw [List.filterMap_cons, recOf_spec w.hNodup h hh hid]
          simp only [List.map_cons, hid]
          rw [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
      exact this lin (fun _ h => h)
    rw [hmap]; exact w.linNodup
  · intro o ho hret _
    rcases w.answered o ho with ⟨hn, _⟩ | ⟨rt, e, he, _, hid, _, _⟩
    · simp [hn] at hret
    · exact List.mem_filterMap.mpr ⟨e, he, recOf_spec w.hNodup o ho hid.symm⟩
  · intro o ho
    obtain ⟨e, _, he⟩ := List.mem_filterMap.mp ho
    rcases w.answered o (recOf_mem he).1 with ⟨_, hn⟩ | ⟨_, _, _, _, _, ho2, _⟩
    · simp [hn]
    · simp [ho2]
  · -- real time
    have key : ∀ l : List (LinE Op Res), l.Pairwise (fun a b => a.lp < b.lp) → (∀ e ∈ l, e ∈ lin) →
        (l.filterMap (recOf H)).Pairwise (fun a b => ∀ r, b.ret = some r → ¬ r < a.invoke) := by
      intro l hp hl
      induction l with
      | nil => exact List.Pairwise.nil
      | cons e es ih =>
        rw [List.pairwise_cons] at hp
        obtain ⟨h, hh, hid, _, hinv⟩ := w.linRec e (hl e List.mem_cons_self)
        rw [List.filterMap_cons, recOf_spec w.hNodup h hh hid]
        refine List.Pairwise.cons ?_ (ih hp.2 (fun x hx => hl x (List.mem_cons_of_mem _ hx)))
        intro b hb r hbr
        obtain ⟨e2, he2, hrec2⟩ := List.mem_filterMap.mp hb
        obtain ⟨hb2, hbid⟩ := recOf_mem hrec2
        have hlt := hp.1 e2 he2
        rcases w.answered b hb2 with ⟨hn, _⟩ | ⟨rt, e3, he3, hret, hid3, _, hlp3⟩
        · simp [hn] at hbr
        · -- e3 is e2: one point per id
          have he3' : e3 = e2 := by
            have hin2 : e2 ∈ lin := hl e2 (List.mem_cons_of_mem _ he2)
            have hids : e3.id = e2.id := by rw [hid3, hbid]
            exact nodup_map_inj _ lin w.linNodup e3 e2 he3 hin2 hids
          subst he3'
          rw [hret] at hbr
          injection hbr with hbr
          subst hbr
          omega
    exact key lin w.linOrder (fun _ h => h)
  · -- legality
    obtain ⟨sEnd, hruns⟩ := w.runs
    have key : ∀ (l : List (LinE Op Res)) (s : S), (∀ e ∈ l, e ∈ lin) → RunsTo spec s l sEnd →
        Legal spec s (l.filterMap (recOf H)) := by
      intro l
      induction l with
      | nil => intro s _ _; trivial
      | cons e es ih =>
        intro s hl hr
        obtain ⟨s1, hs1, hr1⟩ := hr
        obtain ⟨h, hh, hid, hop, _⟩ := w.linRec e (hl e List.mem_cons_self)
        rw [List.filterMap_cons, recOf_spec w.hNodup h hh hid]
        refine ⟨s1, e.res, by rw [hop]; exact hs1, ?_, ih s1 (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hr1⟩
        intro r' hr'
        rcases w.answered h hh with ⟨_, hn⟩ | ⟨rt, e3, he3, _, hid3, ho3, _⟩
        · simp [hn] at hr'
        · have he3' : e3 = e := by
            have hids : e3.id = e.id := by rw [hid3, hid]
            exact nodup_map_inj _ lin w.linNodup e3 e he3 (hl e List.mem_cons_self) hids
          subst he3'
          rw [ho3] at hr'
          injection hr' with hr'
          injection hr' with hr'
          exact hr'.symm
    exact key lin init (fun _ h => h) hruns

end Jank.R3.Proofs.Lin

import Jank.R8.Nrepl.Walk

/-!
# Round 9, nREPL: every causal run function is a finite decision tree (nREPLA6-1, narrowed)

Round 8 proved the sdk's walk for every finite decision tree (Walk.lean: ★ `walk_paths`,
★ `walk_count`, ★ `exhaust_complete`), but not that a World T run (`runTWith`, the sdk's
`interleavePB` over round 3's `tProg`) is one (nREPLA6-1). This file proves, for EVERY run function
`run : List Nat → List Taken` (the decisions a timeline records when fed a path), that it is
exactly some finite decision tree's `DT.run` as soon as four local conditions hold (`Treelike`):

- `bounded`: at most `D` decisions (the sdk's `Decisions.limit` bounds them);
- `value`: the i-th decision's value is the path's i-th value modulo its options, 0 beyond the path
  (what `Decisions.next` does with `Source.path`);
- `wf`: every recorded decision has at least two options (`Decisions.next` records no other);
- `causal`: the i-th decision's name and options, and whether there is one, depend only on the
  decisions before it (the run cannot look ahead in the path).

★ `tree_of_treelike`: under these, `build run D []` is a well-formed tree and `run p =
(build run D []).run p` for every path `p`; ★ `exhaust_of_treelike`: so the sdk's `exhaust` over
such a run (no violation) ends `.complete` after exactly the tree's `leaves` timelines, depth first,
each leaf once (round 8's `exh_gen`, `walk_paths`, `paths_length`).

What this leaves of nREPLA6-1: that World T's run function satisfies the four conditions. They hold
for any program whose decisions all go through `Decisions.next` and whose behaviour depends on the
source only through the values `next` returns; that is a property of round 3's code (Threads.lean:
`decide`, `decideWeighted`, `decideRare`, the scheduler's `decide`), read, not proved. They are
CHECKED on World T's small worlds by `checkTreelike` (Run/R9/Nrepl.lean `tree`): every timeline of a
complete walk, its values against the path, its options, its bound, and causality on the trie of all
timelines. The second half of nREPLA6-1 (the subtree at a scheduler state is a function of that
state, which the graph counters use) is not proved here.
-/

namespace Jank.R9.Nrepl.Tree

open Determinismo Jank.R8.Nrepl.Walk

def pv (p : List Nat) (i : Nat) : Nat := p.getD i 0

def nameOpt (x : Taken) : String × Nat := (x.name, x.options)

structure Treelike (run : List Nat → List Taken) (D : Nat) : Prop where
  bounded : ∀ p : List Nat, (run p).length ≤ D
  value : ∀ (p : List Nat) (i : Nat) (h : i < (run p).length), ((run p)[i]).value = pv p i % ((run p)[i]).options
  wf : ∀ (p : List Nat) (i : Nat) (h : i < (run p).length), 2 ≤ ((run p)[i]).options
  causal : ∀ (p q : List Nat) (k : Nat), (∀ i : Nat, i < k → (run p)[i]? = (run q)[i]?) →
    ((run p)[k]?).map nameOpt = ((run q)[k]?).map nameOpt

theorem taken_ext (x y : Taken) (h1 : x.name = y.name) (h2 : x.options = y.options) (h3 : x.value = y.value) :
    x = y := by
  cases x; cases y; simp_all

/-- Two paths with the same values below `k` give the same decisions below `k`, and the same name
and options at `k`. -/
theorem agree_prefix (run : List Nat → List Taken) (D : Nat) (hT : Treelike run D) :
    ∀ k p q, (∀ i, i < k → pv p i = pv q i) →
      (∀ i, i < k → (run p)[i]? = (run q)[i]?) ∧ ((run p)[k]?).map nameOpt = ((run q)[k]?).map nameOpt := by
  intro k
  induction k with
  | zero => intro p q _; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), hT.causal p q 0 (fun i hi => absurd hi (Nat.not_lt_zero _))⟩
  | succ k ih =>
    intro p q hpq
    obtain ⟨hlt, hk⟩ := ih p q (fun i hi => hpq i (Nat.lt_succ_of_lt hi))
    have hkk : (run p)[k]? = (run q)[k]? := by
      cases hp : (run p)[k]? with
      | none =>
        rw [hp] at hk
        cases hq : (run q)[k]? with
        | none => rfl
        | some y => rw [hq] at hk; cases hk
      | some x =>
        rw [hp] at hk
        cases hq : (run q)[k]? with
        | none => rw [hq] at hk; cases hk
        | some y =>
          rw [hq] at hk
          simp only [Option.map_some, Option.some.injEq, nameOpt, Prod.mk.injEq] at hk
          obtain ⟨hpk, hpx⟩ := List.getElem?_eq_some_iff.mp hp
          obtain ⟨hqk, hqy⟩ := List.getElem?_eq_some_iff.mp hq
          have v1 := hT.value p k hpk
          have v2 := hT.value q k hqk
          rw [hpx] at v1; rw [hqy] at v2
          congr 1
          apply taken_ext x y hk.1 hk.2
          rw [v1, v2, hk.2, hpq k (Nat.lt_succ_self k)]
    have hall : ∀ i, i < k + 1 → (run p)[i]? = (run q)[i]? := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact hlt i h
      · subst h; exact hkk
    exact ⟨hall, hT.causal p q (k + 1) hall⟩

/-- The tree read off the run: at prefix `q` (values chosen so far), the decision the run takes at
position `q.length` when fed `q`, if any. -/
def build (run : List Nat → List Taken) : Nat → List Nat → DT
  | 0, _ => .leaf
  | f + 1, q => match (run q)[q.length]? with
    | none => .leaf
    | some x => .node x.name x.options (fun v => build run f (q ++ [v]))

theorem build_wf (run : List Nat → List Taken) (D : Nat) (hT : Treelike run D) :
    ∀ f q, (build run f q).WF := by
  intro f
  induction f with
  | zero => intro q; trivial
  | succ f ih =>
    intro q
    unfold build
    split
    · trivial
    · rename_i x hx
      obtain ⟨hl, hxe⟩ := List.getElem?_eq_some_iff.mp hx
      refine ⟨?_, fun i _ => ih _⟩
      have := hT.wf q q.length hl
      rw [hxe] at this
      exact this

theorem pv_append_lt (q : List Nat) (v i : Nat) (h : i < q.length) : pv (q ++ [v]) i = pv q i := by
  unfold pv
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem pv_append_eq (q : List Nat) (v : Nat) : pv (q ++ [v]) q.length = v := by
  unfold pv
  simp [List.getD_eq_getElem?_getD]

theorem pv_drop (p : List Nat) (k : Nat) : pv p k = (p.drop k).headD 0 := by
  unfold pv
  rw [List.getD_eq_getElem?_getD]
  cases h : p.drop k with
  | nil =>
    have : p.length ≤ k := by simpa using h
    simp [List.getElem?_eq_none this]
  | cons a r =>
    have h0 := congrArg (·[0]?) h
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
    simp [h0]

/-- The main induction: when `p`'s decisions below `q.length` are `q`'s run's, and the fuel covers
the bound, the run's decisions from `q.length` on are the subtree's at `q`. -/
theorem build_run (run : List Nat → List Taken) (D : Nat) (hT : Treelike run D) :
    ∀ f q p, D ≤ f + q.length →
      (∀ i, i < q.length → (run p)[i]? = (run q)[i]?) →
      (∀ i, i < q.length → ∃ x, (run q)[i]? = some x ∧ x.value = pv q i) →
      (run p).drop q.length = (build run f q).run (p.drop q.length) := by
  intro f
  induction f with
  | zero =>
    intro q p hD _ _
    simp only [build, DT.run]
    have := hT.bounded p
    exact List.drop_eq_nil_of_le (by omega)
  | succ f ih =>
    intro q p hD hpq hqv
    have hc := hT.causal p q q.length hpq
    unfold build
    split
    · rename_i hnone
      simp only [DT.run]
      rw [hnone] at hc
      simp only [Option.map_none] at hc
      have : (run p)[q.length]? = none := by
        cases h : (run p)[q.length]? with
        | none => rfl
        | some _ => rw [h] at hc; cases hc
      exact List.drop_eq_nil_of_le (by simpa using this)
    · rename_i x hx
      rw [hx] at hc
      cases hp : (run p)[q.length]? with
      | none => rw [hp] at hc; cases hc
      | some y =>
        rw [hp] at hc
        simp only [Option.map_some, Option.some.injEq, nameOpt, Prod.mk.injEq] at hc
        obtain ⟨hpl, hpy⟩ := List.getElem?_eq_some_iff.mp hp
        obtain ⟨hql, hqx⟩ := List.getElem?_eq_some_iff.mp hx
        have hxo := hT.wf q q.length hql
        rw [hqx] at hxo
        let v := (p.drop q.length).headD 0 % x.options
        have hyv : y = ⟨x.name, x.options, v⟩ := by
          have := hT.value p q.length hpl
          rw [hpy] at this
          refine taken_ext y ⟨x.name, x.options, v⟩ hc.1 hc.2 ?_
          show y.value = (p.drop q.length).headD 0 % x.options
          rw [this, hc.2, pv_drop]
        simp only [DT.run]
        rw [List.drop_eq_getElem_cons hpl, hpy, hyv]
        congr 1
        -- the rest: the subtree at q ++ [v]
        have hv : v < x.options := Nat.mod_lt _ (by omega)
        -- q ++ [v]'s run agrees with q's below q.length, and its decision at q.length is (x, v)
        have hpre := agree_prefix run D hT q.length (q ++ [v]) q (fun i hi => pv_append_lt q v i hi)
        have hq'x : (run (q ++ [v]))[q.length]? = some ⟨x.name, x.options, v⟩ := by
          have hno := hpre.2
          rw [hx] at hno
          cases h : (run (q ++ [v]))[q.length]? with
          | none => rw [h] at hno; cases hno
          | some z =>
            rw [h] at hno
            simp only [Option.map_some, Option.some.injEq, nameOpt, Prod.mk.injEq] at hno
            obtain ⟨hzl, hze⟩ := List.getElem?_eq_some_iff.mp h
            have := hT.value (q ++ [v]) q.length hzl
            rw [hze, pv_append_eq, hno.2, Nat.mod_eq_of_lt hv] at this
            congr 1
            exact taken_ext _ _ hno.1 hno.2 this
        have hlen : (q ++ [v]).length = q.length + 1 := by simp
        have := ih (q ++ [v]) p (by rw [hlen]; omega)
          (fun i hi => by
            rw [hlen] at hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
            · rw [hpq i h, hpre.1 i h]
            · subst h; rw [hp, hq'x, hyv])
          (fun i hi => by
            rw [hlen] at hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
            · obtain ⟨z, hz, hzv⟩ := hqv i h
              refine ⟨z, by rw [hpre.1 i h, hz], ?_⟩
              rw [hzv, pv_append_lt q v i h]
            · subst h; exact ⟨_, hq'x, by rw [pv_append_eq]⟩)
        rw [hlen] at this
        rw [this, List.tail_drop]

/-- ★ Every run function satisfying the four conditions is exactly a finite, well-formed decision
tree's run, on every path. -/
theorem tree_of_treelike (run : List Nat → List Taken) (D : Nat) (hT : Treelike run D) :
    (build run D []).WF ∧ ∀ p, run p = (build run D []).run p := by
  refine ⟨build_wf run D hT D [], fun p => ?_⟩
  have := build_run run D hT D [] p (by simp) (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun i hi => absurd hi (Nat.not_lt_zero _))
  simpa using this

theorem foldr_max_le (l : List Nat) (f : Nat) (h : ∀ x ∈ l, x ≤ f) : l.foldr max 0 ≤ f := by
  induction l with
  | nil => simp
  | cons a l ihl =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨h a List.mem_cons_self, ihl (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem build_height (run : List Nat → List Taken) : ∀ f q, (build run f q).height ≤ f := by
  intro f
  induction f with
  | zero => intro q; simp [build, DT.height]
  | succ f ih =>
    intro q
    unfold build
    split
    · simp [DT.height]
    · rename_i x _
      simp only [DT.height]
      have := foldr_max_le ((List.range x.options).map fun i => (build run f (q ++ [i])).height) f
        (fun y hy => by
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
          exact ih _)
      omega

/-- ★ So the sdk's `exhaust` over such a run (one without violations) ends complete after exactly
the tree's `leaves` timelines. -/
theorem exhaust_of_treelike (run : List Nat → List Taken) (D : Nat) (hT : Treelike run D)
    (ended : Source → Ended)
    (hend : ∀ path, (ended (Source.path path)).taken = (run path.toList).toArray ∧
      (ended (Source.path path)).violation = none)
    (maxRuns : Nat) (hm : (build run D []).leaves ≤ maxRuns) :
    exhaust ended maxRuns = .complete (build run D []).leaves := by
  obtain ⟨hwf, hrun⟩ := tree_of_treelike run D hT
  generalize ht : build run D [] = t at hwf hrun hm ⊢
  have hw := walk_paths t hwf
  have hlen := paths_length t
  have hpos : 0 < t.leaves := by
    rw [← hlen]; cases hp : t.paths with
    | nil => rw [hp] at hw; exact hw.elim
    | cons _ _ => simp
  unfold exhaust
  simp only [Id.run_bind]
  rw [exh_gen t ended _ (fun i path => by
      simp only [(hend path).2]
      cases nextPath (ended (Source.path path)).taken <;> rfl)
      (fun path => by rw [(hend path).1, hrun path.toList])
      t.paths #[] (List.range maxRuns) (by simpa using hw) (by rw [hlen]; simpa using hm)]
  rw [hlen]
  have hlt : t.leaves - 1 < maxRuns := by omega
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_range hlt]
  simp only [Option.getD_some]
  rw [Nat.sub_add_cancel hpos]
  rfl

end Jank.R9.Nrepl.Tree

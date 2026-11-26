import Determinismo
import Init.Internal.Order.While

/-!
# Round 8, nREPL: what the sdk's exhaustive walk counts

Round 6's counter (Graph.lean `countFrom`) and round 8's (Exact.lean `countLayers`) give the number
of timelines the sdk's `exhaust` would run over `interleavePB`. Round 6 checked that against 21
complete walks of rounds 3–5 but proved nothing. This file proves the walk's half for every finite
decision tree, on the sdk's own definitions (`Decisions.next`, `decide`, `nextPath`; Search.lean and
Decide.lean of `.lake/packages/determinismo/sdk/lean`, read only):

- ★ `nextPath_eq`: the sdk's `nextPath` (a `while` loop) is `npLoop`, a plain recursion: the last
  decision with an option left is advanced, the decisions after it dropped.
- ★ `nextPathL_cons`: in list form, `nextPath` of `x :: xs` is `x`'s value before `nextPath xs`
  when that exists, else `x` advanced alone, else none.
- ★ `prog_run`: a program that takes decisions along a tree with the sdk's `decide` and a
  `Source.path` source records exactly `DT.run`'s decisions: the path's values (modulo each
  decision's options), then first options.
- ★ `walk_paths`: from the empty path, the walk (run, then `nextPath` of what it took, until none)
  runs the tree's leaves in depth-first order, each once: `WalkFrom t [] t.paths`.
- ★ `walk_count`: so a complete walk runs `t.leaves` timelines, and ★ `leaves_node` is the
  recurrence the counters compute: a decision's timelines are the sum over its options.

What is not proved: that `interleavePB` over World T's `tProg` is such a tree whose subtree at a
scheduler state depends only on that state (round 6's nREPLA6-1 with the counters' choice rule copied
from ThreadSearch.lean), and that `countFrom` (a `partial def`, opaque to proofs) or `countLayers`
(array loops) evaluate the recurrence. Those rest on reading and on the exact reproduction of
rounds 3–6's counts.
-/

namespace Jank.R8.Nrepl.Walk

open Determinismo

/-! ## `nextPath` -/

/-- `nextPath`'s loop, scanning down from `i`. -/
def npLoop (taken : Array Taken) : Nat → Option (Array Nat)
  | 0 => none
  | i + 1 => if taken[i]!.value + 1 < taken[i]!.options then
      some (((taken.extract 0 i).map (·.value)).push (taken[i]!.value + 1)) else npLoop taken i

abbrev NS := Option (Option (Array Nat)) × Nat

theorem loop_gen (taken : Array Taken) (f : Unit → NS → Id (ForInStep NS))
    (hz : f () (none, 0) = ForInStep.done (none, 0))
    (hs : ∀ n, f () (none, n + 1) =
      if taken[n]!.value + 1 < taken[n]!.options then
        ForInStep.done (some (some (((taken.extract 0 n).map (·.value)).push (taken[n]!.value + 1))), n)
      else ForInStep.yield (none, n)) :
    ∀ n, (forIn (m := Id) Lean.Loop.mk ((none : Option (Option (Array Nat))), n) f).run.fst = (npLoop taken n).map some := by
  intro n
  induction n with
  | zero =>
    show (Lean.Loop.forIn Lean.Loop.mk ((none : Option (Option (Array Nat))), 0) f).run.fst = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [bind, hz]
    rfl
  | succ n ih =>
    show (Lean.Loop.forIn Lean.Loop.mk ((none : Option (Option (Array Nat))), n + 1) f).run.fst = _
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [bind, hs, npLoop]
    by_cases h : taken[n]!.value + 1 < taken[n]!.options
    · simp only [h, ↓reduceIte]; rfl
    · simp only [h, ↓reduceIte]; exact ih

/-- ★ The sdk's `nextPath` is `npLoop` from the end. -/
theorem nextPath_eq (taken : Array Taken) : nextPath taken = npLoop taken taken.size := by
  unfold nextPath
  simp only [Id.run_bind]
  rw [loop_gen taken _ rfl (fun n => rfl) taken.size]
  cases npLoop taken taken.size <;> rfl

/-- `nextPath` on lists. -/
def nextPathL (l : List Taken) : Option (List Nat) := (nextPath l.toArray).map Array.toList

theorem npLoop_cons (x : Taken) (xs : List Taken) : ∀ k,
    (npLoop (x :: xs).toArray (k + 1)).map Array.toList =
      match (npLoop xs.toArray k).map Array.toList with
      | some q => some (x.value :: q)
      | none => if x.value + 1 < x.options then some [x.value + 1] else none := by
  intro k
  induction k with
  | zero =>
    simp only [npLoop, List.getElem!_toArray, List.getElem!_cons_zero, Option.map_none]
    by_cases h : x.value + 1 < x.options
    · simp [h]
    · simp [h]
  | succ k ih =>
    rw [npLoop]
    simp only [List.getElem!_toArray, List.getElem!_cons_succ]
    by_cases h : xs[k]!.value + 1 < xs[k]!.options
    · simp only [h, ↓reduceIte, npLoop, List.getElem!_toArray, Option.map_some]
      simp [List.take_succ_cons]
    · simp only [h, ↓reduceIte]
      rw [ih]
      simp only [npLoop, List.getElem!_toArray, h, ↓reduceIte]

/-- ★ `nextPath` of `x :: xs`. -/
theorem nextPathL_cons (x : Taken) (xs : List Taken) :
    nextPathL (x :: xs) = match nextPathL xs with
      | some q => some (x.value :: q)
      | none => if x.value + 1 < x.options then some [x.value + 1] else none := by
  unfold nextPathL
  rw [nextPath_eq, nextPath_eq]
  simp only [List.size_toArray, List.length_cons]
  exact npLoop_cons x xs xs.length

theorem nextPathL_nil : nextPathL [] = none := by
  unfold nextPathL; rw [nextPath_eq]; rfl

/-! ## Decision trees -/

/-- A finite decision tree: a timeline's end, or a decision with `n` options (`kids i` for i < n). -/
inductive DT where
  | leaf
  | node (name : String) (n : Nat) (kids : Nat → DT)

/-- Every decision has at least two options (the sdk records no decision with one). -/
def DT.WF : DT → Prop
  | .leaf => True
  | .node _ n kids => 2 ≤ n ∧ ∀ i, i < n → (kids i).WF

/-- The decisions a run takes on `path`: its values modulo each decision's options, then 0s
(`Source.path`, `Decisions.next`). -/
def DT.run : DT → List Nat → List Taken
  | .leaf, _ => []
  | .node name n kids, p => ⟨name, n, p.headD 0 % n⟩ :: (kids (p.headD 0 % n)).run p.tail

/-- The leaves' decision lists, depth first, options in increasing order. -/
def DT.paths : DT → List (List Taken)
  | .leaf => [[]]
  | .node name n kids => (List.range n).flatMap fun i => ((kids i).paths).map (⟨name, n, i⟩ :: ·)

def DT.leaves : DT → Nat
  | .leaf => 1
  | .node _ n kids => ((List.range n).map fun i => (kids i).leaves).sum

/-- ★ The counters' recurrence: a decision's timelines are the sum over its options. -/
theorem leaves_node (name : String) (n : Nat) (kids : Nat → DT) :
    (DT.node name n kids).leaves = ((List.range n).map fun i => (kids i).leaves).sum := rfl

theorem paths_length : ∀ t : DT, t.paths.length = t.leaves
  | .leaf => rfl
  | .node name n kids => by
    simp only [DT.paths, DT.leaves, List.length_flatMap, List.length_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact paths_length (kids i)

/-- The depth of a tree (the most decisions of a run). -/
def DT.depth : DT → List Nat → Nat
  | .leaf, _ => 0
  | .node _ n kids, p => 1 + (kids (p.headD 0 % n)).depth p.tail

/-! ## The sdk's decisions along a tree -/

/-- A program taking the tree's decisions with the sdk's `decide`. -/
def DT.prog : DT → EStateM Stop Decisions Unit
  | .leaf => pure ()
  | .node name n kids => do
    let v ← decide (σ := Decisions) name n
    (kids v).prog

/-- What a source still feeds: no random draws, and the given values from the current position on. -/
def Feeds (d : Decisions) (p : List Nat) : Prop :=
  d.source.random = false ∧ d.source.given.toList.drop d.taken.size = p

theorem next_feeds (d : Decisions) (name : String) (n : Nat) (p : List Nat) (hn : 2 ≤ n)
    (hf : Feeds d p) (hl : d.taken.size < d.limit) :
    d.next name (List.replicate n 1) =
      .ok (p.headD 0 % n, { d with taken := d.taken.push ⟨name, n, p.headD 0 % n⟩ }) := by
  obtain ⟨hr, hg⟩ := hf
  unfold Decisions.next
  have h1 : ¬ (List.replicate n 1).length ≤ 1 := by simp; omega
  have h2 : ¬ d.taken.size ≥ d.limit := by omega
  have h1' : ¬ n ≤ 1 := by omega
  simp only [↓reduceIte, h2, List.length_replicate, h1']
  cases p with
  | nil =>
    have hle : d.source.given.size ≤ d.taken.size := by
      have := congrArg List.length hg
      simp at this; omega
    have : ¬ d.taken.size < d.source.given.size := by omega
    simp only [this, ↓reduceDIte, hr, Bool.false_eq_true, List.headD, Nat.zero_mod, ↓reduceIte]
  | cons a ps =>
    have h0 := congrArg (·[0]?) hg
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
    have hlt : d.taken.size < d.source.given.size := by
      rw [Array.getElem?_toList] at h0
      rcases Nat.lt_or_ge d.taken.size d.source.given.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at h0; cases h0
    have hv : d.source.given[d.taken.size] = a := by
      rw [Array.getElem?_toList, Array.getElem?_eq_getElem hlt] at h0
      exact Option.some.inj h0
    simp only [hlt, ↓reduceDIte, hv, List.headD]

theorem feeds_next (d : Decisions) (x : Taken) (p : List Nat) (hf : Feeds d p) :
    Feeds { d with taken := d.taken.push x } p.tail := by
  obtain ⟨hr, hg⟩ := hf
  refine ⟨hr, ?_⟩
  simp only [Array.size_push]
  rw [← List.drop_drop, hg]
  cases p <;> rfl

/-- ★ The program records exactly `DT.run`'s decisions (when the limit leaves room). -/
theorem prog_run : ∀ (t : DT) (p : List Nat) (d : Decisions), t.WF → Feeds d p →
    d.taken.size + t.depth p ≤ d.limit →
    t.prog.run d = .ok () { d with taken := d.taken ++ (t.run p).toArray }
  | .leaf, p, d, _, _, _ => by
    simp [DT.prog, DT.run, EStateM.run, pure, EStateM.pure]
  | .node name n kids, p, d, ⟨hn, hk⟩, hf, hl => by
    have hl' : d.taken.size < d.limit := by simp [DT.depth] at hl; omega
    have hnx := next_feeds d name n p hn hf hl'
    have hv : p.headD 0 % n < n := Nat.mod_lt _ (by omega)
    have ih := prog_run (kids (p.headD 0 % n)) p.tail { d with taken := d.taken.push ⟨name, n, p.headD 0 % n⟩ }
      (hk _ hv) (feeds_next d _ p hf) (by simp [DT.depth] at hl ⊢; omega)
    simp only [DT.prog, EStateM.run, bind, EStateM.bind, Determinismo.decide, decideWeighted, get, getThe,
      MonadStateOf.get, EStateM.get, Chaotic.decisions, hnx, set, MonadStateOf.set, EStateM.set,
      Chaotic.setDecisions, pure, EStateM.pure]
    simp only [EStateM.run] at ih
    rw [ih]
    simp [DT.run]

/-! ## The walk -/

/-- The walk from path `p` runs exactly the timelines `L`: each run's decisions, then `nextPath` of
them, until it gives none (Search.lean `exhaust`'s loop). -/
def WalkFrom (t : DT) : List Nat → List (List Taken) → Prop
  | _, [] => False
  | p, r :: rest => r = t.run p ∧ (match nextPathL r with
      | none => rest = []
      | some q => WalkFrom t q rest)

theorem walkFrom_congr (t : DT) (p p' : List Nat) (h : t.run p = t.run p') :
    ∀ L, WalkFrom t p L → WalkFrom t p' L
  | [], hw => hw
  | r :: rest, ⟨h1, h2⟩ => ⟨h1.trans h, h2⟩

/-- One option's block of a decision, then what follows it. -/
theorem walk_lift (name : String) (n : Nat) (kids : Nat → DT) (i : Nat) (hi : i < n)
    (R : List (List Taken))
    (hR : (i + 1 < n → WalkFrom (.node name n kids) [i + 1] R) ∧ (¬ i + 1 < n → R = [])) :
    ∀ (L : List (List Taken)) (p : List Nat), WalkFrom (kids i) p L →
      WalkFrom (.node name n kids) (i :: p) (L.map (⟨name, n, i⟩ :: ·) ++ R)
  | [], _, hw => hw.elim
  | r :: rest, p, ⟨h1, h2⟩ => by
    have hmod : i % n = i := Nat.mod_eq_of_lt hi
    refine ⟨?_, ?_⟩
    · simp [DT.run, hmod, h1]
    · rw [nextPathL_cons]
      revert h2
      cases hq : nextPathL r with
      | some q =>
        intro h2
        exact walk_lift name n kids i hi R hR rest q h2
      | none =>
        intro h2
        subst h2
        by_cases hn : i + 1 < n
        · simp only [hn, ↓reduceIte, List.map_nil, List.nil_append]
          exact hR.1 hn
        · simp only [hn, ↓reduceIte, List.map_nil, List.nil_append]
          exact hR.2 hn

/-- The blocks of options `i` … `n − 1`. -/
def blocks (name : String) (n : Nat) (kids : Nat → DT) (i : Nat) : List (List Taken) :=
  (List.range' i (n - i)).flatMap fun j => ((kids j).paths).map (⟨name, n, j⟩ :: ·)

theorem blocks_succ (name : String) (n : Nat) (kids : Nat → DT) (i : Nat) (hi : i < n) :
    blocks name n kids i = ((kids i).paths).map (⟨name, n, i⟩ :: ·) ++ blocks name n kids (i + 1) := by
  unfold blocks
  have : n - i = (n - (i + 1)) + 1 := by omega
  rw [this, List.range'_succ]
  simp

theorem blocks_end (name : String) (n : Nat) (kids : Nat → DT) : blocks name n kids n = [] := by
  simp [blocks]

theorem walk_node (name : String) (n : Nat) (kids : Nat → DT)
    (ih : ∀ i, i < n → WalkFrom (kids i) [] (kids i).paths) :
    ∀ m i, i + m + 1 = n → WalkFrom (.node name n kids) [i] (blocks name n kids i)
  | 0, i, hm => by
    have hi : i < n := by omega
    rw [blocks_succ name n kids i hi, show i + 1 = n by omega, blocks_end]
    exact walk_lift name n kids i hi [] ⟨fun h => by omega, fun _ => rfl⟩ _ [] (ih i hi)
  | m + 1, i, hm => by
    have hi : i < n := by omega
    rw [blocks_succ name n kids i hi]
    exact walk_lift name n kids i hi _ ⟨fun _ => walk_node name n kids ih m (i + 1) (by omega),
      fun h => by omega⟩ _ [] (ih i hi)

/-- ★ From the empty path, the walk runs the tree's leaves in depth-first order, each once. -/
theorem walk_paths : ∀ t : DT, t.WF → WalkFrom t [] t.paths
  | .leaf, _ => by
    refine ⟨rfl, ?_⟩
    simp [DT.run, nextPathL_nil]
  | .node name n kids, ⟨hn, hk⟩ => by
    have ih : ∀ i, i < n → WalkFrom (kids i) [] (kids i).paths := fun i hi => walk_paths (kids i) (hk i hi)
    have h0 := walk_node name n kids ih (n - 1) 0 (by omega)
    have hp : (DT.node name n kids).paths = blocks name n kids 0 := by
      simp [DT.paths, blocks, List.range_eq_range']
    rw [hp]
    exact walkFrom_congr _ [0] [] (by simp [DT.run]) _ h0

/-- The walk as a function: run, then `nextPath`, at most `fuel` timelines. -/
def walk (t : DT) : Nat → List Nat → List (List Taken)
  | 0, _ => []
  | fuel + 1, p =>
    let r := t.run p
    r :: match nextPathL r with
      | none => []
      | some q => walk t fuel q

theorem walk_of_walkFrom (t : DT) : ∀ (L : List (List Taken)) (p : List Nat), WalkFrom t p L →
    walk t L.length p = L
  | [], _, hw => hw.elim
  | r :: rest, p, ⟨h1, h2⟩ => by
    simp only [walk, List.length_cons]
    rw [← h1]
    congr 1
    revert h2
    cases nextPathL r with
    | none => intro h2; simp [h2]
    | some q => intro h2; exact walk_of_walkFrom t rest q h2

/-- ★ A complete walk of a tree runs `t.leaves` timelines: its leaves, depth first. -/
theorem walk_count (t : DT) (h : t.WF) : walk t t.leaves [] = t.paths ∧ (walk t t.leaves []).length = t.leaves := by
  have hw := walk_of_walkFrom t t.paths [] (walk_paths t h)
  rw [paths_length] at hw
  exact ⟨hw, by rw [hw, paths_length]⟩

/-! ## The sdk's `exhaust` -/

/-- The most decisions on any run. -/
def DT.height : DT → Nat
  | .leaf => 0
  | .node _ n kids => 1 + ((List.range n).map fun i => (kids i).height).foldr max 0

theorem le_foldr_max (l : List Nat) (x : Nat) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem depth_le_height : ∀ (t : DT) (p : List Nat), t.WF → t.depth p ≤ t.height
  | .leaf, _, _ => Nat.le_refl _
  | .node name n kids, p, ⟨hn, hk⟩ => by
    have hv : p.headD 0 % n < n := Nat.mod_lt _ (by omega)
    have h1 := depth_le_height (kids (p.headD 0 % n)) p.tail (hk _ hv)
    have h2 : (kids (p.headD 0 % n)).height ≤ ((List.range n).map fun i => (kids i).height).foldr max 0 :=
      le_foldr_max _ _ (List.mem_map.mpr ⟨_, List.mem_range.mpr hv, rfl⟩)
    simp only [DT.depth, DT.height]
    omega

/-- A run of the tree's program from a source, as `exhaust` sees it (no property of its own). -/
def treeRun (t : DT) (limit : Nat) (src : Source) : Ended :=
  match t.prog.run { source := src, limit } with
  | .ok _ d => { taken := d.taken, violation := none }
  | .error _ d => { taken := d.taken, violation := none }

theorem treeRun_path (t : DT) (h : t.WF) (limit : Nat) (hl : t.height ≤ limit) (path : Array Nat) :
    (treeRun t limit (Source.path path)).violation = none ∧
    (treeRun t limit (Source.path path)).taken = (t.run path.toList).toArray := by
  have hf : Feeds { source := Source.path path, limit } path.toList := ⟨rfl, by simp [Source.path]⟩
  have hr := prog_run t path.toList { source := Source.path path, limit } h hf
    (by simp; exact Nat.le_trans (depth_le_height t _ h) hl)
  unfold treeRun
  rw [hr]
  simp

abbrev XS := Option Exhausted × Array Nat

theorem exh_gen (t : DT) (run : Source → Ended)
    (f : Nat → XS → Id (ForInStep XS))
    (hf : ∀ i path, f i (none, path) = match nextPath (run (Source.path path)).taken with
      | none => ForInStep.done (some (.complete (i + 1)), path)
      | some q => ForInStep.yield (none, q))
    (hrun : ∀ path, (run (Source.path path)).taken = (t.run path.toList).toArray) :
    ∀ (L : List (List Taken)) (path : Array Nat) (is : List Nat), WalkFrom t path.toList L →
      L.length ≤ is.length →
      (forIn (m := Id) is ((none : Option Exhausted), path) f).run.fst = some (.complete (is[L.length - 1]! + 1))
  | [], _, _, hw, _ => hw.elim
  | r :: rest, path, [], _, hle => by simp at hle
  | r :: rest, path, i :: is, ⟨h1, h2⟩, hle => by
    rw [List.forIn_cons]
    have hn : nextPath (run (Source.path path)).taken = (nextPathL r).map List.toArray := by
      rw [hrun, ← h1]
      unfold nextPathL
      cases nextPath r.toArray <;> simp
    simp only [hf, hn]
    revert h2
    cases hq : nextPathL r with
    | none =>
      intro h2
      subst h2
      rfl
    | some q =>
      intro h2
      have hl' : rest.length ≤ is.length := by simp at hle; omega
      have ih := exh_gen t run f hf hrun rest q.toArray is (by simpa using h2) hl'
      have hr0 : rest ≠ [] := by intro h; subst h; exact h2.elim
      have hlen : rest.length - 1 + 1 = rest.length := by
        cases rest with
        | nil => exact absurd rfl hr0
        | cons _ _ => simp
      simp only [Option.map_some, bind, Id.run] at ih ⊢
      rw [ih]
      simp only [List.length_cons, Nat.add_sub_cancel]
      rw [← hlen, List.getElem!_cons_succ, hlen]

/-- ★ The sdk's `exhaust` over a tree's program (a run per path, `nextPath` between runs) ends
complete after exactly `t.leaves` timelines, when `maxRuns` allows them and the decision limit
the tree's height. -/
theorem exhaust_complete (t : DT) (h : t.WF) (limit : Nat) (hl : t.height ≤ limit) (maxRuns : Nat)
    (hm : t.leaves ≤ maxRuns) :
    ∃ r, exhaust (treeRun t limit) maxRuns = .complete r ∧ r = t.leaves := by
  have hw := walk_paths t h
  have hlen := paths_length t
  have hpos : 0 < t.leaves := by
    rw [← hlen]; cases hp : t.paths with
    | nil => rw [hp] at hw; exact hw.elim
    | cons _ _ => simp
  unfold exhaust
  simp only [Id.run_bind]
  rw [exh_gen t (treeRun t limit) _ (fun i path => by
      have := (treeRun_path t h limit hl path).1
      simp only [this]
      cases nextPath (treeRun t limit (Source.path path)).taken <;> rfl) (fun path => (treeRun_path t h limit hl path).2) t.paths #[] (List.range maxRuns)
      (by simpa using hw) (by rw [hlen]; simpa using hm)]
  refine ⟨_, rfl, ?_⟩
  rw [hlen]
  have hlt : t.leaves - 1 < maxRuns := by omega
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_range hlt]
  simp
  omega

end Jank.R8.Nrepl.Walk

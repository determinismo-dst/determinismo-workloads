import Elle.R4.LAIndex
import Elle.R4.GraphLemmas

/-!
# Round 4: list-append's dependency graph and explainers (list_append.clj:618-807)

Which pairs `ww-graph`, `wr-graph`, `rw-graph` and D1's unread graph link, and what their
explainers return.
-/

namespace Elle.R4

open Elle Elle.ListAppend

/-- A `ww` edge `x -> y`: `y` appended `e` to `k`, and `ww-mop-dep` names `x`. -/
def WWSrc (p : Pre) (x y : Nat) : Prop :=
  ∃ o ∈ p.possible, o.index = y ∧ ∃ m ∈ o.value, ∃ e, m.f = .append ∧ m.v = .int e ∧ wwMopDep p y m.k e = some x

/-- A `wr` edge `x -> y`: `y` read `k`, and `wr-mop-dep` names `x`. -/
def WRSrc (p : Pre) (x y : Nat) : Prop :=
  ∃ o ∈ p.possible, o.index = y ∧ ∃ m ∈ o.value, m.f = .r ∧ wrMopDep p y m.k m.v = some x

/-- An `rw` edge `x -> y`: `y` appended `e` to `k`, and `rw-mop-deps` names `x`. -/
def RWSrc (p : Pre) (un : List (Nat × Nat × Nat)) (x y : Nat) : Prop :=
  ∃ o ∈ p.possible, o.index = y ∧ ∃ m ∈ o.value, ∃ e, m.f = .append ∧ m.v = .int e ∧ x ∈ rwMopDeps p y m.k e ∧
    (un.any fun (r', a', k') => x == r' && y == a' && m.k == k') = false

theorem graph_pair {p : Pre} {un : List (Nat × Nat × Nat)} {x y : Nat} (h : (graph p un).graph.HasPair x y) :
    WWSrc p x y ∨ WRSrc p x y ∨ RWSrc p un x y ∨ ∃ k, (x, y, k) ∈ un := by
  unfold graph at h
  simp only [Id.run, bind, pure] at h
  let P : Graph × Graph → Prop := fun s =>
    (∀ x y, s.1.HasPair x y → WWSrc p x y) ∧ (∀ x y, s.2.HasPair x y → WRSrc p x y)
  have hP0 : P ({}, {}) := ⟨fun x y h => by obtain ⟨r, hr⟩ := h; simp at hr,
                           fun x y h => by obtain ⟨r, hr⟩ := h; simp at hr⟩
  let R : Graph → Prop := fun g => ∀ x y, g.HasPair x y → RWSrc p un x y
  have hR0 : R {} := fun x y h => by obtain ⟨r, hr⟩ := h; simp at hr
  have hstepP : ∀ o ∈ p.possible, ∀ s : Graph × Graph, P s → ∀ m ∈ o.value, P (match m.f, m.v with
      | .append, .int e => match wwMopDep p o.index m.k e with
        | some d => (s.1.link d o.index Rels.WW, s.2)
        | _ => (s.1, s.2)
      | .r, v => match wrMopDep p o.index m.k v with
        | some d => (s.1, s.2.link d o.index Rels.WR)
        | _ => (s.1, s.2)
      | _, _ => (s.1, s.2)) := by
    intro o ho s hs m hm
    split
    · rename_i e hf hv
      split
      · rename_i d hd
        refine ⟨?_, hs.2⟩
        intro x y hxy
        rcases link_pair hxy with ⟨rfl, rfl⟩ | h2
        · exact ⟨o, ho, rfl, m, hm, e, hf, hv, hd⟩
        · exact hs.1 x y h2
      · exact hs
    · rename_i v hf
      split
      · rename_i d hd
        refine ⟨hs.1, ?_⟩
        intro x y hxy
        rcases link_pair hxy with ⟨rfl, rfl⟩ | h2
        · exact ⟨o, ho, rfl, m, hm, hf, hd⟩
        · exact hs.2 x y h2
      · exact hs
    · exact hs
  have hloop : ∀ o ∈ p.possible, ∀ s : Graph × Graph, P s → P ((forIn (m := Id) o.value (s.1, s.2) fun m s =>
        match m.f, m.v with
        | .append, .int e =>
          match wwMopDep p o.index m.k e with
          | some d => ForInStep.yield (s.fst.link d o.index Rels.WW, s.snd)
          | _ => ForInStep.yield (s.fst, s.snd)
        | .r, v =>
          match wrMopDep p o.index m.k v with
          | some d => ForInStep.yield (s.fst, s.snd.link d o.index Rels.WR)
          | _ => ForInStep.yield (s.fst, s.snd)
        | _, _ => ForInStep.yield (s.fst, s.snd)).run) := by
    intro o ho s hs
    refine forIn_list_inv o.value (s.1, s.2) _ P hs ?_
    intro m hm s' hs'
    have := hstepP o ho s' hs' m hm
    revert this
    split <;> (try split) <;> exact id
  have hloopR : ∀ o ∈ p.possible, ∀ g : Graph, R g → R ((forIn (m := Id) o.value g fun m g =>
        match m.f, m.v with
        | .append, .int e =>
          ForInStep.yield (List.foldl (fun g d => g.link d o.index Rels.RW) g
            (List.filter (fun x => !un.any (fun (r', a', k') => x == r' && o.index == a' && m.k == k'))
              (rwMopDeps p o.index m.k e)))
        | _, _ => ForInStep.yield g).run) := by
    intro o ho g hg
    refine forIn_list_inv o.value g _ R hg ?_
    intro m hm g' hg'
    split
    · rename_i e hf hv
      intro x y hxy
      rcases foldl_link_pair _ g' id (fun _ => o.index) (fun _ => Rels.RW) hxy with h1 | ⟨d, hd, rfl, rfl⟩
      · exact hg' x y h1
      · obtain ⟨hd1, hd2⟩ := List.mem_filter.mp hd
        exact ⟨o, ho, rfl, m, hm, e, hf, hv, hd1, by simpa using hd2⟩
    · exact hg'
  split at h
  all_goals
    obtain ⟨an, han, hpair⟩ := combine_pair h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at han
  · rcases han with rfl | rfl | rfl
    · left; refine (forIn_list_inv p.possible _ _ P hP0 ?_).1 x y hpair
      intro o ho s hs; exact hloop o ho s hs
    · right; left; refine (forIn_list_inv p.possible _ _ P hP0 ?_).2 x y hpair
      intro o ho s hs; exact hloop o ho s hs
    · right; right; left; refine forIn_list_inv p.possible _ _ R hR0 ?_ x y hpair
      intro o ho s hs; exact hloopR o ho s hs
  · rcases han with rfl | rfl | rfl | rfl
    · left; refine (forIn_list_inv p.possible _ _ P hP0 ?_).1 x y hpair
      intro o ho s hs; exact hloop o ho s hs
    · right; left; refine (forIn_list_inv p.possible _ _ P hP0 ?_).2 x y hpair
      intro o ho s hs; exact hloop o ho s hs
    · right; right; left; refine forIn_list_inv p.possible _ _ R hR0 ?_ x y hpair
      intro o ho s hs; exact hloopR o ho s hs
    · right; right; right
      rcases foldl_link_pair un {} (·.1) (·.2.1) (fun _ => Rels.WW) hpair with h1 | ⟨⟨r, a, k⟩, hk, rfl, rfl⟩
      · obtain ⟨r, hr⟩ := h1; simp at hr
      · exact ⟨k, hk⟩


/-! ## The explainers -/

/-- The mops of op `b` in the history (what the explainers look at). -/
def mopsOf (p : Pre) (b : Nat) : List Mop := (p.hist[b]?.map (·.value)).getD []

/-- The `ww` explainer found nothing for `a -> b`. -/
def NoWW (p : Pre) (a b : Nat) : Prop :=
  ∀ m ∈ mopsOf p b, ∀ e, m.f = .append → m.v = .int e → wwMopDep p b m.k e ≠ some a

theorem findSome_some {α β : Type} {l : List α} {f : α → Option β} {y : β} (h : l.findSome? f = some y) :
    ∃ x ∈ l, f x = some y := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.findSome?_cons] at h
    split at h
    · rename_i y' hy; cases h; exact ⟨x, List.mem_cons_self, hy⟩
    · obtain ⟨x', hx', h'⟩ := ih h; exact ⟨x', List.mem_cons_of_mem _ hx', h'⟩

theorem findSome_none {α β : Type} {l : List α} {f : α → Option β} (h : l.findSome? f = none) :
    ∀ x ∈ l, f x = none := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.findSome?_cons] at h
    split at h
    · cases h
    · rename_i hx
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ih h y hy

theorem wwExplain_none {p : Pre} {a b : Nat}
    (h : (mopsOf p b).findSome? (fun m => match m.f, m.v with
      | .append, .int e => if (wwMopDep p b m.k e == some a) = true then some ({ type := "ww", key := some m.k } : Step) else none
      | _, _ => none) = none) : NoWW p a b := by
  intro m hm e hf hv hww
  have := findSome_none h m hm
  simp only [hf, hv, hww, beq_self_eq_true, ↓reduceIte] at this
  cases this

theorem graph_explain_some {p : Pre} {un : List (Nat × Nat × Nat)} {a b : Nat} {s : Step}
    (h : (graph p un).explain a b = some s) :
    (s.type = "ww" ∧ s.unread = false ∧ ∃ m ∈ mopsOf p b, ∃ e, m.f = .append ∧ m.v = .int e ∧ wwMopDep p b m.k e = some a) ∨
    (s.type = "wr" ∧ s.unread = false ∧ NoWW p a b ∧ ∃ m ∈ mopsOf p b, m.f = .r ∧ wrMopDep p b m.k m.v = some a) ∨
    (s.type = "rw" ∧ s.unread = false ∧ NoWW p a b ∧ ∃ m ∈ mopsOf p b, ∃ e, m.f = .append ∧ m.v = .int e ∧
      a ∈ rwMopDeps p b m.k e ∧ (un.any fun (r', a', k') => a == r' && b == a' && m.k == k') = false) ∨
    (s.type = "ww" ∧ s.unread = true ∧ NoWW p a b ∧ ∃ k, (a, b, k) ∈ un) := by
  unfold graph at h
  simp only [Id.run, bind, pure] at h
  -- the four explainers, tried in turn
  have hww : ∀ s', (mopsOf p b).findSome? (fun m => match m.f, m.v with
      | .append, .int e => if (wwMopDep p b m.k e == some a) = true then some ({ type := "ww", key := some m.k } : Step) else none
      | _, _ => none) = some s' →
      s'.type = "ww" ∧ s'.unread = false ∧ ∃ m ∈ mopsOf p b, ∃ e, m.f = .append ∧ m.v = .int e ∧ wwMopDep p b m.k e = some a := by
    intro s' hs'
    obtain ⟨m, hm, hfm⟩ := findSome_some hs'
    split at hfm
    · rename_i e hf hv
      split at hfm
      · rename_i hw; cases hfm; exact ⟨rfl, rfl, m, hm, e, hf, hv, by simpa using hw⟩
      · cases hfm
    · cases hfm
  have hwr : ∀ s', (mopsOf p b).findSome? (fun m =>
      if (m.f == F.r && wrMopDep p b m.k m.v == some a) = true then some ({ type := "wr", key := some m.k } : Step)
      else none) = some s' →
      s'.type = "wr" ∧ s'.unread = false ∧ ∃ m ∈ mopsOf p b, m.f = .r ∧ wrMopDep p b m.k m.v = some a := by
    intro s' hs'
    obtain ⟨m, hm, hfm⟩ := findSome_some hs'
    split at hfm
    · rename_i hc; cases hfm
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, rfl, m, hm, hc.1, hc.2⟩
    · cases hfm
  have hrw : ∀ s', (mopsOf p b).findSome? (fun m => match m.f, m.v with
      | .append, .int e =>
        if ((rwMopDeps p b m.k e).contains a && !un.any (fun (r', a', k') => a == r' && b == a' && m.k == k')) = true then
          some ({ type := "rw", key := some m.k } : Step) else none
      | _, _ => none) = some s' →
      s'.type = "rw" ∧ s'.unread = false ∧ ∃ m ∈ mopsOf p b, ∃ e, m.f = .append ∧ m.v = .int e ∧
        a ∈ rwMopDeps p b m.k e ∧ (un.any fun (r', a', k') => a == r' && b == a' && m.k == k') = false := by
    intro s' hs'
    obtain ⟨m, hm, hfm⟩ := findSome_some hs'
    split at hfm
    · rename_i e hf hv
      split at hfm
      · rename_i hc; cases hfm
        simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hc
        exact ⟨rfl, rfl, m, hm, e, hf, hv, hc.1, hc.2⟩
      · cases hfm
    · cases hfm
  split at h
  all_goals
    rw [combine_explain] at h
    simp only [List.findSome?_cons, List.findSome?_nil] at h
  · split at h
    · rename_i s1 h1; cases h; exact Or.inl (hww _ h1)
    · rename_i h1
      split at h
      · rename_i s2 h2; cases h
        obtain ⟨t, u, hm⟩ := hwr _ h2
        exact Or.inr (Or.inl ⟨t, u, wwExplain_none h1, hm⟩)
      · rename_i h2
        split at h
        · rename_i s3 h3; cases h
          obtain ⟨t, u, hm⟩ := hrw _ h3
          exact Or.inr (Or.inr (Or.inl ⟨t, u, wwExplain_none h1, hm⟩))
        · cases h
  · split at h
    · rename_i s1 h1; cases h; exact Or.inl (hww _ h1)
    · rename_i h1
      split at h
      · rename_i s2 h2; cases h
        obtain ⟨t, u, hm⟩ := hwr _ h2
        exact Or.inr (Or.inl ⟨t, u, wwExplain_none h1, hm⟩)
      · rename_i h2
        split at h
        · rename_i s3 h3; cases h
          obtain ⟨t, u, hm⟩ := hrw _ h3
          exact Or.inr (Or.inr (Or.inl ⟨t, u, wwExplain_none h1, hm⟩))
        · split at h
          · rename_i s4 h4; cases h
            obtain ⟨⟨r', a', k⟩, hf, hs4⟩ := Option.map_eq_some_iff.mp h4
            cases hs4
            have := List.find?_some hf
            simp only [Bool.and_eq_true, beq_iff_eq] at this
            obtain ⟨rfl, rfl⟩ := this
            exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, wwExplain_none h1, k, List.mem_of_find?_eq_some hf⟩))
          · cases h


/-- When no explainer of `graph` explains `a -> b`. -/
theorem graph_explain_none {p : Pre} {un : List (Nat × Nat × Nat)} {a b : Nat}
    (h : (graph p un).explain a b = none) :
    NoWW p a b ∧ (∀ m ∈ mopsOf p b, m.f = .r → wrMopDep p b m.k m.v ≠ some a) ∧
    (∀ m ∈ mopsOf p b, ∀ e, m.f = .append → m.v = .int e → a ∈ rwMopDeps p b m.k e →
      (un.any fun (r', a', k') => a == r' && b == a' && m.k == k') = true) ∧
    (∀ k, (a, b, k) ∉ un) := by
  unfold graph at h
  simp only [Id.run, bind, pure] at h
  have hwr : ∀ (hn : (mopsOf p b).findSome? (fun m =>
      if (m.f == F.r && wrMopDep p b m.k m.v == some a) = true then some ({ type := "wr", key := some m.k } : Step)
      else none) = none), ∀ m ∈ mopsOf p b, m.f = .r → wrMopDep p b m.k m.v ≠ some a := by
    intro hn m hm hf hw
    have := findSome_none hn m hm
    simp [hf, hw] at this
  have hrw : ∀ (hn : (mopsOf p b).findSome? (fun m => match m.f, m.v with
      | .append, .int e =>
        if ((rwMopDeps p b m.k e).contains a && !un.any (fun (r', a', k') => a == r' && b == a' && m.k == k')) = true then
          some ({ type := "rw", key := some m.k } : Step) else none
      | _, _ => none) = none), ∀ m ∈ mopsOf p b, ∀ e, m.f = .append → m.v = .int e → a ∈ rwMopDeps p b m.k e →
      (un.any fun (r', a', k') => a == r' && b == a' && m.k == k') = true := by
    intro hn m hm e hf hv hr
    have := findSome_none hn m hm
    simp only [hf, hv] at this
    split at this
    · cases this
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true', not_and] at hc
      cases hany : (un.any fun (r', a', k') => a == r' && b == a' && m.k == k')
      · exact absurd hany (by simpa using hc hr)
      · rfl
  split at h
  all_goals
    rw [combine_explain] at h
    simp only [List.findSome?_cons, List.findSome?_nil] at h
  · rename_i hemp
    split at h
    · cases h
    · rename_i h1
      split at h
      · cases h
      · rename_i h2
        split at h
        · cases h
        · rename_i h3
          refine ⟨wwExplain_none h1, hwr h2, hrw h3, ?_⟩
          intro k hk; simp at hemp; rw [hemp] at hk; cases hk
  · split at h
    · cases h
    · rename_i h1
      split at h
      · cases h
      · rename_i h2
        split at h
        · cases h
        · rename_i h3
          split at h
          · cases h
          · rename_i h4
            refine ⟨wwExplain_none h1, hwr h2, hrw h3, ?_⟩
            intro k hk
            have : (un.find? fun (r, x, _) => r == a && x == b).isSome := by
              apply List.find?_isSome.mpr; exact ⟨_, hk, by simp⟩
            rw [Option.isSome_iff_exists] at this
            obtain ⟨z, hz⟩ := this
            rw [hz] at h4; cases h4

end Elle.R4

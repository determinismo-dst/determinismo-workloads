import Elle.R4.Prelude
import Elle.Core

/-!
# Round 4: edges of the replica's graphs

`Graph.link`, `union`, `combine` (Bifurcan's digraph operations and `elle.core/combine`): which
pairs an edge can come from.
-/

namespace Elle.R4

open Elle

/-- An edge between `a` and `b`, whatever its relationships. -/
def _root_.Elle.Graph.HasPair (g : Graph) (a b : Nat) : Prop := ∃ r, (a, b, r) ∈ g.edges

theorem addVertex_edges (g : Graph) (v : Nat) : (g.addVertex v).edges = g.edges := by
  unfold Graph.addVertex; split <;> rfl

theorem link_pair {g : Graph} {a b x y : Nat} {s : Rels} (h : (g.link a b s).HasPair x y) :
    (x = a ∧ y = b) ∨ g.HasPair x y := by
  obtain ⟨r, hr⟩ := h
  unfold Graph.link at hr
  simp only [addVertex_edges] at hr
  split at hr
  · obtain ⟨⟨x', y', r'⟩, hm, he⟩ := List.mem_map.mp hr
    split at he
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp only [Prod.mk.injEq] at he
      exact Or.inl ⟨he.1 ▸ hc.1, he.2.1 ▸ hc.2⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr ⟨r', hm⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact Or.inr ⟨r, hr⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at hr
      exact Or.inl ⟨hr.1, hr.2.1⟩

theorem link_hasPair_self (g : Graph) (a b : Nat) (s : Rels) : (g.link a b s).HasPair a b := by
  unfold Graph.link
  simp only [addVertex_edges]
  split
  · rename_i hany
    obtain ⟨⟨x', y', r'⟩, hm, hc⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨r' ||| s, List.mem_map.mpr ⟨(x', y', r'), hm, by simp⟩⟩
  · exact ⟨s, by simp⟩

theorem link_keeps {g : Graph} {a b x y : Nat} {s : Rels} (h : g.HasPair x y) : (g.link a b s).HasPair x y := by
  obtain ⟨r, hr⟩ := h
  unfold Graph.link
  simp only [addVertex_edges]
  split
  · by_cases hxy : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨r ||| s, List.mem_map.mpr ⟨(x, y, r), hr, by simp⟩⟩
    · refine ⟨r, List.mem_map.mpr ⟨(x, y, r), hr, ?_⟩⟩
      have : (x == a && y == b) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        by_cases hx : x = a
        · exact Or.inr (fun hy => hxy ⟨hx, hy⟩)
        · exact Or.inl hx
      simp [this]
  · exact ⟨r, List.mem_append_left _ hr⟩

/-- A fold of links adds only the pairs it links. -/
theorem foldl_link_pair {α : Type} (l : List α) (g : Graph) (src dst : α → Nat) (s : α → Rels)
    {x y : Nat} (h : (l.foldl (fun g a => g.link (src a) (dst a) (s a)) g).HasPair x y) :
    g.HasPair x y ∨ ∃ a ∈ l, src a = x ∧ dst a = y := by
  induction l generalizing g with
  | nil => exact Or.inl h
  | cons a as ih =>
    rcases ih _ h with h1 | ⟨a', ha', h2⟩
    · rcases link_pair h1 with ⟨rfl, rfl⟩ | h3
      · exact Or.inr ⟨a, List.mem_cons_self, rfl, rfl⟩
      · exact Or.inl h3
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', h2⟩

theorem foldl_addVertex_edges (g : Graph) (vs : List Nat) : (vs.foldl Graph.addVertex g).edges = g.edges := by
  induction vs generalizing g with
  | nil => rfl
  | cons v vs ih => simp only [List.foldl_cons]; rw [ih]; exact addVertex_edges _ _

theorem union_pair {g1 g2 : Graph} {x y : Nat} (h : (g1.union g2).HasPair x y) : g1.HasPair x y ∨ g2.HasPair x y := by
  unfold Graph.union at h
  have h' := foldl_link_pair g2.edges (g2.verts.foldl Graph.addVertex g1) (·.1) (·.2.1) (·.2.2) h
  rcases h' with h1 | ⟨⟨a, b, r⟩, hm, rfl, rfl⟩
  · left
    obtain ⟨r, hr⟩ := h1
    exact ⟨r, foldl_addVertex_edges g1 g2.verts ▸ hr⟩
  · exact Or.inr ⟨r, hm⟩

theorem union_keeps_right {g1 g2 : Graph} {x y : Nat} (h : g2.HasPair x y) : (g1.union g2).HasPair x y := by
  unfold Graph.union
  obtain ⟨r, hr⟩ := h
  suffices ∀ (l : List (Nat × Nat × Rels)) (g : Graph), (x, y, r) ∈ l ∨ g.HasPair x y →
      (l.foldl (fun g (e : Nat × Nat × Rels) => g.link e.1 e.2.1 e.2.2) g).HasPair x y from
    this _ _ (Or.inl hr)
  intro l
  induction l with
  | nil =>
    intro g h
    rcases h with h | h
    · simp at h
    · exact h
  | cons e es ih =>
    intro g h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (link_hasPair_self _ _ _ _)
      · exact Or.inl h
    · exact Or.inr (link_keeps h)

/-- `combine`'s graph: each pair comes from one of the analyses. -/
theorem combine_pair {as : List Analysis} {x y : Nat} (h : (combine as).graph.HasPair x y) :
    ∃ a ∈ as, a.graph.HasPair x y := by
  unfold combine at h
  simp only at h
  suffices ∀ (l : List Analysis) (g : Graph), (l.foldl (fun g a => g.union a.graph) g).HasPair x y →
      g.HasPair x y ∨ ∃ a ∈ l, a.graph.HasPair x y by
    rcases this as {} h with ⟨r, hr⟩ | h2
    · simp at hr
    · exact h2
  intro l
  induction l with
  | nil => intro g h; exact Or.inl h
  | cons a as ih =>
    intro g h
    rcases ih _ h with h1 | ⟨a', ha', h2⟩
    · rcases union_pair h1 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨a, List.mem_cons_self, h3⟩
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', h2⟩

theorem combine_explain (as : List Analysis) (a b : Nat) :
    (combine as).explain a b = as.findSome? (fun an => an.explain a b) := rfl

theorem project_pair {g : Graph} {r : Rels} {x y : Nat} (h : (g.project r).HasPair x y) : g.HasPair x y := by
  unfold Graph.project at h
  suffices ∀ (l : List (Nat × Nat × Rels)) (g' : Graph), (∀ x y, g'.HasPair x y → ∃ s, (x, y, s) ∈ g.edges) →
      (∀ e ∈ l, e ∈ g.edges) →
      (l.foldl (fun g' (e : Nat × Nat × Rels) =>
        let r' := Rels.inter r e.2.2
        if r' == 0 then g' else g'.link e.1 e.2.1 r') g').HasPair x y → g.HasPair x y from
    this g.edges {} (fun x y h => by obtain ⟨s, hs⟩ := h; simp at hs) (fun e he => he) h
  intro l
  induction l with
  | nil => intro g' hg _ h; exact hg _ _ h
  | cons e es ih =>
    intro g' hg hl h
    simp only [List.foldl_cons] at h
    apply ih _ _ (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) h
    intro x' y' h2
    split at h2
    · exact hg _ _ h2
    · rcases link_pair h2 with ⟨rfl, rfl⟩ | h3
      · exact ⟨e.2.2, hl e List.mem_cons_self⟩
      · exact hg _ _ h3

theorem select_pair {g : Graph} {s : List Nat} {x y : Nat} (h : (g.select s).HasPair x y) : g.HasPair x y := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (List.mem_filter.mp hr).1⟩

end Elle.R4

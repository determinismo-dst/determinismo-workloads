import Elle.R4.LASound

/-!
# Round 4: the process and real-time orders

`pairIndex` (`pair-index-fold`, history.clj:421) pairs a completion with an invocation of its
process before it, with no operation of that process between; `process-graph` (core.clj:286, with
D3's `:info` edges) and `realtime-graph` (core.clj:371, with D3's `without-info`) link only out of
`:ok` operations. So their explained steps are session-order and real-time edges of every
interpretation in which both ends committed.
-/

namespace Elle.R4.LA

open Elle Elle.R4

/-- A `for` loop over a list in `Id` whose body always yields, with an invariant indexed by how
many elements it has passed. -/
theorem forIn_list_idx_inv {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (P : Nat → β → Prop) (h0 : P 0 init)
    (hs : ∀ n (hn : n < l.length) b, P n b → ∃ b', (f l[n] b).run = .yield b' ∧ P (n + 1) b') :
    P l.length (forIn l init f).run := by
  induction l generalizing init P with
  | nil => simpa using h0
  | cons a as ih =>
    obtain ⟨b', hb', hP⟩ := hs 0 (by simp) init h0
    rw [List.forIn_cons]
    simp only [List.getElem_cons_zero] at hb'
    show P (as.length + 1) (match (f a init).run with | .done b => pure b | .yield b => forIn as b f : Id β)
    rw [hb']
    exact ih b' (fun n b => P (n + 1) b) hP (fun n hn b hb => by
      have := hs (n + 1) (by simp; omega) b hb
      simpa using this)

theorem forIn_array_idx_inv {α β : Type} (l : Array α) (init : β) (f : α → β → Id (ForInStep β))
    (P : Nat → β → Prop) (h0 : P 0 init)
    (hs : ∀ n (hn : n < l.size) b, P n b → ∃ b', (f l[n] b).run = .yield b' ∧ P (n + 1) b') :
    P l.size (forIn l init f).run := by
  rw [← Array.forIn_toList]
  have := forIn_list_idx_inv l.toList init f P h0 (fun n hn b hb => by
    have := hs n (by simpa using hn) b hb
    simpa using this)
  simpa using this

theorem lookup_filter_ne {l : List (Nat × Nat)} {q pr : Nat} (hne : pr ≠ q) :
    (l.filter (fun x => x.1 != q)).lookup pr = l.lookup pr := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    by_cases hap : a = q
    · subst hap
      have : (pr == a) = false := by simpa using hne
      simp [List.filter, List.lookup, this, ih]
    · have hb : (a != q) = true := by simpa using hap
      simp only [List.filter, hb]
      by_cases hpa : pr = a
      · subst hpa; simp [List.lookup]
      · rw [lookup_cons_ne hpa, lookup_cons_ne hpa]; exact ih

theorem lookup_filter_eq {l : List (Nat × Nat)} {q : Nat} : (l.filter (fun x => x.1 != q)).lookup q = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    by_cases hap : a = q
    · subst hap; simp [List.filter, ih]
    · have hb : (a != q) = true := by simpa using hap
      simp only [List.filter, hb]
      rw [lookup_cons_ne (Ne.symm hap)]; exact ih

/-- The process of op `i` (none past the end). -/
def procAt (h : History) (i : Nat) : Option Nat := (h[i]?).map (·.process)

/-- What the pair index pairs a completion with: an invocation of its process before it, with no
operation of that process between. -/
def PairOK (h : History) (c j : Nat) : Prop :=
  (∃ oc, h[c]? = some oc ∧ oc.type = .invoke) ∨
  (j < c ∧ (∃ oj, h[j]? = some oj ∧ oj.type = .invoke) ∧ procAt h j = procAt h c ∧
    ∀ l, j < l → l < c → procAt h l ≠ procAt h c)

theorem pairIndex_ok (hwf : WF h) {c j : Nat} (hl : (pairIndex h).lookup c = some j) : PairOK h c j := by
  unfold pairIndex at hl
  simp only [Id.run, bind, pure] at hl
  let P : Nat → List (Nat × Nat) × List (Nat × Nat) → Prop := fun n s =>
    (∀ pr i, s.1.lookup pr = some i → i < n ∧ (∃ oi, h[i]? = some oi ∧ oi.type = .invoke ∧ oi.process = pr) ∧
      ∀ l, i < l → l < n → procAt h l ≠ some pr) ∧
    (∀ c j, s.2.lookup c = some j → PairOK h c j)
  refine (forIn_array_idx_inv h ([], []) _ P ⟨fun pr i h => by simp at h, fun c j h => by simp at h⟩ ?_).2 c j hl
  · intro n hn s ⟨hrun, hpairs⟩
    have hidx : h[n].index = n := hwf.index n hn
    have hhn : h[n]? = some h[n] := Array.getElem?_eq_getElem hn
    have hproc : procAt h n = some h[n].process := by simp [procAt, hhn]
    split
    · rename_i hinv
      refine ⟨_, rfl, ?_, hpairs⟩
      intro pr i hi
      rw [hidx] at hi
      by_cases hpr : pr = h[n].process
      · subst hpr
        rw [lookup_cons_self] at hi; cases hi
        refine ⟨by omega, ⟨h[n], hhn, by simpa [Op.isInvoke] using hinv, rfl⟩, fun l h1 h2 => by omega⟩
      · rw [lookup_cons_ne hpr, lookup_filter_ne hpr] at hi
        have hi' := hi
        obtain ⟨h1, h2, h3⟩ := hrun pr i hi'
        refine ⟨by omega, h2, fun l hl1 hl2 => ?_⟩
        rcases Nat.lt_or_ge l n with hlt | hge
        · exact h3 l hl1 hlt
        · have : l = n := by omega
          subst this; rw [hproc]; intro he; cases he; exact hpr rfl
    · rename_i hinv
      split
      · rename_i i hi
        obtain ⟨h1, ⟨oi, hoi, hti, hpi⟩, h3⟩ := hrun _ i hi
        refine ⟨_, rfl, ?_, ?_⟩
        · intro pr i' hi'
          by_cases hpr : pr = h[n].process
          · subst hpr; rw [lookup_filter_eq] at hi'; cases hi'
          · rw [lookup_filter_ne hpr] at hi'
            obtain ⟨g1, g2, g3⟩ := hrun pr i' hi'
            refine ⟨by omega, g2, fun l hl1 hl2 => ?_⟩
            rcases Nat.lt_or_ge l n with hlt | hge
            · exact g3 l hl1 hlt
            · have : l = n := by omega
              subst this; rw [hproc]; intro he; cases he; exact hpr rfl
        · intro c j hcj
          rw [hidx] at hcj
          by_cases hci : c = i
          · subst hci; rw [lookup_cons_self] at hcj; cases hcj
            exact Or.inl ⟨oi, hoi, hti⟩
          · rw [lookup_cons_ne hci] at hcj
            by_cases hcn : c = n
            · subst hcn; rw [lookup_cons_self] at hcj; cases hcj
              refine Or.inr ⟨h1, ⟨oi, hoi, hti⟩, ?_, ?_⟩
              · simp [procAt, hoi, hhn, hpi]
              · intro l hl1 hl2; rw [hproc]; exact h3 l hl1 hl2
            · rw [lookup_cons_ne hcn] at hcj
              exact hpairs c j hcj
      · rename_i hnone
        refine ⟨_, rfl, ?_, hpairs⟩
        intro pr i' hi'
        obtain ⟨g1, g2, g3⟩ := hrun pr i' hi'
        refine ⟨by omega, g2, fun l hl1 hl2 => ?_⟩
        rcases Nat.lt_or_ge l n with hlt | hge
        · exact g3 l hl1 hlt
        · have : l = n := by omega
          subst this; rw [hproc]; intro he; cases he
          rw [hi'] at hnone; cases hnone


/-- A session-order step out of a completion `a` of `b`'s process before `b`: `a` precedes `b`'s
invocation. -/
theorem lt_invIdx_of_proc (hwf : WF h) {a b : Nat} {oa ob : Op} (hoa : h[a]? = some oa) (hob : h[b]? = some ob)
    (hia : oa.type ≠ .invoke) (hib : ob.type ≠ .invoke) (hproc : oa.process = ob.process) (hab : a < b) :
    a < invIdx h b := by
  unfold invIdx
  cases hl : (pairIndex h).lookup b with
  | none => simpa using hab
  | some j =>
    simp only [Option.getD_some]
    rcases pairIndex_ok hwf hl with ⟨oc, hoc, hti⟩ | ⟨hjb, ⟨oj, hoj, htj⟩, _, hbetween⟩
    · rw [hob] at hoc; cases hoc; exact absurd hti hib
    · rcases Nat.lt_or_ge a j with hlt | hge
      · exact hlt
      · exfalso
        rcases Nat.eq_or_lt_of_le hge with he | hlt
        · subst he; rw [hoa] at hoj; cases hoj; exact hia htj
        · exact hbetween a hlt hab (by simp [procAt, hoa, hob, hproc])

/-- A real-time explanation `a -> b` (`RealtimeExplainer`): `a` precedes `b`'s invocation. -/
theorem lt_invIdx_of_realtime (hwf : WF h) {a b : Nat} {oa ob ib : Op} (hoa : h[a]? = some oa)
    (hob : h[b]? = some ob) (hib : ob.type ≠ .invoke) (hinv : invocation h (pairIndex h) ob = some ib)
    (hlt : oa.index < ib.index) : a < invIdx h b ∧ a ≠ b := by
  unfold invocation at hinv
  rw [op_index hwf hob] at hinv
  cases hl : (pairIndex h).lookup b with
  | none => rw [hl] at hinv; cases hinv
  | some j =>
    rw [hl] at hinv
    simp only [Option.bind_some] at hinv
    rw [op_index hwf hoa, op_index hwf hinv] at hlt
    refine ⟨by simp [invIdx, hl, hlt], ?_⟩
    rcases pairIndex_ok hwf hl with ⟨oc, hoc, hti⟩ | ⟨hjb, _, _, _⟩
    · rw [hob] at hoc; cases hoc; exact absurd hti hib
    · omega

/-- `process-graph` links only out of `:ok` ops. -/
theorem processGraph_src_ok (hwf : WF h) (intoInfo : Bool) {x y : Nat}
    (hxy : (processGraph h intoInfo).graph.HasPair x y) : ∃ ox, h[x]? = some ox ∧ ox.type = .ok := by
  unfold processGraph at hxy
  simp only [Id.run, bind, pure] at hxy
  let P : Graph × List (Nat × Nat) → Prop := fun s =>
    (∀ x y, s.1.HasPair x y → ∃ ox, h[x]? = some ox ∧ ox.type = .ok) ∧
    (∀ pr l, s.2.lookup pr = some l → ∃ ol, h[l]? = some ol ∧ ol.type = .ok)
  refine (forIn_array_inv h _ _ P ⟨fun x y h => by obtain ⟨r, hr⟩ := h; simp at hr,
    fun pr l h => by simp at h⟩ ?_).1 x y hxy
  intro o ho s ⟨hg, hl⟩
  have hoat : h[o.index]? = some o := op_at hwf ho
  have hput : o.isOk = true → ∀ pr l, (amPut s.2 o.process o.index).lookup pr = some l →
      ∃ ol, h[l]? = some ol ∧ ol.type = .ok := by
    intro hok pr l hpl
    have hok' : o.type = .ok := by simpa [Op.isOk] using hok
    by_cases hpr : pr = o.process
    · subst hpr; rw [amPut_self] at hpl; cases hpl; exact ⟨o, hoat, hok'⟩
    · rw [amPut_ne _ hpr] at hpl; exact hl pr l hpl
  have hlink : ∀ (g : Graph) (l : Nat), (∀ x y, g.HasPair x y → ∃ ox, h[x]? = some ox ∧ ox.type = .ok) →
      s.2.lookup o.process = some l →
      ∀ x y, (g.link l o.index Rels.PROCESS).HasPair x y → ∃ ox, h[x]? = some ox ∧ ox.type = .ok := by
    intro g l hg' hll x y hxy
    rcases link_pair hxy with ⟨rfl, rfl⟩ | h2
    · exact hl _ _ hll
    · exact hg' x y h2
  split
  · split
    · rename_i l hll
      split
      · rename_i hok
        split
        · rename_i l' hll'
          cases hll'
          exact ⟨hlink _ _ (hlink _ _ hg hll) hll, hput hok⟩
        · exact ⟨hlink _ _ hg hll, hput hok⟩
      · exact ⟨hlink _ _ hg hll, hl⟩
    · split
      · rename_i hok
        split
        · rename_i l hll; cases hll
        · exact ⟨hg, hput hok⟩
      · exact ⟨hg, hl⟩
  · split
    · rename_i hok
      split
      · rename_i l hll; exact ⟨hlink _ _ hg hll, hput hok⟩
      · exact ⟨hg, hput hok⟩
    · exact ⟨hg, hl⟩

/-- `realtime-graph` links only out of `:ok` ops. -/
theorem realtimeGraph_src_ok (hwf : WF h) (noInfo : Bool) {x y : Nat}
    (hxy : (realtimeGraph h noInfo).graph.HasPair x y) : ∃ ox, h[x]? = some ox ∧ ox.type = .ok := by
  unfold realtimeGraph at hxy
  simp only [Id.run, bind, pure] at hxy
  let P : List Nat × Graph → Prop := fun s =>
    (∀ a ∈ s.1, ∃ oa, h[a]? = some oa ∧ oa.type = .ok) ∧
    (∀ x y, s.2.HasPair x y → ∃ ox, h[x]? = some ox ∧ ox.type = .ok)
  refine (forIn_array_inv h _ _ P ⟨fun a ha => by simp at ha,
    fun x y h => by obtain ⟨r, hr⟩ := h; simp at hr⟩ ?_).2 x y hxy
  intro o ho s ⟨hb, hg⟩
  have hoat : h[o.index]? = some o := op_at hwf ho
  split
  · split
    · rename_i c hc
      split
      · refine ⟨hb, fun x y hxy => ?_⟩
        rcases foldl_link_pair s.1 s.2 id (fun _ => c.index) (fun _ => Rels.REALTIME) hxy with h1 | ⟨a, ha, rfl, _⟩
        · exact hg x y h1
        · exact hb a ha
      · refine ⟨hb, fun x y hxy => ?_⟩
        obtain ⟨r, hr⟩ := hxy
        have key : ∀ (l : List Nat) (g : Graph), (l.foldl (fun g a => (g.addVertex a).addVertex c.index) g).edges = g.edges := by
          intro l
          induction l with
          | nil => intro g; rfl
          | cons a as ih => intro g; simp only [List.foldl_cons]; rw [ih, addVertex_edges, addVertex_edges]
        have := key s.1 s.2
        exact hg x y ⟨r, this ▸ hr⟩
    · exact ⟨hb, hg⟩
  · rename_i hok
    refine ⟨fun a ha => ?_, hg⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact hb a (List.mem_filter.mp ha).1
    · split at ha
      · simp at ha
      · simp only [List.mem_singleton] at ha; subst ha; exact ⟨o, hoat, hok⟩
  · exact ⟨hb, hg⟩

end Elle.R4.LA

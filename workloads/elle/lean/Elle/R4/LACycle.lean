import Elle.R4.Orders

/-!
# Round 4: every cycle list-append reports holds in every clean interpretation

For the analysis Elle searches (`graph`, with D1's unread pairs in its second pass, and the
process or real-time graph `additional-graphs` picks), every closed walk of its edges that its
explainers explain lifts into every clean interpretation's DSG (`lift_cycle`): the interpretation
shows what `classify`'s branch names (`Claim`), or, through D1's unread steps, a G-single.
-/

namespace Elle.R4.LA

open Elle Elle.R4 Elle.ListAppend

variable {h : History} {flip : Bool} {fx : Fx} {p : Pre} {I : Interp}

/-- The extra graphs the theorem covers: none, the process graph (with or without D3's `:info`
edges), the real-time graph (with or without them). -/
def ExtraOK (e : Extra) : Prop :=
  e = .none ∨ e = .process ∨ e = .processInfo ∨ e = .realtime ∨ e = .realtimeNoInfo

theorem hist_at (hwf : WF h) (hp : preprocess h flip fx = .ok p) {o : Op} (ho : o ∈ p.possible) :
    p.hist[o.index]? = some o := by
  rw [preprocess_eq hp] at ho ⊢
  exact op_at hwf (possible_mem ho).1

theorem mopsOf_src (hwf : WF h) (hp : preprocess h flip fx = .ok p) {o : Op} (ho : o ∈ p.possible)
    {m : Mop} (hm : m ∈ o.value) : m ∈ mopsOf p o.index := by
  simp [mopsOf, hist_at hwf hp ho, hm]

/-- A graph pair is explained. -/
theorem graph_explain_complete (hwf : WF h) (hp : preprocess h flip fx = .ok p) {un : List (Nat × Nat × Nat)}
    {x y : Nat} (hxy : (graph p un).graph.HasPair x y) : (graph p un).explain x y ≠ none := by
  intro hn
  obtain ⟨hnw, hnr, hnrw, hnu⟩ := graph_explain_none hn
  rcases graph_pair hxy with ⟨o, ho, rfl, m, hm, e, hf, hv, hww⟩ | ⟨o, ho, rfl, m, hm, hf, hwr⟩ |
      ⟨o, ho, rfl, m, hm, e, hf, hv, hrw, hnot⟩ | ⟨k, hk⟩
  · exact hnw m (mopsOf_src hwf hp ho hm) e hf hv hww
  · exact hnr m (mopsOf_src hwf hp ho hm) hf hwr
  · have := hnrw m (mopsOf_src hwf hp ho hm) e hf hv hrw
    rw [hnot] at this; cases this
  · exact hnu k hk

/-- The source of a `ww` edge committed (its element was read, `:ok`). -/
theorem ww_src_com (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false) (hI : I.Clean h)
    {a : Nat} {o : Op} (ho : o ∈ p.possible) {m : Mop} (hm : m ∈ o.value) {e : Int} (hf : m.f = .append)
    (hv : m.v = .int e) (hww : wwMopDep p o.index m.k e = some a) : I.com a := by
  obtain ⟨pe, x, hpe, hwx, _, hob4, _⟩ := wwMopDep_some hww
  have hpemem : pe ∈ aiOf p m.k := by
    rcases prevElem_some hpe with ⟨i, hi, _⟩ | ⟨_, hl⟩
    · exact List.mem_of_getElem? hi
    · exact List.mem_of_getLast? hl
  have hxmem : x ∈ aiOf p m.k := by
    rcases hob4 with rfl | ⟨_, j, _, _, hj⟩
    · exact hpemem
    · exact List.mem_of_getElem? hj
  rcases ai_cases hwf hp hu m.k with h0 | ⟨t, o', j, mr, hot, hok, hj, hfr, hkr, hL, _⟩ | ⟨e0, h0, hs⟩
  · rw [h0] at hxmem; cases hxmem
  · obtain ⟨w, hw, hxw⟩ : ∃ w ∈ I.ord m.k, x ∈ apps h w m.k := by
      have := read_writer hI hot hok hj hfr (hL ▸ hxmem); rwa [hkr] at this
    rw [ord_writer_of_wi hwf hp hu hI hwx hw hxw]
    exact ord_com hI hw
  · exfalso
    rw [h0] at hpemem
    rcases prevElem_some hpe with ⟨n, hn, hn1⟩ | ⟨heL, _⟩
    · rw [h0] at hn1; have := (List.getElem?_eq_some_iff.mp hn1).1; simp at this
    · rw [h0] at heL
      obtain ⟨m0, hm0, hv0⟩ := hs
      have hposs : o ∈ possible h.toList := by rw [preprocess_eq hp] at ho; exact ho
      have : m ∈ appendMops (possible h.toList) m.k := mem_appendMops.mpr ⟨⟨o, hposs, hm⟩, hf, rfl⟩
      rw [hm0] at this; simp only [List.mem_singleton] at this; subst this
      rw [hv] at hv0; cases hv0
      exact heL (List.mem_singleton_self _)

/-- Every edge of the analysis leaves a committed transaction. -/
theorem src_com (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false) (hI : I.Clean h)
    {un : List (Nat × Nat × Nat)} (hun : un = [] ∨ un = unreadPairs p) {extra : Extra} (he : ExtraOK extra)
    {x y : Nat} (hxy : (combine ([graph p un] ++ extraAnalysesOf extra h)).graph.HasPair x y) : I.com x := by
  obtain ⟨an, han, hpair⟩ := combine_pair hxy
  rcases List.mem_append.mp han with han | han
  · simp only [List.mem_singleton] at han; subst han
    rcases graph_pair hpair with ⟨o, ho, rfl, m, hm, e, hf, hv, hww⟩ | ⟨o, ho, rfl, m, hm, hf, hwr⟩ |
        ⟨o, ho, rfl, m, hm, e, hf, hv, hrw, _⟩ | ⟨k, hk⟩
    · exact ww_src_com hwf hp hu hI ho hm hf hv hww
    · exact (wr_lift hwf hp hu hI (mopsOf_src hwf hp ho hm) hf hwr).1
    · obtain ⟨hra, _⟩ := rwMopDeps_mem hrw
      obtain ⟨oa, _, _, hoa, hoka, _⟩ := reader_read hwf hp hra
      exact hI.okCom x oa hoa hoka
    · rcases hun with rfl | rfl
      · cases hk
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, hrw, _⟩ := unreadPairs_mem hk
        obtain ⟨hra, _⟩ := rwMopDeps_mem hrw
        obtain ⟨oa, _, _, hoa, hoka, _⟩ := reader_read hwf hp hra
        exact hI.okCom x oa hoa hoka
  · have hok : ∃ ox, h[x]? = some ox ∧ ox.type = .ok := by
      rcases he with rfl | rfl | rfl | rfl | rfl <;> simp only [extraAnalysesOf, List.mem_singleton,
        List.not_mem_nil] at han
      · subst han; exact processGraph_src_ok hwf _ hpair
      · subst han; exact processGraph_src_ok hwf _ hpair
      · subst han; exact realtimeGraph_src_ok hwf _ hpair
      · subst han; exact realtimeGraph_src_ok hwf _ hpair
    obtain ⟨ox, hox, hok⟩ := hok
    exact hI.okCom x ox hox hok


theorem processGraph_explain {intoInfo : Bool} {a b : Nat} {s : Step}
    (hs : (processGraph h intoInfo).explain a b = some s) :
    s.type = "process" ∧ ∃ oa ob, h[a]? = some oa ∧ h[b]? = some ob ∧ oa.process = ob.process ∧ oa.index < ob.index := by
  unfold processGraph at hs
  simp only [Id.run, bind, pure] at hs
  split at hs
  · rename_i oa ob hoa hob
    split at hs
    · rename_i hc; cases hs
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact ⟨rfl, oa, ob, hoa, hob, hc.1, hc.2⟩
    · cases hs
  · cases hs

theorem realtimeGraph_explain {noInfo : Bool} {a b : Nat} {s : Step}
    (hs : (realtimeGraph h noInfo).explain a b = some s) :
    s.type = "realtime" ∧ ∃ oa ob ib, h[a]? = some oa ∧ h[b]? = some ob ∧
      invocation h (pairIndex h) ob = some ib ∧ oa.index < ib.index := by
  unfold realtimeGraph at hs
  simp only [Id.run, bind, pure] at hs
  split at hs
  · rename_i oa ob hoa hob
    split at hs
    · rename_i ib hib
      split at hs
      · rename_i hc; cases hs; exact ⟨rfl, oa, ob, ib, hoa, hob, hib, hc⟩
      · cases hs
    · cases hs
  · cases hs

/-- **Each explained step lifts** into every clean interpretation in which its target committed
(as every vertex of a cycle did: `src_com`). -/
theorem step_lift (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false) (hI : I.Clean h)
    {un : List (Nat × Nat × Nat)} (hun : un = [] ∨ un = unreadPairs p) {extra : Extra} (he : ExtraOK extra)
    {a b : Nat} {s : Step} (hab : (combine ([graph p un] ++ extraAnalysesOf extra h)).graph.HasPair a b)
    (hb : I.com b) (hs : (combine ([graph p un] ++ extraAnalysesOf extra h)).explain a b = some s) :
    StepLift (Interp.dsg h I) s a b := by
  rw [combine_explain, List.findSome?_append] at hs
  simp only [List.findSome?_cons, List.findSome?_nil] at hs
  cases hg : (graph p un).explain a b with
  | some s' =>
    rw [hg] at hs; simp only [Option.some_or] at hs; cases hs
    rcases graph_explain_some hg with ⟨ht, _, m, hm, e, hf, hv, hww⟩ | ⟨ht, _, _, m, hm, hf, hwr⟩ |
        ⟨ht, _, hnw, m, hm, e, hf, hv, hrw, _⟩ | ⟨ht, hu', _, k, hk⟩
    · exact Or.inl ⟨ht, Or.inl (ww_lift hwf hp hu hI hb hm hf hv hww).2⟩
    · exact Or.inr (Or.inl ⟨ht, (wr_lift hwf hp hu hI hm hf hwr).2.2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨ht, (rw_lift hwf hp hu hI hb hm hf hv hrw hnw).2⟩))
    · rcases hun with rfl | rfl
      · cases hk
      · rcases (unread_lift hwf hp hu hI hb hk).2 with h1 | h1
        · exact Or.inl ⟨ht, Or.inl h1⟩
        · exact Or.inl ⟨ht, Or.inr ⟨hu', h1⟩⟩
  | none =>
    rw [hg] at hs; simp only [Option.none_or] at hs
    -- the pair is no edge of `graph`, so it is one of the extra graph's
    obtain ⟨an, han, hpair⟩ := combine_pair hab
    have hpx : an ∈ extraAnalysesOf extra h := by
      rcases List.mem_append.mp han with h1 | h1
      · simp only [List.mem_singleton] at h1; subst h1
        exact absurd hg (graph_explain_complete hwf hp hpair)
      · exact h1
    obtain ⟨ob, hob, hobt⟩ := com_op hI hb
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp only [extraAnalysesOf, List.mem_singleton,
        List.not_mem_nil, List.findSome?_cons, List.findSome?_nil] at hpx hs
    all_goals subst hpx
    · obtain ⟨oa, hoa, hok⟩ := processGraph_src_ok hwf _ hpair
      have hs' : (processGraph h).explain a b = some s := by
        cases hx : (processGraph h).explain a b <;> rw [hx] at hs <;> simp_all
      obtain ⟨ht, oa', ob', hoa', hob', hproc, hlt⟩ := processGraph_explain hs'
      rw [hoa] at hoa'; cases hoa'; rw [hob] at hob'; cases hob'
      have hab' : a < b := by rw [op_index hwf hoa, op_index hwf hob] at hlt; exact hlt
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega, ⟨oa, ob, hoa, hok, hob, hproc⟩, hb, ?_⟩)))
      exact lt_invIdx_of_proc hwf hoa hob (by rw [hok]; decide) hobt hproc hab'
    · obtain ⟨oa, hoa, hok⟩ := processGraph_src_ok hwf _ hpair
      have hs' : (processGraph h true).explain a b = some s := by
        cases hx : (processGraph h true).explain a b <;> rw [hx] at hs <;> simp_all
      obtain ⟨ht, oa', ob', hoa', hob', hproc, hlt⟩ := processGraph_explain hs'
      rw [hoa] at hoa'; cases hoa'; rw [hob] at hob'; cases hob'
      have hab' : a < b := by rw [op_index hwf hoa, op_index hwf hob] at hlt; exact hlt
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega, ⟨oa, ob, hoa, hok, hob, hproc⟩, hb, ?_⟩)))
      exact lt_invIdx_of_proc hwf hoa hob (by rw [hok]; decide) hobt hproc hab'
    · obtain ⟨oa, hoa, hok⟩ := realtimeGraph_src_ok hwf _ hpair
      have hs' : (realtimeGraph h).explain a b = some s := by
        cases hx : (realtimeGraph h).explain a b <;> rw [hx] at hs <;> simp_all
      obtain ⟨ht, oa', ob', ib, hoa', hob', hinv, hlt⟩ := realtimeGraph_explain hs'
      rw [hoa] at hoa'; cases hoa'; rw [hob] at hob'; cases hob'
      obtain ⟨hlt', hne⟩ := lt_invIdx_of_realtime hwf hoa hob hobt hinv hlt
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hne, ⟨oa, hoa, hok⟩, hb, hlt'⟩)))
    · obtain ⟨oa, hoa, hok⟩ := realtimeGraph_src_ok hwf _ hpair
      have hs' : (realtimeGraph h true).explain a b = some s := by
        cases hx : (realtimeGraph h true).explain a b <;> rw [hx] at hs <;> simp_all
      obtain ⟨ht, oa', ob', ib, hoa', hob', hinv, hlt⟩ := realtimeGraph_explain hs'
      rw [hoa] at hoa'; cases hoa'; rw [hob] at hob'; cases hob'
      obtain ⟨hlt', hne⟩ := lt_invIdx_of_realtime hwf hoa hob hobt hinv hlt
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hne, ⟨oa, hoa, hok⟩, hb, hlt'⟩)))


theorem mapM_some {α β : Type} {f : α → Option β} {l : List α} {r : List β} (h : l.mapM f = some r) :
    r.length = l.length ∧ ∀ i (hi : i < l.length) (hr : i < r.length), f l[i] = some r[i] := by
  induction l generalizing r with
  | nil => simp at h; subst h; simp
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some y =>
      rw [hx] at h
      simp only at h
      cases hxs : xs.mapM f with
      | none => rw [hxs] at h; cases h
      | some ys =>
        rw [hxs] at h
        simp only [pure, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hall⟩ := ih hxs
        refine ⟨by simp [hlen], fun i hi hr => ?_⟩
        rcases i with _ | i
        · simpa using hx
        · simpa using hall i (by simpa using hi) (by simpa using hr)

/-- What `explain-cycle` gives: one step per consecutive pair. -/
theorem explainCycle_spec {a : Analysis} {ops : List Nat} {steps : List Step}
    (h : explainCycle a ops = some steps) (hne : ops ≠ []) :
    ops.length = steps.length + 1 ∧
      ∀ i (hi : i < steps.length), a.explain (ops.getD i 0) (ops.getD (i + 1) 0) = some steps[i] := by
  unfold explainCycle at h
  obtain ⟨hlen, hall⟩ := mapM_some h
  have hzlen : (ops.zip (ops.drop 1)).length = ops.length - 1 := by
    simp [List.length_zip, List.length_drop]
  have hpos : 0 < ops.length := List.length_pos_iff.mpr hne
  refine ⟨by omega, fun i hi => ?_⟩
  have hiz : i < (ops.zip (ops.drop 1)).length := by omega
  have := hall i hiz hi
  simp only [List.getElem_zip, List.getElem_drop] at this
  have h1 : i < ops.length := by omega
  have h2 : 1 + i < ops.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem (show i + 1 < ops.length by omega), Option.getD_some]
  simpa only [Nat.add_comm 1 i] using this

/-- **Theorem 1 for list-append, clean interpretations, the service as deployed next.** For a
well-formed history, models that prohibit G1a (D5's fix leaves `:info` appends indexed), the main
search's graph or D1's second one (`un` its unread pairs), and the process or real-time graph:
every cycle Elle's search returns (a closed walk of the analysis's edges) and explains shows, in
every clean interpretation, what `classify` names it (`Claim`), or a G-single through one of D1's
unread steps. -/
theorem la_cycle_clean (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false)
    (hI : I.Clean h) {un : List (Nat × Nat × Nat)} (hun : un = [] ∨ un = unreadPairs p)
    {extra : Extra} (he : ExtraOK extra) {ops : List Nat} {steps : List Step}
    (hne : steps ≠ []) (hclosed : ops.head? = ops.getLast?)
    (hpairs : ∀ i, i + 1 < ops.length →
      (combine ([graph p un] ++ extraAnalysesOf extra h)).graph.HasPair (ops.getD i 0) (ops.getD (i + 1) 0))
    (hexp : explainCycle (combine ([graph p un] ++ extraAnalysesOf extra h)) ops = some steps) :
    ((∃ s ∈ steps, s.unread = true) ∧ (Interp.dsg h I).GSingle .none) ∨ Claim (Interp.dsg h I) steps := by
  have hops : ops ≠ [] := by
    intro h0; subst h0; unfold explainCycle at hexp; simp at hexp; exact hne hexp
  obtain ⟨hlen, hstep⟩ := explainCycle_spec hexp hops
  apply lift_cycle (Interp.dsg h I) (Interp.dsg_rw_irrefl I) ops steps hlen hne hclosed
  intro i hi
  have hpair := hpairs i (by omega)
  -- the step's target leaves the next edge (the walk is closed)
  have hb : I.com (ops.getD (i + 1) 0) := by
    by_cases hlast : i + 1 < steps.length
    · exact src_com hwf hp hu hI hun he (hpairs (i + 1) (by omega))
    · have hi1 : i + 1 = steps.length := by omega
      have : ops.getD (i + 1) 0 = ops.getD 0 0 := by
        have h1 : ops.getLast? = ops[i + 1]? := by rw [List.getLast?_eq_getElem?, hlen, hi1]; rfl
        have h2 : ops.head? = ops[0]? := by cases ops <;> rfl
        rw [hclosed, h1] at h2
        simp only [List.getD_eq_getElem?_getD, ← h2]
      rw [this]
      exact src_com hwf hp hu hI hun he (hpairs 0 (by omega))
  exact step_lift hwf hp hu hI hun he hpair hb (hstep i hi)

end Elle.R4.LA

import Elle.R4.LACycle

/-!
# Round 4: every interpretation, dirty ones included (models allowing G1a: D4 with D5)

Read uncommitted and its session and strong variants allow G1a: an interpretation in which an
`:info` (or failed) transaction aborted and its appends were read still counts. Their verdicts
need the dependencies to hold in *every* interpretation (Elle §4: an interpretation chooses which
indeterminate transactions committed; its version order may hold aborted appends, a dirty
update, between committed versions).

`GInterp.Valid` writes Round 1's specification down declaratively: committed transactions, each
key's version order (its committed appenders), and each writer's *base*, what its appends went on
(the version before it, then aborted elements). Versions are chain prefixes (`chain`), a writer's
elements aren't in its own base (`own`), a read holding a writer's `n`-th element holds that
writer's base and its first `n + 1` appends (`pins`: the specification's decomposition of a read
into writer segments), and every element read was appended by someone (`appended`).
-/

namespace Elle.R4.LA

open Elle Elle.R4 Elle.ListAppend

structure GInterp where
  com : Nat → Prop
  ord : Nat → List Nat
  base : Nat → Nat → List Int

structure GInterp.Valid (h : History) (I : GInterp) : Prop where
  okCom : ∀ (i : Nat) (o : Op), h[i]? = some o → o.type = .ok → I.com i
  comPoss : ∀ i, I.com i → ∃ o, h[i]? = some o ∧ (o.type = .ok ∨ o.type = .info)
  ordNodup : ∀ k, (I.ord k).Nodup
  ordMem : ∀ k w, w ∈ I.ord k ↔ I.com w ∧ apps h w k ≠ []
  chain : ∀ (k i j w w' : Nat), i < j → (I.ord k)[i]? = some w → (I.ord k)[j]? = some w' →
    I.base k w ++ apps h w k <+: I.base k w'
  own : ∀ k w, w ∈ I.ord k → ∀ x ∈ apps h w k, x ∉ I.base k w
  pins : ∀ (t : Nat) (o : Op), h[t]? = some o → o.type = .ok → ∀ m ∈ o.value, m.f = .r → ∀ w ∈ I.ord m.k, ∀ (n : Nat) (x : Int),
    (apps h w m.k)[n]? = some x → x ∈ toL m.v → I.base m.k w ++ (apps h w m.k).take (n + 1) <+: toL m.v
  appended : ∀ (t : Nat) (o : Op), h[t]? = some o → o.type = .ok → ∀ m ∈ o.value, m.f = .r → ∀ x ∈ toL m.v,
    ∃ (w : Nat) (o' : Op), h[w]? = some o' ∧ o'.type ≠ .invoke ∧ x ∈ appsOf o' m.k

/-- The write-dependency and order part of an interpretation's DSG (all a G0 needs; read and
anti-dependencies are left out, so a G0 here is one of the specification's DSG). -/
def GInterp.dsg (h : History) (I : GInterp) : DSG where
  ww a b := ∃ k i, (I.ord k)[i]? = some a ∧ (I.ord k)[i + 1]? = some b
  wr _ _ := False
  rw _ _ := False
  so a b := a ≠ b ∧ (∃ oa ob, h[a]? = some oa ∧ oa.type = .ok ∧ h[b]? = some ob ∧ oa.process = ob.process) ∧
    I.com b ∧ a < invIdx h b
  rt a b := a ≠ b ∧ (∃ oa, h[a]? = some oa ∧ oa.type = .ok) ∧ I.com b ∧ a < invIdx h b

variable {h : History} {flip : Bool} {fx : Fx} {p : Pre} {I : GInterp}

theorem g_ww_plus_of_lt {k i j a b : Nat} (ha : (I.ord k)[i]? = some a) (hb : (I.ord k)[j]? = some b) (hij : i < j) :
    Plus (GInterp.dsg h I).ww a b := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
  clear hij
  induction d generalizing b with
  | zero => exact .one ⟨k, i, ha, hb⟩
  | succ d ih =>
    have hlen : i + 1 + d < (I.ord k).length := by
      have := (List.getElem?_eq_some_iff.mp hb).1; omega
    have hc : (I.ord k)[i + 1 + d]? = some (I.ord k)[i + 1 + d] := List.getElem?_eq_getElem hlen
    exact (ih hc).snoc ⟨k, i + 1 + d, hc, by rw [show i + 1 + d + 1 = i + 1 + (d + 1) by omega]; exact hb⟩

/-! ## The indices under D5's fix -/

/-- Under D5's fix, `write-index` holds `:ok` ops only. -/
theorem wi_writer_d5 (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = true)
    {k w : Nat} {x : Int} (hw : wiGet p.wi k x = some w) :
    ∃ o, h[w]? = some o ∧ o.type = .ok ∧ x ∈ appsOf o k := by
  rw [preprocess_eq hp] at hw
  simp only [preOf, hu, ↓reduceIte] at hw
  obtain ⟨o, ho, hidx, _, m, hm, hf, hk, hv⟩ := wiGet_writeIndex hw
  have hmem : o ∈ h.toList := (List.mem_filter.mp ho).1
  have hok : o.type = .ok := by simpa [Op.isOk] using (List.mem_filter.mp ho).2
  refine ⟨o, hidx ▸ op_at hwf hmem, hok, ?_⟩
  unfold appsOf
  exact List.mem_filterMap.mpr ⟨m, hm, by simp [hf, hk, hv]⟩

/-- An `:ok` op's element is no `:info` op's (unique appends). -/
theorem not_infoElem (hwf : WF h) {fx : Fx} {k : Nat} {o : Op} (ho : o ∈ h.toList) (hok : o.type = .ok)
    {e : Int} (he : e ∈ appsOf o k) : (infoElemsOf fx h).contains (k, e) = false := by
  unfold infoElemsOf
  split
  · rfl
  · apply Bool.eq_false_iff.mpr
    intro hc
    simp only [List.contains_iff_mem, List.mem_flatMap, List.mem_filter, List.mem_filterMap] at hc
    obtain ⟨oi, ⟨hoi, hinfo⟩, m, hm, hmx⟩ := hc
    split at hmx
    · rename_i e' hf hv
      simp only [Option.some.injEq, Prod.mk.injEq] at hmx
      obtain ⟨rfl, rfl⟩ := hmx
      have hoi' := (possible_mem hoi).1
      have hei : e' ∈ appsOf oi m.k := by unfold appsOf; exact List.mem_filterMap.mpr ⟨m, hm, by simp [hf, hv]⟩
      have hinfo' : oi.type = .info := by simpa [Op.isInfo] using hinfo
      have := hwf.uniq o ho oi hoi' (by rw [hok]; decide) (by rw [hinfo']; decide) m.k e' he hei
      have e1 := op_at hwf ho
      have e2 := op_at hwf hoi'
      rw [this] at e1; rw [e1] at e2; cases e2
      rw [hok] at hinfo'; cases hinfo'
    · cases hmx

/-- What the append index holds under D5's fix: nothing, an `:ok` read without `:info` elements,
or the one append on the key. -/
theorem ai_cases_d5 (hwf : WF h) (hp : preprocess h flip fx = .ok p) (k : Nat) :
    aiOf p k = [] ∨
    (∃ (t : Nat) (o : Op) (m : Mop), h[t]? = some o ∧ o.type = .ok ∧ m ∈ o.value ∧ m.f = .r ∧ m.k = k ∧
       (toL m.v).Nodup ∧ aiOf p k = (if unInfoOf fx then filtRead fx h k (toL m.v) else toL m.v)) ∨
    (∃ e0, aiOf p k = [e0] ∧ SingleAppend (possible h.toList) k e0) := by
  unfold aiOf
  cases hl : p.ai.lookup k with
  | none => exact Or.inl rfl
  | some l =>
    simp only [Option.getD_some]
    have hl' := hl
    rw [preprocess_eq hp] at hl'
    simp only [preOf] at hl'
    have hsrc : ∃ L, l = dedup L ∧ AISrc (psVOf fx h) k L := by
      split at hl'
      · exact appendIndex_src hl'
      · exact appendIndex_src hl'
    obtain ⟨L, rfl, hsrc⟩ := hsrc
    rcases hsrc with rfl | ⟨_, hr⟩ | ⟨e0, rfl, hs⟩
    · left; rfl
    · right; left
      obtain ⟨o, ho, m, hm, hf, hk, L', hv, hL⟩ := readVal_psV hr
      obtain ⟨hmem, hty⟩ := possible_mem ho
      have hok : o.type = .ok := by
        rcases hty with h1 | h1
        · exact h1
        · have := hwf.nilReads o hmem (by rw [h1]; decide) m hm hf; rw [hv] at this; cases this
      have hnd : L'.Nodup := by
        rcases hwf.okReads o hmem hok m hm hf with h1 | ⟨l', h1, h2⟩
        · rw [hv] at h1; cases h1
        · rw [hv] at h1; cases h1; exact h2
      have hLnd : L.Nodup := by
        rw [hL]; split
        · exact hnd.sublist (List.filter_sublist)
        · exact hnd
      refine ⟨o.index, o, m, op_at hwf hmem, hok, hm, hf, hk, by rw [hv]; exact hnd, ?_⟩
      rw [dedup_of_nodup _ hLnd, hL, hv]; rfl
    · right; right
      refine ⟨e0, by simp [dedup], ?_⟩
      obtain ⟨m0, hm0, hv0⟩ := hs
      exact ⟨m0, by rw [← appendMops_psV]; exact hm0, hv0⟩


/-! ## ww under D5's fix -/

theorem idx_in_left {A B : List Int} (hnd : (A ++ B).Nodup) {i : Nat} {y : Int} (hi : (A ++ B)[i]? = some y)
    (hy : y ∈ A) : i < A.length := by
  rcases Nat.lt_or_ge i A.length with hlt | hge
  · exact hlt
  · exfalso
    rw [List.getElem?_append_right hge] at hi
    exact (List.nodup_append.mp hnd).2.2 y hy y (List.mem_of_getElem? hi) rfl

theorem idx_in_right {A B : List Int} (hnd : (A ++ B).Nodup) {i : Nat} {z : Int} (hi : (A ++ B)[i]? = some z)
    (hz : z ∈ B) : A.length ≤ i := by
  rcases Nat.lt_or_ge i A.length with hlt | hge
  · exfalso
    rw [List.getElem?_append_left hlt] at hi
    exact (List.nodup_append.mp hnd).2.2 z (List.mem_of_getElem? hi) z hz rfl
  · exact hge

theorem filtRead_mem {fx : Fx} {k : Nat} {l : List Int} {x : Int} (hx : x ∈ l)
    (hn : (infoElemsOf fx h).contains (k, x) = false) : x ∈ filtRead fx h k l := by
  unfold filtRead; exact List.mem_filter.mpr ⟨hx, by rw [hn]; rfl⟩

/-- **D4 with D5: a `ww` explanation into an `:ok` op holds in every interpretation**, dirty ones
included: for models allowing G1a only `:ok` appends are indexed, the version order comes from a
read without `:info` elements, and failed elements are stepped over; the writer it names precedes
`b` in the version order of every interpretation. -/
theorem ww_lift_d5 (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = true) (hI : I.Valid h)
    {a b : Nat} {e : Int} {m : Mop} {ob : Op} (hob : h[b]? = some ob) (hokb : ob.type = .ok)
    (hm : m ∈ mopsOf p b) (hf : m.f = .append) (hv : m.v = .int e) (hww : wwMopDep p b m.k e = some a) :
    I.com a ∧ Plus (GInterp.dsg h I).ww a b := by
  obtain ⟨ob', hob', hmb⟩ := mopsOf_mem hp hm
  rw [hob] at hob'; cases hob'
  have heb' : e ∈ appsOf ob m.k := append_apps hmb hf hv
  have heb : e ∈ apps h b m.k := by rw [apps_of_op hob]; exact heb'
  have hbc := hI.okCom b ob hob hokb
  have hbord : b ∈ I.ord m.k := (hI.ordMem _ _).mpr ⟨hbc, List.ne_nil_of_mem heb⟩
  obtain ⟨pe, x, hpe, hwx, hab, hob4, _⟩ := wwMopDep_some hww
  obtain ⟨oa, hoa, hoka, hxa'⟩ := wi_writer_d5 hwf hp hu hwx
  have hxa : x ∈ apps h a m.k := by rw [apps_of_op hoa]; exact hxa'
  have hac := hI.okCom a oa hoa hoka
  have haord : a ∈ I.ord m.k := (hI.ordMem _ _).mpr ⟨hac, List.ne_nil_of_mem hxa⟩
  refine ⟨hac, ?_⟩
  obtain ⟨ia, hia⟩ := idx_of_mem haord
  obtain ⟨ib, hib⟩ := idx_of_mem hbord
  rcases Nat.lt_or_ge ia ib with hlt | hge
  · exact g_ww_plus_of_lt hia hib hlt
  exfalso
  have hlt : ib < ia := by
    rcases Nat.eq_or_lt_of_le hge with he | he
    · subst he; rw [hia] at hib; cases hib; exact absurd rfl hab
    · exact he
  have hpemem : pe ∈ aiOf p m.k := by
    rcases prevElem_some hpe with ⟨i, hi, _⟩ | ⟨_, hl⟩
    · exact List.mem_of_getElem? hi
    · exact List.mem_of_getLast? hl
  have hxmem : x ∈ aiOf p m.k := by
    rcases hob4 with rfl | ⟨_, j, _, _, hj⟩
    · exact hpemem
    · exact List.mem_of_getElem? hj
  rcases ai_cases_d5 hwf hp m.k with h0 | ⟨t, o, mr, hot, hok, hmr, hfr, hkr, hnd', hai⟩ | ⟨e0, h0, hs⟩
  · rw [h0] at hxmem; cases hxmem
  · simp only [hu, ↓reduceIte] at hai
    have hbposs : ob ∈ h.toList := op_mem h hob
    have hxL : x ∈ toL mr.v := by rw [hai] at hxmem; exact (List.mem_filter.mp hxmem).1
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hxa
    have hpin := hI.pins t o hot hok mr hmr hfr a (hkr ▸ haord) n x (hkr ▸ hn) hxL
    rw [hkr] at hpin
    have hch := hI.chain m.k ib ia b a hlt hib hia
    obtain ⟨R, hR⟩ := (List.prefix_append _ _).trans hpin
    have heB : e ∈ I.base m.k a := hch.mem (List.mem_append_right _ heb)
    have hxR : x ∈ R := by
      have : x ∈ I.base m.k a ++ R := by rw [hR]; exact hxL
      rcases List.mem_append.mp this with h1 | h1
      · exact absurd h1 (hI.own m.k a haord x hxa)
      · exact h1
    have hsplit : aiOf p m.k = filtRead fx h m.k (I.base m.k a) ++ filtRead fx h m.k R := by
      rw [hai, ← hR]; unfold filtRead; rw [List.filter_append]
    have hndai : (aiOf p m.k).Nodup := by rw [hai]; exact hnd'.sublist List.filter_sublist
    have heF : e ∈ filtRead fx h m.k (I.base m.k a) := filtRead_mem heB (not_infoElem hwf hbposs hokb heb')
    have hxF : x ∈ filtRead fx h m.k R := filtRead_mem hxR (not_infoElem hwf (op_mem h hoa) hoka hxa')
    rcases prevElem_some hpe with ⟨n0, hn0, hn1⟩ | ⟨heL, _⟩
    · obtain ⟨n2, hn2, hxn2⟩ := atOrBefore_idx hndai hn0 hob4
      rw [hsplit] at hn1 hxn2 hndai
      have h1 := idx_in_left hndai hn1 heF
      have h2 := idx_in_right hndai hxn2 hxF
      omega
    · exact heL (by rw [hsplit]; exact List.mem_append_left _ heF)
  · rw [h0] at hpemem
    rcases prevElem_some hpe with ⟨n, hn, hn1⟩ | ⟨heL, _⟩
    · rw [h0] at hn1; have := (List.getElem?_eq_some_iff.mp hn1).1; simp at this
    · rw [h0] at heL
      obtain ⟨m0, hm0, hv0⟩ := hs
      have hbposs : ob ∈ possible h.toList := possible_of (op_mem h hob) (Or.inl hokb)
      have : m ∈ appendMops (possible h.toList) m.k := mem_appendMops.mpr ⟨⟨ob, hbposs, hmb⟩, hf, rfl⟩
      rw [hm0] at this; simp only [List.mem_singleton] at this; subst this
      rw [hv] at hv0; cases hv0
      exact heL (List.mem_singleton_self _)


/-! ## G0 cycles under D5's fix, in every interpretation -/

/-- Under D5's fix every edge of the analysis leaves an `:ok` op. -/
theorem src_ok_d5 (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = true)
    {un : List (Nat × Nat × Nat)} (hun : un = [] ∨ un = unreadPairs p) {extra : Extra} (he : ExtraOK extra)
    {x y : Nat} (hxy : (combine ([graph p un] ++ extraAnalysesOf extra h)).graph.HasPair x y) :
    ∃ ox, h[x]? = some ox ∧ ox.type = .ok := by
  obtain ⟨an, han, hpair⟩ := combine_pair hxy
  rcases List.mem_append.mp han with han | han
  · simp only [List.mem_singleton] at han; subst han
    rcases graph_pair hpair with ⟨o, ho, rfl, m, hm, e, hf, hv, hww⟩ | ⟨o, ho, rfl, m, hm, hf, hwr⟩ |
        ⟨o, ho, rfl, m, hm, e, hf, hv, hrw, _⟩ | ⟨k, hk⟩
    · obtain ⟨_, x', _, hwx, _⟩ := wwMopDep_some hww
      obtain ⟨oa, hoa, hok, _⟩ := wi_writer_d5 hwf hp hu hwx
      exact ⟨oa, hoa, hok⟩
    · obtain ⟨_, _, hwe, _⟩ := wrMopDep_some hwr
      obtain ⟨oa, hoa, hok, _⟩ := wi_writer_d5 hwf hp hu hwe
      exact ⟨oa, hoa, hok⟩
    · obtain ⟨hra, _⟩ := rwMopDeps_mem hrw
      obtain ⟨oa, _, _, hoa, hoka, _⟩ := reader_read hwf hp hra
      exact ⟨oa, hoa, hoka⟩
    · rcases hun with rfl | rfl
      · cases hk
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, hrw, _⟩ := unreadPairs_mem hk
        obtain ⟨hra, _⟩ := rwMopDeps_mem hrw
        obtain ⟨oa, _, _, hoa, hoka, _⟩ := reader_read hwf hp hra
        exact ⟨oa, hoa, hoka⟩
  · rcases he with rfl | rfl | rfl | rfl | rfl <;> simp only [extraAnalysesOf, List.mem_singleton,
      List.not_mem_nil] at han
    · subst han; exact processGraph_src_ok hwf _ hpair
    · subst han; exact processGraph_src_ok hwf _ hpair
    · subst han; exact realtimeGraph_src_ok hwf _ hpair
    · subst han; exact realtimeGraph_src_ok hwf _ hpair

/-- A write-dependency or order step of the analysis lifts into every interpretation, under D5's
fix, when its target is an `:ok` op (as every vertex of a cycle is). -/
theorem step_lift_d5 (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = true) (hI : I.Valid h)
    {un : List (Nat × Nat × Nat)} (hun : un = [] ∨ un = unreadPairs p) {extra : Extra} (he : ExtraOK extra)
    {a b : Nat} {s : Step} (hab : (combine ([graph p un] ++ extraAnalysesOf extra h)).graph.HasPair a b)
    {ob : Op} (hob : h[b]? = some ob) (hokb : ob.type = .ok)
    (hs : (combine ([graph p un] ++ extraAnalysesOf extra h)).explain a b = some s)
    (hkind : (s.type = "ww" ∧ s.unread = false) ∨ s.type = "process" ∨ s.type = "realtime") :
    StepLift (GInterp.dsg h I) s a b := by
  have hbc := hI.okCom b ob hob hokb
  have hobt : ob.type ≠ .invoke := by rw [hokb]; decide
  rw [combine_explain, List.findSome?_append] at hs
  simp only [List.findSome?_cons, List.findSome?_nil] at hs
  cases hg : (graph p un).explain a b with
  | some s' =>
    rw [hg] at hs; simp only [Option.some_or] at hs; cases hs
    rcases graph_explain_some hg with ⟨ht, _, m, hm, e, hf, hv, hww⟩ | ⟨ht, _, _⟩ | ⟨ht, _, _⟩ | ⟨ht, hu', _⟩
    · exact Or.inl ⟨ht, Or.inl (ww_lift_d5 hwf hp hu hI hob hokb hm hf hv hww).2⟩
    · rcases hkind with ⟨h1, _⟩ | h1 | h1 <;> rw [ht] at h1 <;> exact absurd h1 (by decide)
    · rcases hkind with ⟨h1, _⟩ | h1 | h1 <;> rw [ht] at h1 <;> exact absurd h1 (by decide)
    · rcases hkind with ⟨_, h1⟩ | h1 | h1
      · rw [hu'] at h1; cases h1
      · rw [ht] at h1; exact absurd h1 (by decide)
      · rw [ht] at h1; exact absurd h1 (by decide)
  | none =>
    rw [hg] at hs; simp only [Option.none_or] at hs
    obtain ⟨an, han, hpair⟩ := combine_pair hab
    have hpx : an ∈ extraAnalysesOf extra h := by
      rcases List.mem_append.mp han with h1 | h1
      · simp only [List.mem_singleton] at h1; subst h1
        exact absurd hg (graph_explain_complete hwf hp hpair)
      · exact h1
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp only [extraAnalysesOf, List.mem_singleton,
        List.not_mem_nil, List.findSome?_cons, List.findSome?_nil] at hpx hs
    all_goals subst hpx
    · obtain ⟨oa, hoa, hok⟩ := processGraph_src_ok hwf _ hpair
      have hs' : (processGraph h).explain a b = some s := by
        cases hx : (processGraph h).explain a b <;> rw [hx] at hs <;> simp_all
      obtain ⟨ht, oa', ob', hoa', hob', hproc, hlt⟩ := processGraph_explain hs'
      rw [hoa] at hoa'; cases hoa'; rw [hob] at hob'; cases hob'
      have hab' : a < b := by rw [op_index hwf hoa, op_index hwf hob] at hlt; exact hlt
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega, ⟨oa, ob, hoa, hok, hob, hproc⟩, hbc, ?_⟩)))
      exact lt_invIdx_of_proc hwf hoa hob (by rw [hok]; decide) hobt hproc hab'
    · obtain ⟨oa, hoa, hok⟩ := processGraph_src_ok hwf _ hpair
      have hs' : (processGraph h true).explain a b = some s := by
        cases hx : (processGraph h true).explain a b <;> rw [hx] at hs <;> simp_all
      obtain ⟨ht, oa', ob', hoa', hob', hproc, hlt⟩ := processGraph_explain hs'
      rw [hoa] at hoa'; cases hoa'; rw [hob] at hob'; cases hob'
      have hab' : a < b := by rw [op_index hwf hoa, op_index hwf hob] at hlt; exact hlt
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega, ⟨oa, ob, hoa, hok, hob, hproc⟩, hbc, ?_⟩)))
      exact lt_invIdx_of_proc hwf hoa hob (by rw [hok]; decide) hobt hproc hab'
    · obtain ⟨oa, hoa, hok⟩ := realtimeGraph_src_ok hwf _ hpair
      have hs' : (realtimeGraph h).explain a b = some s := by
        cases hx : (realtimeGraph h).explain a b <;> rw [hx] at hs <;> simp_all
      obtain ⟨ht, oa', ob', ib, hoa', hob', hinv, hlt⟩ := realtimeGraph_explain hs'
      rw [hoa] at hoa'; cases hoa'; rw [hob] at hob'; cases hob'
      obtain ⟨hlt', hne⟩ := lt_invIdx_of_realtime hwf hoa hob hobt hinv hlt
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hne, ⟨oa, hoa, hok⟩, hbc, hlt'⟩)))
    · obtain ⟨oa, hoa, hok⟩ := realtimeGraph_src_ok hwf _ hpair
      have hs' : (realtimeGraph h true).explain a b = some s := by
        cases hx : (realtimeGraph h true).explain a b <;> rw [hx] at hs <;> simp_all
      obtain ⟨ht, oa', ob', ib, hoa', hob', hinv, hlt⟩ := realtimeGraph_explain hs'
      rw [hoa] at hoa'; cases hoa'; rw [hob] at hob'; cases hob'
      obtain ⟨hlt', hne⟩ := lt_invIdx_of_realtime hwf hoa hob hobt hinv hlt
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hne, ⟨oa, hoa, hok⟩, hbc, hlt'⟩)))

/-- **D4 with D5, no false positive for read uncommitted and its variants.** Under D5's fix (the
models allow G1a), every G0 cycle Elle's search returns and explains (its steps `ww`, `process`
or `realtime`, as `classify` names a G0, G0-process or G0-realtime), holds as a G0 of the same
variant in every interpretation, dirty ones included. -/
theorem la_g0_cycle_d5 (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = true) (hI : I.Valid h)
    {un : List (Nat × Nat × Nat)} (hun : un = [] ∨ un = unreadPairs p) {extra : Extra} (he : ExtraOK extra)
    {ops : List Nat} {steps : List Step} (hne : steps ≠ []) (hclosed : ops.head? = ops.getLast?)
    (hpairs : ∀ i, i + 1 < ops.length →
      (combine ([graph p un] ++ extraAnalysesOf extra h)).graph.HasPair (ops.getD i 0) (ops.getD (i + 1) 0))
    (hexp : explainCycle (combine ([graph p un] ++ extraAnalysesOf extra h)) ops = some steps)
    (hkinds : ∀ s ∈ steps, (s.type = "ww" ∧ s.unread = false) ∨ s.type = "process" ∨ s.type = "realtime") :
    (GInterp.dsg h I).G0 (stepsVar steps) := by
  have hops : ops ≠ [] := by
    intro h0; subst h0; unfold explainCycle at hexp; simp at hexp; exact hne hexp
  obtain ⟨hlen, hstep⟩ := explainCycle_spec hexp hops
  have hirr : ∀ a, ¬ (GInterp.dsg h I).rw a a := fun _ h => h
  have hl := lift_cycle (GInterp.dsg h I) hirr ops steps hlen hne hclosed (by
    intro i hi
    have hpair := hpairs i (by omega)
    have hokb : ∃ ob, h[ops.getD (i + 1) 0]? = some ob ∧ ob.type = .ok := by
      by_cases hlast : i + 1 < steps.length
      · exact src_ok_d5 hwf hp hu hun he (hpairs (i + 1) (by omega))
      · have hi1 : i + 1 = steps.length := by omega
        have : ops.getD (i + 1) 0 = ops.getD 0 0 := by
          have h1 : ops.getLast? = ops[i + 1]? := by rw [List.getLast?_eq_getElem?, hlen, hi1]; rfl
          have h2 : ops.head? = ops[0]? := by cases ops <;> rfl
          rw [hclosed, h1] at h2
          simp only [List.getD_eq_getElem?_getD, ← h2]
        rw [this]
        exact src_ok_d5 hwf hp hu hun he (hpairs 0 (by omega))
    obtain ⟨ob, hob, hokb⟩ := hokb
    exact step_lift_d5 hwf hp hu hI hun he hpair hob hokb (hstep i hi) (hkinds _ (List.getElem_mem hi)))
  rcases hl with ⟨_, a, b, hrw, _⟩ | hc
  · exact hrw.elim
  · have h0 : rwCount steps = 0 := by
      rw [rwCount_eq]
      apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro s hs
      rcases hkinds s hs with ⟨h1, _⟩ | h1 | h1 <;> simp [isRW, h1]
    have hwr : (steps.any (·.type == "wr")) = false := by
      apply Bool.eq_false_iff.mpr
      intro ha
      obtain ⟨s, hs, hw⟩ := List.any_eq_true.mp ha
      simp only [beq_iff_eq] at hw
      rcases hkinds s hs with ⟨h1, _⟩ | h1 | h1 <;> rw [hw] at h1 <;> exact absurd h1 (by decide)
    unfold Claim at hc
    simpa [h0, hwr] using hc


/-! ## D23: the edge D5 restores -/

/-- Under D5's fix an `:ok` op's appends are indexed, under its own index. -/
theorem wi_of_d5 (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = true)
    {k w : Nat} {o : Op} {x : Int} (ho : h[w]? = some o) (hok : o.type = .ok) (hx : x ∈ appsOf o k) :
    wiGet p.wi k x = some w := by
  have hmem := op_mem h ho
  obtain ⟨m, hm, hmx⟩ := List.mem_filterMap.mp hx
  have hf : m.f = .append ∧ m.k = k := by
    split at hmx
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc
    · cases hmx
  have hv : m.v = .int x := by
    split at hmx
    · split at hmx
      · rename_i e he; cases hmx; exact he
      · cases hmx
    · cases hmx
  have hsome : (wiGet p.wi k x).isSome := by
    rw [preprocess_eq hp]
    simp only [preOf, hu, ↓reduceIte]
    have := wiGet_writeIndex_isSome (hs := oks h.toList) (List.mem_filter.mpr ⟨hmem, by simp [Op.isOk, hok]⟩)
      (by rw [hok]; decide) hm hf.1 hv
    rwa [hf.2] at this
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨o', ho', hok', hx'⟩ := wi_writer_d5 hwf hp hu hw'
  have : w' = w := writer_unique hwf ho' ho (by rw [hok']; decide) (by rw [hok]; decide) hx' hx
  rw [hw', this]

/-- **D23's class: D5 restores the write dependency the D3 fix lost.** Under D5's fix (models
allowing G1a), if the element before an append `e` of op `t0` in the version order (the
`:info`-free order: the last observed element when `e` is unread) is an element `b` of another
`:ok` op `t1`, then `ww-mop-dep` names `t1`: the step `t1 -ww-> t0` is explained. With `t0`
before `t1` in real time (or the process order) that is a G0-realtime (G0-process) cycle of `:ok`
operations, which `la_g0_cycle_d5` shows holds in every interpretation. D23 is the instance where
`t0` reads `[b]`, `t1` reads an `:info` transaction's elements, and `e` is unread: with the D3 fix
alone the version order was that `:info` read, `t0`'s predecessor was the `:info` transaction, and
the cycle needed the real-time edge into it that the fix removed. -/
theorem d23_ww (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = true)
    {t0 t1 k : Nat} {e b : Int} (hpe : prevElem p k e = some b) {o1 : Op} (h1 : h[t1]? = some o1)
    (hok1 : o1.type = .ok) (hb : b ∈ appsOf o1 k) (hne : t1 ≠ t0) : wwMopDep p t0 k e = some t1 :=
  wwMopDep_of_indexed hpe (wi_of_d5 hwf hp hu h1 hok1 hb) hne

/-- Under D5's fix the version order read from an `:ok` read holds no `:info` op's element. -/
theorem ai_no_info (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = true) {k : Nat}
    (hread : ∃ (t : Nat) (o : Op) (m : Mop), h[t]? = some o ∧ o.type = .ok ∧ m ∈ o.value ∧ m.f = .r ∧ m.k = k ∧
      (toL m.v).Nodup ∧ aiOf p k = filtRead fx h k (toL m.v)) {x : Int} (hx : x ∈ aiOf p k) :
    (infoElemsOf fx h).contains (k, x) = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hai⟩ := hread
  rw [hai] at hx
  have := (List.mem_filter.mp hx).2
  simpa using this

end Elle.R4.LA

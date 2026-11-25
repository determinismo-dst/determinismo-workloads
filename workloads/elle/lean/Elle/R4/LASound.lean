import Elle.R4.LAChain
import Elle.R4.LAGraph

/-!
# Round 4: list-append's inferred dependencies hold in every clean interpretation

For a well-formed history, `preprocess`'s indices (for models that prohibit G1a: every `:ok` and
`:info` append indexed) and every clean interpretation `I`:

- a `ww` explanation `a -> b` (`ww-mop-dep`, with D4's step-over): `a` precedes `b` in the key's
  version order (a path of write dependencies);
- a `wr` explanation: a read dependency;
- an `rw` explanation that the `ww` explainer didn't take: an anti-dependency from `a` to the next
  writer, which precedes or is `b`; or, only where `a`'s own unread append came next, `a` precedes
  `b`;
- D1's unread step: `a` precedes `b`, or the interpretation has a G-single through `a`.

These are the paper's recoverability (unique appends name each element's writer) and
traceability (each read is a prefix of one chain) arguments.
-/

namespace Elle.R4.LA

open Elle Elle.R4 Elle.ListAppend

variable {h : History} {flip : Bool} {fx : Fx} {p : Pre} {I : Interp}

/-! ## What `preprocess` holds, for models prohibiting G1a -/

theorem psV_eq (hu : unInfoOf fx = false) : psVOf fx h = possible h.toList := by
  rw [psVOf_eq]; simp [hu]

theorem possible_mem {o : Op} (ho : o ∈ possible h.toList) : o ∈ h.toList ∧ (o.type = .ok ∨ o.type = .info) := by
  unfold possible at ho
  obtain ⟨hm, hp⟩ := List.mem_filter.mp ho
  refine ⟨hm, ?_⟩
  simp only [Op.isOk, Op.isInfo, Bool.or_eq_true, beq_iff_eq] at hp
  exact hp

theorem possible_of {o : Op} (hm : o ∈ h.toList) (hp : o.type = .ok ∨ o.type = .info) : o ∈ possible h.toList := by
  unfold possible
  exact List.mem_filter.mpr ⟨hm, by simp [Op.isOk, Op.isInfo]; exact hp⟩

theorem op_at (hwf : WF h) {o : Op} (hm : o ∈ h.toList) : h[o.index]? = some o := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
  simp only [Array.length_toList] at hi
  have : h.toList[i] = h[i] := by simp
  rw [this, hwf.index i hi]
  simp [hi]

/-- `write-index` names an element's writer. -/
theorem wi_writer (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false)
    {k w : Nat} {x : Int} (hw : wiGet p.wi k x = some w) :
    ∃ o, h[w]? = some o ∧ (o.type = .ok ∨ o.type = .info) ∧ x ∈ appsOf o k := by
  rw [preprocess_eq hp] at hw
  simp only [preOf, hu, Bool.false_eq_true, ↓reduceIte] at hw
  obtain ⟨o, ho, hidx, _, m, hm, hf, hk, hv⟩ := wiGet_writeIndex hw
  obtain ⟨hmem, hty⟩ := possible_mem ho
  refine ⟨o, hidx ▸ op_at hwf hmem, hty, ?_⟩
  unfold appsOf
  exact List.mem_filterMap.mpr ⟨m, hm, by simp [hf, hk, hv]⟩

/-- An `:ok` or `:info` op's appends are indexed, under its own index. -/
theorem wi_of (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false)
    {k w : Nat} {o : Op} {x : Int} (ho : h[w]? = some o) (hty : o.type = .ok ∨ o.type = .info)
    (hx : x ∈ appsOf o k) : wiGet p.wi k x = some w := by
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
    simp only [preOf, hu, Bool.false_eq_true, ↓reduceIte]
    have := wiGet_writeIndex_isSome (possible_of hmem hty) (by rcases hty with h | h <;> rw [h] <;> decide) hm hf.1 hv
    rwa [hf.2] at this
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨o', ho', hty', hx'⟩ := wi_writer hwf hp hu hw'
  have : w' = w := writer_unique hwf ho' ho
    (by rcases hty' with h | h <;> rw [h] <;> decide) (by rcases hty with h | h <;> rw [h] <;> decide) hx' hx
  rw [hw', this]

/-- An op's `:ok` read: it ended `:ok` (other ops read `nil`). -/
theorem read_ok (hwf : WF h) {t : Nat} {o : Op} {m : Mop} (ho : h[t]? = some o) (hm : m ∈ o.value)
    (hr : m.f = .r) (hv : m.v ≠ .nil) : o.type = .ok := by
  by_cases hne : o.type = .ok
  · exact hne
  · exact absurd (hwf.nilReads o (op_mem h ho) hne m hm hr) hv

/-- What the append index holds for `k`: nothing, an `:ok` read, or the one append on `k`. -/
theorem ai_cases (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false) (k : Nat) :
    aiOf p k = [] ∨
    (∃ (t : Nat) (o : Op) (j : Nat) (m : Mop), h[t]? = some o ∧ o.type = .ok ∧ o.value[j]? = some m ∧ m.f = .r ∧ m.k = k ∧
       toL m.v = aiOf p k ∧ (aiOf p k).Nodup) ∨
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
    rw [psV_eq hu] at hsrc
    rcases hsrc with rfl | ⟨hne, o, ho, m, hm, hf, hk, hv⟩ | ⟨e0, rfl, hs⟩
    · left; rfl
    · right; left
      obtain ⟨hmem, hty⟩ := possible_mem ho
      have hok : o.type = .ok := by
        rcases hty with h1 | h1
        · exact h1
        · have := hwf.nilReads o hmem (by rw [h1]; decide) m hm hf; rw [hv] at this; cases this
      have hnd : L.Nodup := by
        rcases hwf.okReads o hmem hok m hm hf with h1 | ⟨l', h1, h2⟩
        · rw [hv] at h1; cases h1
        · rw [hv] at h1; cases h1; exact h2
      obtain ⟨j, hj⟩ := mem_value_idx hm
      refine ⟨o.index, o, j, m, op_at hwf hmem, hok, hj, hf, hk, ?_, ?_⟩
      · rw [dedup_of_nodup _ hnd, hv]; rfl
      · rw [dedup_of_nodup _ hnd]; exact hnd
    · right; right
      exact ⟨e0, by simp [dedup], hs⟩


/-! ## Helpers -/

theorem mopsOf_mem (hp : preprocess h flip fx = .ok p) {b : Nat} {m : Mop} (hm : m ∈ mopsOf p b) :
    ∃ o, h[b]? = some o ∧ m ∈ o.value := by
  unfold mopsOf at hm
  rw [preprocess_eq hp] at hm
  simp only [preOf] at hm
  cases ho : h[b]? with
  | none => simp [ho] at hm
  | some o => simp [ho] at hm; exact ⟨o, rfl, hm⟩

theorem append_apps {o : Op} {m : Mop} {e : Int} (hm : m ∈ o.value) (hf : m.f = .append) (hv : m.v = .int e) :
    e ∈ appsOf o m.k := by
  unfold appsOf
  exact List.mem_filterMap.mpr ⟨m, hm, by simp [hf, hv]⟩

theorem atOrBefore_idx {vs : List Int} (hnd : vs.Nodup) {n : Nat} {pe x : Int} (hpe : vs[n]? = some pe)
    (h : AtOrBefore vs pe x) : ∃ n2 ≤ n, vs[n2]? = some x := by
  rcases h with rfl | ⟨i, j, hji, hi, hj⟩
  · exact ⟨n, Nat.le_refl _, hpe⟩
  · have hn : n < vs.length := (List.getElem?_eq_some_iff.mp hpe).1
    have : n = i := (hnd.getElem?_inj hn).mp (hpe.trans hi.symm)
    exact ⟨j, this ▸ hji, hj⟩

theorem nodup_idx_eq {α : Type} {vs : List α} (hnd : vs.Nodup) {i j : Nat} {x : α} (hi : vs[i]? = some x)
    (hj : vs[j]? = some x) : i = j := by
  have hil : i < vs.length := (List.getElem?_eq_some_iff.mp hi).1
  exact (hnd.getElem?_inj hil).mp (hi.trans hj.symm)

theorem nodup_idx_unique {vs : List Int} (hnd : vs.Nodup) {i j : Nat} {x : Int} (hi : vs[i]? = some x)
    (hj : vs[j]? = some x) : i = j := by
  have hil : i < vs.length := (List.getElem?_eq_some_iff.mp hi).1
  exact (hnd.getElem?_inj hil).mp (hi.trans hj.symm)

theorem com_type (hI : I.Clean h) {w : Nat} {o : Op} (hc : I.com w) (ho : h[w]? = some o) :
    o.type = .ok ∨ o.type = .info := by
  obtain ⟨o', ho', ht⟩ := hI.comPoss w hc
  rw [ho] at ho'; cases ho'; exact ht

theorem noninv {o : Op} (ht : o.type = .ok ∨ o.type = .info) : o.type ≠ .invoke := by
  rcases ht with h | h <;> rw [h] <;> decide

/-- The writer an index names, of an element in the version order, is that element's writer
there. -/
theorem ord_writer_of_wi (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false)
    (hI : I.Clean h) {k a w : Nat} {x : Int} (hwx : wiGet p.wi k x = some a) (hw : w ∈ I.ord k)
    (hxw : x ∈ apps h w k) : a = w := by
  obtain ⟨oa, hoa, htya, hxa⟩ := wi_writer hwf hp hu hwx
  obtain ⟨ow, how, htyw⟩ := com_op hI (ord_com hI hw)
  rw [apps_of_op how] at hxw
  exact writer_unique hwf hoa how (noninv htya) htyw hxa hxw

/-! ## ww -/

/-- **A `ww` explanation holds**: `a` precedes `b` in the version order, in every clean
interpretation where `b` committed (and then `a` did too). -/
theorem ww_lift (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false) (hI : I.Clean h)
    {a b : Nat} {e : Int} {m : Mop} (hb : I.com b) (hm : m ∈ mopsOf p b) (hf : m.f = .append)
    (hv : m.v = .int e) (hww : wwMopDep p b m.k e = some a) :
    I.com a ∧ Plus (Interp.dsg h I).ww a b := by
  obtain ⟨ob, hob, hmb⟩ := mopsOf_mem hp hm
  have heb : e ∈ apps h b m.k := by rw [apps_of_op hob]; exact append_apps hmb hf hv
  have hbord : b ∈ I.ord m.k := (hI.ordMem _ _).mpr ⟨hb, List.ne_nil_of_mem heb⟩
  obtain ⟨pe, x, hpe, hwx, hab, hob4, _⟩ := wwMopDep_some hww
  have hpemem : pe ∈ aiOf p m.k := by
    rcases prevElem_some hpe with ⟨i, hi, _⟩ | ⟨_, hl⟩
    · exact List.mem_of_getElem? hi
    · exact List.mem_of_getLast? hl
  have hxmem : x ∈ aiOf p m.k := by
    rcases hob4 with rfl | ⟨_, j, _, _, hj⟩
    · exact hpemem
    · exact List.mem_of_getElem? hj
  rcases ai_cases hwf hp hu m.k with h0 | ⟨t, o, j, mr, hot, hok, hj, hfr, hkr, hL, hnd⟩ | ⟨e0, h0, hs⟩
  · rw [h0] at hxmem; cases hxmem
  · -- the append index is an :ok read: a prefix of the chain
    have hLp : aiOf p m.k <+: Interp.chainAll h I m.k := by
      rw [← hL, ← hkr]; exact read_prefix hI hot hok hj hfr
    obtain ⟨w, hw, hxw⟩ : ∃ w ∈ I.ord m.k, x ∈ apps h w m.k := by
      have := read_writer hI hot hok hj hfr (hL ▸ hxmem); rwa [hkr] at this
    have haw := ord_writer_of_wi hwf hp hu hI hwx hw hxw
    subst haw
    refine ⟨ord_com hI hw, ?_⟩
    obtain ⟨ia, hia⟩ := idx_of_mem hw
    obtain ⟨ib, hib⟩ := idx_of_mem hbord
    have hne : ia ≠ ib := by
      intro he; subst he; rw [hia] at hib; cases hib; exact hab rfl
    rcases Nat.lt_or_ge ia ib with hlt | hge
    · exact ww_plus_of_lt hia hib hlt
    · exfalso
      have hlt : ib < ia := by omega
      rcases prevElem_some hpe with ⟨n, hn, hn1⟩ | ⟨heL, _⟩
      · obtain ⟨n2, hn2, hxn2⟩ := atOrBefore_idx hnd hn hob4
        have hP : (aiOf p m.k).take (n + 1) <+: Interp.chainAll h I m.k := (List.take_prefix _ _).trans hLp
        have hxP : x ∈ (aiOf p m.k).take (n + 1) :=
          List.mem_iff_getElem?.mpr ⟨n2, by rw [List.getElem?_take_of_lt (by omega)]; exact hxn2⟩
        have heP := prefix_holds_earlier hwf hI hP hia hib hlt hxw hxP heb
        obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp heP
        have hqlt : q < n + 1 := by
          have := (List.getElem?_eq_some_iff.mp hq).1; simp at this; omega
        rw [List.getElem?_take_of_lt hqlt] at hq
        have := nodup_idx_unique hnd hq hn1
        omega
      · exact heL (prefix_holds_earlier hwf hI hLp hia hib hlt hxw hxmem heb)
  · -- a single append on the key: no ww edge comes from it
    exfalso
    rw [h0] at hpemem
    rcases prevElem_some hpe with ⟨n, hn, hn1⟩ | ⟨heL, _⟩
    · rw [h0] at hn1
      have := (List.getElem?_eq_some_iff.mp hn1).1; simp at this
    · rw [h0] at heL
      obtain ⟨m0, hm0, hv0⟩ := hs
      have hbposs : ob ∈ possible h.toList := possible_of (op_mem h hob) (com_type hI hb hob)
      have : m ∈ appendMops (possible h.toList) m.k := mem_appendMops.mpr ⟨⟨ob, hbposs, hmb⟩, hf, rfl⟩
      rw [hm0] at this
      simp only [List.mem_singleton] at this
      subst this
      rw [hv] at hv0; cases hv0
      exact heL (List.mem_singleton_self _)


/-! ## wr -/

theorem peek_ne_nil {v : Val} {e : Int} (h : peekV v = some e) : v ≠ .nil := by
  intro hv; subst hv; simp [peekV, ListAppend.Val.toList] at h

/-- **A `wr` explanation holds**: a read dependency, in every clean interpretation (both ends
committed: the reader is `:ok`, the writer's element was read). -/
theorem wr_lift (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false) (hI : I.Clean h)
    {a b : Nat} {m : Mop} (hm : m ∈ mopsOf p b) (hr : m.f = .r) (hwr : wrMopDep p b m.k m.v = some a) :
    I.com a ∧ I.com b ∧ (Interp.dsg h I).wr a b := by
  obtain ⟨e, hpeek, hwe, hab⟩ := wrMopDep_some hwr
  obtain ⟨ob, hob, hmb⟩ := mopsOf_mem hp hm
  have hok := read_ok hwf hob hmb hr (peek_ne_nil hpeek)
  have hbc := hI.okCom b ob hob hok
  obtain ⟨j, hj⟩ := mem_value_idx hmb
  have hpeek' : (toL m.v).getLast? = some e := hpeek
  by_cases hext : appsBefore ob j m.k = []
  · obtain ⟨i', hi'le, hval, hnot⟩ := hI.extRead b ob hob hok j m hj hr hext
    rw [hval] at hpeek'
    rcases i' with _ | i
    · simp [Interp.chainUpTo] at hpeek'
    · have hilen : i < (I.ord m.k).length := by omega
      obtain ⟨z, hz, hzw⟩ := chainUpTo_last hI hilen
      rw [hz] at hpeek'; cases hpeek'
      have haw := ord_writer_of_wi hwf hp hu hI hwe (List.getElem_mem hilen) hzw
      subst haw
      refine ⟨ord_com hI (List.getElem_mem hilen), hbc, m.k, i, ⟨ob, j, m, hob, hok, hj, hr, rfl, hext, hval⟩,
        List.getElem?_eq_getElem hilen, hab⟩
  · exfalso
    obtain ⟨i, _, hval⟩ := hI.intRead b ob hob hok j m hj hr hext
    rw [hval, List.getLast?_append] at hpeek'
    cases hl : (appsBefore ob j m.k).getLast? with
    | none => exact hext (List.getLast?_eq_none_iff.mp hl)
    | some z =>
      rw [hl] at hpeek'; simp at hpeek'; subst hpeek'
      have hz : z ∈ appsOf ob m.k := (appsBefore_prefix ob j m.k).mem (List.mem_of_getLast? hl)
      have := wi_of hwf hp hu hob (Or.inl hok) hz
      rw [hwe] at this; cases this
      exact hab rfl


/-! ## rw and D1's unread steps -/

/-- A reader `read-index` names read the key, `:ok`. -/
theorem reader_read (hwf : WF h) (hp : preprocess h flip fx = .ok p) {k r : Nat} {pe : Option Int}
    (hr : r ∈ riGet p.ri k pe) :
    ∃ (o : Op) (j : Nat) (m : Mop), h[r]? = some o ∧ o.type = .ok ∧ o.value[j]? = some m ∧ m.f = .r ∧
      m.k = k ∧ peekV m.v = pe := by
  rw [preprocess_eq hp] at hr
  simp only [preOf] at hr
  obtain ⟨o, ho, hidx, m, hm, hf, hk, hpk, hni⟩ := riGet_readIndex hr
  obtain ⟨hmem, hty⟩ := possible_mem ho
  have hok : o.type = .ok := by
    rcases hty with h1 | h1
    · exact h1
    · have hnil := hwf.nilReads o hmem (by rw [h1]; decide) m hm hf
      have hT : (Val.nil == Val.nil) = true := rfl
      simp [Op.isInfo, h1, hnil, hT] at hni
  obtain ⟨j, hj⟩ := mem_value_idx hm
  exact ⟨o, j, m, hidx ▸ op_at hwf hmem, hok, hj, hf, hk, hpk⟩

theorem wwMopDep_of_indexed {b k a : Nat} {e y : Int} (hpe : prevElem p k e = some y)
    (hw : wiGet p.wi k y = some a) (hab : a ≠ b) : wwMopDep p b k e = some a := by
  unfold wwMopDep
  simp only [hpe]
  split
  · rw [committedFrom_self hw]; simp [hab]
  · simp [hw, hab]

theorem ord_idx_ne {k ia ib a b : Nat} (hia : (I.ord k)[ia]? = some a) (hib : (I.ord k)[ib]? = some b)
    (hab : a ≠ b) : ia ≠ ib := by
  intro he; subst he; rw [hia] at hib; cases hib; exact hab rfl

theorem star_ww_of_le {k i j a b : Nat} (ha : (I.ord k)[i]? = some a) (hb : (I.ord k)[j]? = some b) (hij : i ≤ j) :
    Star (Interp.dsg h I).ww a b := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · rw [ha] at hb; cases hb; exact Star.refl _
  · exact Or.inr (ww_plus_of_lt ha hb hlt)

/-- `b`'s element is outside version `i` when `b` comes at or after the `i`-th writer. -/
theorem idx_ge_of_not_mem (hwf : WF h) (hI : I.Clean h) {k i ib b : Nat} {e : Int}
    (hib : (I.ord k)[ib]? = some b) (heb : e ∈ apps h b k) (hnot : e ∉ Interp.chainUpTo h I k i) : i ≤ ib := by
  rcases Nat.lt_or_ge ib i with hlt | hge
  · exfalso; apply hnot
    exact mem_chainUpTo.mpr ⟨b, List.mem_iff_getElem?.mpr ⟨ib, by rw [List.getElem?_take_of_lt hlt]; exact hib⟩, heb⟩
  · exact hge

/-- **An `rw` explanation holds** (one the `ww` explainer didn't take): an anti-dependency from `a`
to the next writer, which precedes or is `b`; or `a`'s own append came next, before `b`. -/
theorem rw_lift (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false) (hI : I.Clean h)
    {a b : Nat} {e : Int} {m : Mop} (hb : I.com b) (hm : m ∈ mopsOf p b) (hf : m.f = .append)
    (hv : m.v = .int e) (hrw : a ∈ rwMopDeps p b m.k e) (hnoww : NoWW p a b) :
    I.com a ∧ ((∃ c, (Interp.dsg h I).rw a c ∧ Star (Interp.dsg h I).ww c b) ∨ Plus (Interp.dsg h I).ww a b) := by
  obtain ⟨hra, hab⟩ := rwMopDeps_mem hrw
  obtain ⟨oa, ja, ma, hoa, hoka, hja, hfa, hka, hpka⟩ := reader_read hwf hp hra
  have hac := hI.okCom a oa hoa hoka
  refine ⟨hac, ?_⟩
  obtain ⟨ob, hob, hmb⟩ := mopsOf_mem hp hm
  have heb : e ∈ apps h b m.k := by rw [apps_of_op hob]; exact append_apps hmb hf hv
  have hbord : b ∈ I.ord m.k := (hI.ordMem _ _).mpr ⟨hb, List.ne_nil_of_mem heb⟩
  obtain ⟨ib, hib⟩ := idx_of_mem hbord
  by_cases hext : appsBefore oa ja ma.k = []
  · obtain ⟨i, hile, hval, hnot⟩ := hI.extRead a oa hoa hoka ja ma hja hfa hext
    rw [hka] at hval hnot hile
    have hER : Interp.ExtRead h I a m.k i := ⟨oa, ja, ma, hoa, hoka, hja, hfa, hka, hka ▸ hext, hval⟩
    -- the version after the one `a` read
    have next : ∀ c, (I.ord m.k)[i]? = some c → i ≤ ib →
        ((∃ c, (Interp.dsg h I).rw a c ∧ Star (Interp.dsg h I).ww c b) ∨ Plus (Interp.dsg h I).ww a b) := by
      intro c hc hle
      by_cases hca : c = a
      · subst hca
        right
        exact ww_plus_of_lt hc hib (by have := ord_idx_ne hc hib hab; omega)
      · left
        exact ⟨c, ⟨m.k, i, hER, hc, Ne.symm hca⟩, star_ww_of_le hc hib hle⟩
    have hiblen : ib < (I.ord m.k).length := (List.getElem?_eq_some_iff.mp hib).1
    cases hpe : prevElem p m.k e with
    | none =>
      rw [hpe] at hpka
      have hV0 : toL ma.v = [] := by
        unfold peekV at hpka; exact List.getLast?_eq_none_iff.mp hpka
      rw [hval] at hV0
      have hi0 := chainUpTo_eq_nil hI hile hV0
      subst hi0
      exact next _ (List.getElem?_eq_getElem (by omega)) (Nat.zero_le _)
    | some pe =>
      rw [hpe] at hpka
      have hVl : (Interp.chainUpTo h I m.k i).getLast? = some pe := by rw [← hval]; exact hpka
      rcases prevElem_some hpe with ⟨n, hn, hn1⟩ | ⟨heL, hlast⟩
      · rcases ai_cases hwf hp hu m.k with h0 | ⟨t, o, j, mr, hot, hok, hj, hfr, hkr, hL, hnd⟩ | ⟨e0, h0, _⟩
        · rw [h0] at hn; simp at hn
        · have hLp : aiOf p m.k <+: Interp.chainAll h I m.k := by
            rw [← hL, ← hkr]; exact read_prefix hI hot hok hj hfr
          -- `a` read a version before the last: the next writer's first element is `e`
          have hilen : i < (I.ord m.k).length := by
            rcases Nat.lt_or_ge i (I.ord m.k).length with hlt | hge
            · exact hlt
            · exfalso
              have hi' : i = (I.ord m.k).length := by omega
              have hVall : Interp.chainUpTo h I m.k i = Interp.chainAll h I m.k := by rw [hi']; rfl
              have hC := chainAll_nodup hwf hI m.k
              have hlenL := hLp.length_le
              have hn1l : n + 1 < (aiOf p m.k).length := (List.getElem?_eq_some_iff.mp hn1).1
              have hpeC : (Interp.chainAll h I m.k)[n]? = some pe := by
                rw [← prefix_getElem? hLp (by omega)]; exact hn
              rw [hVall, List.getLast?_eq_getElem?] at hVl
              have := nodup_idx_unique hC hpeC hVl
              omega
          have hen := next_after_version hwf hI hilen hLp hn hn1 hVl
          have hbi : (I.ord m.k)[i] = b :=
            com_writer_unique hwf hI (ord_com hI (List.getElem_mem hilen)) hb hen heb
          left
          exact ⟨b, ⟨m.k, i, hER, by rw [List.getElem?_eq_getElem hilen, hbi], hab⟩, Star.refl _⟩
        · rw [h0] at hn1; have := (List.getElem?_eq_some_iff.mp hn1).1; simp at this
      · rcases ai_cases hwf hp hu m.k with h0 | ⟨t, o, j, mr, hot, hok, hj, hfr, hkr, hL, hnd⟩ | ⟨e0, h0, hs⟩
        · rw [h0] at hlast; simp at hlast
        · have hLp : aiOf p m.k <+: Interp.chainAll h I m.k := by
            rw [← hL, ← hkr]; exact read_prefix hI hot hok hj hfr
          have hLV : aiOf p m.k = Interp.chainUpTo h I m.k i :=
            prefix_eq_of_last hLp (chainUpTo_prefix_chainAll _ _) (chainAll_nodup hwf hI m.k) hlast hVl
          have hle := idx_ge_of_not_mem hwf hI hib heb (hLV ▸ heL)
          exact next _ (List.getElem?_eq_getElem (by omega)) hle
        · exfalso
          rw [h0] at heL
          obtain ⟨m0, hm0, hv0⟩ := hs
          have hbposs : ob ∈ possible h.toList := possible_of (op_mem h hob) (com_type hI hb hob)
          have : m ∈ appendMops (possible h.toList) m.k := mem_appendMops.mpr ⟨⟨ob, hbposs, hmb⟩, hf, rfl⟩
          rw [hm0] at this; simp only [List.mem_singleton] at this; subst this
          rw [hv] at hv0; cases hv0
          exact heL (List.mem_singleton_self _)
  · -- an internal read ends with `a`'s own element, which the ww explainer takes first
    exfalso
    obtain ⟨i, hi, hval⟩ := hI.intRead a oa hoa hoka ja ma hja hfa hext
    cases hl : (appsBefore oa ja ma.k).getLast? with
    | none => exact hext (List.getLast?_eq_none_iff.mp hl)
    | some y =>
      have hpk : peekV ma.v = some y := by
        show (toL ma.v).getLast? = some y
        rw [hval, List.getLast?_append, hl]; rfl
      rw [hpka] at hpk
      have hy : y ∈ appsOf oa ma.k := (appsBefore_prefix oa ja ma.k).mem (List.mem_of_getLast? hl)
      rw [hka] at hy
      have hwy := wi_of hwf hp hu hoa (Or.inl hoka) hy
      exact hnoww m hm e hf hv (wwMopDep_of_indexed hpk hwy hab)


theorem unreadPairs_mem {a b k : Nat} (hun : (a, b, k) ∈ unreadPairs p) :
    ∃ o ∈ p.possible, o.index = b ∧ ∃ m ∈ o.value, ∃ e, m.f = .append ∧ m.v = .int e ∧ m.k = k ∧
      e ∉ aiOf p k ∧ a ∈ rwMopDeps p b k e ∧
      ∃ oa, p.hist[a]? = some oa ∧ ∃ m' ∈ oa.value, ∃ e', m'.f = .append ∧ m'.k = k ∧ m'.v = .int e' ∧
        e' ∉ aiOf p k := by
  unfold unreadPairs at hun
  rw [mem_dedup] at hun
  obtain ⟨o, ho, hx⟩ := List.mem_flatMap.mp hun
  obtain ⟨m, hm, hx⟩ := List.mem_flatMap.mp hx
  split at hx
  · rename_i e hf hv
    dsimp only at hx
    split at hx
    · simp at hx
    · rename_i hknown
      obtain ⟨r, hr, hx⟩ := List.mem_filterMap.mp hx
      split at hx
      · rename_i hua
        simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        refine ⟨o, ho, rfl, m, hm, e, hf, hv, rfl, by simpa [aiOf] using hknown, hr, ?_⟩
        cases hoa : p.hist[r]? with
        | none => simp [hoa] at hua
        | some oa =>
          simp only [hoa, Option.map_some, Option.getD_some, List.any_eq_true] at hua
          obtain ⟨m', hm', hc⟩ := hua
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨hf', hk'⟩, hv'⟩ := hc
          split at hv'
          · rename_i e' he'
            exact ⟨oa, rfl, m', hm', e', hf', hk', he', by simpa [aiOf] using hv'⟩
          · cases hv'
      · cases hx
  · simp at hx

/-- **D1's unread step holds as its claim says**: `a` precedes `b`, or the interpretation has a
G-single through `a` (the version after the one `a` read came before `a`'s own). -/
theorem unread_lift (hwf : WF h) (hp : preprocess h flip fx = .ok p) (hu : unInfoOf fx = false) (hI : I.Clean h)
    {a b k : Nat} (hb : I.com b) (hun : (a, b, k) ∈ unreadPairs p) :
    I.com a ∧ (Plus (Interp.dsg h I).ww a b ∨ (Interp.dsg h I).GSingle .none) := by
  obtain ⟨o, ho, hob, m, hm, e, hf, hv, hk, heai, hrw, oa', hoa', m', hm', e', hf', hk', hv', he'ai⟩ := unreadPairs_mem hun
  subst hk
  obtain ⟨hra, hab⟩ := rwMopDeps_mem hrw
  obtain ⟨oa, ja, ma, hoa, hoka, hja, hfa, hka, hpka⟩ := reader_read hwf hp hra
  have hac := hI.okCom a oa hoa hoka
  refine ⟨hac, ?_⟩
  rw [preprocess_eq hp] at ho hoa'
  simp only [preOf] at ho hoa'
  rw [hoa] at hoa'
  have e1 : oa = oa' := Option.some.inj hoa'
  subst e1
  have hobh : h[b]? = some o := hob ▸ op_at hwf (possible_mem ho).1
  have heb : e ∈ apps h b m.k := by rw [apps_of_op hobh]; exact append_apps hm hf hv
  have hbord : b ∈ I.ord m.k := (hI.ordMem _ _).mpr ⟨hb, List.ne_nil_of_mem heb⟩
  have he'a : e' ∈ apps h a m.k := by rw [apps_of_op hoa, ← hk']; exact append_apps hm' hf' hv'
  have haord : a ∈ I.ord m.k := (hI.ordMem _ _).mpr ⟨hac, List.ne_nil_of_mem he'a⟩
  obtain ⟨ib, hib⟩ := idx_of_mem hbord
  obtain ⟨ia, hia⟩ := idx_of_mem haord
  rcases Nat.lt_or_ge ia ib with hlt | hge
  · exact Or.inl (ww_plus_of_lt hia hib hlt)
  right
  have hba : ib < ia := by have := ord_idx_ne hia hib hab; omega
  -- the version `a` read: the last observed one
  have hpe : prevElem p m.k e = (aiOf p m.k).getLast? := by
    unfold prevElem
    simp only [show (p.ai.lookup m.k).getD [] = aiOf p m.k from rfl]
    split
    · rename_i i hi; exact absurd (List.mem_of_getElem? (findIdx_beq_some hi).1) heai
    · rfl
  rw [hpe] at hpka
  -- b's element is in no version holding everything up to `a`'s last read, so `a`'s read is
  -- external and before b
  have hsingle : ∀ e0, ¬ SingleAppend (possible h.toList) m.k e0 := by
    rintro e0 ⟨m0, hm0, hv0⟩
    have hbposs : o ∈ possible h.toList := ho
    have h1 : m ∈ appendMops (possible h.toList) m.k := mem_appendMops.mpr ⟨⟨o, hbposs, hm⟩, hf, rfl⟩
    have haposs : oa ∈ possible h.toList := possible_of (op_mem h hoa) (Or.inl hoka)
    have h2 : m' ∈ appendMops (possible h.toList) m.k := mem_appendMops.mpr ⟨⟨oa, haposs, hm'⟩, hf', hk'⟩
    rw [hm0] at h1 h2; simp only [List.mem_singleton] at h1 h2; subst h1; subst h2
    rw [hv] at hv'; cases hv'
    have := com_writer_unique hwf hI hac hb he'a heb
    exact hab this
  have hLeq : ∀ V, V <+: Interp.chainAll h I m.k → V.getLast? = (aiOf p m.k).getLast? → V ≠ [] →
      e ∉ V := by
    intro V hV hlast hne
    rcases ai_cases hwf hp hu m.k with h0 | ⟨t, o2, j, mr, hot, hok, hj, hfr, hkr, hL, hnd⟩ | ⟨e0, _, hs⟩
    · rw [h0] at hlast; simp at hlast; exact absurd hlast hne
    · have hLp : aiOf p m.k <+: Interp.chainAll h I m.k := by
        rw [← hL, ← hkr]; exact read_prefix hI hot hok hj hfr
      obtain ⟨z, hz⟩ : ∃ z, V.getLast? = some z := by
        cases hl : V.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
        | some z => exact ⟨z, rfl⟩
      have := prefix_eq_of_last hV hLp (chainAll_nodup hwf hI m.k) hz (hlast ▸ hz)
      rw [this]; exact heai
    · exact absurd hs (hsingle e0)
  by_cases hext : appsBefore oa ja ma.k = []
  · obtain ⟨i, hile, hval, hnot⟩ := hI.extRead a oa hoa hoka ja ma hja hfa hext
    rw [hka] at hval hnot hile
    have hER : Interp.ExtRead h I a m.k i := ⟨oa, ja, ma, hoa, hoka, hja, hfa, hka, hka ▸ hext, hval⟩
    have hile' : i ≤ ib := by
      by_cases hV : Interp.chainUpTo h I m.k i = []
      · rw [chainUpTo_eq_nil hI hile hV]; exact Nat.zero_le _
      · apply idx_ge_of_not_mem hwf hI hib heb
        apply hLeq _ (chainUpTo_prefix_chainAll _ _) _ hV
        rw [← hval]; exact hpka
    have hilen : i < (I.ord m.k).length := by
      have := (List.getElem?_eq_some_iff.mp hib).1; omega
    have hci := List.getElem?_eq_getElem hilen
    have hca : (I.ord m.k)[i] ≠ a := by
      intro he; rw [he] at hci; have := nodup_idx_eq (hI.ordNodup m.k) hci hia; omega
    refine ⟨a, (I.ord m.k)[i], ⟨m.k, i, hER, hci, Ne.symm hca⟩, ?_⟩
    exact (ww_plus_of_lt hci hia (by omega)).mono fun _ _ h => Or.inl (Or.inl h)
  · exfalso
    obtain ⟨i, hi, hval⟩ := hI.intRead a oa hoa hoka ja ma hja hfa hext
    rw [hka] at hi hval
    -- `a`'s read holds every writer before `a`, `b` among them
    have hRp := read_prefix hI hoa hoka hja hfa
    rw [hka] at hRp
    have hRne : toL ma.v ≠ [] := by rw [hval]; intro h0; exact hext (by rw [hka]; exact (List.append_eq_nil_iff.mp h0).2)
    apply hLeq _ hRp hpka hRne
    rw [hval]
    apply List.mem_append_left
    exact mem_chainUpTo.mpr ⟨b, List.mem_iff_getElem?.mpr ⟨ib, by
      rw [List.getElem?_take_of_lt (by have := nodup_idx_eq (hI.ordNodup m.k) hi hia; omega)]; exact hib⟩, heb⟩

end Elle.R4.LA

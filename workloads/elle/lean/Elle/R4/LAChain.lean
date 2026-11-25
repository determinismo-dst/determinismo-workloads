import Elle.R4.Interp

/-!
# Round 4: the version chain of a clean list-append interpretation

Traceability (Elle §4.1.2): each key's versions are prefixes of one chain, the concatenation of
its writers' appends in version order. With unique appends (recoverability), each element has one
writer, the chain has no element twice, and a prefix of the chain that holds an element of a
writer holds every element of the writers before it.
-/

namespace Elle.R4.LA

open Elle Elle.R4 Elle.ListAppend

variable {h : History} {I : Interp}

theorem op_index (hwf : WF h) {i : Nat} {o : Op} (ho : h[i]? = some o) : o.index = i := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ho
  exact hwf.index i hi

theorem op_mem (h : History) {i : Nat} {o : Op} (ho : h[i]? = some o) : o ∈ h.toList := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ho
  simp

/-- One writer per element (WF's unique appends), among completions. -/
theorem writer_unique (hwf : WF h) {w w' k : Nat} {x : Int} {o o' : Op} (ho : h[w]? = some o) (ho' : h[w']? = some o')
    (hi : o.type ≠ .invoke) (hi' : o'.type ≠ .invoke) (hx : x ∈ appsOf o k) (hx' : x ∈ appsOf o' k) : w = w' := by
  have := hwf.uniq o (op_mem h ho) o' (op_mem h ho') hi hi' k x hx hx'
  rw [op_index hwf ho, op_index hwf ho'] at this
  exact this

theorem com_op (hI : I.Clean h) {w : Nat} (hc : I.com w) : ∃ o, h[w]? = some o ∧ o.type ≠ .invoke := by
  obtain ⟨o, ho, ht⟩ := hI.comPoss w hc
  exact ⟨o, ho, by rcases ht with ht | ht <;> rw [ht] <;> decide⟩

theorem apps_some {w k : Nat} {x : Int} (hx : x ∈ apps h w k) : ∃ o, h[w]? = some o ∧ x ∈ appsOf o k := by
  unfold apps at hx
  cases ho : h[w]? with
  | none => simp [ho] at hx
  | some o => simp [ho] at hx; exact ⟨o, rfl, hx⟩

/-- Two committed writers of one element are one. -/
theorem com_writer_unique (hwf : WF h) (hI : I.Clean h) {w w' k : Nat} {x : Int} (hc : I.com w) (hc' : I.com w')
    (hx : x ∈ apps h w k) (hx' : x ∈ apps h w' k) : w = w' := by
  obtain ⟨o, ho, hi⟩ := com_op hI hc
  obtain ⟨o', ho', hi'⟩ := com_op hI hc'
  obtain ⟨o1, ho1, hx1⟩ := apps_some hx
  obtain ⟨o2, ho2, hx2⟩ := apps_some hx'
  rw [ho] at ho1; cases ho1
  rw [ho'] at ho2; cases ho2
  exact writer_unique hwf ho ho' hi hi' hx1 hx2

theorem ord_com (hI : I.Clean h) {k w : Nat} (hw : w ∈ I.ord k) : I.com w := ((hI.ordMem k w).mp hw).1

theorem mem_chainUpTo {k i : Nat} {x : Int} :
    x ∈ Interp.chainUpTo h I k i ↔ ∃ w ∈ (I.ord k).take i, x ∈ apps h w k := by
  unfold Interp.chainUpTo; simp [List.mem_flatMap]

theorem chainUpTo_prefix_chainAll (k i : Nat) : Interp.chainUpTo h I k i <+: Interp.chainAll h I k := by
  unfold Interp.chainAll Interp.chainUpTo
  rw [List.take_length]
  have : (I.ord k) = (I.ord k).take i ++ (I.ord k).drop i := (List.take_append_drop i _).symm
  conv => rhs; rw [this]
  rw [List.flatMap_append]
  exact List.prefix_append _ _

theorem chainUpTo_succ {k i : Nat} (hi : i < (I.ord k).length) :
    Interp.chainUpTo h I k (i + 1) = Interp.chainUpTo h I k i ++ apps h (I.ord k)[i] k := by
  unfold Interp.chainUpTo
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append]
  simp

/-- The chain has no element twice. -/
theorem chainAll_nodup (hwf : WF h) (hI : I.Clean h) (k : Nat) : (Interp.chainAll h I k).Nodup := by
  unfold Interp.chainAll Interp.chainUpTo
  rw [List.take_length]
  have hsub : ∀ w ∈ I.ord k, I.com w := fun w hw => ord_com hI hw
  have hnd := hI.ordNodup k
  clear hsub
  have key : ∀ (l : List Nat), l.Nodup → (∀ w ∈ l, I.com w) → (l.flatMap fun w => apps h w k).Nodup := by
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons w ws ih =>
      intro hn hc
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨?_, ih (List.nodup_cons.mp hn).2 (fun w' h' => hc w' (List.mem_cons_of_mem _ h')), ?_⟩
      · unfold apps
        cases ho : h[w]? with
        | none => simp
        | some o => simpa using hwf.uniqIn o (op_mem h ho) k
      · intro x hx y hy hxy
        subst hxy
        obtain ⟨w', hw', hx'⟩ := List.mem_flatMap.mp hy
        have := com_writer_unique hwf hI (hc w List.mem_cons_self) (hc w' (List.mem_cons_of_mem _ hw')) hx hx'
        subst this
        exact (List.nodup_cons.mp hn).1 hw'
  exact key _ hnd (fun w hw => ord_com hI hw)

/-- An element in version `i` was appended by one of the first `i` writers. -/
theorem not_mem_chainUpTo_of_idx (hwf : WF h) (hI : I.Clean h) {k i : Nat} {a : Nat} {x : Int}
    (ha : (I.ord k)[i]? = some a) (hx : x ∈ apps h a k) : x ∉ Interp.chainUpTo h I k i := by
  intro hm
  obtain ⟨w, hw, hxw⟩ := mem_chainUpTo.mp hm
  have hwo : w ∈ I.ord k := List.mem_of_mem_take hw
  have haw : a = w := com_writer_unique hwf hI (ord_com hI (List.mem_of_getElem? ha)) (ord_com hI hwo) hx hxw
  subst haw
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hw
  have hjlt : j < i := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp at this; omega
  rw [List.getElem?_take_of_lt hjlt] at hj
  have hilen : i < (I.ord k).length := (List.getElem?_eq_some_iff.mp ha).1
  have := ((hI.ordNodup k).getElem?_inj hilen).mp (ha.trans hj.symm)
  omega

/-- A prefix of the chain holding an element of writer `a` holds every element of the writers
before `a`. -/
theorem prefix_holds_earlier (hwf : WF h) (hI : I.Clean h) {k ia ib a b : Nat} {x y : Int} {P : List Int}
    (hP : P <+: Interp.chainAll h I k) (ha : (I.ord k)[ia]? = some a) (hb : (I.ord k)[ib]? = some b)
    (hlt : ib < ia) (hx : x ∈ apps h a k) (hxP : x ∈ P) (hy : y ∈ apps h b k) : y ∈ P := by
  have hA := chainUpTo_prefix_chainAll (h := h) (I := I) k ia
  rcases List.prefix_or_prefix_of_prefix hP hA with h1 | h1
  · exact absurd (h1.mem hxP) (not_mem_chainUpTo_of_idx hwf hI ha hx)
  · apply h1.mem
    apply mem_chainUpTo.mpr
    refine ⟨b, ?_, hy⟩
    rw [List.mem_iff_getElem?]
    exact ⟨ib, by rw [List.getElem?_take_of_lt hlt]; exact hb⟩

/-- Successive writers give a path of write dependencies. -/
theorem ww_plus_of_lt {k i j a b : Nat} (ha : (I.ord k)[i]? = some a) (hb : (I.ord k)[j]? = some b) (hij : i < j) :
    Plus (Interp.dsg h I).ww a b := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + 1 + d := ⟨j - i - 1, by omega⟩
  clear hij
  induction d generalizing b with
  | zero => exact .one ⟨k, i, ha, hb⟩
  | succ d ih =>
    have hlen : i + 1 + d < (I.ord k).length := by
      have := (List.getElem?_eq_some_iff.mp hb).1; omega
    have hc : (I.ord k)[i + 1 + d]? = some (I.ord k)[i + 1 + d] := List.getElem?_eq_getElem hlen
    exact (ih hc).snoc ⟨k, i + 1 + d, hc, by rw [show i + 1 + d + 1 = i + 1 + (d + 1) by omega]; exact hb⟩

theorem idx_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ i : Nat, l[i]? = some a := List.mem_iff_getElem?.mp h


/-! ## Reads in a clean interpretation -/

theorem filterMap_take_prefix {α β : Type} (f : α → Option β) (l : List α) (j : Nat) :
    (l.take j).filterMap f <+: l.filterMap f := by
  have : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv => rhs; rw [this]
  rw [List.filterMap_append]
  exact List.prefix_append _ _

theorem appsBefore_prefix (o : Op) (j k : Nat) : appsBefore o j k <+: appsOf o k :=
  filterMap_take_prefix _ o.value j

theorem apps_of_op {w k : Nat} {o : Op} (ho : h[w]? = some o) : apps h w k = appsOf o k := by
  simp [apps, ho]

theorem mem_value_idx {o : Op} {m : Mop} (hm : m ∈ o.value) : ∃ j : Nat, o.value[j]? = some m :=
  List.mem_iff_getElem?.mp hm

/-- Every `:ok` read returns a prefix of the chain. -/
theorem read_prefix (hI : I.Clean h) {t j : Nat} {o : Op} {m : Mop} (ho : h[t]? = some o) (hok : o.type = .ok)
    (hj : o.value[j]? = some m) (hr : m.f = .r) : toL m.v <+: Interp.chainAll h I m.k := by
  by_cases hext : appsBefore o j m.k = []
  · obtain ⟨i, _, hv, _⟩ := hI.extRead t o ho hok j m hj hr hext
    rw [hv]; exact chainUpTo_prefix_chainAll _ _
  · obtain ⟨i, hi, hv⟩ := hI.intRead t o ho hok j m hj hr hext
    rw [hv]
    have hlen : i < (I.ord m.k).length := (List.getElem?_eq_some_iff.mp hi).1
    have hti : (I.ord m.k)[i] = t := by
      have := List.getElem?_eq_getElem hlen; rw [hi] at this; exact (Option.some.inj this).symm
    have h1 : Interp.chainUpTo h I m.k i ++ appsBefore o j m.k <+: Interp.chainUpTo h I m.k (i + 1) := by
      rw [chainUpTo_succ hlen, hti, apps_of_op ho]
      exact (List.prefix_append_right_inj _).mpr (appsBefore_prefix o j m.k)
    exact h1.trans (chainUpTo_prefix_chainAll _ _)

/-- Every element of an `:ok` read was appended by a writer in the version order. -/
theorem read_writer (hI : I.Clean h) {t j : Nat} {o : Op} {m : Mop} (ho : h[t]? = some o) (hok : o.type = .ok)
    (hj : o.value[j]? = some m) (hr : m.f = .r) {x : Int} (hx : x ∈ toL m.v) :
    ∃ w ∈ I.ord m.k, x ∈ apps h w m.k := by
  have := (read_prefix hI ho hok hj hr).mem hx
  unfold Interp.chainAll at this
  obtain ⟨w, hw, hxw⟩ := mem_chainUpTo.mp this
  exact ⟨w, List.mem_of_mem_take hw, hxw⟩

theorem chainUpTo_eq_nil {k i : Nat} (hI : I.Clean h) (hi : i ≤ (I.ord k).length)
    (h0 : Interp.chainUpTo h I k i = []) : i = 0 := by
  rcases i with _ | i
  · rfl
  · rw [chainUpTo_succ (by omega)] at h0
    have hw : (I.ord k)[i] ∈ I.ord k := List.getElem_mem _
    have := ((hI.ordMem k _).mp hw).2
    simp_all

theorem chainUpTo_last {k i : Nat} (hI : I.Clean h) (hi : i < (I.ord k).length) :
    ∃ z, (Interp.chainUpTo h I k (i + 1)).getLast? = some z ∧ z ∈ apps h (I.ord k)[i] k := by
  rw [chainUpTo_succ hi]
  have hne := ((hI.ordMem k _).mp (List.getElem_mem hi)).2
  obtain ⟨z, hz⟩ : ∃ z, (apps h (I.ord k)[i] k).getLast? = some z := by
    cases hl : (apps h (I.ord k)[i] k).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
    | some z => exact ⟨z, rfl⟩
  refine ⟨z, ?_, List.mem_of_getLast? hz⟩
  rw [List.getLast?_append, hz]; rfl

/-- Two prefixes of a list without duplicates that end with one element are equal. -/
theorem prefix_eq_of_last {P Q C : List Int} (hP : P <+: C) (hQ : Q <+: C) (hC : C.Nodup) {z : Int}
    (hPz : P.getLast? = some z) (hQz : Q.getLast? = some z) : P = Q := by
  have key : ∀ {A B : List Int}, A <+: B → B <+: C → A.getLast? = some z → B.getLast? = some z → A = B := by
    intro A B hAB hBC hA hB
    obtain ⟨R, rfl⟩ := hAB
    cases R with
    | nil => simp
    | cons r rs =>
      exfalso
      have hBn : (A ++ r :: rs).Nodup := hBC.sublist.nodup hC
      have hzR : z ∈ r :: rs := by
        rw [List.getLast?_append] at hB
        have : (r :: rs).getLast? = some ((r :: rs).getLast (by simp)) := List.getLast?_eq_getLast _
        rw [this] at hB; simp at hB; rw [← hB]; exact List.getLast_mem _
      have hzA : z ∈ A := List.mem_of_getLast? hA
      exact (List.nodup_append.mp hBn).2.2 z hzA z hzR rfl
  rcases List.prefix_or_prefix_of_prefix hP hQ with h1 | h1
  · exact key h1 hQ hPz hQz
  · exact (key h1 hP hQz hPz).symm


theorem prefix_getElem? {xs ys : List Int} (h : xs <+: ys) {i : Nat} (hi : i < xs.length) : xs[i]? = ys[i]? := by
  obtain ⟨t, rfl⟩ := h
  exact (List.getElem?_append_left hi).symm

/-- The element right after a version, in a prefix of the chain: the next writer's first. -/
theorem next_after_version (hwf : WF h) (hI : I.Clean h) {k i n : Nat} {L : List Int} {pe e : Int}
    (hi : i < (I.ord k).length) (hL : L <+: Interp.chainAll h I k)
    (hpe : L[n]? = some pe) (he : L[n + 1]? = some e)
    (hV : (Interp.chainUpTo h I k i).getLast? = some pe) : e ∈ apps h (I.ord k)[i] k := by
  have hC := chainAll_nodup hwf hI k
  have hVp := chainUpTo_prefix_chainAll (h := h) (I := I) k i
  generalize hVdef : Interp.chainUpTo h I k i = V at hV hVp
  generalize hCdef : Interp.chainAll h I k = C at hC hVp hL
  have hVne : V ≠ [] := by intro h0; rw [h0] at hV; simp at hV
  have hVlen : 0 < V.length := List.length_pos_iff.mpr hVne
  -- pe sits at |V| - 1 in C, and at n
  have hCpe1 : C[V.length - 1]? = some pe := by
    rw [List.getLast?_eq_getElem?] at hV
    rw [← hV]
    exact (prefix_getElem? hVp (by omega)).symm
  have hCpe2 : C[n]? = some pe := by
    have hn : n < L.length := (List.getElem?_eq_some_iff.mp hpe).1
    rw [← hpe]; exact (prefix_getElem? hL hn).symm
  have hnV : n = V.length - 1 := by
    have hlt : V.length - 1 < C.length := (List.getElem?_eq_some_iff.mp hCpe1).1
    exact ((hC.getElem?_inj hlt).mp (hCpe1.trans hCpe2.symm)).symm
  have hCe : C[V.length]? = some e := by
    have hn1 : n + 1 < L.length := (List.getElem?_eq_some_iff.mp he).1
    rw [← he, show V.length = n + 1 by omega]; exact (prefix_getElem? hL hn1).symm
  have hS := chainUpTo_prefix_chainAll (h := h) (I := I) k (i + 1)
  rw [chainUpTo_succ hi, hVdef, hCdef] at hS
  have hB := ((hI.ordMem k _).mp (List.getElem_mem hi)).2
  have hBlen : 0 < (apps h (I.ord k)[i] k).length := List.length_pos_iff.mpr hB
  have : (V ++ apps h (I.ord k)[i] k)[V.length]? = some e := by
    rw [← hCe]; exact prefix_getElem? hS (by simp; omega)
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at this
  exact List.mem_of_getElem? this

end Elle.R4.LA

import Elle.R4.GInterp
import Elle.RwRegister

/-!
# Round 4: D8's garbage reads and D7's future reads have no interpretation

- **D8** (list-append): `garbage-read-cases` names an `:ok` read holding an element no operation
  appended. No interpretation reads it (every element of a read was appended by someone:
  `GInterp.Valid.appended`, the specification's decomposition of a read into writers' appends).
- **D7** (rw-register): `future-read` names an `:ok` transaction reading the value it writes later
  itself. With values unique per key, the only writer of that value is the reader, so neither an
  external read (which returns `nil` or another committed transaction's write) nor an internal one
  (which returns the transaction's own last write before it) can return it: round 1's
  specification's `nonAdya` branches (`Spec.interpsRegister`).
-/

namespace Elle.R4.LA

open Elle Elle.R4 Elle.ListAppend

variable {h : History}

/-- **D8: a garbage read has no interpretation.** -/
theorem garbage_no_interp {r k : Nat} {e : Int} (hg : (r, k, e) ∈ garbageReadCases h.toList) :
    ¬ ∃ I : GInterp, I.Valid h := by
  rintro ⟨I, hI⟩
  unfold garbageReadCases at hg
  obtain ⟨o, ho, hx⟩ := List.mem_flatMap.mp hg
  obtain ⟨m, hm, hx⟩ := List.mem_flatMap.mp hx
  split at hx
  · simp at hx
  · rename_i hr
    obtain ⟨x, hxv, hx⟩ := List.mem_filterMap.mp hx
    split at hx
    · cases hx
    · rename_i hna
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨_, rfl, rfl⟩ := hx
      have hoh : o ∈ h.toList := (List.mem_filter.mp ho).1
      have hok : o.type = .ok := by simpa [Op.isOk] using (List.mem_filter.mp ho).2
      obtain ⟨i, hi, hoi⟩ := List.mem_iff_getElem.mp hoh
      have hhi : h[i]? = some o := by
        simp only [Array.length_toList] at hi
        rw [Array.getElem?_eq_getElem hi]; congr 1
      have hfr : m.f = .r := by simpa using hr
      obtain ⟨w, o', hw, hni, hxw⟩ := hI.appended i o hhi hok m hm hfr x hxv
      apply hna
      apply List.contains_iff_mem.mpr
      apply List.mem_flatMap.mpr
      refine ⟨o', op_mem h hw, ?_⟩
      unfold appsOf at hxw
      obtain ⟨m', hm', hmx⟩ := List.mem_filterMap.mp hxw
      apply List.mem_filterMap.mpr
      refine ⟨m', hm', ?_⟩
      split at hmx
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        split at hmx
        · rename_i e' he'
          cases hmx
          simp [hc.1, hc.2, he']
        · cases hmx
      · cases hmx

end Elle.R4.LA

namespace Elle.R4.RR

open Elle Elle.R4 Elle.RwRegister

/-- The values `o` writes to `k` before its `j`-th mop. -/
def writesBefore (o : Op) (j k : Nat) : List Val :=
  (o.value.take j).filterMap fun m => if m.f == .w && m.k == k then some m.v else none

/-- A register history as the service hands it to Elle: operations at their index, written
values integers, each written once per key (by one mop of one completion). -/
structure WF (h : History) : Prop where
  index : ∀ i (hi : i < h.size), h[i].index = i
  intW : ∀ o ∈ h.toList, ∀ m ∈ o.value, m.f = .w → ∃ v, m.v = .int v
  uniqW : ∀ (i i' p p' : Nat) (o o' : Op) (m m' : Mop), h[i]? = some o → h[i']? = some o' →
    o.type ≠ .invoke → o'.type ≠ .invoke → o.value[p]? = some m → o'.value[p']? = some m' →
    m.f = .w → m'.f = .w → m.k = m'.k → m.v = m'.v → i = i' ∧ p = p'

/-- Round 1's specification's reads (`Spec.interpsRegister`): an external read returns `nil` or
another committed transaction's write; a read after the transaction's own write of the key
returns its last one. -/
structure Valid (h : History) (com : Nat → Prop) : Prop where
  okCom : ∀ (i : Nat) (o : Op), h[i]? = some o → o.type = .ok → com i
  extRead : ∀ (t : Nat) (o : Op) (j : Nat) (m : Mop), h[t]? = some o → o.type = .ok → o.value[j]? = some m →
    m.f = .r → writesBefore o j m.k = [] →
    m.v = .nil ∨ ∃ (w : Nat) (ow : Op) (p : Nat) (mw : Mop), w ≠ t ∧ com w ∧ h[w]? = some ow ∧
      ow.type ≠ .invoke ∧ ow.value[p]? = some mw ∧ mw.f = .w ∧ mw.k = m.k ∧ mw.v = m.v
  intRead : ∀ (t : Nat) (o : Op) (j : Nat) (m : Mop), h[t]? = some o → o.type = .ok → o.value[j]? = some m →
    m.f = .r → writesBefore o j m.k ≠ [] → (writesBefore o j m.k).getLast? = some m.v

theorem beq_int {a : Int} {v : Val} (h : (Val.int a == v) = true) : v = .int a := by
  cases v with
  | int b =>
    have : (a == b) = true := h
    simp at this; rw [this]
  | _ => cases h

theorem mem_writesBefore {o : Op} {j k : Nat} {v : Val} (hv : v ∈ writesBefore o j k) :
    ∃ p < j, ∃ m, o.value[p]? = some m ∧ m.f = .w ∧ m.k = k ∧ m.v = v := by
  unfold writesBefore at hv
  obtain ⟨m, hm, hmv⟩ := List.mem_filterMap.mp hv
  obtain ⟨p, hp, hpm⟩ := List.mem_iff_getElem.mp hm
  split at hmv
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    cases hmv
    simp only [List.length_take] at hp
    refine ⟨p, by omega, m, ?_, hc.1, hc.2, rfl⟩
    rw [← hpm, List.getElem_take]; exact List.getElem?_eq_getElem _
  · cases hmv

/-- **D7: a future read has no interpretation.** -/
theorem future_read_no_interp {h : History} (hwf : WF h) {t : Nat} (ht : t ∈ futureReadCases h.toList) :
    ¬ ∃ com, Valid h com := by
  rintro ⟨com, hI⟩
  unfold futureReadCases at ht
  obtain ⟨o, ho, hx⟩ := List.mem_filterMap.mp ht
  dsimp only at hx
  split at hx
  · rename_i hany
    cases hx
    have hoh : o ∈ h.toList := (List.mem_filter.mp ho).1
    have hok : o.type = .ok := by simpa [Op.isOk] using (List.mem_filter.mp ho).2
    obtain ⟨⟨m, i⟩, hmi, hc⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.any_eq_true] at hc
    obtain ⟨⟨hfr, hnil⟩, ⟨m', j⟩, hmj, hc2⟩ := hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc2
    obtain ⟨⟨⟨hij, hfw⟩, hk⟩, hvv⟩ := hc2
    -- positions in the zip
    have pos : ∀ {mm : Mop} {q : Nat}, (mm, q) ∈ o.value.zip (List.range o.value.length) → o.value[q]? = some mm := by
      intro mm q hq
      obtain ⟨r, hr, hre⟩ := List.mem_iff_getElem.mp hq
      simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at hre
      obtain ⟨rfl, rfl⟩ := hre
      simp only [List.length_zip, List.length_range, Nat.min_self] at hr
      exact List.getElem?_eq_getElem hr
    have hpi := pos hmi
    have hpj := pos hmj
    obtain ⟨vw, hvw⟩ := hwf.intW o hoh m' (List.mem_of_getElem? hpj) hfw
    have hmv : m.v = .int vw := by rw [hvw] at hvv; exact beq_int hvv
    obtain ⟨q, hq, hoq⟩ := List.mem_iff_getElem.mp hoh
    simp only [Array.length_toList] at hq
    have hht : h[q]? = some o := by rw [Array.getElem?_eq_getElem hq]; congr 1
    have hinv : o.type ≠ .invoke := by rw [hok]; decide
    by_cases hext : writesBefore o i m.k = []
    · rcases hI.extRead q o i m hht hok hpi hfr hext with hn | ⟨w, ow, p, mw, hwq, _, hw, hwi, hp, hfw', hk', hv'⟩
      · rw [hn] at hnil; exact absurd hnil (by decide)
      · have := hwf.uniqW w q p j ow o mw m' hw hht hwi hinv hp hpj hfw' hfw (by rw [hk', hk]) (by rw [hv', hmv, hvw])
        exact hwq this.1
    · have hl := hI.intRead q o i m hht hok hpi hfr hext
      obtain ⟨p, hp, mw, hpw, hfw', hk', hv'⟩ := mem_writesBefore (List.mem_of_getLast? hl)
      have := hwf.uniqW q q p j o o mw m' hht hht hinv hinv hpw hpj hfw' hfw (by rw [hk', hk]) (by rw [hv', hmv, hvw])
      omega
  · cases hx

end Elle.R4.RR

import Elle.R4.Prelude
import Elle.ListAppend

/-!
# Round 4: what list-append's indices hold, for every history

`write-index`, `read-index`, `sorted-values`/`append-index` and `preprocess` (list_append.clj
247-616), as the replica writes them (`Elle.ListAppend`): each entry comes from an operation of
the history it was built from.
-/

namespace Elle.R4

open Elle Elle.ListAppend

/-! ## write-index -/

/-- `write-index`: an indexed element was appended by that (non-invocation) op. -/
theorem wiGet_writeIndex {hs : List Op} {k : Nat} {e : Int} {w : Nat}
    (h : wiGet (writeIndex hs) k e = some w) :
    ∃ o ∈ hs, o.index = w ∧ o.type ≠ .invoke ∧ ∃ m ∈ o.value, m.f = .append ∧ m.k = k ∧ m.v = .int e := by
  let P : List (Nat × List (Int × Nat)) → Prop := fun acc => ∀ k e w, wiGet acc k e = some w →
    ∃ o ∈ hs, o.index = w ∧ o.type ≠ .invoke ∧ ∃ m ∈ o.value, m.f = .append ∧ m.k = k ∧ m.v = .int e
  have : P (writeIndex hs) := by
    unfold writeIndex
    apply foldl_inv
    · intro k e w h; simp [wiGet] at h
    · intro o ho acc hacc
      by_cases hi : o.isInvoke = true
      · simp only [hi, ↓reduceIte]; exact hacc
      · simp only [hi, Bool.false_eq_true, ↓reduceIte]
        have hty : o.type ≠ .invoke := by
          intro e; apply hi; simp [Op.isInvoke, e]
        apply foldl_inv (P := P)
        · exact hacc
        · intro m hm acc2 hacc2
          split
          · rename_i e0 hf hv
            intro k' e' w' hget
            by_cases hk : k' = m.k
            · subst hk
              simp only [wiGet, amUpdate_self] at hget
              simp only [Option.bind_some] at hget
              by_cases he : e' = e0
              · subst he; rw [amPut_self] at hget; cases hget
                exact ⟨o, ho, rfl, hty, m, hm, hf, rfl, hv⟩
              · rw [amPut_ne _ he] at hget
                apply hacc2 m.k e' w'
                simp only [wiGet]
                cases hl : List.lookup m.k acc2 with
                | none => simp [hl] at hget
                | some l => simpa [hl] using hget
            · simp only [wiGet, amUpdate_ne _ hk] at hget
              exact hacc2 k' e' w' hget
          · exact hacc2
  exact this k e w h

/-- `write-index`: an element some (non-invocation) op appended is indexed. -/
theorem wiGet_writeIndex_isSome {hs : List Op} {o : Op} (ho : o ∈ hs) (hi : o.type ≠ .invoke)
    {m : Mop} (hm : m ∈ o.value) {e : Int} (hf : m.f = .append) (hv : m.v = .int e) :
    (wiGet (writeIndex hs) m.k e).isSome := by
  have keep : ∀ (acc : List (Nat × List (Int × Nat))) (m' : Mop) (i : Nat),
      (wiGet acc m.k e).isSome → (wiGet (match m'.f, m'.v with
        | .append, .int e' => amUpdate acc m'.k [] (amPut · e' i)
        | _, _ => acc) m.k e).isSome := by
    intro acc m' i hacc
    split
    · rename_i e' _ _
      by_cases hk : m.k = m'.k
      · rw [hk] at hacc ⊢
        simp only [wiGet, amUpdate_self, Option.bind_some]
        by_cases he : e = e'
        · subst he; simp [amPut_self]
        · rw [amPut_ne _ he]
          simp only [wiGet] at hacc
          cases hl : List.lookup m'.k acc with
          | none => simp [hl] at hacc
          | some l => simpa [hl] using hacc
      · simp only [wiGet, amUpdate_ne _ hk]; exact hacc
    · exact hacc
  unfold writeIndex
  apply foldl_mono_of_mem hs _ [] (fun acc => (wiGet acc m.k e).isSome) o ho
  · intro b
    have hni : o.isInvoke = false := by simp [Op.isInvoke, hi]
    simp only [hni, Bool.false_eq_true, ↓reduceIte]
    apply foldl_mono_of_mem o.value _ b (fun acc => (wiGet acc m.k e).isSome) m hm
    · intro b2
      simp only [hf, hv]
      simp [wiGet, amUpdate_self, amPut_self]
    · intro m' _ b2 hb2; exact keep b2 m' o.index hb2
  · intro o' _ b hb
    split
    · exact hb
    · apply foldl_inv o'.value _ b (fun acc => (wiGet acc m.k e).isSome) hb
      intro m' _ b2 hb2; exact keep b2 m' o'.index hb2

/-! ## read-index -/

def riGet (ri : List (Nat × List (Option Int × List Nat))) (k : Nat) (pe : Option Int) : List Nat :=
  ((ri.lookup k).bind (·.lookup pe)).getD []

/-- `read-index`: an op listed as a reader of `k` at `pe` read `k`, its last element `pe`. -/
theorem riGet_readIndex {hs : List Op} {k : Nat} {pe : Option Int} {r : Nat}
    (h : r ∈ riGet (readIndex hs) k pe) :
    ∃ o ∈ hs, o.index = r ∧ ∃ m ∈ o.value, m.f = .r ∧ m.k = k ∧ peekV m.v = pe ∧
      (o.isInfo && m.v == .nil) = false := by
  let P : List (Nat × List (Option Int × List Nat)) → Prop := fun acc => ∀ k pe r, r ∈ riGet acc k pe →
    ∃ o ∈ hs, o.index = r ∧ ∃ m ∈ o.value, m.f = .r ∧ m.k = k ∧ peekV m.v = pe ∧
      (o.isInfo && m.v == .nil) = false
  have : P (readIndex hs) := by
    unfold readIndex
    apply foldl_inv
    · intro k pe r h; simp [riGet] at h
    · intro o ho acc hacc
      apply foldl_inv (P := P)
      · exact hacc
      · intro m hm acc2 hacc2
        split
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
          intro k' pe' r' hget
          by_cases hk : k' = m.k
          · subst hk
            simp only [riGet, amUpdate_self, Option.bind_some] at hget
            by_cases hp : pe' = peekV m.v
            · subst hp
              rw [amUpdate_self] at hget
              simp only [Option.getD_some, List.mem_append, List.mem_singleton] at hget
              rcases hget with hget | hget
              · apply hacc2 m.k (peekV m.v) r'
                simp only [riGet]
                cases hl : List.lookup m.k acc2 with
                | none => simp [hl] at hget
                | some l =>
                  simp only [hl, Option.getD_some] at hget
                  simpa [hl] using hget
              · subst hget
                exact ⟨o, ho, rfl, m, hm, by simpa using hc.1, rfl, rfl, by simpa using hc.2⟩
            · rw [amUpdate_ne _ hp] at hget
              apply hacc2 m.k pe' r'
              simp only [riGet]
              cases hl : List.lookup m.k acc2 with
              | none => simp [hl] at hget
              | some l => simpa [hl] using hget
          · simp only [riGet, amUpdate_ne _ hk] at hget
            exact hacc2 k' pe' r' hget
        · exact hacc2
  exact this k pe r h


/-! ## sorted-values and append-index -/

theorem hamt_mem {α : Type} (x : α) : ∀ (n : Nat) (items : List (α × UInt32)) (shift : Nat),
    32 - shift = n → x ∈ Hash.hamtOrder items shift → ∃ hh, (x, hh) ∈ items := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  intro items shift hn h
  rw [Hash.hamtOrder] at h
  by_cases hs : shift ≥ 32
  · rw [dite_eq_left_of_eq_true (eq_true hs)] at h
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp h
    exact ⟨b, hab⟩
  · rw [dite_eq_right_of_eq_false (eq_false hs)] at h
    obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp h
    dsimp only at hc
    split at hc
    · simp at hc
    · rename_i y hy
      simp only [List.mem_singleton] at hc; subst hc
      have : y ∈ items.filter (fun p => Hash.chunk p.2 shift == c) := by rw [hy]; simp
      exact ⟨y.2, (List.mem_filter.mp this).1⟩
    · obtain ⟨hh, hm⟩ := ihn (32 - (shift + 5)) (by omega) _ _ rfl hc
      exact ⟨hh, (List.mem_filter.mp hm).1⟩

theorem mem_vectorsOrder {vs : List (List Int)} {x : List Int} (h : x ∈ Hash.vectorsOrder vs) : x ∈ vs := by
  obtain ⟨hh, hm⟩ := hamt_mem x _ _ 0 rfl h
  obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  exact he.1 ▸ hy

/-- A read value of key `k` some op of `hs` returned. -/
def ReadVal (hs : List Op) (k : Nat) (L : List Int) : Prop :=
  ∃ o ∈ hs, ∃ m ∈ o.value, m.f = .r ∧ m.k = k ∧ m.v = .list L

/-- The append mops of `hs` on key `k`. -/
def appendMops (hs : List Op) (k : Nat) : List Mop :=
  (hs.flatMap (·.value)).filter fun m => m.f == .append && m.k == k

/-- `values-from-single-appends`: one append mop on `k` in all of `hs`, of element `e`. -/
def SingleAppend (hs : List Op) (k : Nat) (e : Int) : Prop :=
  ∃ m, appendMops hs k = [m] ∧ m.v = .int e

theorem mem_appendMops {hs : List Op} {k : Nat} {m : Mop} :
    m ∈ appendMops hs k ↔ (∃ o ∈ hs, m ∈ o.value) ∧ m.f = .append ∧ m.k = k := by
  simp [appendMops, List.mem_flatMap]

/-- The state of `values-from-single-appends`'s fold after the mops `ms`. -/
def SingleInv (ms : List Mop) (acc : List (Nat × Option Int)) : Prop :=
  (∀ k, (acc.lookup k).isSome ↔ (ms.filter fun m => m.f == .append && m.k == k) ≠ []) ∧
  (∀ k e, (k, some e) ∈ acc → ∃ m, (ms.filter fun m => m.f == .append && m.k == k) = [m] ∧ m.v = .int e)

theorem lookup_isSome_iff {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β)) (k : α) :
    (l.lookup k).isSome ↔ ∃ v, (k, v) ∈ l := by
  constructor
  · intro h
    cases hl : l.lookup k with
    | none => simp [hl] at h
    | some v => exact ⟨v, lookup_mem hl⟩
  · rintro ⟨v, hv⟩
    induction l with
    | nil => simp at hv
    | cons x xs ih =>
      obtain ⟨a, b⟩ := x
      by_cases hk : k = a
      · subst hk; simp [lookup_cons_self]
      · rw [lookup_cons_ne hk]
        rcases List.mem_cons.mp hv with h1 | h1
        · simp only [Prod.mk.injEq] at h1; exact absurd h1.1 hk
        · exact ih h1

theorem mem_amPut {α β : Type} [BEq α] [LawfulBEq α] {m : List (α × β)} {k k' : α} {v v' : β}
    (h : (k', v') ∈ amPut m k v) : (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ (k', v') ∈ m) := by
  unfold amPut at h
  split at h
  · obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_map.mp h
    by_cases hak : a = k
    · subst hak; simp at he; exact Or.inl ⟨he.1.symm, he.2.symm⟩
    · have : (a == k) = false := by simpa using hak
      simp only [this, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨hak, hab⟩
  · rcases List.mem_append.mp h with h1 | h1
    · by_cases hk : k' = k
      · subst hk
        rename_i hany
        exfalso; apply hany
        exact List.any_eq_true.mpr ⟨_, h1, by simp⟩
      · exact Or.inr ⟨hk, h1⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at h1
      exact Or.inl h1

theorem mem_amPut_self {α β : Type} [BEq α] [LawfulBEq α] (m : List (α × β)) (k : α) (v : β) :
    (k, v) ∈ amPut m k v := lookup_mem (amPut_self m k v)

theorem singleInv_step (ms : List Mop) (acc : List (Nat × Option Int)) (mo : Mop) (h : SingleInv ms acc) :
    SingleInv (ms ++ [mo]) (if mo.f != .append then acc
      else if (acc.lookup mo.k).isSome then amPut acc mo.k none
      else amPut acc mo.k (match mo.v with | .int e => some e | _ => none)) := by
  obtain ⟨h1, h2⟩ := h
  by_cases hf : mo.f = .append
  · have hf' : (mo.f != .append) = false := by simp [hf]
    simp only [hf', Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hs
      constructor
      · intro k
        by_cases hk : k = mo.k
        · subst hk; simp [amPut_self, List.filter_append, hf]
        · rw [amPut_ne _ hk, h1 k]
          have : (mo.f == .append && mo.k == k) = false := by simp [Ne.symm hk]
          simp [List.filter_append, this]
      · intro k e hmem
        rcases mem_amPut hmem with ⟨_, hv⟩ | ⟨hk, hm⟩
        · simp at hv
        · obtain ⟨m, hm1, hm2⟩ := h2 k e hm
          have : (mo.f == .append && mo.k == k) = false := by simp [Ne.symm hk]
          exact ⟨m, by simp [List.filter_append, this, hm1], hm2⟩
    · rename_i hs
      have h0 : (ms.filter fun m => m.f == .append && m.k == mo.k) = [] := by
        cases hc : (ms.filter fun m => m.f == .append && m.k == mo.k) with
        | nil => rfl
        | cons x xs => exact absurd ((h1 mo.k).mpr (by simp [hc])) hs
      constructor
      · intro k
        by_cases hk : k = mo.k
        · subst hk; simp [amPut_self, List.filter_append, hf]
        · rw [amPut_ne _ hk, h1 k]
          have : (mo.f == .append && mo.k == k) = false := by simp [Ne.symm hk]
          simp [List.filter_append, this]
      · intro k e hmem
        rcases mem_amPut hmem with ⟨hk, hv⟩ | ⟨hk, hm⟩
        · subst hk
          refine ⟨mo, by simp [List.filter_append, h0, hf], ?_⟩
          split at hv
          · rename_i e' he'; simp at hv; subst hv; exact he'
          · simp at hv
        · obtain ⟨m, hm1, hm2⟩ := h2 k e hm
          have : (mo.f == .append && mo.k == k) = false := by simp [Ne.symm hk]
          exact ⟨m, by simp [List.filter_append, this, hm1], hm2⟩
  · have hf' : (mo.f != .append) = true := by simp [hf]
    simp only [hf', ↓reduceIte]
    have hn : ∀ k, (mo.f == .append && mo.k == k) = false := by intro k; simp [hf]
    constructor
    · intro k; rw [h1 k]; simp [List.filter_append, hn]
    · intro k e hm
      obtain ⟨m, hm1, hm2⟩ := h2 k e hm
      exact ⟨m, by simp [List.filter_append, hn, hm1], hm2⟩

theorem foldl_prefix_inv {α β : Type} (l : List α) (f : β → α → β) (init : β) (P : List α → β → Prop)
    (h0 : P [] init) (hs : ∀ pre a b, P pre b → P (pre ++ [a]) (f b a)) : P l (l.foldl f init) := by
  suffices ∀ pre b, P pre b → P (pre ++ l) (l.foldl f b) by simpa using this [] init h0
  induction l with
  | nil => intro pre b hb; simpa using hb
  | cons a as ih =>
    intro pre b hb
    have := ih (pre ++ [a]) (f b a) (hs pre a b hb)
    simpa using this

theorem valuesFromSingleAppends_mem {hs : List Op} {k : Nat} {vss : List (List Int)}
    (h : (k, vss) ∈ valuesFromSingleAppends hs) : ∃ e, vss = [[e]] ∧ SingleAppend hs k e := by
  unfold valuesFromSingleAppends at h
  obtain ⟨⟨k', v⟩, hm, he⟩ := List.mem_filterMap.mp h
  cases v with
  | none => simp at he
  | some e =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨e, rfl, ?_⟩
    have inv : SingleInv (hs.flatMap (·.value)) (hs.foldl (fun (acc : List (Nat × Option Int)) o =>
        o.value.foldl (fun acc mo => if mo.f != .append then acc
          else if (acc.lookup mo.k).isSome then amPut acc mo.k none
          else amPut acc mo.k (match mo.v with | .int e => some e | _ => none)) acc) []) := by
      apply foldl_prefix_inv hs _ [] (fun pre acc => SingleInv (pre.flatMap (·.value)) acc)
      · constructor
        · intro k; simp
        · intro k e hm; simp at hm
      · intro pre o acc hacc
        have := foldl_prefix_inv o.value _ acc
          (fun pre2 acc2 => SingleInv (pre.flatMap (·.value) ++ pre2) acc2) (by simpa using hacc)
          (fun pre2 mo acc2 h2 => by simpa using singleInv_step _ acc2 mo h2)
        simpa using this
    obtain ⟨m, hm1, hm2⟩ := inv.2 _ e hm
    exact ⟨m, by simpa [appendMops] using hm1, hm2⟩

/-- The source of an append-index entry: a non-empty read value of `k`, or `[e]` of the one append
on `k` (or nothing). -/
def AISrc (hs : List Op) (k : Nat) (L : List Int) : Prop :=
  L = [] ∨ (L ≠ [] ∧ ReadVal hs k L) ∨ ∃ e, L = [e] ∧ SingleAppend hs k e

/-- `sorted-values`'s fold over reads (list_append.clj:271-327), as the replica writes it. -/
def fromReadsOf (hs : List Op) : List (Nat × List (List Int)) :=
  hs.foldl (fun (acc : List (Nat × List (List Int))) o => o.value.foldl (fun acc m =>
      match m.f, m.v with
      | .r, .list v => if v.isEmpty then acc else amUpdate acc m.k [] fun vs => if vs.contains v then vs else vs ++ [v]
      | _, _ => acc) acc) []

theorem fromReads_mem {hs : List Op} :
    ∀ k vs, (k, vs) ∈ fromReadsOf hs → ∀ v ∈ vs, v ≠ [] ∧ ReadVal hs k v := by
  unfold fromReadsOf
  apply foldl_inv (P := fun acc => ∀ k vs, (k, vs) ∈ acc → ∀ v ∈ vs, v ≠ [] ∧ ReadVal hs k v)
  · intro k vs h; simp at h
  · intro o ho acc hacc
    apply foldl_inv (P := fun acc => ∀ k vs, (k, vs) ∈ acc → ∀ v ∈ vs, v ≠ [] ∧ ReadVal hs k v)
    · exact hacc
    · intro m hm acc2 hacc2
      split
      · rename_i v hf hv
        split
        · exact hacc2
        · rename_i hne
          intro k vs hmem x hx
          unfold amUpdate amGet at hmem
          rcases mem_amPut hmem with ⟨rfl, rfl⟩ | ⟨_, hm2⟩
          · dsimp only at hx
            split at hx
            · cases hl : List.lookup m.k acc2 with
              | none => simp [hl] at hx
              | some l => rw [hl] at hx; exact hacc2 _ l (lookup_mem hl) x hx
            · rcases List.mem_append.mp hx with hx | hx
              · cases hl : List.lookup m.k acc2 with
                | none => simp [hl] at hx
                | some l => rw [hl] at hx; exact hacc2 _ l (lookup_mem hl) x hx
              · simp only [List.mem_singleton] at hx; subst hx
                exact ⟨by simpa using hne, o, ho, m, hm, hf, rfl, hv⟩
          · exact hacc2 k vs hm2 x hx
      · exact hacc2

theorem sortedValues_mem {hs : List Op} {flip byFirst : Bool} {failed : Option (List (Nat × Int))}
    {k : Nat} {svk : List (List Int)} (h : (k, svk) ∈ sortedValues hs flip byFirst failed) :
    ∀ L ∈ svk, (L ≠ [] ∧ ReadVal hs k L) ∨ ∃ e, L = [e] ∧ SingleAppend hs k e := by
  unfold sortedValues at h
  obtain ⟨⟨k', vs⟩, hm, he⟩ := List.mem_map.mp h
  -- the merged list: reads, then single appends for keys without reads
  have hmerged := foldl_inv (valuesFromSingleAppends hs)
      (fun acc (x : Nat × List (List Int)) => if (acc.lookup x.1).isSome then acc else acc ++ [x])
      (fromReadsOf hs)
      (fun acc => ∀ k vs, (k, vs) ∈ acc → ∀ L ∈ vs, (L ≠ [] ∧ ReadVal hs k L) ∨ ∃ e, L = [e] ∧ SingleAppend hs k e)
      (fun k vs h L hL => Or.inl (fromReads_mem k vs h L hL))
      (by
        intro x hx acc hacc
        split
        · exact hacc
        · intro k vs h L hL
          rcases List.mem_append.mp h with h | h
          · exact hacc k vs h L hL
          · simp only [List.mem_singleton] at h; subst h
            obtain ⟨e, he1, he2⟩ := valuesFromSingleAppends_mem hx
            rw [he1] at hL; simp only [List.mem_singleton] at hL
            exact Or.inr ⟨e, hL, he2⟩)
  have hvs := hmerged k' vs hm
  intro L hL
  cases failed with
  | some fs =>
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hvs L (List.mem_mergeSort.mp hL)
  | none =>
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := List.mem_mergeSort.mp hL
    split at this
    · rw [List.mem_reverse] at this
      split at this
      · exact hvs L this
      · exact hvs L (mem_vectorsOrder this)
    · split at this
      · exact hvs L this
      · exact hvs L (mem_vectorsOrder this)

theorem appendIndex_src {hs : List Op} {flip byFirst : Bool} {failed : Option (List (Nat × Int))}
    {k : Nat} {l : List Int} (h : (appendIndex (sortedValues hs flip byFirst failed)).lookup k = some l) :
    ∃ L, l = dedup L ∧ AISrc hs k L := by
  have hm := lookup_mem h
  unfold appendIndex at hm
  obtain ⟨⟨k', svk⟩, hm2, he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨svk.getLast?.getD [], rfl, ?_⟩
  cases hl : svk.getLast? with
  | none => exact Or.inl rfl
  | some L =>
    simp only [Option.getD_some]
    rcases sortedValues_mem hm2 L (List.mem_of_getLast? hl) with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)


/-! ## preprocess -/

/-- D5's fix is on: the models allow G1a. -/
def unInfoOf (fx : Fx) : Bool := fx.d5 && !fx.g1a

/-- The elements `:info` ops appended (D5's `info-elements`), when D5's fix is on. -/
def infoElemsOf (fx : Fx) (h : History) : List (Nat × Int) :=
  if !unInfoOf fx then [] else
    (possible h.toList).filter Op.isInfo |>.flatMap fun o => o.value.filterMap fun m =>
      match m.f, m.v with | .append, .int e => some (m.k, e) | _, _ => none

/-- A read value as `sorted-values` sees it under D5's fix: without `:info` ops' elements. -/
def filtRead (fx : Fx) (h : History) (k : Nat) (l : List Int) : List Int :=
  l.filter fun e => !(infoElemsOf fx h).contains (k, e)

/-- The ops `sorted-values` reads in `preprocess`. -/
def psVOf (fx : Fx) (h : History) : List Op :=
  if !unInfoOf fx then possible h.toList else (possible h.toList).map fun o => { o with value := o.value.map fun m =>
    match m.f, m.v with
    | .r, .list l => { m with v := .list (l.filter fun e => !(infoElemsOf fx h).contains (m.k, e)) }
    | _, _ => m }

/-- What `preprocess` returns when it doesn't throw. -/
def preOf (h : History) (flip : Bool) (fx : Fx) : Pre :=
  { hist := h, possible := possible h.toList,
    ai := appendIndex (if fx.d12b then sortedValues (psVOf fx h) flip true (some (failedAppends h.toList))
      else sortedValues (psVOf fx h) flip fx.d12),
    wi := writeIndex (if unInfoOf fx then oks h.toList else possible h.toList),
    ri := readIndex (possible h.toList), stepOver := fx.d4 }

theorem preprocess_eq {h : History} {flip : Bool} {fx : Fx} {p : Pre} (hp : preprocess h flip fx = .ok p) :
    p = preOf h flip fx := by
  unfold preprocess at hp
  simp only [bind, Except.bind, pure, Except.pure] at hp
  split at hp
  · simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at hp
  · split at hp
    · simp [throw, throwThe, MonadExceptOf.throw, Except.bind] at hp
    · simp only [Except.ok.injEq] at hp
      subst hp
      rfl

/-- D5's filter on one mop. -/
def filtMop (fx : Fx) (h : History) (m : Mop) : Mop :=
  match m.f, m.v with
  | .r, .list l => { m with v := .list (l.filter fun e => !(infoElemsOf fx h).contains (m.k, e)) }
  | _, _ => m

theorem filtMop_f (fx : Fx) (h : History) (m : Mop) : (filtMop fx h m).f = m.f := by
  unfold filtMop; split <;> rfl
theorem filtMop_k (fx : Fx) (h : History) (m : Mop) : (filtMop fx h m).k = m.k := by
  unfold filtMop; split <;> rfl
theorem filtMop_v_list (fx : Fx) (h : History) (m : Mop) (l : List Int) (hf : m.f = .r) (hv : m.v = .list l) :
    (filtMop fx h m).v = .list (filtRead fx h m.k l) := by
  unfold filtMop; split
  · rename_i l' _ hv'; rw [hv] at hv'; cases hv'; rfl
  · rename_i hn; exact absurd hv (hn l hf)
theorem filtMop_v_list_inv (fx : Fx) (h : History) (m : Mop) (L : List Int) (hv : (filtMop fx h m).v = .list L) :
    ∃ l, m.v = .list l ∧ (m.f = .r → L = filtRead fx h m.k l) ∧ (m.f ≠ .r → L = l) := by
  unfold filtMop at hv; split at hv
  · rename_i l hf hv0; simp only [Val.list.injEq] at hv
    exact ⟨l, hv0, fun _ => by rw [← hv]; rfl, fun h => absurd hf h⟩
  · rename_i hn
    exact ⟨L, hv, fun hf => absurd hv (hn L hf), fun _ => rfl⟩
theorem filtMop_append (fx : Fx) (h : History) (m : Mop) (hf : m.f = .append) : filtMop fx h m = m := by
  unfold filtMop; split
  · rename_i hf2 _; rw [hf] at hf2; cases hf2
  · rfl

theorem psVOf_eq (fx : Fx) (h : History) : psVOf fx h =
    if !unInfoOf fx then possible h.toList else (possible h.toList).map fun o =>
      { o with value := o.value.map (filtMop fx h) } := rfl

theorem readVal_psV {fx : Fx} {h : History} {k : Nat} {L : List Int} (hr : ReadVal (psVOf fx h) k L) :
    ∃ o ∈ possible h.toList, ∃ m ∈ o.value, m.f = .r ∧ m.k = k ∧ ∃ L', m.v = .list L' ∧
      L = (if unInfoOf fx then filtRead fx h k L' else L') := by
  obtain ⟨o, ho, m, hm, hf, hk, hv⟩ := hr
  rw [psVOf_eq] at ho
  by_cases hu : unInfoOf fx = true
  · simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ho
    obtain ⟨o0, ho0, rfl⟩ := List.mem_map.mp ho
    obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
    rw [filtMop_f] at hf; rw [filtMop_k] at hk
    obtain ⟨l, hl, h1, _⟩ := filtMop_v_list_inv fx h m0 L hv
    exact ⟨o0, ho0, m0, hm0, hf, hk, l, hl, by simp [hu, h1 hf, hk]⟩
  · simp only [hu, Bool.not_false, ↓reduceIte] at ho
    exact ⟨o, ho, m, hm, hf, hk, L, hv, by simp [hu]⟩

theorem appendMops_psV {fx : Fx} {h : History} {k : Nat} :
    appendMops (psVOf fx h) k = appendMops (possible h.toList) k := by
  rw [psVOf_eq]
  split
  · rfl
  · unfold appendMops
    simp only [List.flatMap_map]
    induction (possible h.toList) with
    | nil => rfl
    | cons o os ih =>
      simp only [List.flatMap_cons, List.filter_append, ih]
      congr 1
      induction o.value with
      | nil => rfl
      | cons m ms ih2 =>
        simp only [List.map_cons, List.filter_cons, ih2, filtMop_f, filtMop_k]
        split
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rw [filtMop_append fx h m hc.1]
        · rfl


/-! ## The version order's neighbours: prevElem, elemBefore, committedFrom, the mop deps -/

/-- The append index's list for `k`. -/
def aiOf (p : Pre) (k : Nat) : List Int := (p.ai.lookup k).getD []

/-- `x` sits at or before `pe` in `vs`. -/
def AtOrBefore (vs : List Int) (pe x : Int) : Prop :=
  x = pe ∨ ∃ i j : Nat, j ≤ i ∧ vs[i]? = some pe ∧ vs[j]? = some x

theorem findIdx_beq_some {vs : List Int} {e : Int} {i : Nat} (h : vs.findIdx? (· == e) = some i) :
    vs[i]? = some e ∧ ∀ j < i, vs[j]? ≠ some e := by
  obtain ⟨hi, he, hlt⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  refine ⟨by simp [List.getElem?_eq_getElem hi, (beq_iff_eq.mp he)], ?_⟩
  intro j hj hje
  have hjl : j < vs.length := by omega
  rw [List.getElem?_eq_getElem hjl] at hje
  exact hlt j hj (by simp at hje; simp [hje])

theorem findIdx_beq_none {vs : List Int} {e : Int} (h : vs.findIdx? (· == e) = none) : e ∉ vs := by
  intro hm
  have := List.findIdx?_eq_none_iff.mp h e hm
  simp at this

theorem prevElem_some {p : Pre} {k : Nat} {e pe : Int} (h : prevElem p k e = some pe) :
    (∃ i, (aiOf p k)[i]? = some pe ∧ (aiOf p k)[i + 1]? = some e) ∨
    (e ∉ aiOf p k ∧ (aiOf p k).getLast? = some pe) := by
  unfold aiOf
  unfold prevElem at h
  dsimp only at h
  split at h
  · rename_i i hi
    obtain ⟨hie, _⟩ := findIdx_beq_some hi
    split at h
    · left
      refine ⟨i - 1, h, ?_⟩
      have : i - 1 + 1 = i := by omega
      rw [this]; exact hie
    · simp at h
  · rename_i hn
    exact Or.inr ⟨findIdx_beq_none hn, h⟩

theorem prevElem_none {p : Pre} {k : Nat} {e : Int} (h : prevElem p k e = none) :
    (aiOf p k)[0]? = some e ∨ (e ∉ aiOf p k ∧ aiOf p k = []) := by
  unfold aiOf
  unfold prevElem at h
  dsimp only at h
  split at h
  · rename_i i hi
    obtain ⟨hie, _⟩ := findIdx_beq_some hi
    split at h
    · rename_i hpos
      have : i - 1 < ((List.lookup k p.ai).getD []).length := by
        have := (List.getElem?_eq_some_iff.mp hie).1; omega
      simp [List.getElem?_eq_getElem this] at h
    · have : i = 0 := by omega
      subst this; exact Or.inl hie
  · rename_i hn
    exact Or.inr ⟨findIdx_beq_none hn, List.getLast?_eq_none_iff.mp h⟩

theorem elemBefore_some {p : Pre} {k : Nat} {x y : Int} (h : elemBefore p k x = some y) :
    ∃ i, (aiOf p k)[i]? = some y ∧ (aiOf p k)[i + 1]? = some x ∧ ∀ j < i + 1, (aiOf p k)[j]? ≠ some x := by
  unfold aiOf
  unfold elemBefore at h
  dsimp only at h
  split at h
  · rename_i i hi
    obtain ⟨hie, hfirst⟩ := findIdx_beq_some hi
    split at h
    · refine ⟨i - 1, h, ?_, ?_⟩
      · have : i - 1 + 1 = i := by omega
        rw [this]; exact hie
      · have : i - 1 + 1 = i := by omega
        rw [this]; exact hfirst
    · simp at h
  · simp at h

theorem atOrBefore_step {vs : List Int} {pe x y : Int} (hpe : pe ∈ vs) (h : AtOrBefore vs pe x)
    {i : Nat} (hy : vs[i]? = some y) (hx : vs[i + 1]? = some x) (hfirst : ∀ j < i + 1, vs[j]? ≠ some x) :
    AtOrBefore vs pe y := by
  right
  rcases h with rfl | ⟨a, b, hab, ha, hb⟩
  · -- x = pe: its first occurrence is i + 1
    exact ⟨i + 1, i, by omega, hx, hy⟩
  · have : i + 1 ≤ b := by
      rcases Nat.lt_or_ge b (i + 1) with hlt | hge
      · exact absurd hb (hfirst b hlt)
      · exact hge
    exact ⟨a, i, by omega, ha, hy⟩

/-- `committed-previous-element` (D4's step-over): what it finds was indexed, at or before where it
started. -/
theorem committedFrom_some {p : Pre} {k : Nat} {pe x : Int} {w : Nat} (hpe : pe ∈ aiOf p k)
    (h : committedFrom p k (some pe) = some (x, w)) :
    wiGet p.wi k x = some w ∧ AtOrBefore (aiOf p k) pe x := by
  unfold committedFrom at h
  simp only [Id.run] at h
  generalize hr : (forIn (m := Id) Lean.Loop.mk
    ((none, some pe, ((List.lookup k p.ai).getD []).length + 1) : Option (Option (Int × Nat)) × Option Int × Nat) _) = r at h
  have key : (∀ x w, r.1 = some (some (x, w)) → wiGet p.wi k x = some w ∧ AtOrBefore (aiOf p k) pe x) := by
    rw [← hr]
    refine loop_inv (β := Option (Option (Int × Nat)) × Option Int × Nat) _ (fun s => s.2.2)
      (fun s => s.1 = none ∧ ∀ c, s.2.1 = some c → AtOrBefore (aiOf p k) pe c)
      (fun s => ∀ x w, s.1 = some (some (x, w)) → wiGet p.wi k x = some w ∧ AtOrBefore (aiOf p k) pe x) ?_ _ ?_
    · intro s ⟨hs1, hs2⟩
      by_cases hpos : s.2.2 > 0
      · simp only [hpos, ↓reduceIte]
        cases hc : s.2.1 with
        | none => simp only [Id.run, pure]; intro x' w' he; simp at he
        | some c =>
          cases hw : wiGet p.wi k c with
          | some w' =>
            simp only [Id.run, pure, hw]
            intro x' w'' he
            simp only [Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            exact ⟨hw, hs2 c hc⟩
          | none =>
            simp only [Id.run, pure, hw]
            refine ⟨⟨trivial, ?_⟩, by omega⟩
            intro c' hc'
            obtain ⟨i, hy, hx, hfirst⟩ := elemBefore_some hc'
            exact atOrBefore_step hpe (hs2 c hc) hy hx hfirst
      · simp only [hpos, ↓reduceIte]; simp only [Id.run, pure]; intro x' w' he; cases he
    · exact ⟨rfl, fun c hc => by simp at hc; subst hc; exact Or.inl rfl⟩
  obtain ⟨r1, r2⟩ := r
  cases r1 with
  | none => cases h
  | some r' =>
    cases r' with
    | none => cases h
    | some xw =>
      obtain ⟨x', w'⟩ := xw
      cases h
      exact key x w rfl

/-- An indexed element is its own committed previous element. -/
theorem committedFrom_self {p : Pre} {k : Nat} {pe : Int} {w : Nat} (hw : wiGet p.wi k pe = some w) :
    committedFrom p k (some pe) = some (pe, w) := by
  unfold committedFrom
  simp only [Id.run]
  rw [show (forIn Lean.Loop.mk _ _ : Id _) = Lean.Loop.forIn _ _ _ from rfl, Lean.Loop.forIn_eq_of_monadTail]
  simp [hw]
  rfl

/-- `ww-mop-dep`: the op it names wrote an element at or before the one read before `e`. -/
theorem wwMopDep_some {p : Pre} {op k : Nat} {e : Int} {d : Nat} (h : wwMopDep p op k e = some d) :
    ∃ pe x, prevElem p k e = some pe ∧ wiGet p.wi k x = some d ∧ d ≠ op ∧
      AtOrBefore (aiOf p k) pe x ∧ (p.stepOver = false → x = pe) := by
  unfold wwMopDep at h
  split at h
  · simp at h
  · rename_i pe hpe
    have hpemem : pe ∈ aiOf p k := by
      rcases prevElem_some hpe with ⟨i, hi, _⟩ | ⟨_, hl⟩
      · exact List.mem_of_getElem? hi
      · exact List.mem_of_getLast? hl
    split at h
    · rename_i hso
      split at h
      · rename_i x w hcf
        split at h
        · rename_i hne
          simp only [Option.some.injEq] at h; subst h
          obtain ⟨hw, hab⟩ := committedFrom_some hpemem hcf
          exact ⟨pe, x, hpe, hw, by simpa using hne, hab, fun h2 => by simp [h2] at hso⟩
        · simp at h
      · simp at h
    · rename_i hso
      split at h
      · rename_i w hw
        split at h
        · rename_i hne
          simp only [Option.some.injEq] at h; subst h
          exact ⟨pe, pe, hpe, hw, by simpa using hne, Or.inl rfl, fun _ => rfl⟩
        · simp at h
      · simp at h

/-- `wr-mop-dep`: the op it names wrote the read's last element. -/
theorem wrMopDep_some {p : Pre} {op k : Nat} {v : Val} {d : Nat} (h : wrMopDep p op k v = some d) :
    ∃ e, peekV v = some e ∧ wiGet p.wi k e = some d ∧ d ≠ op := by
  unfold wrMopDep at h
  split at h
  · simp at h
  · rename_i e he
    split at h
    · rename_i w hw
      split at h
      · rename_i hne
        simp only [Option.some.injEq] at h; subst h
        exact ⟨e, he, hw, by simpa using hne⟩
      · simp at h
    · simp at h

/-- `rw-mop-deps`: each op it names read `k` with last element the one before `e`. -/
theorem rwMopDeps_mem {p : Pre} {op k : Nat} {e : Int} {r : Nat} (h : r ∈ rwMopDeps p op k e) :
    r ∈ riGet p.ri k (prevElem p k e) ∧ r ≠ op := by
  unfold rwMopDeps at h
  simp only [List.mem_filter, bne_iff_ne, ne_eq] at h
  refine ⟨?_, h.2⟩
  have := (mem_dedup _ _).mp h.1
  simpa [riGet] using this

end Elle.R4

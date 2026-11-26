import Jank.R9.Nrepl.Fix

/-!
# Round 9, nREPL: what Q2's fix does to every reply, for every request and every reply map

core.jank `response-for` (Server.lean `responseFor`, `(merge resp (select-keys req ["id"
"session"]))`) is applied by `responses-for` to each element of a handler's vector.

- ★ `responseFor_nil_keys`: for EVERY request, the message made from a `nil` element (stock
  handler/eval.jank's blank `:out`/`:err`) holds only keys taken from the request, each one `same`
  as "id" or "session": Q2's message without content.
- ★ `responseFor_keeps_keys`: for EVERY request and EVERY reply map, the message keeps every key of
  the reply map (`assoc` never drops a key).
- ★ `dropNils_no_nil`: Q2's `(filterv some? ...)` leaves no `nil` element.
- ★ `q2_messages`: so with Q2, for EVERY request and EVERY vector of maps and nils, each message is
  made from one of the vector's maps and keeps every key of it: no message is made from a `nil`.
- ★ `stock_blank_out`: on stock, an eval whose stdout is blank sends, first, a message holding only
  keys from the request (the instance of `responseFor_nil_keys` for `outReply`).

`JVal.same` is a `partial def` (opaque to proofs): the statements carry it as it comes out of
`List.find?`, never evaluate it.
-/

namespace Jank.R9.Nrepl

open Jank.NreplServer Jank.R3.Nrepl

def keysOf : JVal → List JVal
  | .map kvs => kvs.map Prod.fst
  | _ => []

theorem assocMap_keys_mono (kvs : List (JVal × JVal)) (k v x : JVal) (h : x ∈ kvs.map Prod.fst) :
    x ∈ (assocMap kvs k v).map Prod.fst := by
  unfold assocMap
  split
  · rw [List.map_map]
    have : (Prod.fst ∘ fun (x : JVal × JVal) => if JVal.same x.1 k = true then (x.1, v) else (x.1, x.2)) = Prod.fst := by
      funext p; simp only [Function.comp]; split <;> rfl
    rw [this]; exact h
  · simp only [List.map_append, List.mem_append]; exact Or.inl h

theorem assocMap_keys_sub (kvs : List (JVal × JVal)) (k v x : JVal) (h : x ∈ (assocMap kvs k v).map Prod.fst) :
    x ∈ kvs.map Prod.fst ∨ x = k := by
  unfold assocMap at h
  split at h
  · rw [List.map_map] at h
    have : (Prod.fst ∘ fun (x : JVal × JVal) => if JVal.same x.1 k = true then (x.1, v) else (x.1, x.2)) = Prod.fst := by
      funext p; simp only [Function.comp]; split <;> rfl
    rw [this] at h; exact Or.inl h
  · simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at h
    exact h

def conjStep (acc : List (JVal × JVal)) (e : JVal × JVal) : List (JVal × JVal) := assocMap acc e.1 e.2

theorem foldl_assoc_mono (ys acc : List (JVal × JVal)) (x : JVal) (h : x ∈ acc.map Prod.fst) :
    x ∈ (ys.foldl (fun acc (p : JVal × JVal) => assocMap acc p.1 p.2) acc).map Prod.fst := by
  induction ys generalizing acc with
  | nil => exact h
  | cons y ys ih => exact ih _ (assocMap_keys_mono _ _ _ _ h)

theorem foldl_assoc_sub (ys acc : List (JVal × JVal)) (x : JVal)
    (h : x ∈ (ys.foldl (fun acc (p : JVal × JVal) => assocMap acc p.1 p.2) acc).map Prod.fst) :
    x ∈ acc.map Prod.fst ∨ x ∈ ys.map Prod.fst := by
  induction ys generalizing acc with
  | nil => exact Or.inl h
  | cons y ys ih =>
    rcases ih _ h with h1 | h1
    · rcases assocMap_keys_sub _ _ _ _ h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (by simp [h2])
    · exact Or.inr (by simp [h1])

/-- The fold `select-keys` runs. -/
def selFold (m : JVal) (ks : List JVal) (acc : List (JVal × JVal)) : List (JVal × JVal) :=
  ks.foldl (fun acc k => match jfind m k with
    | some (k', v) => assocMap acc k' v
    | none => acc) acc

theorem jfind_same (m k k' v : JVal) (hf : jfind m k = some (k', v)) : JVal.same k' k = true := by
  unfold jfind at hf
  split at hf
  · have := List.find?_some hf
    simpa using this
  · cases hf

/-- `select-keys`' entries: each key is the request's own key, `same` as one asked for. -/
theorem selFold_keys (m : JVal) (ks0 : List JVal) :
    ∀ (ks : List JVal), (∀ k ∈ ks, k ∈ ks0) → ∀ (acc : List (JVal × JVal)),
      (∀ y ∈ acc.map Prod.fst, ∃ key ∈ ks0, JVal.same y key = true) →
      ∀ x ∈ (selFold m ks acc).map Prod.fst, ∃ key ∈ ks0, JVal.same x key = true := by
  intro ks
  induction ks with
  | nil => intro _ acc hacc x hx; exact hacc x hx
  | cons k ks ih =>
    intro hks acc hacc x hx
    have hk0 : k ∈ ks0 := hks k List.mem_cons_self
    refine ih (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) _ ?_ x hx
    intro y hy
    cases hf : jfind m k with
    | none => simp only [hf] at hy; exact hacc y hy
    | some e =>
      obtain ⟨k', v⟩ := e
      simp only [hf] at hy
      rcases assocMap_keys_sub _ _ _ _ hy with h1 | h1
      · exact hacc y h1
      · exact ⟨k, hk0, by rw [h1]; exact jfind_same m k k' v hf⟩

theorem selectKeys_eq (m : JVal) (ks : List JVal) : selectKeys m ks = .map (selFold m ks []) := rfl

/-- ★ For every request, the message `response-for` makes from `nil` holds only keys of the
request, each `same` as "id" or "session". -/
theorem responseFor_nil_keys (req : JVal) :
    ∀ x ∈ keysOf (responseFor req .nil), ∃ key ∈ [JVal.s "id", JVal.s "session"], JVal.same x key = true := by
  intro x hx
  simp only [responseFor, merge, selectKeys_eq, List.any_cons, List.any_nil, JVal.truthy, Bool.false_or,
    Bool.or_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, conjMap,
    keysOf] at hx
  rcases foldl_assoc_sub _ _ _ hx with h | h
  · simp at h
  · exact selFold_keys req _ _ (fun k hk => hk) [] (by simp) x h

/-- ★ For every request and every reply map, the message keeps every key of the reply. -/
theorem responseFor_keeps_keys (req : JVal) (kvs : List (JVal × JVal)) :
    ∀ x ∈ kvs.map Prod.fst, x ∈ keysOf (responseFor req (.map kvs)) := by
  intro x hx
  simp only [responseFor, merge, selectKeys_eq, List.any_cons, List.any_nil, JVal.truthy, Bool.true_or,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.foldl_cons, List.foldl_nil, conjMap, keysOf]
  exact foldl_assoc_mono _ _ _ hx

def isNil : JVal → Bool
  | .nil => true
  | _ => false

/-- ★ Q2's `(filterv some? v)` leaves no nil. -/
theorem dropNils_no_nil (xs : List JVal) :
    ∃ ys, dropNils (.vec xs) = .vec ys ∧ (∀ y ∈ ys, isNil y = false) ∧ (∀ y ∈ ys, y ∈ xs) := by
  refine ⟨xs.filter (fun x => match x with | .nil => false | _ => true), rfl, ?_, ?_⟩
  · intro y hy
    have := (List.mem_filter.mp hy).2
    cases y <;> simp_all [isNil]
  · intro y hy; exact (List.mem_filter.mp hy).1

/-- ★ With Q2, for every request and every handler vector of maps and nils, every message is made
from one of the vector's maps and keeps every key of that map. -/
theorem q2_messages (req : JVal) (xs : List JVal) (hxs : ∀ x ∈ xs, isNil x = true ∨ ∃ kvs, x = .map kvs) :
    ∀ r ∈ responsesFor req (dropNils (.vec xs)),
      ∃ kvs, JVal.map kvs ∈ xs ∧ ∀ x ∈ kvs.map Prod.fst, x ∈ keysOf r := by
  intro r hr
  obtain ⟨ys, hys, hnn, hsub⟩ := dropNils_no_nil xs
  rw [hys] at hr
  simp only [responsesFor, List.mem_map] at hr
  obtain ⟨y, hy, rfl⟩ := hr
  rcases hxs y (hsub y hy) with h | ⟨kvs, rfl⟩
  · rw [hnn y hy] at h; cases h
  · exact ⟨kvs, hsub _ hy, responseFor_keeps_keys req kvs⟩

/-- ★ Stock: an eval whose stdout is blank sends first a message holding only keys of the request
(the first element of handler/eval.jank's vector is `outReply`'s nil). -/
theorem stock_blank_out (req : JVal) (so : List UInt8) (h : Jank.NreplServer.blank (some so) = true) :
    outReply so = .nil ∧
    ∀ x ∈ keysOf (responseFor req (outReply so)), ∃ key ∈ [JVal.s "id", JVal.s "session"], JVal.same x key = true := by
  have : outReply so = .nil := by simp [outReply, h]
  exact ⟨this, by rw [this]; exact responseFor_nil_keys req⟩


/-! ## Q1's `take-line` (fixes/Q1.diff handler/eval.jank), for every input -/

theorem not_mem_take_of_le (xs : List UInt8) (b : UInt8) (k : Nat)
    (h : ∀ k', xs.findIdx? (· == b) = some k' → k ≤ k') : b ∉ xs.take k := by
  intro hm
  rw [List.mem_take_iff_getElem] at hm
  obtain ⟨j, hj, hjb⟩ := hm
  have hjl : j < xs.length := Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
  cases hf : xs.findIdx? (· == b) with
  | none =>
    have := (List.findIdx?_eq_none_iff.mp hf) _ (List.getElem_mem hjl)
    simp [hjb] at this
  | some k' =>
    have hk := h k' hf
    obtain ⟨_, _, hmin⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    have hjk : j < k' := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)) hk
    exact hmin j hjk (by simp [hjb])

theorem termIdx_le (text : List UInt8) (k : Nat) (h : termIdx text = some k) :
    (∀ k', text.findIdx? (· == 10) = some k' → k ≤ k') ∧ (∀ k', text.findIdx? (· == 13) = some k' → k ≤ k') := by
  unfold termIdx at h
  split at h
  · rename_i a b h1 h2
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun k' hk' => ?_, fun k' hk' => ?_⟩
    · rw [h1] at hk'; simp only [Option.some.injEq] at hk'; subst hk'; exact Nat.min_le_left _ _
    · rw [h2] at hk'; simp only [Option.some.injEq] at hk'; subst hk'; exact Nat.min_le_right _ _
  · rename_i a h1 h2
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun k' hk' => ?_, fun k' hk' => ?_⟩
    · rw [h1] at hk'; simp only [Option.some.injEq] at hk'; subst hk'; exact Nat.le_refl _
    · rw [h2] at hk'; cases hk'
  · rename_i b h1 h2
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun k' hk' => ?_, fun k' hk' => ?_⟩
    · rw [h1] at hk'; cases hk'
    · rw [h2] at hk'; simp only [Option.some.injEq] at hk'; subst hk'; exact Nat.le_refl _
  · cases h

theorem termIdx_none (text : List UInt8) (h : termIdx text = none) : (10 : UInt8) ∉ text ∧ (13 : UInt8) ∉ text := by
  unfold termIdx at h
  split at h
  · cases h
  · cases h
  · cases h
  · rename_i h1 h2
    constructor
    · intro hm; have := (List.findIdx?_eq_none_iff.mp h1) _ hm; simp at this
    · intro hm; have := (List.findIdx?_eq_none_iff.mp h2) _ hm; simp at this

/-- ★ A line `take-line` returns holds no line terminator, for every session input. -/
theorem takeLine_line_clean (i i' : SIn) (l : List UInt8) (h : takeLine i = some (some l, i')) :
    (10 : UInt8) ∉ l ∧ (13 : UInt8) ∉ l := by
  unfold takeLine at h
  split at h
  · rename_i k hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, _⟩ := h
    subst h1
    have ⟨a, b⟩ := termIdx_le _ _ hk
    exact ⟨not_mem_take_of_le _ _ _ a, not_mem_take_of_le _ _ _ b⟩
  · rename_i hk
    split at h
    · split at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, _⟩ := h
        subst h1
        exact termIdx_none _ hk
    · cases h

/-- ★ `take-line` waits (the reader would ask for input) exactly when no terminator is buffered and
no end of input is queued, for every session input. -/
theorem takeLine_none_iff (i : SIn) : takeLine i = none ↔ termIdx i.text = none ∧ i.eof = false := by
  unfold takeLine
  split
  · rename_i k hk; simp [hk]
  · rename_i hk
    cases he : i.eof <;> simp [hk]

/-- ★ When a terminator is buffered, the line, its terminator (`\n`, `\r` or `\r\n`) and the text
left make up the text, for every session input: `take-line` loses and invents nothing. -/
theorem takeLine_split (i i' : SIn) (l : List UInt8) (k : Nat) (hk : termIdx i.text = some k)
    (h : takeLine i = some (some l, i')) :
    ∃ t : List UInt8, (t = [10] ∨ t = [13] ∨ t = [13, 10]) ∧ i.text = l ++ t ++ i'.text := by
  unfold takeLine at h
  rw [hk] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hl, hi'⟩ := h
  subst hl; subst hi'
  have hkl : k < i.text.length := by
    unfold termIdx at hk
    split at hk <;> simp at hk
    · rename_i a b h1 h2
      obtain ⟨ha, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h1
      obtain ⟨hb, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h2
      omega
    · rename_i a h1 _
      obtain ⟨ha, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h1
      omega
    · rename_i b _ h2
      obtain ⟨hb, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h2
      omega
  have hsplit : i.text = i.text.take k ++ i.text.drop k := (List.take_append_drop k i.text).symm
  by_cases hr : i.text.findIdx? (· == 13) = some k
  · obtain ⟨_, hr13, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hr
    by_cases hn : i.text.findIdx? (· == 10) = some (k + 1)
    · obtain ⟨hk1, hn10, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hn
      refine ⟨[13, 10], Or.inr (Or.inr rfl), ?_⟩
      simp only [hr, hn]
      have e1 : i.text[k] = 13 := by simpa using hr13
      have e2 : i.text[k + 1] = 10 := by simpa using hn10
      rw [List.append_assoc]
      conv => lhs; rw [hsplit]
      congr 1
      rw [List.drop_eq_getElem_cons hkl, List.drop_eq_getElem_cons hk1, e1, e2]
      simp
    · refine ⟨[13], Or.inr (Or.inl rfl), ?_⟩
      simp only [hr]
      have e1 : i.text[k] = 13 := by simpa using hr13
      rw [List.append_assoc]
      conv => lhs; rw [hsplit]
      congr 1
      rw [List.drop_eq_getElem_cons hkl, e1]
      simp [hn]
  · have h10 : i.text.findIdx? (· == 10) = some k := by
      unfold termIdx at hk
      split at hk <;> simp at hk
      · rename_i a b h1 h2
        rcases Nat.le_total a b with hab | hab
        · rw [Nat.min_eq_left hab] at hk; subst hk; exact h1
        · rw [Nat.min_eq_right hab] at hk; subst hk; exact absurd h2 hr
      · rename_i a h1 _; subst hk; exact h1
      · rename_i b _ h2; subst hk; exact absurd h2 hr
    obtain ⟨_, hn10, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h10
    refine ⟨[10], Or.inl rfl, ?_⟩
    have e2 : i.text[k] = 10 := by simpa using hn10
    rw [List.append_assoc]
    conv => lhs; rw [hsplit]
    congr 1
    rw [List.drop_eq_getElem_cons hkl, e2]
    simp [hr]

theorem findIdx_app10 (l : List UInt8) (h10 : (10 : UInt8) ∉ l) :
    (l ++ [10]).findIdx? (· == 10) = some l.length := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨by simp, by simp, ?_⟩
  intro j hj
  rw [List.getElem_append_left hj]
  intro h
  exact h10 (by have := List.getElem_mem hj; simp at h; rw [← h]; exact this)

theorem findIdx_app13 (l : List UInt8) (h13 : (13 : UInt8) ∉ l) :
    (l ++ [10]).findIdx? (· == 13) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  simp at hx
  rcases hx with hx | hx
  · simp; intro h; subst h; exact h13 hx
  · subst hx; decide

/-- ★ Type-ahead: a line sent to an empty input is read back whole. -/
theorem takeLine_addInput (i : SIn) (l : List UInt8) (h10 : (10 : UInt8) ∉ l) (h13 : (13 : UInt8) ∉ l)
    (he : i.text = []) (hs : i.skipLf = false) :
    takeLine (addInput i (l ++ [10])) = some (some l, { i with text := [], skipLf := false }) := by
  have hne : (l ++ [10]).isEmpty = false := by simp
  simp only [addInput, hne, hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte, he, List.nil_append]
  unfold takeLine termIdx
  simp only [findIdx_app10 l h10, findIdx_app13 l h13]
  simp

end Jank.R9.Nrepl

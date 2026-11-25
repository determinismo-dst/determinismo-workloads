import Jank.R3.Immer.Maps

/-!
# The findings, as theorems over the replica

- IM1: `assoc` of a key equal to a stored one replaces the stored key (immer's `champ::add`
  replaces the whole stored value); Clojure keeps the stored key.
- IM2: on an array-map transient after `persistent!`, `(get t k nf)`, `(contains? t k)` and
  `(find t k)` do not throw (transient_array_map.cpp 47, 52, 62 have no `assert_active()`); the
  hash-map transient's reads all throw.
-/

namespace Jank.R3.Immer.Findings

open Jank.Equality (V)
open Objects Maps

/-- `(assoc (hash-map '(1) 0) [1] 1)` in jank's replica. -/
def im1Map : JMap :=
  ((JMap.fromPairs [(.list [.int 1], .int 0)]) >>= fun m => m.assoc (.vec [.int 1]) (.int 1)).run' {}

/-- IM1, jank: the map's only key is now the vector `[1]`. -/
theorem im1_jank_key_replaced :
    (match im1Map.entries with | [(.vec [.int 1], .int 1)] => true | _ => false) = true := by decide

/-- IM1, Clojure: the stored key `'(1)` is kept, the value replaced. -/
theorem im1_clojure_keeps_key :
    (match cAssoc [(.list [.int 1], .int 0)] (.vec [.int 1]) (.int 1) with
     | [(.list [.int 1], .int 1)] => true | _ => false) = true := by decide

/-- `(conj #{'(1)} [1])` in jank's replica. -/
def im1Set : JSet := ((JSet.fromList [.list [.int 1]]) >>= fun s => s.conj (.vec [.int 1])).run' {}

/-- IM1 for sets, jank: the set's only element is now `[1]` (Clojure: unchanged, `'(1)`). -/
theorem im1_set_element_replaced :
    (match im1Set.toList with | [.vec [.int 1]] => true | _ => false) = true := by decide

/-- IM2: the array-map transient's non-asserting reads succeed after `persistent!`, for every
content, key and default. -/
theorem im2_dead_array_reads (es : List (V × V)) (k nf : V) :
    (∃ x, ({ body := .array es, active := false } : TMap).read (.get2 k nf) = .ok x) ∧
    (∃ x, ({ body := .array es, active := false } : TMap).read (.contains k) = .ok x) ∧
    (∃ x, ({ body := .array es, active := false } : TMap).read (.find k) = .ok x) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- … and the asserting reads throw, as every read of a hash-map transient does. -/
theorem im2_dead_asserting_reads (es : List (V × V)) (k : V) (h : Champ.Transient (V × V)) (r : TRead) :
    ({ body := .array es, active := false } : TMap).read .count = .throws deadMsg ∧
    ({ body := .array es, active := false } : TMap).read (.get1 k) = .throws deadMsg ∧
    ({ body := .hash h, active := false } : TMap).read r = .throws deadMsg := by
  refine ⟨rfl, rfl, ?_⟩
  cases r <;> rfl

/-- IM2, the program: `(let [t (transient {7 1})] (persistent! t) (get t 7 :nf))` is `1`. -/
theorem im2_example :
    (match (({ body := .array [(.int 7, .int 1)] } : TMap).persistentBang) with
     | .ok (_, t) => match t.read (.get2 (.int 7) (.kw "nf")) with
       | .ok (.val (.int 1)) => true | _ => false
     | _ => false) = true := by decide

end Jank.R3.Immer.Findings

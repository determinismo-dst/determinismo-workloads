import Jank.R3.Immer.Rbts

/-!
# Vector laws over the rbts replica, for every input

Clojure's PersistentVector laws, proved of the immer replica (`Rbts`) that jank's vectors are:

- `iter_eq_get`: iteration (`rbtree_iterator`) reads element `i` exactly as `nth`/`operator[]`.
- `pushBack_size`, `pushBackMut_size`: `conj` adds one (persistent and transient).
- `take_size`, `takeMut_size`: `take n` (`pop` is `take (count - 1)`) has `n` elements.
- `assoc_size`, `assocMut_size`: `assoc` keeps the count.
-/

namespace Jank.R3.Immer.Rbts

variable {α : Type}

/-- Iteration reads element `i` as `get` does (both are `array_for(i)[i & mask<BL>]`). -/
theorem iter_eq_get (t : Tree α) : t.iter = (List.range t.size).map t.get := rfl

theorem iter_length (t : Tree α) : t.iter.length = t.size := by simp [Tree.iter]

theorem pushBack_size [Inhabited α] (t : Tree α) (x : α) (n : Nat) :
    (t.pushBack x n).1.size = t.size + 1 := by
  unfold Tree.pushBack; dsimp only
  repeat' split
  all_goals rfl

theorem pushBackMut_size [Inhabited α] (t : Tree α) (e : Nat) (x : α) (n : Nat) :
    (t.pushBackMut e x n).1.size = t.size + 1 := by
  unfold Tree.pushBackMut Tree.ensureMutableTail; dsimp only
  repeat' split
  all_goals rfl

theorem assoc_size [Inhabited α] (t : Tree α) (i : Nat) (x : α) (n : Nat) :
    (t.assoc i x n).1.size = t.size := by
  unfold Tree.assoc; dsimp only
  repeat' split
  all_goals rfl

theorem assocMut_size [Inhabited α] (t : Tree α) (e i : Nat) (x : α) (n : Nat) :
    (t.assocMut e i x n).1.size = t.size := by
  unfold Tree.assocMut Tree.ensureMutableTail; dsimp only
  repeat' split
  all_goals rfl

theorem take_size [Inhabited α] (t : Tree α) (k n : Nat) (h : k ≤ t.size) :
    (t.take k n).1.size = k := by
  unfold Tree.take; dsimp only
  repeat' split
  all_goals first | rfl | (dsimp only; omega) | (simp_all [Tree.empty]; omega) | simp_all [Tree.empty]

theorem takeMut_size [Inhabited α] (t : Tree α) (e k n : Nat) (h : k ≤ t.size) :
    (t.takeMut e k n).1.size = k := by
  unfold Tree.takeMut; dsimp only
  repeat' split
  all_goals first | rfl | (dsimp only; omega) | (simp_all [Tree.empty]; omega) | simp_all [Tree.empty]

/-- `pop` (`take (count - 1)`) has one element fewer. -/
theorem pop_size [Inhabited α] (t : Tree α) (n : Nat) (h : 0 < t.size) :
    (t.take (t.size - 1) n).1.size = t.size - 1 := take_size t _ n (by omega)

/-- `conj` then `pop` gives back the count. -/
theorem pop_conj_size [Inhabited α] (t : Tree α) (x : α) (n m : Nat) :
    ((t.pushBack x n).1.take t.size m).1.size = t.size :=
  take_size _ _ _ (by rw [pushBack_size]; omega)

end Jank.R3.Immer.Rbts

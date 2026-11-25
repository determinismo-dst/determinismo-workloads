import Jank.R3.Immer.Champ

/-!
# CHAMP facts, for every input

- `mkInner_values`: `make_inner_n(n, nv)` holds exactly the values it is given.
- `doAdd_replaces` (IM1 at the node): when `champ::do_add` reaches a data slot whose stored value
  `Equal` accepts, the new node holds the *new* value in that slot (`copy_inner_replace_value`),
  and nothing is added. For a map the stored value is the pair, so the new key replaces the
  stored key.
-/

namespace Jank.R3.Immer.Champ

variable {α κ : Type}

theorem mkInner_values (nm dm : Nat) (x : α) (xs : List α) (cs : List (Node α)) (s : Al) :
    ((mkInner nm dm (x :: xs) cs).run s).1.values = x :: xs := rfl

theorem doAdd_replaces [Inhabited α] (cfg : Cfg α κ) (r : Nat) (node : Node α) (v : α) (hash : Nat) (s : Al)
    (hn : (node.nodemap &&& bitAt hash (maxShift - 5 * (r + 1)) != 0) = false)
    (hd : (node.datamap &&& bitAt hash (maxShift - 5 * (r + 1)) != 0) = true)
    (he : cfg.eqTT (node.values.getD (node.dataCountBit (bitAt hash (maxShift - 5 * (r + 1)))) default) v = true)
    (hl : node.dataCountBit (bitAt hash (maxShift - 5 * (r + 1))) < (node.values.take node.dataCount).length) :
    ((doAdd cfg (r + 1) node v hash).run s).1.2 = false ∧
    ((doAdd cfg (r + 1) node v hash).run s).1.1.values[node.dataCountBit (bitAt hash (maxShift - 5 * (r + 1)))]? =
      some v := by
  simp only [doAdd, hn, hd, he, Bool.false_eq_true, ↓reduceIte]
  generalize hxs : node.values.take node.dataCount = xs at hl
  generalize node.dataCountBit (bitAt hash (maxShift - 5 * (r + 1))) = o at hl ⊢
  cases xs with
  | nil => simp at hl
  | cons y ys =>
    simp only [copyInnerReplaceValue, hxs, setL]
    cases o with
    | zero => exact ⟨rfl, rfl⟩
    | succ o =>
      refine ⟨rfl, ?_⟩
      show ((mkInner _ _ (y :: ys.set o v) _).run _).1.values[o + 1]? = some v
      rw [mkInner_values]
      simp only [List.getElem?_cons_succ]
      exact List.getElem?_set_self (by simp at hl; omega)

end Jank.R3.Immer.Champ

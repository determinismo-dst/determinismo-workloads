import Jank.R7.Champ.LawOne
import Jank.R7.Champ.Trans

/-!
# Round 8, CHAMP: law 1 (`get` of another key) for the transient steps, without the invariant

Round 7 proved law 1 at the walk level for the persistent steps (`Jank.R7.Champ.add_walk`,
`sub_walk`) and for the transient steps only under round 6's `Inv` (`get_addMut_other`,
`get_subMut_other`). Here the transient steps of round 3's replica of immer's `champ.hpp`
(`doAddMut` = `do_add_mut` 645-738, `doSubMut` = `do_sub_mut` 1346-1483) get the same treatment,
branch by branch: the in-place child write, the in-place value write after
`ensure_mutable_values`, the in-place collision write (which keeps the collision node's order),
the moves (`move_*`: a copy then `delete_*`), the copies under a node the transient does not own
(which run the persistent `do_add`/`do_sub` below it), and `owned`/`owned_values`.

- ★ `addMut_walk`, ★ `get_addMut_other_wf`: **law 1 for `add_mut` (`assoc!`/`conj!`) holds for every
  well-formed champ**, no hash-path invariant, no uniqueness, any owner token.
- ★ `subMut_walk`, ★ `get_subMut_other_hp`: **law 1 for `sub_mut` (`dissoc!`/`disj!`) holds for every
  well-formed champ meeting `HP`**.
- `law1_subMut_fails_without_HP` (`decide +kernel`): `HP` cannot be dropped for `sub_mut`, on the
  copying path (round 7's `badChamp`, nodes not owned by the transient) and on the mutating path
  (`badChampOwned`: the same champ with every node and values buffer owned by the transient).
- ★ `step_wf_HP`, ★ `buildT_wf_HP`, ★ `reach_wf_HP`: every sequence of `add`, `sub`, `add_mut`,
  `sub_mut` from `champ::empty()` keeps `wfNode` and `HP` **for every hash function and every
  equality** (nothing assumed of either); so the counterexample is outside what jank builds.
- ★ `get_add_pair`, ★ `get_addMut_pair`, ★ `get_sub_pair`, ★ `get_subMut_pair`: law 1 for ONE pair of
  keys under jank's real (non-lawful) equality, for every champ jank builds, from three facts
  about that pair only; ★ `law1_reach`: the lawful corollary, for every step of every sequence.
-/

namespace Jank.R8.Champ

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ

variable {α κ : Type} [Inhabited α]

/-! ## Owners do not change the walk -/

theorem collisions_owned (n : Node α) (e : Nat) : (owned n e).collisions = n.collisions := by
  cases n with
  | inner id t nm dm v cs => rfl
  | collision => rfl

theorem collisions_ownedValues (n : Node α) (e : Nat) : (ownedValues n e).collisions = n.collisions := by
  cases n with
  | inner id t nm dm v cs => cases v <;> rfl
  | collision => rfl

theorem walk_owned (n : Node α) (e : Nat) : ∀ r H, walk r (owned n e) H = walk r n H
  | 0, H => by rw [walk.eq_1, walk.eq_1, collisions_owned]
  | r + 1, H => by rw [walk.eq_2, walk.eq_2, slot_owned]

theorem walk_ownedValues (n : Node α) (e : Nat) : ∀ r H, walk r (ownedValues n e) H = walk r n H
  | 0, H => by rw [walk.eq_1, walk.eq_1, collisions_ownedValues]
  | r + 1, H => by rw [walk.eq_2, walk.eq_2, slot_ownedValues]

/-! ## Lists -/

/-- The in-place collision write (`*fst = std::move(v)`): `find?` unchanged when neither the old nor
the new value is accepted. -/
theorem find?_set_false {β : Type} (p : β → Bool) (a : β) (hpa : p a = false) :
    ∀ (l : List β) (i : Nat), (∀ (hi : i < l.length), p l[i] = false) → (l.set i a).find? p = l.find? p
  | [], i, _ => by simp
  | b :: l, 0, h => by
    have hb : p b = false := by have := h (by simp); simpa using this
    simp only [List.set_cons_zero, List.find?_cons, hpa, hb]
  | b :: l, i + 1, h => by
    have ih := find?_set_false p a hpa l i (fun hi => by have := h (by simp; omega); simpa using this)
    simp only [List.set_cons_succ, List.find?_cons]
    rw [ih]

/-! ## `ensure_mutable_values` and the value write -/

/-- `ensure_mutable_values(e)` then `vals[offset] = std::move(v)` edits one data slot. -/
theorem edit_ensureWrite (r : Nat) (N : Node α) (v : α) (D e : Nat) (s : Al) (hw : wfNode (r + 1) N = true)
    (hD : D < 32) (hA0 : N.nodemap.testBit D = false) (hB : N.datamap.testBit D = true) :
    Edit r N (writeValue ((ensureMutableValues N e).run s).1 (pos N.datamap D) v) D (.data v) := by
  obtain ⟨h1, h2, h3, h4, h5, h5', h6, hN⟩ := wf_parts r N hw
  cases N with
  | collision => simp [wfNode] at hw
  | inner nid tok nm dm vals cs =>
    cases vals with
    | none =>
      have : dm = 0 := h5'
      subst this
      exact absurd hB (by simp [Node.datamap, Nat.zero_testBit])
    | some vs =>
      by_cases hvt : (vs.tok == e) = true
      · have em : ((ensureMutableValues (Node.inner nid tok nm dm (some vs) cs) e).run s).1 =
            Node.inner nid tok nm dm (some vs) cs := by
          unfold ensureMutableValues
          rw [if_pos (show (Node.inner nid tok nm dm (some vs) cs).canMutateValues e = true from hvt)]
          rfl
        rw [em]
        exact edit_writeValue r _ v D hw hD hA0 hB vs.id vs.tok vs.xs h5 (fun _ _ => rfl)
      · have em : ((ensureMutableValues (Node.inner nid tok nm dm (some vs) cs) e).run s).1 =
            Node.inner nid tok nm dm (some ⟨s.next, e, (Node.inner nid tok nm dm (some vs) cs).values.take (popcount dm)⟩) cs := by
          unfold ensureMutableValues
          rw [if_neg (show ¬ (Node.inner nid tok nm dm (some vs) cs).canMutateValues e = true from hvt)]
          rfl
        rw [em]
        exact edit_writeValue r _ v D hw hD hA0 hB s.next e _
          (by rw [List.length_take]; exact Nat.le_min.mpr ⟨Nat.le_refl _, h5⟩)
          (fun j hj => getD_take _ _ _ _ hj)

/-! ## Law 1 for `add_mut`, for every well-formed champ -/

/-- The merged branch's walk (`make_merged` / `make_merged_e` below a data slot), shared by `do_add`
and `do_add_mut`. -/
theorem merged_walk (cfg : Cfg α κ) (own : Option Nat) (v : α) (h : Nat) (hv : cfg.hashT v = h) (p : α → Bool)
    (H : Nat) (hpv : p v = false) (hph : ∀ x, p x = true → cfg.hashT x = H) (r : Nat) (hr : r + 1 ≤ 13)
    (val : α) (s : Al) :
    (walk r ((makeMerged own r v h val (cfg.hashT val)).run s).1 (H >>> (65 - 5 * r))).find? p = [val].find? p := by
  generalize hq : (makeMerged own r v h val (cfg.hashT val)).run s = q
  obtain ⟨m, s1⟩ := q
  dsimp only
  have hmw : wfNode r m = true := by
    have := wf_makeMerged own v val h (cfg.hashT val) r s; rw [hq] at this; exact this
  have hmi : (iterNode r m).Perm [v, val] := by
    have := iter_makeMerged own v val h (cfg.hashT val) r s; rw [hq] at this; exact this
  have hmh : HP cfg r m := by
    have := HP_makeMerged cfg own v val h (cfg.hashT val) hv rfl r s; rw [hq] at this; exact this
  have hsub : ∀ x ∈ walk r m (H >>> (65 - 5 * r)), x = v ∨ x = val := by
    intro x hx
    have := hmi.subset (walk_sub r m _ hmw x hx)
    simpa using this
  cases hpval : p val
  · rw [find?_cons_false p val [] hpval, List.find?_nil, List.find?_eq_none]
    intro x hx
    rcases hsub x hx with h1 | h1 <;> rw [h1] <;> simp [hpv, hpval]
  · rw [show [val].find? p = some val by simp [List.find?_cons, hpval]]
    apply find?_unique p _ val
    · have hc := walk_complete cfg r (by omega) m hmw hmh val (hmi.symm.subset (by simp))
      rw [hph val hpval] at hc; exact hc
    · exact hpval
    · intro x hx hpx
      rcases hsub x hx with h1 | h1
      · rw [h1, hpv] at hpx; cases hpx
      · exact h1

/-- ★ `do_add_mut` of `v` (owner token `e`) leaves `get` of a query (predicate `p`, hash `H`) unchanged,
at every level, for every well-formed node: no hash-path invariant, no uniqueness. It uses of the
equality only: `v` is not accepted, a value `Equal` to `v` is not accepted, an accepted value hashes as
the query. -/
theorem addMut_walk (cfg : Cfg α κ) (e : Nat) (v : α) (h : Nat) (hv : cfg.hashT v = h) (p : α → Bool) (H : Nat)
    (hpv : p v = false) (hpe : ∀ x, cfg.eqTT x v = true → p x = false)
    (hph : ∀ x, p x = true → cfg.hashT x = H) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      (walk r ((doAddMut cfg e r N v h).run s).1.1 (H >>> (65 - 5 * r))).find? p =
        (walk r N (H >>> (65 - 5 * r))).find? p := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw
    cases N with
    | inner => simp [wfNode] at hw
    | collision nid tok xs =>
      rw [doAddMut.eq_1]
      unfold findIdx?
      simp only [Node.collisions]
      cases hf : xs.findIdx? (fun x => cfg.eqTT x v) with
      | none =>
        dsimp only
        split
        · show (v :: xs).find? p = xs.find? p
          exact find?_cons_false p v xs hpv
        · show (v :: xs).find? p = xs.find? p
          exact find?_cons_false p v xs hpv
      | some pos =>
        obtain ⟨hpos, hpx, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        dsimp only
        split
        · -- `*fst = std::move(v)`: the collision node written in place, its order kept
          show (setL xs pos v).find? p = xs.find? p
          exact find?_set_false p v hpv xs pos (fun _ => hpe _ hpx)
        · show (v :: eraseAt xs pos).find? p = xs.find? p
          rw [find?_cons_false p v _ hpv]
          exact find?_eraseAt_false p xs pos (fun _ => hpe _ hpx)
  | succ r ih =>
    intro hr N s hw
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      by_cases hm : N.canMutate e = true
      · -- `node->children()[offset] = result.node` in place
        have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (.inner N.id N.tok N.nodemap N.datamap N.vals (setL N.cs (pos N.nodemap D)
              ((doAddMut cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.1),
             ((doAddMut cfg e r (N.cs.getD (pos N.nodemap D) Node.dummy) v h).run s).1.2.1, true) := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_pos hA', if_pos hm]
          cases N with
          | inner => rfl
          | collision => simp [wfNode] at hw
        rw [e1]
        dsimp only
        have o := addMut_step cfg e v h hv r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        have ihc := ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        apply find_edit p r hr N _ D _ (edit_setChild r N _ D hw hD hA o.wf) H
        intro _
        rw [hs]; exact ihc
      · -- not owned: `do_add` below, `copy_inner_replace`, `owned`
        have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (owned ((doAdd cfg (r + 1) N v h).run s).1.1 e, ((doAdd cfg (r + 1) N v h).run s).1.2, false) := by
          rw [doAddMut.eq_2, doAdd.eq_2]; dsimp only; rw [hbit, if_pos hA', if_neg hm, if_pos hA']; rfl
        rw [e1]
        dsimp only
        rw [walk_owned]
        exact add_walk cfg v h hv p H hpv hpe hph (r + 1) hr N s hw
    · have hA0 : N.nodemap.testBit D = false := by simpa using hA
      have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have hs : slot N D = .data (N.values.getD (pos N.datamap D) default) := by
          unfold slot; rw [if_neg hA, if_pos hB]
        by_cases hE : cfg.eqTT (N.values.getD (pos N.datamap D) default) v = true
        · by_cases hm : N.canMutate e = true
          · -- `ensure_mutable_values(e)`, `vals[offset] = std::move(v)`
            have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
                (writeValue ((ensureMutableValues N e).run s).1 (pos N.datamap D) v, false, true) := by
              rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_pos hm]
              rfl
            rw [e1]
            dsimp only
            apply find_edit p r hr N _ D _ (edit_ensureWrite r N v D e s hw hD hA0 hB) H
            intro _
            rw [hs]
            show [v].find? p = [N.values.getD (pos N.datamap D) default].find? p
            rw [find?_cons_false p v [] hpv, find?_cons_false p _ [] (hpe _ hE)]
          · have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
                (ownedValues ((doAdd cfg (r + 1) N v h).run s).1.1 e, ((doAdd cfg (r + 1) N v h).run s).1.2, false) := by
              rw [doAddMut.eq_2, doAdd.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB', if_neg hA', if_pos hB']
              rw [if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE), if_neg hm,
                if_pos (show cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true from hE)]
              rfl
            rw [e1]
            dsimp only
            rw [walk_ownedValues]
            exact add_walk cfg v h hv p H hpv hpe hph (r + 1) hr N s hw
        · -- `make_merged_e` below, moved or copied, `owned_values_safe`
          generalize hval : N.values.getD (pos N.datamap D) default = val at hs hE
          have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
              (ownedValues ((copyInnerReplaceMerged N (2 ^ D) (pos N.datamap D)
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).1).run
                ((makeMerged (some e) r v h val (cfg.hashT val)).run s).2).1 e, true, N.canMutate e) := by
            rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_pos hB']
            rw [if_neg (show ¬ cfg.eqTT (N.values.getD (N.dataCountBit (2 ^ D)) default) v = true by
              rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]; exact hE)]
            rw [show N.dataCountBit (2 ^ D) = pos N.datamap D from rfl, hval]
            split <;> rfl
          rw [e1]
          dsimp only
          rw [walk_ownedValues]
          generalize hq : (makeMerged (some e) r v h val (cfg.hashT val)).run s = q
          obtain ⟨m, s1⟩ := q
          dsimp only
          have hmw : wfNode r m = true := by
            have := wf_makeMerged (some e) v val h (cfg.hashT val) r s; rw [hq] at this; exact this
          have hE' := edit_replaceMerged r N m D s1 hw hD hA0 hB hmw
          apply find_edit p r hr N _ D _ hE' H
          intro _
          rw [hs]
          show (walk r m (H >>> (65 - 5 * r))).find? p = [val].find? p
          have := merged_walk cfg (some e) v h hv p H hpv hph r hr val s
          rw [hq] at this
          exact this
      · -- an empty slot: `move_inner_insert_value` or `copy_inner_insert_value`, `owned_values`
        have hB0 : N.datamap.testBit D = false := by simpa using hB
        have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        have hs : slot N D = .empty := by unfold slot; rw [if_neg hA, if_neg hB]
        have e1 : ((doAddMut cfg e (r + 1) N v h).run s).1 =
            (ownedValues ((copyInnerInsertValue N (2 ^ D) v).run s).1 e, true, N.canMutate e) := by
          rw [doAddMut.eq_2]; dsimp only; rw [hbit, if_neg hA', if_neg hB']
          split <;> rfl
        rw [e1]
        dsimp only
        rw [walk_ownedValues]
        apply find_edit p r hr N _ D _ (edit_insertValue r N v D s hw hD hA0 hB0) H
        intro _
        rw [hs]
        show [v].find? p = ([] : List α).find? p
        rw [find?_cons_false p v [] hpv]

/-- ★ **Law 1 for `add_mut` (`assoc!`/`conj!`) for ONE pair, any equality**: for every well-formed champ
and every owner token, `get k'` is unchanged by `add_mut v` when `v` is not `Equal` to `k'`, no stored
value `Equal` to `v` is `Equal` to `k'`, and every value `Equal` to `k'` hashes as `k'`. -/
theorem get_addMut_pair (cfg : Cfg α κ) (c : Champ α) (e : Nat) (v : α) (k' : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hpv : cfg.eqTK v k' = false)
    (hpe : ∀ x, cfg.eqTT x v = true → cfg.eqTK x k' = false)
    (hph : ∀ x, cfg.eqTK x k' = true → cfg.hashT x = cfg.hashK k') :
    Champ.get cfg ((c.addMut cfg e v).run s).1 k' = Champ.get cfg c k' := by
  have o := addMut_step cfg e v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw
  have := addMut_walk cfg e v (cfg.hashT v) rfl (fun x => cfg.eqTK x k') (cfg.hashK k') hpv hpe hph 13
    (Nat.le_refl _) c.root s hw
  rw [shr13] at this
  unfold Champ.get
  show getLoop cfg k' 13 ((doAddMut cfg e 13 c.root v (cfg.hashT v)).run s).1.1 (cfg.hashK k') = _
  rw [getLoop_walk cfg k' 13 _ _ o.wf, getLoop_walk cfg k' 13 _ _ hw]
  exact this

/-- ★ The same for the persistent `add` (round 7's `add_walk`, stated per pair). -/
theorem get_add_pair (cfg : Cfg α κ) (c : Champ α) (v : α) (k' : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hpv : cfg.eqTK v k' = false)
    (hpe : ∀ x, cfg.eqTT x v = true → cfg.eqTK x k' = false)
    (hph : ∀ x, cfg.eqTK x k' = true → cfg.hashT x = cfg.hashK k') :
    Champ.get cfg ((c.add cfg v).run s).1 k' = Champ.get cfg c k' := by
  have o := add_step cfg v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw
  have := add_walk cfg v (cfg.hashT v) rfl (fun x => cfg.eqTK x k') (cfg.hashK k') hpv hpe hph 13
    (Nat.le_refl _) c.root s hw
  rw [shr13] at this
  unfold Champ.get
  show getLoop cfg k' 13 ((doAdd cfg 13 c.root v (cfg.hashT v)).run s).1.1 (cfg.hashK k') = _
  rw [getLoop_walk cfg k' 13 _ _ o.wf, getLoop_walk cfg k' 13 _ _ hw]
  exact this

/-- The three facts from a lawful equality. -/
theorem lawful_add_facts {cfg : Cfg α κ} (L : Lawful cfg) (v : α) (k' : κ) (hne : L.eqK (L.key v) k' = false) :
    cfg.eqTK v k' = false ∧ (∀ x, cfg.eqTT x v = true → cfg.eqTK x k' = false) ∧
      (∀ x, cfg.eqTK x k' = true → cfg.hashT x = cfg.hashK k') := by
  refine ⟨by rw [L.eqTK_key]; exact hne, ?_, fun x hx => (L.hash_of_eqTK x k' hx).symm⟩
  intro x hx
  cases hk : cfg.eqTK x k'
  · rfl
  · rw [L.eqTT_key] at hx; rw [L.eqTK_key] at hk
    rw [L.trans _ _ _ (L.symm _ _ hx) hk] at hne; cases hne

/-- ★ **Law 1 for `add_mut` (`assoc!`/`conj!`), for every well-formed champ**: under a lawful equality,
`get` of a key not `Equal` to the value added is unchanged, whatever the owner token. Round 7's
`get_addMut_other` assumed `Inv`. -/
theorem get_addMut_other_wf {cfg : Cfg α κ} (L : Lawful cfg) (c : Champ α) (e : Nat) (v : α) (k' : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hne : L.eqK (L.key v) k' = false) :
    Champ.get cfg ((c.addMut cfg e v).run s).1 k' = Champ.get cfg c k' := by
  obtain ⟨h1, h2, h3⟩ := lawful_add_facts L v k' hne
  exact get_addMut_pair cfg c e v k' s hw h1 h2 h3

/-! ## Law 1 for `sub_mut`, for every well-formed champ meeting `HP` -/

theorem subWalk_ownedValues {r : Nat} {N : Node α} {p : α → Bool} {H : Nat} {t : Node α}
    (h : SubWalk r N p H (.tree t)) (e : Nat) : SubWalk r N p H (.tree (ownedValues t e)) := by
  show (walk r (ownedValues t e) _).find? p = _
  rw [walk_ownedValues]; exact h

theorem subWalk_owned {r : Nat} {N : Node α} {p : α → Bool} {H : Nat} {t : Node α}
    (h : SubWalk r N p H (.tree t)) (e : Nat) : SubWalk r N p H (.tree (owned t e)) := by
  show (walk r (owned t e) _).find? p = _
  rw [walk_owned]; exact h

/-- A value passed up from a child and inlined (`copy_inner_replace_inline`, or the move): the walk
of a query not accepting the removed value is unchanged (the inlined value is on its own hash's
walk by `HP` of the child). -/
theorem inline_walk (cfg : Cfg α κ) (k : κ) (p : α → Bool) (H : Nat)
    (hpk : ∀ y, cfg.eqTK y k = true → p y = false) (hph : ∀ x, p x = true → cfg.hashT x = H)
    (r : Nat) (hr : r + 1 ≤ 13) (N : Node α) (hw : wfNode (r + 1) N = true) (D : Nat) (hD : D < 32)
    (hA : N.nodemap.testBit D = true) (hcw : wfNode r (N.cs.getD (pos N.nodemap D) Node.dummy) = true)
    (hk2 : HP cfg r (N.cs.getD (pos N.nodemap D) Node.dummy)) (x : α)
    (o : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy) (.singleton x)) (s1 : Al) :
    SubWalk (r + 1) N p H (.tree ((copyInnerReplaceInline N (2 ^ D) (pos N.nodemap D) x).run s1).1) := by
  have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
  obtain ⟨y, hy, hp⟩ := o
  have hE := edit_replaceInline r N x D s1 hw hD hA
  apply find_edit p r hr N _ D _ hE H
  intro _
  rw [hs]
  show [x].find? p = (walk r (N.cs.getD (pos N.nodemap D) Node.dummy) (H >>> (65 - 5 * r))).find? p
  generalize N.cs.getD (pos N.nodemap D) Node.dummy = c at hp hcw hk2
  have hsub : ∀ z ∈ walk r c (H >>> (65 - 5 * r)), z = y ∨ z = x := by
    intro z hz; have := hp.subset (walk_sub r c _ hcw z hz); simpa using this
  have hpy := hpk y hy
  cases hpx : p x
  · rw [find?_cons_false p x [] hpx, List.find?_nil]
    symm
    rw [List.find?_eq_none]
    intro z hz
    rcases hsub z hz with h1 | h1 <;> rw [h1] <;> simp [hpy, hpx]
  · rw [show [x].find? p = some x by simp [List.find?_cons, hpx]]
    symm
    apply find?_unique p _ x
    · have hcm := walk_complete cfg r (by omega) c hcw hk2 x (hp.symm.subset (by simp))
      rw [hph x hpx] at hcm; exact hcm
    · exact hpx
    · intro z hz hpz
      rcases hsub z hz with h1 | h1
      · rw [h1, hpy] at hpz; cases hpz
      · exact h1

/-- ★ `do_sub_mut` of `k` (owner token `e`) leaves `get` of a query not accepting `k`'s values
unchanged, at every level, for every well-formed node meeting `HP` (no uniqueness), on the mutating
and the copying branches alike. -/
theorem subMut_walk (cfg : Cfg α κ) (e : Nat) (k : κ) (h : Nat) (p : α → Bool) (H : Nat)
    (hpk : ∀ y, cfg.eqTK y k = true → p y = false)
    (hph : ∀ x, p x = true → cfg.hashT x = H) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true → HP cfg r N →
      SubWalk r N p H ((doSubMut cfg e k r N h).run s).1.r := by
  intro r
  induction r with
  | zero =>
    intro _ N s _ _
    rw [doSubMut.eq_1]
    unfold findIdx?
    cases hf : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => trivial
    | some cur =>
      obtain ⟨hcur, hpc, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      dsimp only
      split
      · split <;> trivial
      · split
        · show (eraseAt N.collisions cur).find? p = N.collisions.find? p
          exact find?_eraseAt_false p _ cur (fun _ => hpk _ hpc)
        · show (eraseAt N.collisions cur).find? p = N.collisions.find? p
          exact find?_eraseAt_false p _ cur (fun _ => hpk _ hpc)
  | succ r ih =>
    intro hr N s hw hpN
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 2 ^ D := by rw [bitAt_eq, hDdef]
    have iwP := sub_walk cfg k h p H hpk hph (r + 1) hr N s hw hpN
    rw [doSub.eq_2] at iwP
    dsimp only at iwP
    rw [hbit] at iwP
    rw [doSubMut.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : N.nodemap.testBit D = true
    · have hA' : (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_pos hA']
      have hs : slot N D = .child (N.cs.getD (pos N.nodemap D) Node.dummy) := by unfold slot; rw [if_pos hA]
      have hcw := slot_child_wf r N hw D hD _ hs
      have hok := hpN D hD
      rw [hs] at hok
      obtain ⟨_, hk2⟩ := hok
      by_cases hm : N.canMutate e = true
      · rw [if_pos hm]
        simp only [hm, ↓reduceIte]
        have o : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
            ((doSubMut cfg e k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1.r :=
          subMut_step cfg e k h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        have iw : SubWalk r (N.cs.getD (pos N.nodemap D) Node.dummy) p H
            ((doSubMut cfg e k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1.r :=
          ih (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw hk2
        simp only [StateT.run_bind]
        generalize (doSubMut cfg e k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q at o iw
        obtain ⟨⟨res, ow, mu⟩, s1⟩ := q
        dsimp only at o iw ⊢
        cases res with
        | nothing => trivial
        | singleton x =>
          try dsimp only
          split
          · trivial
          · exact subWalk_ownedValues (inline_walk cfg k p H hpk hph r hr N hw D hD hA hcw hk2 x o s1) e
        | tree t =>
          try dsimp only
          try rw [if_pos hm]
          cases N with
          | collision => simp [wfNode] at hw
          | inner nid tok nm dm vs cs =>
            -- `node->children()[offset] = result.data.tree` in place
            apply find_edit p r hr _ _ D _ (edit_setChild r _ t D hw hD hA o.1) H
            intro _
            rw [hs]
            exact iw
      · rw [if_neg hm]
        simp only [hm, ↓reduceIte, Bool.false_eq_true]
        have o : SubOut cfg k r (N.cs.getD (pos N.nodemap D) Node.dummy)
            ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
          sub_step cfg k h r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw
        have iw : SubWalk r (N.cs.getD (pos N.nodemap D) Node.dummy) p H
            ((doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s).1 :=
          sub_walk cfg k h p H hpk hph r (by omega) (N.cs.getD (pos N.nodemap D) Node.dummy) s hcw hk2
        simp only [StateT.run_bind]
        generalize (doSub cfg k r (N.child (N.childrenCountBit (2 ^ D))) h).run s = q at o iw
        obtain ⟨res, s1⟩ := q
        dsimp only at o iw ⊢
        cases res with
        | nothing => trivial
        | singleton x =>
          try dsimp only
          split
          · trivial
          · exact subWalk_ownedValues (inline_walk cfg k p H hpk hph r hr N hw D hD hA hcw hk2 x o s1) e
        | tree t =>
          try dsimp only
          try rw [if_neg hm]
          apply subWalk_owned
          obtain ⟨htw, _, _⟩ := o
          apply find_edit p r hr N _ D _ (edit_replace r N t D s1 hw hD hA htw) H
          intro _
          rw [hs]
          exact iw
    · have hA' : ¬ (N.nodemap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hA
      rw [if_neg hA'] at iwP ⊢
      by_cases hB : N.datamap.testBit D = true
      · have hB' : (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_pos hB'] at iwP ⊢
        by_cases hE : cfg.eqTK (N.values.getD (pos N.datamap D) default) k = true
        · rw [if_pos (show cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)] at iwP ⊢
          by_cases c1 : (N.nodemap != 0 || decide (N.dataCount > 2)) = true
          · rw [if_pos c1] at iwP ⊢
            split <;> exact subWalk_ownedValues iwP e
          · rw [if_neg c1] at iwP ⊢
            by_cases c2 : (N.dataCount == 2) = true
            · rw [if_pos c2] at iwP ⊢
              split
              · next hsh =>
                split <;> trivial
              · next hsh =>
                rw [if_neg hsh] at iwP
                by_cases hm : N.canMutate e = true
                · simp only [hm, ↓reduceIte]; exact subWalk_ownedValues iwP e
                · simp only [hm, ↓reduceIte, Bool.false_eq_true]; exact subWalk_ownedValues iwP e
            · rw [if_neg c2] at iwP ⊢
              split <;> exact iwP
        · rw [if_neg (show ¬ cfg.eqTK (N.values.getD (N.dataCountBit (2 ^ D)) default) k = true from hE)]
          trivial
      · have hB' : ¬ (N.datamap &&& 2 ^ D != 0) = true := by rw [and_pow_bne]; exact hB
        rw [if_neg hB']
        trivial

/-- ★ **Law 1 for `sub_mut` (`dissoc!`/`disj!`) for ONE pair, any equality**: for every well-formed champ
meeting `HP` and every owner token, `get k'` is unchanged by `sub_mut k` when no value `Equal` to `k`
is `Equal` to `k'` and every value `Equal` to `k'` hashes as `k'`. -/
theorem get_subMut_pair (cfg : Cfg α κ) (c : Champ α) (e : Nat) (k k' : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hp : HP cfg 13 c.root)
    (hpk : ∀ y, cfg.eqTK y k = true → cfg.eqTK y k' = false)
    (hph : ∀ x, cfg.eqTK x k' = true → cfg.hashT x = cfg.hashK k') :
    Champ.get cfg ((c.subMut cfg e k).run s).1 k' = Champ.get cfg c k' := by
  have iw := subMut_walk cfg e k (cfg.hashK k) (fun x => cfg.eqTK x k') (cfg.hashK k') hpk hph 13
    (Nat.le_refl _) c.root s hw hp
  have o := subMut_step cfg e k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
  unfold Champ.subMut
  simp only [StateT.run_bind]
  generalize (doSubMut cfg e k 13 c.root (cfg.hashK k)).run s = q at iw o
  obtain ⟨res, s1⟩ := q
  obtain ⟨rr, ow, mu⟩ := res
  cases rr with
  | nothing => rfl
  | singleton x => rfl
  | tree t =>
    obtain ⟨htw, _, _⟩ := o
    show Champ.get cfg { root := t, size := c.size - 1 } k' = Champ.get cfg c k'
    unfold Champ.get
    rw [getLoop_walk cfg k' 13 t _ htw, getLoop_walk cfg k' 13 c.root _ hw]
    have h' : (walk 13 t (cfg.hashK k' >>> (65 - 5 * 13))).find? (fun x => cfg.eqTK x k') =
        (walk 13 c.root (cfg.hashK k' >>> (65 - 5 * 13))).find? (fun x => cfg.eqTK x k') := iw
    rw [shr13] at h'
    exact h'

/-- ★ The same for the persistent `sub` (round 7's `sub_walk`, stated per pair). -/
theorem get_sub_pair (cfg : Cfg α κ) (c : Champ α) (k k' : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hp : HP cfg 13 c.root)
    (hpk : ∀ y, cfg.eqTK y k = true → cfg.eqTK y k' = false)
    (hph : ∀ x, cfg.eqTK x k' = true → cfg.hashT x = cfg.hashK k') :
    Champ.get cfg ((c.sub cfg k).run s).1 k' = Champ.get cfg c k' := by
  have iw := sub_walk cfg k (cfg.hashK k) (fun x => cfg.eqTK x k') (cfg.hashK k') hpk hph 13
    (Nat.le_refl _) c.root s hw hp
  have o := sub_step cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
  unfold Champ.sub
  simp only [StateT.run_bind]
  generalize (doSub cfg k 13 c.root (cfg.hashK k)).run s = q at iw o
  obtain ⟨sub, s1⟩ := q
  cases sub with
  | nothing => rfl
  | singleton x => rfl
  | tree t =>
    obtain ⟨htw, _, _⟩ := o
    show Champ.get cfg { root := t, size := c.size - 1 } k' = Champ.get cfg c k'
    unfold Champ.get
    rw [getLoop_walk cfg k' 13 t _ htw, getLoop_walk cfg k' 13 c.root _ hw]
    have h' : (walk 13 t (cfg.hashK k' >>> (65 - 5 * 13))).find? (fun x => cfg.eqTK x k') =
        (walk 13 c.root (cfg.hashK k' >>> (65 - 5 * 13))).find? (fun x => cfg.eqTK x k') := iw
    rw [shr13] at h'
    exact h'

theorem lawful_sub_facts {cfg : Cfg α κ} (L : Lawful cfg) (k k' : κ) (hne : L.eqK k k' = false) :
    (∀ y, cfg.eqTK y k = true → cfg.eqTK y k' = false) ∧
      (∀ x, cfg.eqTK x k' = true → cfg.hashT x = cfg.hashK k') := by
  refine ⟨?_, fun x hx => (L.hash_of_eqTK x k' hx).symm⟩
  intro y hy
  cases hk : cfg.eqTK y k'
  · rfl
  · rw [L.eqTK_key] at hy hk
    rw [L.trans _ _ _ (L.symm _ _ hy) hk] at hne; cases hne

/-- ★ **Law 1 for `sub_mut` (`dissoc!`/`disj!`), for every well-formed champ meeting `HP`**: under a
lawful equality, `get` of a key not `Equal` to the one removed is unchanged, whatever the owner token.
Round 7's `get_subMut_other` assumed `Inv`; uniqueness and the size premise are dropped, `HP` cannot
be (`law1_subMut_fails_without_HP`). -/
theorem get_subMut_other_hp {cfg : Cfg α κ} (L : Lawful cfg) (c : Champ α) (e : Nat) (k k' : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hp : HP cfg 13 c.root) (hne : L.eqK k k' = false) :
    Champ.get cfg ((c.subMut cfg e k).run s).1 k' = Champ.get cfg c k' := by
  obtain ⟨h1, h2⟩ := lawful_sub_facts L k k' hne
  exact get_subMut_pair cfg c e k k' s hw hp h1 h2

/-! ## `HP` cannot be dropped for `sub_mut` -/

/-- Round 7's `badChamp` with every node and the values buffer owned by token `e` (the nodes a
transient made itself). -/
def badChampOwned (e : Nat) : Champ Nat :=
  { root := .inner 1 e 2 0 none
      [.inner 2 e 0 (2 ^ 3 ||| 2 ^ 9) (some { id := 3, tok := e, xs := [225, 289] }) []],
    size := 2 }

theorem badChampOwned_wf : wfNode 13 (badChampOwned 7).root = true := by decide +kernel

theorem badChampOwned_get_before : Champ.get natCfg (badChampOwned 7) 225 = none := by decide +kernel

/-- The mutating path: `do_sub_mut` at the owned child returns the singleton 225 (moved, `owned`),
and the owned root inlines it with `move_inner_replace_inline`. -/
theorem badChampOwned_get_after :
    Champ.get natCfg (((badChampOwned 7).subMut natCfg 7 289).run {}).1 225 = some 225 := by decide +kernel

/-- The copying path: a transient's `sub_mut` on round 7's `badChamp`, whose nodes it does not own
(token 7 against the nodes' 0): `do_sub` below, `copy_inner_replace_inline` at the root. -/
theorem badChamp_subMut_get_after :
    Champ.get natCfg ((badChamp.subMut natCfg 7 289).run {}).1 225 = some 225 := by decide +kernel

theorem badChampOwned_not_HP : ¬ HP natCfg 13 (badChampOwned 7).root := fun hp =>
  get_complete natCfg (badChampOwned 7) 225 225 badChampOwned_wf hp (by decide +kernel) rfl (by decide)
    badChampOwned_get_before

/-- **`HP` cannot be dropped from law 1 for `sub_mut`**, on either path: two well-formed champs off
their hash paths, under a lawful equality, where `dissoc!`/`disj!` of 289 (not `Equal` to 225) changes
`get 225` from nothing to 225. -/
theorem law1_subMut_fails_without_HP :
    (wfNode 13 badChamp.root = true ∧ ¬ HP natCfg 13 badChamp.root ∧
      Champ.get natCfg ((badChamp.subMut natCfg 7 289).run {}).1 225 ≠ Champ.get natCfg badChamp 225) ∧
    (wfNode 13 (badChampOwned 7).root = true ∧ ¬ HP natCfg 13 (badChampOwned 7).root ∧
      Champ.get natCfg (((badChampOwned 7).subMut natCfg 7 289).run {}).1 225 ≠
        Champ.get natCfg (badChampOwned 7) 225) ∧
    natLawful.eqK 289 225 = false := by
  refine ⟨⟨badChamp_wf, badChamp_not_HP, ?_⟩, ⟨badChampOwned_wf, badChampOwned_not_HP, ?_⟩, by decide⟩
  · rw [badChamp_subMut_get_after, badChamp_get_before]; simp
  · rw [badChampOwned_get_after, badChampOwned_get_before]; simp

/-! ## What jank builds: `wfNode` and `HP` for every hash and every equality -/

/-- ★ One step of any of the four kinds keeps `wfNode` and `HP` of the root, for every hash function
and every equality (nothing assumed of either), any owner token. -/
theorem step_wf_HP (cfg : Cfg α κ) (c : Champ α) (s : Al) (hw : wfNode 13 c.root = true)
    (hp : HP cfg 13 c.root) (op : TOp α κ) :
    wfNode 13 ((applyT cfg c op).run s).1.root = true ∧ HP cfg 13 ((applyT cfg c op).run s).1.root := by
  cases op with
  | add v =>
    have o := add_step cfg v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw
    exact ⟨o.wf, o.hp hp⟩
  | addMut e v =>
    have o := addMut_step cfg e v (cfg.hashT v) rfl 13 (Nat.le_refl _) c.root s hw
    exact ⟨o.wf, o.hp hp⟩
  | sub k =>
    have o := sub_step cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    show wfNode 13 ((c.sub cfg k).run s).1.root = true ∧ HP cfg 13 ((c.sub cfg k).run s).1.root
    unfold Champ.sub
    simp only [StateT.run_bind]
    generalize (doSub cfg k 13 c.root (cfg.hashK k)).run s = q at o
    obtain ⟨sub, s1⟩ := q
    cases sub with
    | nothing => exact ⟨hw, hp⟩
    | singleton x => exact ⟨hw, hp⟩
    | tree t => exact ⟨o.1, o.2.2 hp⟩
  | subMut e k =>
    have o := subMut_step cfg e k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
    show wfNode 13 ((c.subMut cfg e k).run s).1.root = true ∧ HP cfg 13 ((c.subMut cfg e k).run s).1.root
    unfold Champ.subMut
    simp only [StateT.run_bind]
    generalize (doSubMut cfg e k 13 c.root (cfg.hashK k)).run s = q at o
    obtain ⟨res, s1⟩ := q
    obtain ⟨rr, ow, mu⟩ := res
    cases rr with
    | nothing => exact ⟨hw, hp⟩
    | singleton x => exact ⟨hw, hp⟩
    | tree t => exact ⟨o.1, o.2.2 hp⟩

/-- ★ Every sequence of persistent and transient steps keeps `wfNode` and `HP`, for every hash and
every equality. -/
theorem buildT_wf_HP (cfg : Cfg α κ) :
    ∀ (ops : List (TOp α κ)) (c : Champ α) (s : Al), wfNode 13 c.root = true → HP cfg 13 c.root →
      wfNode 13 ((buildT cfg c ops).run s).1.root = true ∧ HP cfg 13 ((buildT cfg c ops).run s).1.root
  | [], _, _, hw, hp => ⟨hw, hp⟩
  | op :: ops, c, s, hw, hp => by
    have e : ((buildT cfg c (op :: ops)).run s).1 =
        ((buildT cfg ((applyT cfg c op).run s).1 ops).run ((applyT cfg c op).run s).2).1 := rfl
    rw [e]
    obtain ⟨hw1, hp1⟩ := step_wf_HP cfg c s hw hp op
    exact buildT_wf_HP cfg ops _ _ hw1 hp1

/-- ★ **Every champ a jank program builds from `champ::empty()`** (any mix of `conj`/`assoc`,
`disj`/`dissoc`, `conj!`/`assoc!`, `disj!`/`dissoc!`, any owner tokens) is well formed and meets `HP`,
for every hash function and every equality. -/
theorem reach_wf_HP (cfg : Cfg α κ) (ops : List (TOp α κ)) (s : Al) :
    wfNode 13 ((buildT cfg Champ.empty ops).run s).1.root = true ∧
      HP cfg 13 ((buildT cfg Champ.empty ops).run s).1.root :=
  buildT_wf_HP cfg ops Champ.empty s rfl (inv_empty cfg).hp

/-- ★ **Law 1 for every step of every sequence jank can run** (lawful equality): after any sequence
of persistent and transient steps from `champ::empty()`, one more step of any kind leaves `get` of a
key not `Equal` to the step's key unchanged. Proved from `wfNode` and `HP` alone (`reach_wf_HP`), not
from round 6's `Inv`. -/
theorem law1_reach {cfg : Cfg α κ} (L : Lawful cfg) (ops : List (TOp α κ)) (s s' : Al) (op : TOp α κ)
    (k' : κ) (hne : match op with
      | .add v | .addMut _ v => L.eqK (L.key v) k' = false
      | .sub k | .subMut _ k => L.eqK k k' = false) :
    Champ.get cfg ((applyT cfg ((buildT cfg Champ.empty ops).run s).1 op).run s').1 k' =
      Champ.get cfg ((buildT cfg Champ.empty ops).run s).1 k' := by
  obtain ⟨hw, hp⟩ := reach_wf_HP cfg ops s
  generalize ((buildT cfg Champ.empty ops).run s).1 = c at hw hp ⊢
  cases op with
  | add v => exact get_add_other_wf L c v k' s' hw hne
  | addMut e v => exact get_addMut_other_wf L c e v k' s' hw hne
  | sub k => exact get_sub_other_hp L c k k' s' hw hp hne
  | subMut e k => exact get_subMut_other_hp L c e k k' s' hw hp hne

end Jank.R8.Champ

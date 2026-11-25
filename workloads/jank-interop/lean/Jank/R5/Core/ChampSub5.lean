import Jank.R5.Core.ChampWf5

/-!
# Round 5, core: `get` after `sub` (`dissoc`/`disj`), for every input

★ `get_sub`: for every well-formed champ holding at most one value `Equal` to `k`, `champ::get(k)`
after `champ::sub(k)` finds nothing. The premise is the law's own: with two stored values both `=`
to `k` (jank's D12 lets `1` and `1N` both sit in one set, each `=` to `1`), removing one leaves the
other. Under an equality that agrees with the hash, a champ built by adds holds at most one value
`=` to any key; that invariant (iteration yields each key once) is not proved here.

The proof follows `do_sub` (champ.hpp) through every case the replica has: a collision node shrunk
or collapsed to the one value left, a data slot removed, a two-value node collapsed into its
parent's slot (the value passed up is the other one, never `Equal` to `k`), inlined by the first
ancestor that keeps other entries, and the root's own collapse.
-/

namespace Jank.R3.Immer.Champ

variable {α κ : Type}

/-! ## Lists -/

theorem countP_le_flatMap {β γ : Type} (p : γ → Bool) (f : β → List γ) :
    ∀ (l : List β) (c : β), c ∈ l → (f c).countP p ≤ (l.flatMap f).countP p
  | [], _, h => by simp at h
  | a :: l, c, h => by
    rw [List.flatMap_cons, List.countP_append]
    rcases List.mem_cons.mp h with h | h
    · rw [h]; omega
    · have := countP_le_flatMap p f l c h; omega

/-- In a list with at most one element satisfying `p`, removing the one at `i` (which does) leaves
none. -/
theorem others_false {β : Type} (p : β → Bool) :
    ∀ (l : List β) (i : Nat) (x : β), l[i]? = some x → p x = true → l.countP p ≤ 1 →
      ∀ y ∈ eraseAt l i, p y = false
  | [], _, _, hx, _, _ => by simp at hx
  | a :: l, 0, x, hx, hp, hc => by
    have hax : a = x := by simpa using hx
    have h1 : (a :: l).countP p = l.countP p + 1 := by simp [List.countP_cons, hax, hp]
    have h0 : l.countP p = 0 := by omega
    intro y hy
    have hy' : y ∈ l := by simpa [eraseAt] using hy
    have := List.countP_eq_zero.mp h0 y hy'
    simpa using this
  | a :: l, i + 1, x, hx, hp, hc => by
    have hx' : l[i]? = some x := by simpa using hx
    have hpos : 0 < l.countP p := List.countP_pos_iff.mpr ⟨x, List.mem_of_getElem? hx', hp⟩
    have h1 : (a :: l).countP p = l.countP p + (if p a then 1 else 0) := List.countP_cons
    have hpa : p a = false := by
      cases hpa : p a with
      | false => rfl
      | true =>
        rw [hpa] at h1
        have : (if true = true then 1 else 0) = 1 := rfl
        omega
    have hc' : l.countP p ≤ 1 := by omega
    intro y hy
    have e : eraseAt (a :: l) (i + 1) = a :: eraseAt l i := by unfold eraseAt; simp
    rw [e] at hy
    rcases List.mem_cons.mp hy with hy | hy
    · rw [hy]; exact hpa
    · exact others_false p l i x hx' hp hc' y hy

theorem other_mem {β : Type} (d : β) :
    ∀ (L : List β), L.length = 2 → ∀ i, i < 2 → L.getD (if i == 0 then 1 else 0) d ∈ eraseAt L i
  | [_, _], _, 0, _ => by simp [eraseAt]
  | [_, _], _, 1, _ => by simp [eraseAt]
  | [_, _], _, _ + 2, hi => by omega
  | [], h, _, _ => by simp at h
  | [_], h, _, _ => by simp at h
  | _ :: _ :: _ :: _, h, _, _ => by simp at h

/-! ## `get` on an inner node: an empty slot, a data slot -/

theorem getLoop_empty (cfg : Cfg α κ) (k : κ) (r nid tok nm dm : Nat) (vv : Option (Vals α))
    (cs : List (Node α)) (hash d : Nat) (hhash : hash &&& 31 = d) (h1 : nm.testBit d = false)
    (h2 : dm.testBit d = false) :
    getLoop cfg k (r + 1) (.inner nid tok nm dm vv cs) hash = none := by
  rw [getLoop.eq_2]
  dsimp only
  rw [hhash, one_shl]
  split
  · next hc => exact absurd hc (by show ¬ ((nm &&& 2 ^ d != 0) = true); rw [and_pow_bne, h1]; simp)
  · split
    · next hc => exact absurd hc (by show ¬ ((dm &&& 2 ^ d != 0) = true); rw [and_pow_bne, h2]; simp)
    · rfl

theorem getLoop_data_val (cfg : Cfg α κ) (k : κ) (r nid tok nm dm : Nat) (vv : Option (Vals α))
    (cs : List (Node α)) (hash d : Nat) (x : α) (hhash : hash &&& 31 = d) (h1 : nm.testBit d = false)
    (h2 : dm.testBit d = true)
    (hval : (Node.inner nid tok nm dm vv cs).values[popcount (dm &&& (2 ^ d - 1))]? = some x) :
    getLoop cfg k (r + 1) (.inner nid tok nm dm vv cs) hash = if cfg.eqTK x k then some x else none := by
  rw [getLoop.eq_2]
  dsimp only
  rw [hhash, one_shl]
  split
  · next hc => exact absurd hc (by show ¬ ((nm &&& 2 ^ d != 0) = true); rw [and_pow_bne, h1]; simp)
  · split
    · split
      · next v' heq =>
        have e := hval.symm.trans heq
        cases e
        rfl
      · next heq =>
        have e := hval.symm.trans heq
        cases e
    · next hc => exact absurd (by show (dm &&& 2 ^ d != 0) = true; rw [and_pow_bne]; exact h2) hc

/-! ## `do_sub`, case by case -/

/-- What `do_sub` returns, when the subtree holds at most one value `Equal` to `k`: a value passed
up is not `Equal` to `k`, and a tree has nothing `get` finds along `k`'s hash. -/
def SubOk (cfg : Cfg α κ) (k : κ) (r : Nat) (hash : Nat) : Sub α → Prop
  | .nothing => True
  | .singleton x => cfg.eqTK x k = false
  | .tree t => getLoop cfg k r t hash = none

theorem doSub_ok [Inhabited α] (cfg : Cfg α κ) (k : κ) (h : Nat) :
    ∀ r, r ≤ 13 → ∀ (N : Node α) (s : Al), wfNode r N = true →
      (iterNode r N).countP (fun x => cfg.eqTK x k) ≤ 1 →
      SubOk cfg k r (h >>> (65 - 5 * r)) ((doSub cfg k r N h).run s).1 := by
  intro r
  induction r with
  | zero =>
    intro _ N s hw hu
    have hl : N.collisions.length ≥ 2 := by
      cases N with
      | inner => simp [wfNode] at hw
      | collision nid tok xs => simpa [wfNode, Node.collisions] using hw
    have hu' : N.collisions.countP (fun x => cfg.eqTK x k) ≤ 1 := hu
    rw [doSub.eq_1]
    unfold findIdx?
    cases hf : N.collisions.findIdx? (fun x => cfg.eqTK x k) with
    | none => exact True.intro
    | some cur =>
      obtain ⟨hcur, hpc, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
      have hget : N.collisions[cur]? = some N.collisions[cur] := List.getElem?_eq_getElem hcur
      have hoth := others_false (fun x => cfg.eqTK x k) N.collisions cur N.collisions[cur] hget hpc hu'
      dsimp only
      split
      · show (eraseAt N.collisions cur).find? (fun x => cfg.eqTK x k) = none
        rw [List.find?_eq_none]
        intro y hy
        simp [hoth y hy]
      · next hlen =>
        show cfg.eqTK (N.collisions.getD (if cur == 0 then 1 else 0) default) k = false
        apply hoth
        exact other_mem default _ (by omega) cur (by omega)
  | succ r ih =>
    intro hr N s hw hu
    obtain ⟨hcs, hvals, hch⟩ := wf_facts r N hw
    have hit : iterNode (r + 1) N = N.values.take N.dataCount ++ (N.cs.take N.childrenCount).flatMap (iterNode r) := by
      rw [iterNode.eq_2]
    have huV : (N.values.take N.dataCount).countP (fun x => cfg.eqTK x k) ≤ 1 := by
      rw [hit, List.countP_append] at hu; omega
    have hD := idxAt_lt h (maxShift - 5 * (r + 1))
    generalize hDdef : idxAt h (maxShift - 5 * (r + 1)) = D at hD
    have hbit : bitAt h (maxShift - 5 * (r + 1)) = 1 <<< D := by unfold bitAt; rw [hDdef]
    have hh : (h >>> (65 - 5 * (r + 1))) &&& 31 = D := by rw [hidx]; exact hDdef
    have hoffN : N.childrenCountBit (1 <<< D) = popcount (N.nodemap &&& (2 ^ D - 1)) := by
      unfold Node.childrenCountBit; rw [one_shl]
    have hoffD : N.dataCountBit (1 <<< D) = popcount (N.datamap &&& (2 ^ D - 1)) := by
      unfold Node.dataCountBit; rw [one_shl]
    rw [doSub.eq_2]
    dsimp only
    rw [hbit]
    by_cases hA : (N.nodemap &&& 1 <<< D != 0) = true
    · rw [if_pos hA]
      have hAt : N.nodemap.testBit D = true := testBit_of_bne _ _ hA
      have hlt := popcount_lt N.nodemap D hD hAt
      have hmem : N.child (N.childrenCountBit (1 <<< D)) ∈ N.cs.take N.childrenCount := by
        unfold Node.child; rw [hoffN]
        exact getD_mem_take _ _ _ _ hlt (by omega)
      have huC : (iterNode r (N.child (N.childrenCountBit (1 <<< D)))).countP (fun x => cfg.eqTK x k) ≤ 1 := by
        have := countP_le_flatMap (fun x => cfg.eqTK x k) (iterNode r) _ _ hmem
        rw [hit, List.countP_append] at hu; omega
      have hcw : wfNode r (N.child (N.childrenCountBit (1 <<< D))) = true := by
        apply hch; exact hmem
      have hok := ih (by omega) _ s hcw huC
      simp only [StateT.run_bind]
      generalize ((doSub cfg k r (N.child (N.childrenCountBit (1 <<< D))) h).run s) = q at hok
      obtain ⟨sub, s1⟩ := q
      cases sub with
      | nothing => trivial
      | singleton x =>
        have hx : cfg.eqTK x k = false := hok
        split
        · exact hx
        · -- `copy_inner_replace_inline`: x in the slot of k's bit
          show getLoop cfg k (r + 1) ((copyInnerReplaceInline N (1 <<< D) (N.childrenCountBit (1 <<< D)) x).run s1).1
            (h >>> (65 - 5 * (r + 1))) = none
          have e3 : ((copyInnerReplaceInline N (1 <<< D) (N.childrenCountBit (1 <<< D)) x).run s1).1 =
              ((mkInner (clearBit N.nodemap (1 <<< D)) (N.datamap ||| 1 <<< D)
                (insertAt (N.values.take N.dataCount) (N.dataCountBit (1 <<< D)) x)
                (eraseAt (N.cs.take N.childrenCount) (N.childrenCountBit (1 <<< D)))).run s1).1 := rfl
          obtain ⟨nid, vv, e2, ev⟩ := mkInner_run (clearBit N.nodemap (1 <<< D)) (N.datamap ||| 1 <<< D)
            (insertAt (N.values.take N.dataCount) (N.dataCountBit (1 <<< D)) x)
            (eraseAt (N.cs.take N.childrenCount) (N.childrenCountBit (1 <<< D))) s1
          rw [e3, e2]
          have hle := popcount_and_le N.datamap (2 ^ D - 1)
          have g1 : (clearBit N.nodemap (1 <<< D)).testBit D = false := by
            rw [one_shl, clearBit_testBit _ _ _ hD]; simp
          have g2 : (N.datamap ||| 1 <<< D).testBit D = true := by
            rw [one_shl]; simp [Nat.testBit_or, Nat.testBit_two_pow]
          have gi : popcount ((N.datamap ||| 1 <<< D) &&& (2 ^ D - 1)) = N.dataCountBit (1 <<< D) := by
            rw [hoffD, one_shl, or_pow_mask]
          have g3 : (Node.inner nid 0 (clearBit N.nodemap (1 <<< D)) (N.datamap ||| 1 <<< D) vv
              (eraseAt (N.cs.take N.childrenCount) (N.childrenCountBit (1 <<< D)))).values[popcount
                ((N.datamap ||| 1 <<< D) &&& (2 ^ D - 1))]? = some x := by
            rw [ev, gi]
            exact insertAt_getElem? _ _ _ (by rw [hoffD, List.length_take]; unfold Node.dataCount; omega)
          rw [getLoop_data_val cfg k r nid 0 _ _ vv _ _ D x hh g1 g2 g3]
          simp [hx]
      | tree t' =>
        have ht' : getLoop cfg k r t' (h >>> (65 - 5 * r)) = none := hok
        show getLoop cfg k (r + 1) ((copyInnerReplace N (N.childrenCountBit (1 <<< D)) t').run s1).1
          (h >>> (65 - 5 * (r + 1))) = none
        have e3 : ((copyInnerReplace N (N.childrenCountBit (1 <<< D)) t').run s1).1 =
            .inner s1.next 0 N.nodemap N.datamap N.vals
              (setL (N.cs.take N.childrenCount) (N.childrenCountBit (1 <<< D)) t') := rfl
        rw [e3, getLoop_child cfg k r _ 0 _ _ _ _ _ D hh hAt, ← hoffN, setL_getD, shr_step h r hr]
        · exact ht'
        · rw [List.length_take, hoffN]; unfold Node.childrenCount; omega
    · rw [if_neg hA]
      have hAt : N.nodemap.testBit D = false := by
        have h' := hA
        rw [one_shl, and_pow_bne] at h'
        simpa using h'
      by_cases hB : (N.datamap &&& 1 <<< D != 0) = true
      · rw [if_pos hB]
        have hBt : N.datamap.testBit D = true := testBit_of_bne _ _ hB
        have hltD := popcount_lt N.datamap D hD hBt
        have hcl : (clearBit N.datamap (1 <<< D)).testBit D = false := by
          rw [one_shl, clearBit_testBit _ _ _ hD]; simp
        by_cases hE : cfg.eqTK (N.values.getD (N.dataCountBit (1 <<< D)) default) k = true
        · rw [if_pos hE]
          by_cases c1 : (N.nodemap != 0 || decide (N.dataCount > 2)) = true
          · -- `copy_inner_remove_value`
            rw [if_pos c1]
            show getLoop cfg k (r + 1) ((copyInnerRemoveValue N (1 <<< D) (N.dataCountBit (1 <<< D))).run s).1
              (h >>> (65 - 5 * (r + 1))) = none
            obtain ⟨nid, vv, e2, _⟩ := mkInner_run N.nodemap (clearBit N.datamap (1 <<< D))
              (eraseAt (N.values.take N.dataCount) (N.dataCountBit (1 <<< D))) (N.cs.take N.childrenCount) s
            have e3 : ((copyInnerRemoveValue N (1 <<< D) (N.dataCountBit (1 <<< D))).run s).1 =
                ((mkInner N.nodemap (clearBit N.datamap (1 <<< D))
                  (eraseAt (N.values.take N.dataCount) (N.dataCountBit (1 <<< D))) (N.cs.take N.childrenCount)).run s).1 := rfl
            rw [e3, e2]
            exact getLoop_empty cfg k r nid 0 _ _ vv _ _ D hh hAt hcl
          · rw [if_neg c1]
            by_cases c2 : (N.dataCount == 2) = true
            · rw [if_pos c2]
              split
              · -- the other value, passed up
                show cfg.eqTK (N.values.getD (if (N.dataCountBit (1 <<< D) == 0) = true then 1 else 0) default) k = false
                have hdc : N.dataCount = 2 := by simpa using c2
                have hdc' : popcount N.datamap = 2 := hdc
                have hlen : (N.values.take 2).length = 2 := by
                  rw [List.length_take]; omega
                have hv2 : N.dataCountBit (1 <<< D) < 2 := by
                  rw [hoffD]; omega
                have hget : (N.values.take 2)[N.dataCountBit (1 <<< D)]? =
                    some (N.values.getD (N.dataCountBit (1 <<< D)) default) := by
                  rw [List.getElem?_take_of_lt hv2, getElem?_of_lt N.values (N.dataCountBit (1 <<< D)) (by omega)]
                have hother : N.values.getD (if (N.dataCountBit (1 <<< D) == 0) = true then 1 else 0) default =
                    (N.values.take 2).getD (if (N.dataCountBit (1 <<< D) == 0) = true then 1 else 0) default := by
                  have hj : (if (N.dataCountBit (1 <<< D) == 0) = true then 1 else 0) < 2 := by split <;> omega
                  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
                have huV2 : (N.values.take 2).countP (fun x => cfg.eqTK x k) ≤ 1 := by
                  have e : N.values.take 2 = N.values.take N.dataCount := by rw [hdc]
                  rw [e]; exact huV
                rw [hother]
                exact others_false (fun x => cfg.eqTK x k) _ _ _ hget hE huV2 _
                  (other_mem default _ hlen _ hv2)
              · -- the root keeps the other value
                show getLoop cfg k (r + 1) ((mkInner 0 (clearBit N.datamap (1 <<< D))
                  [N.values.getD (if (N.dataCountBit (1 <<< D) == 0) = true then 1 else 0) default] []).run s).1
                  (h >>> (65 - 5 * (r + 1))) = none
                obtain ⟨nid, vv, e2, _⟩ := mkInner_run 0 (clearBit N.datamap (1 <<< D))
                  [N.values.getD (if (N.dataCountBit (1 <<< D) == 0) = true then 1 else 0) default] ([] : List (Node α)) s
                rw [e2]
                exact getLoop_empty cfg k r nid 0 _ _ vv _ _ D hh (Nat.zero_testBit D) hcl
            · -- `empty()`
              rw [if_neg c2]
              show getLoop cfg k (r + 1) (Champ.empty (α := α)).root (h >>> (65 - 5 * (r + 1))) = none
              exact getLoop_empty cfg k r 1 0 0 0 none [] _ D hh (Nat.zero_testBit D) (Nat.zero_testBit D)
        · rw [if_neg hE]; trivial
      · rw [if_neg hB]; trivial

/-- ★ **`get` after `dissoc`/`disj`** finds nothing, for every well-formed champ holding at most one
value `Equal` to the key. -/
theorem get_sub [Inhabited α] (cfg : Cfg α κ) (c : Champ α) (k : κ) (s : Al)
    (hw : wfNode 13 c.root = true) (hu : c.toList.countP (fun x => cfg.eqTK x k) ≤ 1) :
    Champ.get cfg ((c.sub cfg k).run s).1 k = none := by
  by_cases hg : Champ.get cfg c k = none
  · rw [sub_absent cfg c k s hw hg]; exact hg
  · have ⟨_, ht⟩ := doSub_found cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw
      (by rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero]; exact hg)
    have ht := ht rfl
    have hok := doSub_ok cfg k (cfg.hashK k) 13 (Nat.le_refl _) c.root s hw hu
    rw [show (65 : Nat) - 5 * 13 = 0 from rfl, Nat.shiftRight_zero] at hok
    unfold Champ.sub
    simp only [StateT.run_bind]
    generalize ((doSub cfg k 13 c.root (cfg.hashK k)).run s) = q at ht hok
    obtain ⟨sub, s1⟩ := q
    cases sub with
    | tree t => exact hok
    | _ => cases ht

end Jank.R3.Immer.Champ

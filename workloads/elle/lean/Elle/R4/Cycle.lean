import Elle.R4.Dsg

/-!
# Round 4: lifting a closed walk of explained steps into a DSG

A cycle Elle reports is a closed walk whose steps each lift, in an interpretation's DSG, to a
segment: a write-dependency path (`w`), a dependency path (`d`), or an anti-dependency followed by
write dependencies (`a`). Which phenomena the closed walk of segments shows depends only on where
its `a` segments are. The walk is given periodically (vertex `v j`, segment kind `K j`, period `n`)
so that a rotation is a shift.
-/

namespace Elle.R4

inductive Kind where
  | w | d | a
  deriving DecidableEq, Repr

namespace DSG
variable (D : DSG)

/-- What a segment of kind `k` from `a` to `b` is in the DSG. -/
def SegOK (x : Var) : Kind → Nat → Nat → Prop
  | .w, a, b => Plus (D.W x) a b
  | .d, a, b => Plus (D.Dd x) a b
  | .a, a, b => ∃ c, D.rw a c ∧ Star D.ww c b

variable {D}

theorem segOK_dd {x : Var} {k : Kind} {a b : Nat} (hk : k ≠ .a) (h : D.SegOK x k a b) : Plus (D.Dd x) a b := by
  cases k with
  | w => exact Plus.mono (fun _ _ h => Or.inl h) h
  | d => exact h
  | a => exact absurd rfl hk

theorem segOK_any {x : Var} {k : Kind} {a b : Nat} (h : D.SegOK x k a b) :
    Plus (fun u w => D.Dd x u w ∨ D.rw u w) a b := by
  cases k with
  | w => exact Plus.mono (fun _ _ h => Or.inl (Or.inl h)) h
  | d => exact Plus.mono (fun _ _ h => Or.inl h) h
  | a =>
    obtain ⟨c, hc, hcb⟩ := h
    exact Star.trans_plus (.one (Or.inr hc)) (hcb.mono fun _ _ h => Or.inl (Or.inl (Or.inl h)))

end DSG

/-! ## Chains of segments -/

/-- Segments `i .. j - 1` joined: a path from `v i` to `v j`. -/
theorem chain_star {R : Nat → Nat → Prop} (v : Nat → Nat) (i : Nat) :
    ∀ j, i ≤ j → (∀ t, i ≤ t → t < j → Plus R (v t) (v (t + 1))) → Star R (v i) (v j) := by
  intro j hij
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  clear hij
  induction k with
  | zero => intro _; exact Star.refl _
  | succ k ih =>
    intro h
    exact (ih fun t h1 h2 => h t h1 (by omega)).trans (Or.inr (by
      have := h (i + k) (by omega) (by omega)
      rwa [show i + k + 1 = i + (k + 1) by omega] at this))

theorem chain_plus {R : Nat → Nat → Prop} (v : Nat → Nat) (i j : Nat) (hij : i < j)
    (h : ∀ t, i ≤ t → t < j → Plus R (v t) (v (t + 1))) : Plus R (v i) (v j) := by
  have h1 := chain_star v i (j - 1) (by omega) (fun t h1 h2 => h t h1 (by omega))
  have h2 := h (j - 1) (by omega) (by omega)
  have : j - 1 + 1 = j := by omega
  rw [this] at h2
  exact Star.plus_trans h1 h2

/-! ## The phenomena of a closed walk of segments -/

section Periodic
variable {D : DSG} {x : Var} {n : Nat} {v : Nat → Nat} {K : Nat → Kind}

/-- The walk's data repeat with period `n`. -/
structure Cyc (D : DSG) (x : Var) (n : Nat) (v : Nat → Nat) (K : Nat → Kind) : Prop where
  pos : 0 < n
  v_per : ∀ j, v (j + n) = v j
  K_per : ∀ j, K (j + n) = K j
  seg : ∀ j, D.SegOK x (K j) (v j) (v (j + 1))

theorem per_mod {f : Nat → α} (hp : ∀ j, f (j + n) = f j) (j : Nat) : f j = f (j % n) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj : j < n
    · rw [Nat.mod_eq_of_lt hj]
    · have : j = (j - n) + n := by omega
      rw [this, hp, Nat.add_mod_right]
      by_cases hn : n = 0
      · subst hn; simp
      · exact ih _ (by omega)

theorem cyc_G1c (c : Cyc D x n v K) (h : ∀ t < n, K t ≠ .a) : D.G1c x := by
  refine ⟨v 0, ?_⟩
  have := chain_plus (R := D.Dd x) v 0 n c.pos fun t _ ht => DSG.segOK_dd (h t ht) (c.seg t)
  rwa [show v n = v 0 by simpa using c.v_per 0] at this

theorem cyc_G0 (c : Cyc D x n v K) (h : ∀ t < n, K t = .w) : D.G0 x := by
  refine ⟨v 0, ?_⟩
  have := chain_plus (R := D.W x) v 0 n c.pos fun t _ ht => by
    have hs := c.seg t; rw [h t ht] at hs; exact hs
  rwa [show v n = v 0 by simpa using c.v_per 0] at this

theorem cyc_GSingle (hirr : ∀ a, ¬ D.rw a a) (c : Cyc D x n v K) {i : Nat} (hi : i < n) (hia : K i = .a)
    (hone : ∀ t < n, t ≠ i → K t ≠ .a) : D.GSingle x := by
  have hs := c.seg i
  rw [hia] at hs
  obtain ⟨c', hrw, hcb⟩ := hs
  refine ⟨v i, c', hrw, ?_⟩
  have hback : Star (D.Dd x) (v (i + 1)) (v (i + n)) := chain_star v (i + 1) (i + n) (by omega) fun t h1 h2 => by
    apply DSG.segOK_dd _ (c.seg t)
    rw [per_mod c.K_per t]
    apply hone _ (Nat.mod_lt _ c.pos)
    intro he
    -- t is strictly between i and i + n, so its residue isn't i's
    have : t % n = (t - n) % n + 0 ∨ True := Or.inr trivial
    rcases Nat.lt_or_ge t n with ht | ht
    · rw [Nat.mod_eq_of_lt ht] at he; omega
    · have : t % n = t - n := by
        rw [show t = (t - n) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
      omega
  rw [c.v_per] at hback
  have hstar : Star (D.Dd x) c' (v i) := (hcb.mono fun _ _ h => Or.inl (Or.inl h)).trans hback
  exact hstar.plus_of_ne fun he => hirr (v i) (he ▸ hrw)

theorem cyc_G2 (hirr : ∀ a, ¬ D.rw a a) (c : Cyc D x n v K) {i : Nat} (hi : i < n) (hia : K i = .a) :
    D.G2 x := by
  have hs := c.seg i
  rw [hia] at hs
  obtain ⟨c', hrw, hcb⟩ := hs
  refine ⟨v i, c', hrw, ?_⟩
  have hback := chain_star (R := fun u w => D.Dd x u w ∨ D.rw u w) v (i + 1) (i + n) (by omega)
    fun t _ _ => DSG.segOK_any (c.seg t)
  rw [c.v_per] at hback
  have hstar : Star (fun u w => D.Dd x u w ∨ D.rw u w) c' (v i) :=
    (hcb.mono fun _ _ h => Or.inl (Or.inl (Or.inl h))).trans hback
  exact hstar.plus_of_ne fun he => hirr (v i) (he ▸ hrw)

/-- The relation of `G-nonadjacent`'s cycles. -/
def NRel (D : DSG) (x : Var) (u w : Nat) : Prop := D.Dd x u w ∨ ∃ y, D.Dd x u y ∧ D.rw y w

theorem cyc_GNonadj (c : Cyc D x n v K) (hadj : ∀ t, K (t + 1) = .a → K t ≠ .a) : D.GNonadj x := by
  -- a segment that is not an anti-dependency
  have hex : ∃ s < n, K s ≠ .a := by
    rcases Classical.em (K 0 = .a) with h0 | h0
    · refine ⟨n - 1, by have := c.pos; omega, ?_⟩
      have := hadj (n - 1)
      rw [show n - 1 + 1 = 0 + n by have := c.pos; omega, c.K_per] at this
      exact this h0
    · exact ⟨0, c.pos, h0⟩
  obtain ⟨s, _, hs⟩ := hex
  -- after segments s .. j - 1: either the walk ends with a dependency into v j, or segment j - 1
  -- was an anti-dependency and the walk reaches v j
  let St : Nat → Prop := fun j =>
    (∃ u, Star (NRel D x) (v s) u ∧ D.Dd x u (v j)) ∨ (K (j - 1) = .a ∧ Plus (NRel D x) (v s) (v j))
  have hstar : ∀ j, St j → Star (NRel D x) (v s) (v j) := by
    intro j h
    rcases h with ⟨u, hu, hud⟩ | ⟨_, hp⟩
    · exact hu.trans (Or.inr (.one (Or.inl hud)))
    · exact Or.inr hp
  have step : ∀ j, s < j → St j → St (j + 1) := by
    intro j hsj hj
    have hseg := c.seg j
    by_cases hk : K j = .a
    · -- the segment before is not an anti-dependency, so the walk ends with a dependency
      rw [hk] at hseg
      obtain ⟨c', hrw, hcb⟩ := hseg
      have hprev : K (j - 1) ≠ .a := by
        have := hadj (j - 1); rw [show j - 1 + 1 = j by omega] at this; exact this hk
      rcases hj with ⟨u, hu, hud⟩ | ⟨hka, _⟩
      · right
        refine ⟨by simpa using hk, ?_⟩
        exact Star.plus_trans hu (Star.trans_plus (.one (Or.inr ⟨v j, hud, hrw⟩))
          (hcb.mono fun _ _ h => Or.inl (Or.inl (Or.inl h))))
      · exact absurd hka hprev
    · have hp := DSG.segOK_dd hk hseg
      obtain ⟨y, hy, hyb⟩ := hp.last
      left
      exact ⟨y, (hstar j hj).trans (hy.mono fun _ _ h => Or.inl h), hyb⟩
  have hst : ∀ k, k < n → St (s + 1 + k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hp := DSG.segOK_dd hs (c.seg s)
      obtain ⟨y, hy, hyb⟩ := hp.last
      exact Or.inl ⟨y, hy.mono fun _ _ h => Or.inl h, hyb⟩
    | succ k ih =>
      intro hk
      have := step (s + 1 + k) (by omega) (ih (by omega))
      rwa [show s + 1 + k + 1 = s + 1 + (k + 1) by omega] at this
  have hend := hst (n - 1) (by have := c.pos; omega)
  rw [show s + 1 + (n - 1) = s + n by have := c.pos; omega] at hend
  refine ⟨v s, ?_⟩
  have hv := c.v_per s
  rcases hend with ⟨u, hu, hud⟩ | ⟨_, hp⟩
  · rw [hv] at hud; exact Star.plus_trans hu (.one (Or.inl hud))
  · rw [hv] at hp; exact hp

end Periodic

end Elle.R4

import Elle.R4.Prelude

/-!
# Round 4: a direct serialization graph and its phenomena, declaratively

Adya's DSG (thesis §3.2-3.4) over committed transactions, with Elle's session (`so`) and real-time
(`rt`) orders: ww, wr and rw dependencies as relations. The phenomena are written as Round 1's
specification (`Spec.cyclePhen`) computes them: G0 a cycle of write dependencies (with `so`/`rt`
for the process and realtime variants), G1c a cycle of write and read dependencies, G-single an
anti-dependency closed by dependencies, G2 an anti-dependency closed by anything, G-nonadjacent
a cycle in which every anti-dependency follows a dependency.
-/

namespace Elle.R4

/-! ## Paths -/

/-- One or more steps of `R`. -/
inductive Plus (R : Nat → Nat → Prop) : Nat → Nat → Prop
  | one {a b} : R a b → Plus R a b
  | cons {a b c} : R a b → Plus R b c → Plus R a c

/-- Zero or more steps of `R`. -/
def Star (R : Nat → Nat → Prop) (a b : Nat) : Prop := a = b ∨ Plus R a b

namespace Plus
variable {R S : Nat → Nat → Prop}

theorem trans {a b c} (h1 : Plus R a b) (h2 : Plus R b c) : Plus R a c := by
  induction h1 with
  | one h => exact .cons h h2
  | cons h _ ih => exact .cons h (ih h2)

theorem mono {a b} (hRS : ∀ x y, R x y → S x y) (h : Plus R a b) : Plus S a b := by
  induction h with
  | one h => exact .one (hRS _ _ h)
  | cons h _ ih => exact .cons (hRS _ _ h) ih

theorem snoc {a b c} (h1 : Plus R a b) (h2 : R b c) : Plus R a c := h1.trans (.one h2)

/-- A path ends with an edge. -/
theorem last {a b} (h : Plus R a b) : ∃ y, Star R a y ∧ R y b := by
  induction h with
  | one h => exact ⟨_, Or.inl rfl, h⟩
  | cons h _ ih =>
    obtain ⟨y, hy, hyb⟩ := ih
    rcases hy with rfl | hy
    · exact ⟨_, Or.inr (.one h), hyb⟩
    · exact ⟨y, Or.inr (.cons h hy), hyb⟩

end Plus

namespace Star
variable {R S : Nat → Nat → Prop}

theorem refl (a : Nat) : Star R a a := Or.inl rfl

theorem trans {a b c} (h1 : Star R a b) (h2 : Star R b c) : Star R a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (h1.trans h2)

theorem mono {a b} (hRS : ∀ x y, R x y → S x y) (h : Star R a b) : Star S a b := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (h.mono hRS)

theorem plus_of_ne {a b} (h : Star R a b) (hne : a ≠ b) : Plus R a b := by
  rcases h with rfl | h
  · exact absurd rfl hne
  · exact h

theorem plus_trans {a b c} (h1 : Star R a b) (h2 : Plus R b c) : Plus R a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact h1.trans h2

theorem trans_plus {a b c} (h1 : Plus R a b) (h2 : Star R b c) : Plus R a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact h1.trans h2

theorem of_plus {a b} (h : Plus R a b) : Star R a b := Or.inr h

end Star

/-! ## The graph and its phenomena -/

/-- A DSG: dependencies, anti-dependencies, and the session and real-time orders. -/
structure DSG where
  ww : Nat → Nat → Prop
  wr : Nat → Nat → Prop
  rw : Nat → Nat → Prop
  so : Nat → Nat → Prop
  rt : Nat → Nat → Prop

/-- Which orders join the dependencies: none, the session order (process variants), or both (realtime variants). -/
inductive Var where
  | none | process | realtime
  deriving DecidableEq, Repr

def Var.le : Var → Var → Bool
  | .none, _ => true
  | .process, .none => false
  | .process, _ => true
  | .realtime, .realtime => true
  | .realtime, _ => false

def Var.suffix : Var → String
  | .none => "" | .process => "-process" | .realtime => "-realtime"

namespace DSG
variable (D : DSG)

/-- Write dependencies, with the variant's orders (Spec.cyclePhen's `w`). -/
def W (x : Var) (a b : Nat) : Prop :=
  D.ww a b ∨ (x ≠ .none ∧ D.so a b) ∨ (x = .realtime ∧ D.rt a b)

/-- Dependencies, with the variant's orders (Spec.cyclePhen's `d`). -/
def Dd (x : Var) (a b : Nat) : Prop := D.W x a b ∨ D.wr a b

def G0 (x : Var) : Prop := ∃ v, Plus (D.W x) v v
def G1c (x : Var) : Prop := ∃ v, Plus (D.Dd x) v v
def GSingle (x : Var) : Prop := ∃ a b, D.rw a b ∧ Plus (D.Dd x) b a
def G2 (x : Var) : Prop := ∃ a b, D.rw a b ∧ Plus (fun u w => D.Dd x u w ∨ D.rw u w) b a
/-- `hasCycle (seqExtension gd grw)`: every anti-dependency taken right after a dependency. -/
def GNonadj (x : Var) : Prop := ∃ v, Plus (fun u w => D.Dd x u w ∨ ∃ y, D.Dd x u y ∧ D.rw y w) v v

variable {D}

theorem W_mono {x y : Var} (hxy : x.le y = true) {a b} (h : D.W x a b) : D.W y a b := by
  rcases h with h | ⟨hx, h⟩ | ⟨hx, h⟩
  · exact Or.inl h
  · right; left; refine ⟨?_, h⟩
    intro hy; subst hy; cases x <;> simp_all [Var.le]
  · subst hx
    cases y
    · simp [Var.le] at hxy
    · simp [Var.le] at hxy
    · exact Or.inr (Or.inr ⟨rfl, h⟩)

theorem Dd_mono {x y : Var} (hxy : x.le y = true) {a b} (h : D.Dd x a b) : D.Dd y a b := by
  rcases h with h | h
  · exact Or.inl (W_mono hxy h)
  · exact Or.inr h

theorem G0_G1c {x} (h : D.G0 x) : D.G1c x := by
  obtain ⟨v, hv⟩ := h; exact ⟨v, hv.mono fun _ _ h => Or.inl h⟩

theorem G1c_GNonadj {x} (h : D.G1c x) : D.GNonadj x := by
  obtain ⟨v, hv⟩ := h; exact ⟨v, hv.mono fun _ _ h => Or.inl h⟩

theorem GSingle_G2 {x} (h : D.GSingle x) : D.G2 x := by
  obtain ⟨a, b, hab, hp⟩ := h; exact ⟨a, b, hab, hp.mono fun _ _ h => Or.inl h⟩

theorem GSingle_GNonadj {x} (h : D.GSingle x) : D.GNonadj x := by
  obtain ⟨a, b, hab, hp⟩ := h
  obtain ⟨y, hy, hya⟩ := hp.last
  refine ⟨b, ?_⟩
  rcases hy with rfl | hy
  · exact .one (Or.inr ⟨a, hya, hab⟩)
  · exact (hy.mono fun _ _ h => Or.inl h).snoc (Or.inr ⟨a, hya, hab⟩)

theorem G0_mono {x y : Var} (hxy : x.le y = true) (h : D.G0 x) : D.G0 y := by
  obtain ⟨v, hv⟩ := h; exact ⟨v, hv.mono fun _ _ h => W_mono hxy h⟩
theorem G1c_mono {x y : Var} (hxy : x.le y = true) (h : D.G1c x) : D.G1c y := by
  obtain ⟨v, hv⟩ := h; exact ⟨v, hv.mono fun _ _ h => Dd_mono hxy h⟩
theorem GSingle_mono {x y : Var} (hxy : x.le y = true) (h : D.GSingle x) : D.GSingle y := by
  obtain ⟨a, b, hab, hv⟩ := h; exact ⟨a, b, hab, hv.mono fun _ _ h => Dd_mono hxy h⟩
theorem G2_mono {x y : Var} (hxy : x.le y = true) (h : D.G2 x) : D.G2 y := by
  obtain ⟨a, b, hab, hv⟩ := h
  exact ⟨a, b, hab, hv.mono fun _ _ h => h.elim (fun h => Or.inl (Dd_mono hxy h)) Or.inr⟩
theorem GNonadj_mono {x y : Var} (hxy : x.le y = true) (h : D.GNonadj x) : D.GNonadj y := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, hv.mono fun _ _ h => h.elim (fun h => Or.inl (Dd_mono hxy h))
    (fun ⟨z, h1, h2⟩ => Or.inr ⟨z, Dd_mono hxy h1, h2⟩)⟩

end DSG

end Elle.R4

import Jank.Multi

/-!
# Multimethod dispatch: where jank's preference walk and Clojure's agree (round 3, proofs)

Round 2's `Jank.Multi.no_prefs_same` is already a theorem for every hierarchy (any `H`, not only
those built by `derive`), every method table and every dispatch value, without preferences: the
search's 2,048,000 programs (4 tags, 3 methods, no prefers) are a special case of it. Here the
statement is widened to preferences:

- `jank_prefers_direct`: jank's dispatch (`is_preferred` walking the *var*, R100) sees exactly the
  preferences declared between the two dispatch values themselves;
- `clj_prefers_of_direct`: Clojure's walk sees those too;
- `root_methods_same`: when every method is defined on a tag without parents (the diamond case
  `prefer-method` exists for: a value deriving from two roots that both have methods), jank's
  dispatch equals Clojure's for every hierarchy, method table, preference table and dispatch
  value; R100 needs a method on a tag with parents and a preference reached through them;
- `agree_of_dominates_agree`: in general, the two dispatches agree whenever the two `dominates`
  agree on the pairs of method tags (the only place the hierarchy argument enters).
-/

namespace Jank.R3.Proofs.Multi

open Jank.Multi

/-- jank's preference walk (the hierarchy argument is the var: `none`) is the direct lookup. -/
theorem jank_prefers_direct (mm : MM) (f : Nat) (x y : Tag) :
    prefers mm none (f + 1) x y = (look mm.prefers x).contains y := by
  simp [prefers]

/-- Clojure's walk includes the direct preferences. -/
theorem clj_prefers_of_direct (mm : MM) (h : H) (f : Nat) (x y : Tag)
    (hd : (look mm.prefers x).contains y = true) : prefers mm (some h) (f + 1) x y = true := by
  simp only [prefers, hd, Bool.true_or]

/-- For two tags without parents, Clojure's walk is the direct lookup too. -/
theorem clj_prefers_roots (mm : MM) (h : H) (f : Nat) (x y : Tag)
    (hx : look h.parents x = []) (hy : look h.parents y = []) :
    prefers mm (some h) (f + 1) x y = (look mm.prefers x).contains y := by
  simp [prefers, hx, hy]

/-- `dominates` agrees on two parentless tags. -/
theorem dominates_roots (mm : MM) (h : H) (x y : Tag)
    (hx : look h.parents x = []) (hy : look h.parents y = []) :
    dominates mm h none x y = dominates mm h (some h) x y := by
  unfold dominates
  rw [show (16 : Nat) = 15 + 1 from rfl, jank_prefers_direct, clj_prefers_roots mm h 15 x y hx hy]

/-- `bestMethod` with its dominance relation as a parameter: the same code
(multi_function.cpp 261 `find_and_cache_best_method` / MultiFn.findAndCacheBestMethod). -/
def bestD (mm : MM) (h : H) (d : Tag → Tag → Bool) (dv : Tag) : Out := Id.run do
  let mut best : Option Tag := none
  for e in mm.methods do
    if let some k := e then
      if isa h dv k then
        match best with
        | none => best := some k
        | some b => if d k b then best := some k
        let b := best.getD k
        if !d b k then return .ambiguous k b
  match best with
  | some b => return .method b
  | none => return (if mm.methods.contains none then .deflt else .noMethod)

theorem bestMethod_eq (mm : MM) (h : H) (hier : Option H) (dv : Tag) :
    bestMethod mm h hier dv = bestD mm h (dominates mm h hier) dv := rfl

theorem forIn_congr_inv {α β : Type} (P : β → Prop) (f g : α → β → Id (ForInStep β)) :
    ∀ (xs : List α), (∀ a ∈ xs, ∀ b, P b → f a b = g a b) →
      (∀ a ∈ xs, ∀ b, P b → ∀ b', f a b = .yield b' → P b') →
      ∀ b, P b → forIn xs b f = forIn xs b g
  | [], _, _, b, _ => rfl
  | a :: as, hfg, hP, b, hb => by
    simp only [List.forIn_cons]
    rw [hfg a List.mem_cons_self b hb]
    cases hg : g a b with
    | done b' => rfl
    | yield b' =>
      have hb' : P b' := hP a List.mem_cons_self b hb b' (by rw [hfg a List.mem_cons_self b hb, hg])
      exact forIn_congr_inv P f g as (fun a' ha' => hfg a' (List.mem_cons_of_mem _ ha'))
        (fun a' ha' => hP a' (List.mem_cons_of_mem _ ha')) b' hb'

/-- The dispatch only asks `d` about pairs of method tags: two relations that agree there give
the same answer. -/
theorem bestD_congr (mm : MM) (h : H) (d1 d2 : Tag → Tag → Bool) (dv : Tag)
    (hd : ∀ x y, some x ∈ mm.methods → some y ∈ mm.methods → d1 x y = d2 x y) :
    bestD mm h d1 dv = bestD mm h d2 dv := by
  unfold bestD
  simp only [Id.run]
  congr 1
  apply forIn_congr_inv (fun (s : Option Out × Option Tag) => ∀ b, s.2 = some b → some b ∈ mm.methods)
  · intro e he s hs
    rcases e with _ | k
    · rfl
    · simp only
      split
      · rcases hb : s.2 with _ | b
        · simp only [Option.getD_some]
          rw [hd k k he he]
        · simp only
          have hbm := hs b hb
          rw [hd k b he hbm]
          split
          · simp only [Option.getD_some]; rw [hd k k he he]
          · simp only [Option.getD_some]; rw [hd b k hbm he]
      · rfl
  · intro e he s hs s' hs'
    rcases e with _ | k
    · simp only [pure] at hs'; injection hs' with hs'; subst hs'; exact hs
    · simp only at hs'
      split at hs'
      · rcases hb : s.2 with _ | b
        · rw [hb] at hs'; simp only at hs'
          split at hs'
          · cases hs'
          · injection hs' with hs'; subst hs'; intro b' hb'; simp at hb'; subst hb'; exact he
        · rw [hb] at hs'; simp only at hs'
          split at hs'
          · split at hs'
            · cases hs'
            · injection hs' with hs'; subst hs'; intro b' hb'; simp at hb'; subst hb'; exact he
          · split at hs'
            · cases hs'
            · injection hs' with hs'; subst hs'; intro b' hb'; simp at hb'; subst hb'; exact hs b hb
      · injection hs' with hs'; subst hs'; exact hs
  · intro b hb; cases hb

/-- jank's dispatch equals Clojure's whenever the two dominance relations agree on method tags. -/
theorem agree_of_dominates_agree (mm : MM) (h : H) (dv : Tag)
    (hd : ∀ x y, some x ∈ mm.methods → some y ∈ mm.methods →
      dominates mm h none x y = dominates mm h (some h) x y) :
    jankCall mm h dv = cljCall mm h dv := by
  unfold jankCall cljCall
  rw [bestMethod_eq, bestMethod_eq]
  exact bestD_congr mm h _ _ dv hd

/-- Methods on parentless tags: jank's dispatch is Clojure's, whatever the preferences. -/
theorem root_methods_same (mm : MM) (h : H) (dv : Tag)
    (hroot : ∀ k, some k ∈ mm.methods → look h.parents k = []) :
    jankCall mm h dv = cljCall mm h dv :=
  agree_of_dominates_agree mm h dv fun x y hx hy => dominates_roots mm h x y (hroot x hx) (hroot y hy)

/-- Round 2's theorem again, as a corollary: no preferences, every input. -/
theorem no_prefs_same' (methods : List (Option Tag)) (h : H) (dv : Tag) :
    jankCall { methods, prefers := [] } h dv = cljCall { methods, prefers := [] } h dv :=
  no_prefs_same methods h dv

end Jank.R3.Proofs.Multi

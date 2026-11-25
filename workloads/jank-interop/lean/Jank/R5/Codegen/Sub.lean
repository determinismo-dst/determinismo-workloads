import Jank.R5.Codegen.Gen

/-!
# Round 5, codegen: the three-subexpression roots over a smaller child world

The depth-2 world is 354,197,993,668 timelines, of which `let2` (312,527,871,808) and `if`
(41,565,561,344) have three depth-1 subexpressions each. `subWorld` keeps those two root kinds and
draws each depth-1 subexpression from the productions that hold at most one leaf subexpression
(`kindsK1`: the leaves, `log`, `identity`, `loop`, `def`, `case`, `loop2`, `list?`, `3`,
`case1`), so every pair and triple of siblings among them meets: constants shared across
siblings, loops and defs side by side, values of every leaf kind in the condition and both
branches. ★ `subWorld_size` gives its exact size.
-/

namespace Jank.R5.Codegen

open Jank.Codegen Jank.Analyzer
open Jank.Codegen.ProgSearch (Ctx)
open DT

theorem bind_assoc {α β γ : Type} (t : DT α) (g : α → DT β) (f : β → DT γ) :
    DT.bind (DT.bind t g) f = DT.bind t (fun a => DT.bind (g a) f) := by
  induction t with
  | ret a => rfl
  | node name n k ih => simp only [DT.bind, ih]

/-- A pick among two or more values, then a continuation: the sum over the values. -/
theorem leaves_pick_bind {β : Type} (name : String) (a : Nat) (rest : List Nat) (h : 1 ≤ rest.length)
    (f : Option Nat → DT β) :
    leaves (pick name (a :: rest) >>= f) =
      sumFin (rest.length + 1) (fun i => leaves (f (some ((a :: rest).getD i.val a)))) := by
  have hn : ¬ (rest.length + 1 ≤ 1) := by omega
  simp only [bind_eq, pick, bind_assoc, dec, List.length_cons, hn, ite_false, DT.bind, leaves]

/-- The depth-1 productions with at most one subexpression. -/
def kindsK1 : List Nat := [0, 1, 2, 3, 4, 5, 9, 13, 15, 16, 17, 18, 19]

/-- genE at depth 1 with its kind drawn from `kindsK1`. -/
def genK1 (c : Ctx) (tail : Bool) : DT Form :=
  pick "expr.kind" kindsK1 >>= fun o => kindT (genT 0) 1 c tail (o.getD 0)

def cntK1 (n : Nat) : Nat := sumFin kindsK1.length (fun i => kindCount (cnt 0) n (kindsK1.getD i.val 0))

theorem leaves_genK1 : Counts genK1 cntK1 := by
  intro c t h
  have h1 := leaves_pick_bind "expr.kind" 0 [1, 2, 3, 4, 5, 9, 13, 15, 16, 17, 18, 19] (by decide)
    (fun o => kindT (genT 0) 1 c t (o.getD 0))
  exact h1.trans (sumFin_congr _ _ _ (fun i => leaves_kindT (genT 0) (cnt 0) (leaves_genT 0) 1 c t h _))

/-- The root kinds kept: `let2` (8) and `if` (10). -/
def rootsK3 : List Nat := [8, 10]

def subWorld : DT Form :=
  pick "expr.kind" rootsK3 >>= fun o => kindT genK1 2 root true (o.getD 0)

/-- ★ The sub-world's exact size. -/
theorem subWorld_size : leaves subWorld = 9246393 := by
  have h1 := leaves_pick_bind "expr.kind" 8 [10] (by decide) (fun o => kindT genK1 2 root true (o.getD 0))
  have h2 := sumFin_congr ([10].length + 1) _
    (fun i => kindCount cntK1 ([] : List String).length ((some ((8 :: [10]).getD i.val 8)).getD 0))
    (fun i => leaves_kindT genK1 cntK1 leaves_genK1 2 root true rfl _)
  have h3 : sumFin ([10].length + 1)
      (fun i => kindCount cntK1 ([] : List String).length ((some ((8 :: [10]).getD i.val 8)).getD 0)) =
      9246393 := by decide
  exact h1.trans (h2.trans h3)

end Jank.R5.Codegen

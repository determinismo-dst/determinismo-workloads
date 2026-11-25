import Jank.Codegen.ProgSearch
import Jank.R5.Codegen.Tree

/-!
# Round 5, codegen: round 2's clean program generator as a decision tree

`Jank.Codegen.ProgSearch.genE`/`genFnCall` are `partial`, so nothing can be proved about them.
`genT` restates them for the clean grammar (`Ctx.clean = true`, round 2's control: every
production of a known deviation left out) as a `DT`, line by line, with the same decisions in
the same order and the same names and option counts. `Run/R5/Codegen.lean` checks the
restatement against the original on every depth-1 timeline, on every timeline of the small
depth-2 partitions, and on random depth-2 timelines (forms and decisions identical).

On it:
- `cnt d n`: the number of timelines at depth `d` with `n` locals in scope, and
  ★ `leaves_genT`: the tree has exactly `cnt d c.locals.length` timelines for every context
  without a recur target (the clean grammar builds no other: every context it passes down keeps
  `recurArity = none`, which the proof carries as its hypothesis, so kind 14 always draws a `try`).
- `cnt 2 0`, the size of round 2's depth-2 control, as a number (`world2`), and per root kind.
-/

namespace Jank.R5.Codegen

open Jank.Codegen Jank.Analyzer
open Jank.Codegen.ProgSearch (Ctx kw int)
open DT

def caseTests : List Int := [0, 2147483647, 2147483648, 4294967296]

/-- `pickName name c` in the clean grammar (ProgSearch.lean 51–52): `x` or `y`. -/
def pickNameT (name : String) : DT String :=
  pick name ["x", "y"] >>= fun o => pure (o.getD "x")

/-- The vector/list literals (kind 3; clean: `[]` and `()`). -/
def litOf (v : Nat) : Form :=
  match v with
  | 0 => .vec [.vec []]
  | 1 => .vec [.lit (.persistentList none [])]
  | 2 => .vec []
  | _ => .lit (.persistentList none [])

/-- Kind 2: a local, or 0 when none is in scope. -/
def localT (c : Ctx) : DT Form :=
  match c.locals with
  | [] => pure (int 0)
  | _ => pick "expr.local" c.locals >>= fun o => pure (.sym (o.getD "x"))

/-- The leaves (genE at depth 0: kinds 0–3). -/
def leafKindT (c : Ctx) (k : Nat) : DT Form :=
  match k with
  | 0 => dec "expr.int" 3 >>= fun i => pure (int i)
  | 1 => pick "expr.kw" ["a", "b"] >>= fun o => pure (kw (o.getD "a"))
  | 2 => localT c
  | _ => dec "expr.lit" 2 >>= fun v => pure (litOf (v + 2))

def leafT (c : Ctx) : DT Form := dec "expr.kind" 4 >>= fun k => leafKindT c k

/-- The def's metadata value (kind 13, clean). -/
def defMeta (m : Nat) : JV :=
  match m with
  | 0 => .int 1
  | 1 => .list [.sym "" "quote" none, .vec [.sym "" "x" none] none] none
  | _ => .int 2

/-- genFnCall (clean: kinds 0–2), the subexpressions drawn by `g` (genE one level down). -/
def fnKindT (g : Ctx → Bool → DT Form) (c : Ctx) (k : Nat) : DT Form :=
  match k with
  | 0 =>
    pickNameT "fn.param" >>= fun p =>
    g { c with locals := p :: c.locals, recurArity := none } true >>= fun body =>
    g c false >>= fun arg =>
    pure (.call (.fn_ none [p] [body]) [arg])
  | 1 =>
    pickNameT "fn.param" >>= fun p =>
    let q := if p == "acc" then "acc2" else "acc"
    g { c with locals := q :: p :: c.locals, recurArity := none } false >>= fun body =>
    pure (.call (.fn_ (some "self") [p, q]
      [.if_ (.call (.sym "pos?") [.sym p]) (.recur [.call (.sym "dec") [.sym p], .call (.sym "add") [.sym q, int 1]])
        (some (.vector2 (.sym q) body))]) [int 2, int 0])
  | _ =>
    pick "fn.name" ["self"] >>= fun o =>
    let fname := o.getD "self"
    pure (.call (.call (.fn_ (some fname) [] [.fn_ none [] [.sym fname]]) []) [])

def fnCallT (g : Ctx → Bool → DT Form) (c : Ctx) : DT Form :=
  dec "fn.kind" 3 >>= fun k => fnKindT g c k

/-- One production of genE above depth 0 (ProgSearch.lean 60–152, clean branches), the
subexpressions drawn by `g`. -/
def kindT (g : Ctx → Bool → DT Form) (depth : Nat) (c : Ctx) (tail : Bool) (k : Nat) : DT Form :=
  match k with
  | 0 => dec "expr.int" 3 >>= fun i => pure (int i)
  | 1 => pick "expr.kw" ["a", "b"] >>= fun o => pure (kw (o.getD "a"))
  | 2 => localT c
  | 3 => dec "expr.lit" 2 >>= fun v => pure (litOf (v + 2))
  | 4 => g c false >>= fun e => pure (.call (.sym "log") [e])
  | 5 => g c false >>= fun e => pure (.call (.sym "identity") [e])
  | 6 => g c false >>= fun a => g c false >>= fun b => pure (.call (.sym "vector") [a, b])
  | 7 =>
    pickNameT "let.name" >>= fun n =>
    g c false >>= fun v =>
    g { c with locals := n :: c.locals } tail >>= fun body =>
    pure (.let_ [(n, v)] [body])
  | 8 =>
    pickNameT "let2.name1" >>= fun n1 =>
    pickNameT "let2.name2" >>= fun n2 =>
    g c false >>= fun v1 =>
    g { c with locals := n1 :: c.locals } false >>= fun v2 =>
    g { c with locals := n2 :: n1 :: c.locals } tail >>= fun body =>
    pure (.let_ [(n1, v1), (n2, v2)] [body])
  | 9 =>
    let n := s!"L{depth}"
    dec "loop.init" 3 >>= fun init =>
    g { c with locals := n :: c.locals, recurArity := none } false >>= fun body =>
    pure (.loop [(n, int init)] [.if_ (.call (.sym "lt") [.sym n, int 2])
      (.recur [.call (.sym "inc") [.sym n]]) (some body)])
  | 10 =>
    g c false >>= fun cond => g c tail >>= fun th => g c tail >>= fun el =>
    pure (.if_ cond th (some el))
  | 11 => g c false >>= fun a => g c tail >>= fun b => pure (.do_ [a, b])
  | 12 => fnCallT g c
  | 13 =>
    pick "def.name" ["v", "w"] >>= fun o =>
    let vname := o.getD "v"
    dec "def.meta" 3 >>= fun m =>
    g c false >>= fun v =>
    pure (.do_ [.def_ vname [("k", defMeta m)] (some v),
                .vec [.sym vname, .call (.sym "meta-of") [.varq vname]]])
  | 14 =>
    if c.recurArity.isSome then g c tail
    else
      g { c with inTry := true } false >>= fun body =>
      g { c with inTry := true } false >>= fun h =>
      dec "try.finally" 2 >>= fun fin =>
      pure (.try_ [.call (.sym "log") [body], .throw_ (kw "boom")] (some ("e", [h]))
        (if fin == 1 then some [.call (.sym "log") [kw "fin"]] else none))
  | 15 =>
    dec "case.value" 2 >>= fun v =>
    pure (.case_ (int (caseTests.getD v 0)) [(caseTests.getD v 0, kw "hit"), (1, kw "one")] (kw "miss"))
  | 16 =>
    let n := s!"M{depth}"
    g { c with locals := n :: c.locals, recurArity := none } false >>= fun z =>
    pure (.loop [(n, int 0)] [.let_ [("z", z)] [.if_ (.call (.sym "lt") [.sym n, int 2])
      (.recur [.call (.sym "inc") [.sym n]]) (some (.sym "z"))]])
  | 17 => g c false >>= fun e => pure (.call (.sym "list?") [.call (.sym "first") [e]])
  | 18 => pure (int 3)
  | _ =>
    dec "case1.value" 2 >>= fun v =>
    pure (.case_ (int (caseTests.getD v 0)) [(caseTests.getD v 0, kw "hit")] (kw "miss"))

/-- `genE depth c tail` with `c.clean = true`, as a decision tree. -/
def genT : Nat → Ctx → Bool → DT Form
  | 0, c, _ => leafT c
  | d + 1, c, tail => dec "expr.kind" 20 >>= fun k => kindT (genT d) (d + 1) c tail k

/-! ## Counting -/

theorem leaves_bind_eq {α β : Type} (t : DT α) (f : α → DT β) (a b : Nat)
    (ht : leaves t = a) (hf : ∀ x, leaves (f x) = b) : leaves (t >>= f) = a * b := by
  rw [leaves_bind_const' t f b hf, ht]

theorem leaves_dec_bind {β : Type} (name : String) (n : Nat) (h : 2 ≤ n) (f : Nat → DT β) :
    leaves (dec name n >>= f) = sumFin n (fun i => leaves (f i.val)) := by
  have : ¬ n ≤ 1 := by omega
  simp only [bind_eq, dec, this, ite_false, DT.bind, leaves]

theorem leaves_localT (c : Ctx) : leaves (localT c) = max 1 c.locals.length := by
  unfold localT
  split
  · rename_i h; simp [h, leaves_pure]
  · rename_i h
    rw [leaves_bind_eq _ _ (max 1 c.locals.length) 1 (leaves_pick _ _) (fun _ => rfl)]
    simp

def leafKindCount (n : Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 3 * 1
  | 1 => 2 * 1
  | 2 => max 1 n
  | _ => 2 * 1

def leafCount (n : Nat) : Nat := sumFin 4 (fun i => leafKindCount n i.val)

/-- genFnCall's kinds, counted with `C m` timelines for a subexpression with `m` locals. -/
def fnKindCount (C : Nat → Nat) (n : Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 2 * (C (n + 1) * (C n * 1))
  | 1 => 2 * (C (n + 2) * 1)
  | _ => 1 * 1

/-- genE's kinds above depth 0, counted with `C m` timelines for a subexpression with `m`
locals. -/
def kindCount (C : Nat → Nat) (n : Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 3 * 1
  | 1 => 2 * 1
  | 2 => max 1 n
  | 3 => 2 * 1
  | 4 => C n * 1
  | 5 => C n * 1
  | 6 => C n * (C n * 1)
  | 7 => 2 * (C n * (C (n + 1) * 1))
  | 8 => 2 * (2 * (C n * (C (n + 1) * (C (n + 2) * 1))))
  | 9 => 3 * (C (n + 1) * 1)
  | 10 => C n * (C n * (C n * 1))
  | 11 => C n * (C n * 1)
  | 12 => sumFin 3 (fun i => fnKindCount C n i.val)
  | 13 => 2 * (3 * (C n * 1))
  | 14 => C n * (C n * (2 * 1))
  | 15 => 2 * 1
  | 16 => C (n + 1) * 1
  | 17 => C n * 1
  | 18 => 1
  | _ => 2 * 1

/-- The number of timelines of `genE d` with `n` locals in scope (no recur target). -/
def cnt : Nat → Nat → Nat
  | 0, n => leafCount n
  | d + 1, n => sumFin 20 (fun i => kindCount (cnt d) n i.val)

theorem leaves_leafT (c : Ctx) : leaves (leafT c) = leafCount c.locals.length := by
  unfold leafT leafCount
  rw [leaves_dec_bind _ _ (by decide)]
  apply sumFin_congr
  intro i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => exact leaves_localT c
  | ⟨3, _⟩ => rfl

/-- What `g` must satisfy: `C m` timelines with `m` locals, for every context without a recur
target. -/
def Counts (g : Ctx → Bool → DT Form) (C : Nat → Nat) : Prop :=
  ∀ c t, c.recurArity = none → leaves (g c t) = C c.locals.length

theorem ext_count {g : Ctx → Bool → DT Form} {C : Nat → Nat} (hg : Counts g C) (c : Ctx) (t : Bool)
    (m : Nat) (h : c.recurArity = none) (hm : c.locals.length = m) : leaves (g c t) = C m := by
  rw [hg c t h, hm]

theorem leaves_fnKindT (g : Ctx → Bool → DT Form) (C : Nat → Nat) (hg : Counts g C)
    (c : Ctx) (h : c.recurArity = none) (k : Nat) :
    leaves (fnKindT g c k) = fnKindCount C c.locals.length k := by
  unfold fnKindT fnKindCount
  split
  · refine leaves_bind_eq _ _ _ _ rfl ?_; intro p
    refine leaves_bind_eq _ _ _ _ ?_ ?_
    · exact ext_count hg _ _ _ (by simp) (by simp)
    intro body
    exact leaves_bind_eq _ _ _ _ (hg _ _ h) (fun _ => rfl)
  · refine leaves_bind_eq _ _ _ _ rfl ?_; intro p
    exact leaves_bind_eq _ _ _ _ (ext_count hg _ _ _ (by simp) (by simp)) (fun _ => rfl)
  · exact leaves_bind_eq _ _ _ _ rfl (fun _ => rfl)

theorem leaves_fnCallT (g : Ctx → Bool → DT Form) (C : Nat → Nat) (hg : Counts g C)
    (c : Ctx) (h : c.recurArity = none) :
    leaves (fnCallT g c) = sumFin 3 (fun i => fnKindCount C c.locals.length i.val) := by
  unfold fnCallT
  rw [leaves_dec_bind _ _ (by decide)]
  exact sumFin_congr _ _ _ (fun i => leaves_fnKindT g C hg c h i.val)

theorem leaves_kindT (g : Ctx → Bool → DT Form) (C : Nat → Nat) (hg : Counts g C)
    (depth : Nat) (c : Ctx) (t : Bool) (h : c.recurArity = none) (k : Nat) :
    leaves (kindT g depth c t k) = kindCount C c.locals.length k := by
  have hl : ∀ (c' : Ctx) (t' : Bool), c'.recurArity = none → leaves (g c' t') = C c'.locals.length :=
    hg
  unfold kindT kindCount
  split
  · rfl
  · rfl
  · exact leaves_localT c
  · rfl
  · exact leaves_bind_eq _ _ _ _ (hl c false h) (fun _ => rfl)
  · exact leaves_bind_eq _ _ _ _ (hl c false h) (fun _ => rfl)
  · exact leaves_bind_eq _ _ _ _ (hl c false h)
      (fun _ => leaves_bind_eq _ _ _ _ (hl c false h) (fun _ => rfl))
  · refine leaves_bind_eq _ _ _ _ rfl ?_; intro n
    refine leaves_bind_eq _ _ _ _ (hl c false h) ?_; intro v
    exact leaves_bind_eq _ _ _ _ (ext_count hg _ _ _ (by simp [h]) (by simp)) (fun _ => rfl)
  · refine leaves_bind_eq _ _ _ _ rfl ?_; intro n1
    refine leaves_bind_eq _ _ _ _ rfl ?_; intro n2
    refine leaves_bind_eq _ _ _ _ (hl c false h) ?_; intro v1
    refine leaves_bind_eq _ _ _ _ (ext_count hg _ _ _ (by simp [h]) (by simp)) ?_; intro v2
    exact leaves_bind_eq _ _ _ _ (ext_count hg _ _ _ (by simp [h]) (by simp)) (fun _ => rfl)
  · refine leaves_bind_eq _ _ _ _ rfl ?_; intro i
    exact leaves_bind_eq _ _ _ _ (ext_count hg _ _ _ (by simp) (by simp)) (fun _ => rfl)
  · refine leaves_bind_eq _ _ _ _ (hl c false h) ?_; intro a
    refine leaves_bind_eq _ _ _ _ (hl c t h) ?_; intro b
    exact leaves_bind_eq _ _ _ _ (hl c t h) (fun _ => rfl)
  · refine leaves_bind_eq _ _ _ _ (hl c false h) ?_; intro a
    exact leaves_bind_eq _ _ _ _ (hl c t h) (fun _ => rfl)
  · exact leaves_fnCallT g C hg c h
  · refine leaves_bind_eq _ _ _ _ rfl ?_; intro o
    refine leaves_bind_eq _ _ _ _ rfl ?_; intro m
    exact leaves_bind_eq _ _ _ _ (hl c false h) (fun _ => rfl)
  · simp only [h, Option.isSome_none, Bool.false_eq_true, ite_false]
    refine leaves_bind_eq _ _ _ _ (ext_count hg _ _ _ rfl (by simp)) ?_; intro b
    refine leaves_bind_eq _ _ _ _ (ext_count hg _ _ _ rfl (by simp)) ?_; intro hh
    exact leaves_bind_eq _ _ _ _ rfl (fun _ => rfl)
  · exact leaves_bind_eq _ _ _ _ rfl (fun _ => rfl)
  · exact leaves_bind_eq _ _ _ _ (ext_count hg _ _ _ (by simp) (by simp)) (fun _ => rfl)
  · exact leaves_bind_eq _ _ _ _ (hl c false h) (fun _ => rfl)
  · rfl
  · exact leaves_bind_eq _ _ _ _ rfl (fun _ => rfl)

/-- ★ The decision tree of genE (clean grammar) at depth `d` has exactly `cnt d n` timelines,
`n` the number of locals in scope, for every context without a recur target. -/
theorem leaves_genT (d : Nat) : Counts (genT d) (cnt d) := by
  induction d with
  | zero => intro c t _; exact leaves_leafT c
  | succ d ih =>
    intro c t h
    show leaves (dec "expr.kind" 20 >>= fun k => kindT (genT d) (d + 1) c t k) = _
    rw [leaves_dec_bind _ _ (by decide)]
    exact sumFin_congr _ _ _ (fun i => leaves_kindT (genT d) (cnt d) ih (d + 1) c t h i.val)

/-- Round 2's control world, the root context (`{ clean := true }`, tail position). -/
def root : Ctx := { clean := true }

/-- ★ Round 2's depth-1 control world has exactly 3,464 timelines (round 2's complete walk). -/
theorem world1 : leaves (genT 1 root true) = 3464 := by
  rw [leaves_genT 1 root true rfl]; decide

end Jank.R5.Codegen

namespace Jank.R5.Codegen

/-- ★ Round 2's depth-2 control world has exactly 354,197,993,668 timelines (round 4's Knuth
estimate: ≈3.3·10¹¹). -/
theorem world2 : DT.leaves (genT 2 root true) = 354197993668 := by
  rw [leaves_genT 2 root true rfl]; decide

end Jank.R5.Codegen

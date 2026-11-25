/-!
# Round 5, codegen: decision trees

A generator drawn by `Determinismo.decide`/`pick` is a tree: each recorded decision is a node
with one child per option (a decision with one option is not recorded, so it is no node), and a
timeline is a root-to-leaf path. `DT` is that tree as a monad, so a generator written in it can
be counted (`leaves`) and run along a path (`walk`), with the counting rules proved once.
-/

namespace Jank.R5.Codegen

/-- A decision tree whose leaves carry values of `α`. -/
inductive DT (α : Type) where
  | ret (a : α)
  | node (name : String) (n : Nat) (k : Fin n → DT α)

namespace DT

def bind {α β : Type} : DT α → (α → DT β) → DT β
  | ret a, f => f a
  | node name n k, f => node name n (fun i => bind (k i) f)

instance : Monad DT where
  pure := ret
  bind := bind

/-- `∑ i < n, f i` over `Fin n`. -/
def sumFin : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + sumFin n (fun i => f i.succ)

/-- The number of timelines (root-to-leaf paths). -/
def leaves {α : Type} : DT α → Nat
  | ret _ => 1
  | node _ n k => sumFin n (fun i => leaves (k i))

theorem sumFin_congr (n : Nat) (f g : Fin n → Nat) (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumFin, h 0, ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)]

theorem sumFin_mul (n : Nat) (f : Fin n → Nat) (c : Nat) :
    sumFin n (fun i => f i * c) = sumFin n f * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp only [sumFin, ih (fun i => f i.succ), Nat.add_mul]

theorem sumFin_const (n c : Nat) : sumFin n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih => simp only [sumFin, ih, Nat.succ_mul]; omega

/-- Binding a continuation whose every tree has `c` timelines multiplies by `c`. -/
theorem leaves_bind_const {α β : Type} (t : DT α) (f : α → DT β) (c : Nat)
    (h : ∀ a, leaves (f a) = c) : leaves (bind t f) = leaves t * c := by
  induction t with
  | ret a => simp [bind, leaves, h]
  | node name n k ih =>
    simp only [bind, leaves]
    rw [sumFin_congr n _ _ ih, sumFin_mul]

theorem leaves_pure {α : Type} (a : α) : leaves (pure a : DT α) = 1 := rfl

theorem bind_eq {α β : Type} (t : DT α) (f : α → DT β) : (t >>= f) = bind t f := rfl

theorem leaves_bind_const' {α β : Type} (t : DT α) (f : α → DT β) (c : Nat)
    (h : ∀ a, leaves (f a) = c) : leaves (t >>= f) = leaves t * c :=
  leaves_bind_const t f c h

/-- `Determinismo.decide name n`: a node when there are two options or more. -/
def dec (name : String) (n : Nat) : DT Nat :=
  if n ≤ 1 then ret 0 else node name n (fun i => ret i.val)

theorem leaves_dec (name : String) (n : Nat) : leaves (dec name n) = max 1 n := by
  unfold dec
  split
  · simp [leaves]; omega
  · simp only [leaves]
    rw [sumFin_const]; omega

/-- `Determinismo.pick name items` (Decide.lean `pick`: `items.getD (decide name items.length) first`). -/
def pick {α : Type} (name : String) (items : List α) : DT (Option α) :=
  match items with
  | [] => ret none
  | first :: _ => bind (dec name items.length) (fun i => ret (some (items.getD i first)))

theorem leaves_pick {α : Type} (name : String) (items : List α) :
    leaves (pick name items) = max 1 items.length := by
  unfold pick
  split
  · simp [leaves]
  · rw [leaves_bind_const _ _ 1 (fun _ => rfl), leaves_dec]; simp

/-- The value at the end of a path and the decisions taken (a path's values past a node's options
wrap, as `Decisions.next` does; past its end the first option is taken). `none` only at a node
with no option, which `dec` never builds. -/
def walk {α : Type} : DT α → List Nat → Option (α × List (String × Nat × Nat))
  | ret a, _ => some (a, [])
  | node name n k, path =>
    if h : 0 < n then
      let i : Fin n := ⟨path.headD 0 % n, Nat.mod_lt _ h⟩
      (walk (k i) path.tail).map fun (a, ds) => (a, (name, n, i.val) :: ds)
    else none

/-- Every timeline: the value and the decisions of each leaf, in exhaust order. Only for small
trees. -/
def all {α : Type} : DT α → List (α × List Nat)
  | ret a => [(a, [])]
  | node _ n k => (List.finRange n).flatMap fun i => (all (k i)).map fun (a, p) => (a, i.val :: p)

end DT

end Jank.R5.Codegen

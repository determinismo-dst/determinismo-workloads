/-!
# Persistent vector: jank's index checks (persistent_vector.cpp, core/seq.cpp `subvec`)

The vector's storage is immer's RRB vector (third-party/immer). Its tree arithmetic is immer's,
not jank's, and is abstracted here as a `List` (assumption A-vec in the report). What is jank's
own code is the layer of bounds checks and dispatch around it, modeled here function by
function, beside Clojure's documented behavior (APersistentVector / PersistentVector).
-/

namespace Jank.Vector

/-- A key: an integer (`is_integral`: small, heap or big integer) or something else. -/
inductive Key where
  | int (i : Int)
  | other
  deriving Repr, BEq

variable {α : Type}

/-- persistent_vector.cpp `get(key, fallback)`. -/
def get (v : List α) (key : Key) (fallback : α) : α :=
  match key with
  | .int i => if i < 0 ∨ v.length ≤ i.toNat then fallback else v.getD i.toNat fallback
  | .other => fallback

/-- persistent_vector.cpp `nth(index)`: out of bounds or non-integer → throws (none). -/
def nth (v : List α) (key : Key) : Option α :=
  match key with
  | .int i => if i < 0 ∨ v.length ≤ i.toNat then none else v[i.toNat]?
  | .other => none

/-- persistent_vector.cpp `contains(key)`. -/
def contains (v : List α) (key : Key) : Bool :=
  match key with
  | .int i => i ≥ 0 && decide (i.toNat < v.length)
  | .other => false

/-- persistent_vector.cpp `assoc(key, val)`: non-integer or `i > size || 0 > i` → throws;
`i == size` → `push_back`; else `set`. -/
def assoc (v : List α) (key : Key) (x : α) : Option (List α) :=
  match key with
  | .int i =>
    if i > v.length ∨ 0 > i then none
    else if i.toNat == v.length then some (v ++ [x])
    else some (v.set i.toNat x)
  | .other => none

/-- persistent_vector.cpp `pop`: empty → throws; else `take(size - 1)`. -/
def pop (v : List α) : Option (List α) := if v.isEmpty then none else some (v.take (v.length - 1))

/-- core/seq.cpp `subvec(o, start, end)`. -/
def subvec (v : List α) (s e : Int) : Option (List α) :=
  if e < s ∨ s < 0 ∨ e > v.length then none
  else if s == e then some []
  else some ((v.drop s.toNat).take (e - s).toNat)

/-! ## Laws (Clojure's documented behavior), proved of jank's checks -/

theorem get_in_range (v : List α) (i : Nat) (h : i < v.length) (fb : α) :
    get v (.int i) fb = v[i] := by
  have h0 : ¬ ((i : Int) < 0 ∨ v.length ≤ (i : Int).toNat) := by omega
  simp only [get, h0, if_false]
  simp [List.getD, h]

theorem get_out_of_range (v : List α) (i : Int) (h : ¬ (0 ≤ i ∧ i.toNat < v.length)) (fb : α) :
    get v (.int i) fb = fb := by
  unfold get
  by_cases h1 : i < 0
  · simp [h1]
  · have : v.length ≤ i.toNat := by omega
    simp [this]

theorem contains_iff (v : List α) (i : Int) :
    contains v (.int i) = true ↔ 0 ≤ i ∧ i.toNat < v.length := by
  simp [contains]

/-- `(get v i)` is `(nth v i nil)`, and `nth` without a default throws exactly when `contains?`
is false. -/
theorem nth_some_iff_contains (v : List α) (i : Int) :
    (nth v (.int i)).isSome = contains v (.int i) := by
  unfold nth contains
  by_cases h1 : i < 0
  · simp [h1]; omega
  · by_cases h2 : v.length ≤ i.toNat
    · simp [h1, h2]
    · have : i.toNat < v.length := by omega
      simp [h1, h2, this]; omega

theorem assoc_count (v : List α) (x : α) : assoc v (.int v.length) x = some (v ++ [x]) := by
  simp [assoc]

theorem assoc_get (v : List α) (i : Nat) (h : i < v.length) (x fb : α) :
    (assoc v (.int i) x).map (fun w => get w (.int i) fb) = some x := by
  have h' : ¬ ((i : Int) > v.length ∨ 0 > (i : Int)) := by omega
  have h'' : ((i : Int).toNat == v.length) = false := by simp; omega
  have h3 : ¬ ((i : Int) < 0 ∨ v.length ≤ i) := by omega
  simp only [assoc, h', h'', ite_false, Option.map_some, get, Bool.false_eq_true]
  simp [List.getD, h, h3]

theorem pop_conj (v : List α) (x : α) : pop (v ++ [x]) = some v := by
  simp [pop]

theorem subvec_length (v : List α) (s e : Nat) (h1 : s ≤ e) (h2 : e ≤ v.length) :
    (subvec v s e).map List.length = some (e - s) := by
  unfold subvec
  have hn : ¬ ((e : Int) < s ∨ (s : Int) < 0 ∨ (e : Int) > v.length) := by omega
  simp only [hn, ite_false]
  by_cases hse : s = e
  · subst hse; simp
  · have : ((s : Int) == (e : Int)) = false := by simp; omega
    simp only [this]
    simp [List.length_take, List.length_drop]
    omega

/-! ## Transients after `persistent!` (transient_vector.cpp)

At jank f3d82d654, `count`, `conj_in_place`, `assoc_in_place`, `pop_in_place`, `get`, `call`,
`to_persistent` called `assert_active()`; `nth(index)` (line 53), `find`, `contains` did not
(`tNthF3d`). At jank 7135b7708 `nth(index)` (line 53, `assert_active()` at 55), `find` (199) and
`contains` (220) call it too; `nth(index, fallback)` (76) goes through `get` (178, asserting).
Clojure's `TransientVector.nth` calls `ensureEditable()` ("Transient used after persistent! call"). -/

structure Transient (α : Type) where
  data : List α
  active : Bool

/-- jank f3d82d654 transient_vector.cpp `nth(index)`: no `assert_active()`. -/
def tNthF3d (t : Transient α) (i : Nat) : Except String α :=
  match t.data[i]? with
  | some x => .ok x
  | none => .error "index out of bounds"

/-- jank 7135b7708 transient_vector.cpp:53 `nth(index)`: `assert_active()` first. -/
def tNth (t : Transient α) (i : Nat) : Except String α :=
  if !t.active then .error "This `transient_vector` has already been made persistent."
  else match t.data[i]? with
    | some x => .ok x
    | none => .error "index out of bounds"

/-- Clojure TransientVector.nth: `ensureEditable()` first. -/
def cTNth (t : Transient α) (i : Nat) : Except String α :=
  if !t.active then .error "IllegalAccessError: Transient used after persistent! call"
  else match t.data[i]? with
    | some x => .ok x
    | none => .error "IndexOutOfBoundsException"

/-- jank f3d82d654 (D15): `nth` worked after `persistent!`. -/
theorem transient_nth_after_persistent_f3d82d654 (x : α) :
    (tNthF3d { data := [x], active := false } 0 |>.toOption) = some x ∧
    (cTNth { data := [x], active := false } 0 |>.toOption) = none := by
  simp [tNthF3d, cTNth, Except.toOption]

/-- jank 7135b7708: `nth` after `persistent!` throws, as Clojure's does. -/
theorem transient_nth_after_persistent (x : α) :
    (tNth { data := [x], active := false } 0 |>.toOption) = none ∧
    (cTNth { data := [x], active := false } 0 |>.toOption) = none := by
  simp [tNth, cTNth, Except.toOption]

end Jank.Vector

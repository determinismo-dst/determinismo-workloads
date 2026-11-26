import Jank.Hash

/-!
# Round 7, coordinator: jank's `case` dispatch, stock and corrected

jank 94d32623's `case` macro (src/jank/clojure/core.jank 4300-4531) turns each test constant
into an integer key at macro-expansion time; the compiled `case*` switches on
`jank_shift_mask_case_integer` of the value (c_api.cpp 991-1037, codegen cpp_processor.cpp
1140-1170). A key and the value's integer must agree for the branch to be found.

- **Keys.** `:ints` mode (every test an i64, core.jank `i64?` 4300) keys a test by `int` of it
  (`prep-ints` 4376-4391). `:hashes` mode keys it by `case-hash` (4314-4321): the test itself when
  it is an i32, else `hash`.
- **The value's integer** (c_api.cpp `to_case_integer_or_hash` 991-1012): an integer inside the
  int range is itself, an integer outside it is `hash::integer`, anything else its `to_hash`.
- **Collisions** (`merge-hash-collisions` 4393-4433, `prep-hashes` 4435-4463): tests whose keys
  collide are merged into one `condp` branch keyed by the shared hash, and the keys are computed
  again by `case-hash`; when any collision exists, `case-map-collison-merged` (4351-4362) gives
  the other branches no `condp` check.

The shift/mask step (`shift-mask`, `maybe-min-hash`) applies one function to both a key and a
value's integer, and `maybe-min-hash` keeps the keys distinct, so it is left out: a key equals a
value's integer after the step exactly when it does before.

Clojure's property (Compiler.java CaseExpr, core.clj `case`): the value of the branch whose test
equals the value, else the default.
-/

namespace Jank.R7.Coord.Case

/-- The C++ `i32` range. -/
def inI32 (x : Int) : Bool := decide (-2147483648 ≤ x) && decide (x ≤ 2147483647)

/-- hash.cpp `integer(i64)`: the i64's bits as a u64. -/
def hashInt (x : Int) : Nat :=
  (Jank.Hash.integer (UInt64.ofNat (x % 18446744073709551616).toNat)).toNat

/-- The values a test or a case value can be in this model: an integer (a long), or another
value, named by an id and carrying its jank hash (a `u32`). -/
inductive Val where
  | int (i : Int)
  | other (id : Nat) (h : Nat)
  deriving DecidableEq, Repr

/-- jank's `hash` of a value (`to_hash`). -/
def Val.hash : Val → Nat
  | .int i => hashInt i
  | .other _ h => h

/-- core.jank `case-hash`: an i32 integer is its own key, anything else its hash. -/
def caseHash : Val → Int
  | .int i => if inI32 i then i else hashInt i
  | v => v.hash

/-- c_api.cpp `to_case_integer_or_hash`: what the switch compares with the keys. -/
def valueKey : Val → Int
  | .int i => if inI32 i then i else hashInt i
  | v => v.hash

theorem valueKey_eq_caseHash (v : Val) : valueKey v = caseHash v := by
  cases v <;> rfl

/-! ## Integer tests: the mode (S40's correction, R44) -/

/-- Stock mode choice: `:ints` when every test is an i64 (all longs here), keyed by `int`, which
leaves an i64 as it is (`to_int`). -/
def keyStockInts (t : Int) : Int := t

/-- Round 7's mode choice: `:ints` only when every test is an i32; otherwise `:hashes`. -/
def keyFixed (tests : List Int) (t : Int) : Int :=
  if tests.all inI32 then t else caseHash (.int t)

/-- ★ With round 7's mode, every integer test's key is the integer the switch computes for a
value equal to it, whatever the other tests are. -/
theorem keyFixed_eq_valueKey (tests : List Int) (t : Int) (ht : t ∈ tests) :
    keyFixed tests t = valueKey (.int t) := by
  unfold keyFixed valueKey caseHash
  by_cases hall : tests.all inI32 = true
  · have hi : inI32 t = true := (List.all_eq_true.mp hall) t ht
    simp [hall, hi]
  · simp [hall]

/-- R44 on stock: `(case 2147483648 2147483648 :hit :miss)` keys the test 2147483648, while the
switch computes `hash::integer(2147483648)` = 386683422 for the value. -/
theorem r44_stock_miss :
    keyStockInts 2147483648 = 2147483648 ∧ valueKey (.int 2147483648) = 386683422 := by
  decide +kernel

/-! ## Collisions (X1) -/

/-- A test and its branch's value (`then`), here a `Nat` naming the branch. -/
abbrev Clause := Val × Nat

/-- Clojure's `case`: the branch of the test equal to the value, else the default. -/
def clj (clauses : List Clause) (default : Nat) (v : Val) : Nat :=
  match clauses.find? (fun c => c.1 == v) with
  | some c => c.2
  | none => default

/-- A compiled branch: its key, and either a `condp` over the clauses it covers or no check. -/
structure Branch where
  key : Int
  checked : Bool
  clauses : List Clause

/-- The bucket of a clause: every clause whose `case-hash` it shares. -/
def bucketOf (clauses : List Clause) (c : Clause) : List Clause :=
  clauses.filter (fun d => caseHash d.1 == caseHash c.1)

def hasCollision (clauses : List Clause) : Bool :=
  clauses.any (fun c => (bucketOf clauses c).length > 1)

/-- Stock `prep-hashes` (core.jank 4435-4463). Without a collision, each clause is keyed by its
`case-hash` and checked (`case-map-with-check`). With one, a colliding bucket becomes one checked
branch keyed by `case-hash` of its hash as an integer (the second round), and every lone clause is
keyed by its `case-hash` with no check (`case-map-collison-merged`). -/
def stockBranches (clauses : List Clause) : List Branch :=
  if hasCollision clauses then
    clauses.map fun c =>
      let b := bucketOf clauses c
      if b.length > 1 then ⟨caseHash (.int (caseHash c.1)), true, b⟩
      else ⟨caseHash c.1, false, [c]⟩
  else
    clauses.map fun c => ⟨caseHash c.1, true, [c]⟩

/-- Round 7's X1: every bucket is one checked branch keyed by `case-hash` of its first test, so
its key is the bucket's hash in the second round too. -/
def fixedBranches (clauses : List Clause) : List Branch :=
  clauses.map fun c => ⟨caseHash c.1, true, bucketOf clauses c⟩

/-- The switch: the first branch whose key is the value's integer; a checked branch runs its
`condp` (the first clause equal to the value, else the default), an unchecked one its value. -/
def dispatch (branches : List Branch) (default : Nat) (v : Val) : Nat :=
  match branches.find? (fun b => b.key == valueKey v) with
  | none => default
  | some b =>
    if b.checked then
      match b.clauses.find? (fun c => c.1 == v) with
      | some c => c.2
      | none => default
    else
      match b.clauses with
      | c :: _ => c.2
      | [] => default

theorem find?_filter_imp {α} (l : List α) (p q : α → Bool) (h : ∀ a, p a = true → q a = true) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases hq : q a = true
    · by_cases hp : p a = true
      · simp [hq, hp]
      · simp [hq, hp, ih]
    · have hp : p a = false := by
        cases hpa : p a
        · rfl
        · exact absurd (h a hpa) hq
      simp [hq, hp, ih]

/-- ★ With X1, dispatch is Clojure's `case` for every list of clauses and every value: the first
branch whose key is the value's integer covers exactly the clauses of the value's `case-hash`,
and its `condp` finds the clause equal to the value. -/
theorem fixed_eq_clj (clauses : List Clause) (default : Nat) (v : Val) :
    dispatch (fixedBranches clauses) default v = clj clauses default v := by
  unfold dispatch fixedBranches clj
  rw [valueKey_eq_caseHash, List.find?_map]
  cases hc : clauses.find? ((fun b : Branch => b.key == caseHash v) ∘
      (fun c : Clause => (⟨caseHash c.1, true, bucketOf clauses c⟩ : Branch))) with
  | none =>
    have hnone : clauses.find? (fun c => c.1 == v) = none := by
      rw [List.find?_eq_none] at hc ⊢
      intro x hx hxv
      have : x.1 = v := by simpa using hxv
      exact hc x hx (by simp [this])
    simp [hnone]
  | some c =>
    have hck : caseHash c.1 = caseHash v := by
      have := List.find?_some hc
      simpa using this
    simp only [Option.map_some, if_true]
    have : (bucketOf clauses c).find? (fun d => d.1 == v) = clauses.find? (fun d => d.1 == v) := by
      unfold bucketOf
      apply find?_filter_imp
      intro d hd
      have : d.1 = v := by simpa using hd
      simp [this, hck]
    rw [this]

/-! ## The instances (jank's real hashes) -/

/-- jank's hash of `{}` and of `#{}`: hash.hpp `unordered` of no element, 4279838538 (past the
int range; Clojure's `(hash {})` is the same Murmur3 value, -15128758 as an int). -/
def emptyCollHash : Nat := (Jank.Hash.unorderedRange []).toNat

def emptyMap : Val := .other 0 emptyCollHash
def emptySet : Val := .other 1 emptyCollHash

/-- `(case x {} :map #{} :set :none)` with `:map` = 1, `:set` = 2, `:none` = 0. -/
def collide : List Clause := [(emptyMap, 1), (emptySet, 2)]

/-- `(case x {} :map #{} :set 4294967296 :big :none)` with `:big` = 3. -/
def collideBig : List Clause := [(emptyMap, 1), (emptySet, 2), (.int 4294967296, 3)]

/-- X1 on stock: `{}` misses its branch (its key was hashed again, 4279838538 is not an i32), and
987256456, jank's hash of 4294967296, takes the unchecked `:big` branch. -/
theorem x1_stock :
    emptyCollHash = 4279838538 ∧ hashInt 4294967296 = 987256456 ∧
    dispatch (stockBranches collide) 0 emptyMap = 0 ∧ clj collide 0 emptyMap = 1 ∧
    dispatch (stockBranches collide) 0 emptySet = 0 ∧ clj collide 0 emptySet = 2 ∧
    dispatch (stockBranches collideBig) 0 (.int 987256456) = 3 ∧
    clj collideBig 0 (.int 987256456) = 0 := by
  decide +kernel

/-- The control: without a collision the `4294967296` branch keeps its check. -/
theorem x1_control :
    dispatch (stockBranches [(.int 4294967296, 3)]) 0 (.int 987256456) = 0 := by
  decide +kernel

/-- X1's correction on the same inputs. -/
theorem x1_fixed :
    dispatch (fixedBranches collide) 0 emptyMap = 1 ∧
    dispatch (fixedBranches collide) 0 emptySet = 2 ∧
    dispatch (fixedBranches collideBig) 0 (.int 987256456) = 0 := by
  decide +kernel

end Jank.R7.Coord.Case

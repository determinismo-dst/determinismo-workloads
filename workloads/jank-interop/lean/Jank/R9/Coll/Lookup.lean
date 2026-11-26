set_option linter.deprecated false

/-!
# Round 9, area Coll: a vector's and a string's index (M9-1, M9-2)

jank (94d32623, `upstream-r5/compiler+runtime/`):
- `persistent_vector::get` 218-233, `find` 235-251, `contains` 253-264, `assoc` 266-290, `nth`
  322-341 (persistent_vector.cpp): the key must be `is_integral` (math.cpp 616-624: a small
  integer, an `integer` or a `big_integer`); its value is `to_i64` (math.cpp 10-30), which throws for
  a BigInt past the i64 range (big_integer.cpp `to_i64` 200-208); out of `[0, count)` is the fallback
  (`get`), nil (`find`), false (`contains`) or a throw (`assoc` past `count`, `nth`).
- `persistent_string::get` 78-93 the same; `contains` 95-105 throws for a non-integral key;
  `nth` 107-126 throws for a non-integral key.
- seq.cpp `nth` 648-696 first converts the index with `to_int` (a double truncates) and rejects a
  negative one, then calls the type's `nth` with the original index.

Clojure 1.12 (clojure-ref/src/jvm/clojure/lang):
- APersistentVector.valAt/containsKey/entryAt/assoc/invoke: `Util.isInteger(key)` (Integer, Long,
  BigInt, BigInteger), then `((Number) key).intValue()`: the low 32 bits, as a signed int.
- RT.getFrom / RT.contains / RT.nthFrom on a String: any `Number` key, `intValue()` (a double:
  Java's `(int)` cast, truncation toward zero, saturating). `nth` itself casts its index with
  RT.intCast (checked: throws past the int range).

Keys are modelled by what both read of them: an integer key (long or BigInt) by its value; a
non-integer number (double, ratio) by Java's `intValue` of it and by `to_int`'s truncation, which
agree on the values used here (|x| < 2^31).
-/

namespace Jank.R9.Coll.Lookup

/-- A key. -/
inductive Key where
  /-- a long or a BigInt: `is_integral` in jank, `Util.isInteger` in Clojure -/
  | int (v : Int)
  /-- a double or a ratio, by its truncation toward zero (Java `intValue`, jank `to_int`) -/
  | frac (t : Int)
  /-- anything else (a keyword, a string, nil) -/
  | other
  deriving DecidableEq, Repr

/-- What a lookup gives: the element at an index, the not-found value, or a throw. -/
inductive R where
  | at (i : Nat)
  | nf
  | err
  deriving DecidableEq, Repr

/-- Java's `intValue` of an integer: its low 32 bits as a signed int. -/
def low32 (v : Int) : Int := (v + 2 ^ 31) % 2 ^ 32 - 2 ^ 31

def inI64 (v : Int) : Bool := -2 ^ 63 ≤ v && v < 2 ^ 63

def inRange (n : Nat) (i : Int) : Bool := 0 ≤ i && i < n

/-- jank `persistent_vector::get(key, fallback)` (also `persistent_string::get`). -/
def jankVecGet (n : Nat) : Key → R
  | .int v => if !inI64 v then .err else if inRange n v then .at v.toNat else .nf
  | _ => .nf

/-- Clojure APersistentVector.valAt(key, notFound). -/
def cljVecGet (n : Nat) : Key → R
  | .int v => if inRange n (low32 v) then .at (low32 v).toNat else .nf
  | _ => .nf

/-- jank `persistent_vector::contains`. -/
def jankVecContains (n : Nat) : Key → Option Bool
  | .int v => if !inI64 v then none else some (inRange n v)
  | _ => some false

/-- Clojure APersistentVector.containsKey. -/
def cljVecContains (n : Nat) : Key → Option Bool
  | .int v => some (inRange n (low32 v))
  | _ => some false

/-- Clojure RT.getFrom on a String (any Number). -/
def cljStrGet (n : Nat) : Key → R
  | .int v => if inRange n (low32 v) then .at (low32 v).toNat else .nf
  | .frac t => if inRange n t then .at t.toNat else .nf
  | .other => .nf

/-- jank `persistent_string::get`: as the vector's. -/
def jankStrGet (n : Nat) (k : Key) : R := jankVecGet n k

/-- Clojure RT.contains on a String: a Number key reads `intValue`; anything else throws. -/
def cljStrContains (n : Nat) : Key → Option Bool
  | .int v => some (inRange n (low32 v))
  | .frac t => some (inRange n t)
  | .other => none

/-- jank `persistent_string::contains`: a non-integral key throws. -/
def jankStrContains (n : Nat) : Key → Option Bool
  | .int v => if !inI64 v then none else some (inRange n v)
  | _ => none

theorem low32_id (v : Int) (h1 : -2 ^ 31 ≤ v) (h2 : v < 2 ^ 31) : low32 v = v := by
  unfold low32; omega

/-- ★ For every vector size and every integer key that fits an int, jank's `get` is Clojure's. -/
theorem vec_get_agree_int (n : Nat) (v : Int) (h1 : -2 ^ 31 ≤ v) (h2 : v < 2 ^ 31) :
    jankVecGet n (.int v) = cljVecGet n (.int v) := by
  have hi : inI64 v = true := by simp [inI64]; omega
  simp [jankVecGet, cljVecGet, hi, low32_id v h1 h2]

/-- ★ For every vector size and non-integer key, both give the not-found value. -/
theorem vec_get_agree_nonint (n : Nat) (k : Key) (hk : ∀ v, k ≠ .int v) :
    jankVecGet n k = cljVecGet n k := by
  cases k with
  | int v => exact absurd rfl (hk v)
  | frac t => rfl
  | other => rfl

/-- ★ M9-1, exactly: for every vector of at most 2^31 elements (Clojure's `count` is an int) and every
key in the i64 range, jank's `get` differs from Clojure's iff the key's low 32 bits index the vector
and the key itself does not. -/
theorem vec_get_differs_iff (n : Nat) (hn : n ≤ 2 ^ 31) (v : Int) (hv : inI64 v = true) :
    jankVecGet n (.int v) ≠ cljVecGet n (.int v) ↔
      (inRange n (low32 v) = true ∧ inRange n v = false) := by
  simp only [jankVecGet, cljVecGet, hv, Bool.not_true, Bool.false_eq_true, if_false]
  by_cases a : inRange n v = true
  · have hl : low32 v = v := by
      simp [inRange] at a; exact low32_id v (by omega) (by omega)
    rw [if_pos a, hl, if_pos a]
    simp [a]
  · have a' : inRange n v = false := by simpa using a
    rw [if_neg a]
    by_cases b : inRange n (low32 v) = true
    · rw [if_pos b]; simp [a', b]
    · rw [if_neg b]; simp [b]

/-- The tests' instances. -/
theorem vM1_instances :
    jankVecGet 3 (.int 4294967297) = .nf ∧ cljVecGet 3 (.int 4294967297) = .at 1 ∧
    jankVecContains 3 (.int 4294967297) = some false ∧ cljVecContains 3 (.int 4294967297) = some true ∧
    jankVecGet 3 (.int 2147483648) = .nf ∧ cljVecGet 3 (.int 2147483648) = .nf ∧
    jankStrGet 3 (.int 4294967297) = .nf ∧ cljStrGet 3 (.int 4294967297) = .at 1 ∧
    jankVecGet 3 (.int 18446744073709551617) = .err ∧ cljVecGet 3 (.int 18446744073709551617) = .at 1 := by
  decide

/-- M9-2's instances: `(get "abc" 1.5)`, `(contains? "abc" 1.5)`. -/
theorem vM2_instances :
    jankStrGet 3 (.frac 1) = .nf ∧ cljStrGet 3 (.frac 1) = .at 1 ∧
    jankStrContains 3 (.frac 1) = none ∧ cljStrContains 3 (.frac 1) = some true := by
  decide

/-- ★ On a string, jank's `get` is Clojure's for every integer key that fits an int. -/
theorem str_get_agree_int (n : Nat) (v : Int) (h1 : -2 ^ 31 ≤ v) (h2 : v < 2 ^ 31) :
    jankStrGet n (.int v) = cljStrGet n (.int v) := by
  have hi : inI64 v = true := by simp [inI64]; omega
  simp [jankStrGet, jankVecGet, cljStrGet, hi, low32_id v h1 h2]

/-- ★ M9-2: for every string size and every truncation `t` that indexes it, a non-integer key finds a
character in Clojure and the not-found value in jank; `contains?` is true in Clojure and throws in
jank. -/
theorem str_frac_differs (n : Nat) (t : Int) (ht : inRange n t = true) :
    jankStrGet n (.frac t) = .nf ∧ cljStrGet n (.frac t) = .at t.toNat ∧
    jankStrContains n (.frac t) = none ∧ cljStrContains n (.frac t) = some true := by
  simp [jankStrGet, jankVecGet, cljStrGet, jankStrContains, cljStrContains, ht]

/-! ## A complete walk: every key in a window, every size up to 4 -/

def keysWindow : List Key :=
  ((List.range 11).map fun (i : Nat) => Key.int ((i : Int) - 5)) ++
  [Key.int 2147483647, .int 2147483648, .int (-2147483648), .int (-2147483649), .int 4294967296,
   .int 4294967297, .int 4294967298, .int (-4294967295), .int (2 ^ 63 - 1), .int (2 ^ 63),
   .int (2 ^ 64 + 1), .frac 0, .frac 1, .frac 2, .frac (-1), .other]

/-- Disagreements of `get` on vectors over the window and sizes 0-4: (size, key). -/
def vecGetCensus : List (Nat × Key) :=
  (List.range 5).flatMap fun n => (keysWindow.filter fun k => jankVecGet n k != cljVecGet n k).map (n, ·)

end Jank.R9.Coll.Lookup

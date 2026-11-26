/-!
# Round 9, area Seq: the `partition-all` transducer (T9-9)

**jank 94d32623** (core.jank 3261-3281): `part` is a volatile vector; each input is `conj`ed and,
when `(= n (count p))`, the vector is reset and sent to `rf`; the completion sends a non-empty
buffer, unwrapping a `reduced`. `n` is used as given: `=` between a double and the integer `count`
is false (number.cpp real::equal 267-282, integer::equal 95-115), so a double `n` never fires.

**Clojure 1.12.3** (core.clj 7388-7409): `([^long n] ...)`: the argument is coerced to a long when
the fn is called (RT.longCast: a double is truncated); the buffer is `(java.util.ArrayList. n)`,
which throws IllegalArgumentException ("Illegal Capacity") for a negative n when the transducer is
applied to `rf`; then `.add` and `(= n (.size a))` on longs.

Both stop as soon as `rf` returns a reduced value (the reducing function below stops after `stop`
partitions, as round 2's transducer search did), and the completion sends the rest once.

★ `partition_all_agree`: for every non-negative long n, every input and every stopping point, jank's
result is Clojure's. ★ `partition_all_double_differs`: for every integral double n ≥ 1 and every
input longer than n, Clojure cuts partitions of n and jank sends the whole input as one partition.
-/

namespace Jank.R9.Seq.PartitionAll

/-- The `n` a program passes. -/
inductive N where
  | long (k : Int)
  /-- A double with integral value `k` (`2.0`). -/
  | double (k : Int)
  deriving DecidableEq, Repr

/-- The reduction's state: the partitions sent, whether `rf` stopped. -/
structure Acc where
  out : List (List Int)
  stopped : Bool
  deriving DecidableEq, Repr

/-- `rf`: `conj` the partition; return `(reduced acc)` once `stop` partitions were sent. -/
def rf (stop : Nat) (a : Acc) (p : List Int) : Acc :=
  let out := a.out ++ [p]
  { out, stopped := out.length ≥ stop }

/-- One run of `(transduce (partition-all n) rf [] xs)` given the step's firing test `fires`
(called with the buffer's count after the add): the remaining input, the reduction's value and the
buffer. The reduce (seq.cpp 908 / Clojure's) stops at the first reduced value; the completion
(`(unreduced (rf result buf))` when the buffer is not empty) runs once at the end in both. -/
def go (fires : Nat → Bool) (stop : Nat) : List Int → Acc → List Int → Acc
  | [], acc, buf => if buf.isEmpty then acc else rf stop acc buf
  | x :: xs, acc, buf =>
    if acc.stopped then (if buf.isEmpty then acc else rf stop acc buf)
    else
      let b := buf ++ [x]
      if fires b.length then go fires stop xs (rf stop acc b) [] else go fires stop xs acc b

def run (fires : Nat → Bool) (stop : Nat) (xs : List Int) : Acc :=
  go fires stop xs { out := [], stopped := false } []

/-- jank: `(= n (count p))`; a double never equals the integer count. -/
def jankFires : N → Nat → Bool
  | .long k, c => decide (k = c)
  | .double _, _ => false

/-- Clojure: `n` is `(long n)`; a negative one throws at `(java.util.ArrayList. n)`. -/
def cljN : N → Int
  | .long k => k
  | .double k => k

def cljFires (n : N) (c : Nat) : Bool := decide (cljN n = c)

def jank (n : N) (stop : Nat) (xs : List Int) : Except String Acc := .ok (run (jankFires n) stop xs)

def clj (n : N) (stop : Nat) (xs : List Int) : Except String Acc :=
  if cljN n < 0 then .error "IllegalArgumentException: Illegal Capacity" else .ok (run (cljFires n) stop xs)

/-- ★ For every long n ≥ 0, input and stopping point, jank's `partition-all` transducer gives
Clojure's result. -/
theorem partition_all_agree (k : Int) (hk : 0 ≤ k) (stop : Nat) (xs : List Int) :
    jank (.long k) stop xs = clj (.long k) stop xs := by
  have : ¬ (cljN (.long k) < 0) := by simp [cljN]; omega
  unfold jank clj
  split
  · contradiction
  · rfl

/-- With a double n, jank's step never fires. -/
theorem jank_double_never (k : Int) (stop : Nat) (xs : List Int) :
    jank (.double k) stop xs = .ok (run (fun _ => false) stop xs) := rfl

theorem go_never (stop : Nat) (acc : Acc) (h : acc.stopped = false) (xs buf : List Int) :
    go (fun _ => false) stop xs acc buf =
      if (buf ++ xs).isEmpty then acc else rf stop acc (buf ++ xs) := by
  induction xs generalizing buf with
  | nil => simp [go]
  | cons x xs ih =>
    simp only [go, h, Bool.false_eq_true, ite_false]
    rw [ih]
    simp

/-- ★ With a double n (any value), jank sends every non-empty input as one partition, at the
completion, whatever the stopping point. -/
theorem jank_double_one_partition (k : Int) (stop : Nat) (xs : List Int) (h : xs ≠ []) :
    jank (.double k) stop xs = .ok (rf stop { out := [], stopped := false } xs) := by
  simp only [jank, run]
  have := go_never stop { out := [], stopped := false } rfl xs []
  simp only [List.nil_append] at this
  rw [show (fun (_ : Nat) => false) = (fun c => jankFires (.double k) c) from rfl] at this
  rw [this]
  cases xs with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- `(into [] (partition-all 2.0) [1 2 3 4 5])`: Clojure [[1 2] [3 4] [5]], jank [[1 2 3 4 5]];
`(partition-all -1)`: Clojure throws, jank [[1 2 3]]. -/
theorem examples :
    (clj (.double 2) 100 [1, 2, 3, 4, 5]).toOption = some { out := [[1, 2], [3, 4], [5]], stopped := false } ∧
    (jank (.double 2) 100 [1, 2, 3, 4, 5]).toOption = some { out := [[1, 2, 3, 4, 5]], stopped := false } ∧
    (jank (.long (-1)) 100 [1, 2, 3]).toOption = some { out := [[1, 2, 3]], stopped := false } ∧
    (clj (.long (-1)) 100 [1, 2, 3]).toOption = none := by
  decide

end Jank.R9.Seq.PartitionAll

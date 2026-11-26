/-!
# Round 9, area Seq: `sort` and `sort-by`, jank's std::stable_sort against Clojure's TimSort (T9-1, T9-2)

**jank 94d32623.** core.jank 5661-5682: `(sort coll)` is `cpp/jank.runtime.sort`, `(sort comp coll)`
is the 2-arity, and `(sort-by keyfn comp coll)` is `(sort (fn [x y] (comp (keyfn x) (keyfn y))) coll)`.
core/seq.cpp `sort` 1098-1129 copies the seq into a `native_vector` and calls libstdc++'s
`std::stable_sort` with `less(a, b) = runtime::compare(a, b) < 0`; the comparator arity 1131-1176
uses `less(a, b) = o == jank_true ? true : o == jank_false ? false : to_int(o) < 0` where
`o = comp(a, b)`; `to_int` (math.hpp 1409-1436) is the object's `to_integer()`: an `i64` (a long
is itself, a double truncates, NaN gives 0).

**libstdc++ 15** (`bits/stl_algo.h`, the library jank links on Linux): `__stable_sort` takes a
buffer of (n+1)/2 elements, sorts [0, (n+1)/2) and [(n+1)/2, n) with `__merge_sort_with_buffer`
(insertion sorts of 7-element chunks, then pairwise `__move_merge` passes), and merges the halves
with `__merge_adaptive`: forward (`__move_merge_adaptive`) when len1 <= len2, else backward
(`__move_merge_adaptive_backward`). `__insertion_sort` moves an element to the front when
`less(x, first)`, else walks it left while `less(x, prev)`. Every merge takes the right run's element
when `less(right, left)`. Validated against g++-15's own std::stable_sort (Run/R9/Seq.lean prints the
cases; .r9-scratch/seq/cc/stable.cpp).

**Clojure 1.12.3** (core.clj `sort`): `(. java.util.Arrays (sort a comp))`, Java's TimSort with
`comp` as a `java.util.Comparator`; an fn's `compare` is AFunction.compare (AFunction.java 52-64):
a Boolean result `true` is -1; `false` asks `(comp y x)`: true is 1, else 0; any other result is a
Number and its `intValue()` (a long's low 32 bits; a double truncated and saturated). `sort-by`
calls `(. comp (compare (keyfn x) (keyfn y)))`, the same int. For n < 32 TimSort is
`countRunAndMakeAscending` (a strictly descending prefix is reversed, an ascending one kept) then
`binarySort` of the rest (pivot goes right of every element it does not compare below).
Replicated for n < 32 only (MIN_MERGE = 32); validated against Clojure 1.12.3 itself.

Both are stable sorts. They agree whenever the comparison is a total preorder (searched completely
below for every length <= 8 over a 3-value domain with distinct tags), and differ on comparisons that
are not: `compare` with ##NaN (NaN compares 0 with every number in both), a boolean comparator that is
not strict (`<=`, `(constantly true)`), and a numeric comparator result whose sign `to_int` and
`intValue` see differently.
-/

namespace Jank.R9.Seq.Sort

/-- A sort key: a number (an integer stands for any ordered number) or ##NaN. -/
inductive Key where
  | num (v : Int)
  | nan
  deriving DecidableEq, Repr, Inhabited

/-- An element: its key and a tag (its position in the input), so that stability is visible. -/
structure El where
  key : Key
  tag : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `compare` on two numbers (Clojure's Numbers.compare and jank's `(r < l) - (l < r)` alike):
NaN compares 0 with everything. -/
def numCompare : Key → Key → Int
  | .num a, .num b => if a < b then -1 else if b < a then 1 else 0
  | _, _ => 0

/-- What a comparator fn returns. -/
inductive Res where
  | bool (b : Bool)
  | long (n : Int)
  deriving DecidableEq, Repr

/-- The comparators searched. -/
inductive Comp where
  /-- `(sort coll)`: `compare`. -/
  | compare
  /-- `(sort <= coll)` (and `<`, `>=`, `>`): a boolean fn. -/
  | le | lt | ge | gt
  /-- `(sort (constantly true) coll)`, `(constantly false)`. -/
  | constT | constF
  /-- `(sort #(- %1 %2) coll)`: a long result. -/
  | minus
  deriving DecidableEq, Repr

def Comp.code : Comp → String
  | .compare => "compare" | .le => "<=" | .lt => "<" | .ge => ">=" | .gt => ">"
  | .constT => "(constantly true)" | .constF => "(constantly false)" | .minus => "#(- %1 %2)"

def keyLt : Key → Key → Bool
  | .num a, .num b => decide (a < b)
  | _, _ => false

/-- The fn's result on two keys. -/
def Comp.call : Comp → Key → Key → Res
  | .compare, a, b => .long (numCompare a b)
  | .le, a, b => .bool (keyLt a b || (!keyLt b a && a != .nan && b != .nan))
  | .lt, a, b => .bool (keyLt a b)
  | .ge, a, b => .bool (keyLt b a || (!keyLt a b && a != .nan && b != .nan))
  | .gt, a, b => .bool (keyLt b a)
  | .constT, _, _ => .bool true
  | .constF, _, _ => .bool false
  | .minus, .num a, .num b => .long (a - b)
  | .minus, _, _ => .long 0

/-- A long's `intValue()`: its low 32 bits, signed. -/
def intValue (n : Int) : Int := (Int32.ofInt n).toInt

/-- jank's comparator adaptor (seq.cpp 1148-1162): `true`, `false`, else `to_int(o) < 0`. -/
def jankLess (c : Comp) (x y : El) : Bool :=
  match c.call x.key y.key with
  | .bool b => b
  | .long n => decide (n < 0)

/-- jank's `(sort coll)` (seq.cpp 1110): `runtime::compare(a, b) < 0`. -/
def jankLessDefault (x y : El) : Bool := decide (numCompare x.key y.key < 0)

/-- Clojure's AFunction.compare (AFunction.java 52-64). -/
def cljCmp (c : Comp) (x y : El) : Int :=
  match c.call x.key y.key with
  | .bool true => -1
  | .bool false => match c.call y.key x.key with
    | .bool true => 1
    | _ => 0
  | .long n => intValue n

/-! ## libstdc++'s std::stable_sort -/

section Std
variable {α : Type} (less : α → α → Bool)

/-- `__unguarded_linear_insert`, on the sorted prefix kept reversed (its last element first):
walk left while `less(v, prev)`. -/
def linIns (v : α) : List α → List α
  | [] => [v]
  | y :: ys => if less v y then y :: linIns v ys else v :: y :: ys

/-- `__insertion_sort` over a list; the prefix is kept reversed. -/
def insSortRev : List α → List α → List α
  | acc, [] => acc
  | acc, x :: xs =>
    match acc.getLast? with
    | none => insSortRev [x] xs
    | some fst =>
      -- `if (__comp(__i, __first))`: move to the front
      if less x fst then insSortRev (acc ++ [x]) xs
      else insSortRev (linIns less x acc) xs

def insertionSort (xs : List α) : List α := (insSortRev less [] xs).reverse

/-- `__move_merge` / `__move_merge_adaptive`: take the right run's head when `less(right, left)`. -/
def mergeFuel : Nat → List α → List α → List α
  | _, [], ys => ys
  | _, xs, [] => xs
  | 0, xs, ys => xs ++ ys
  | f + 1, x :: xs, y :: ys =>
    if less y x then y :: mergeFuel f (x :: xs) ys else x :: mergeFuel f xs (y :: ys)

def mergeF (xs ys : List α) : List α := mergeFuel less (xs.length + ys.length) xs ys

/-- `__move_merge_adaptive_backward`, on both runs reversed (last elements first); the result is
built from the back: take the left run's last element when `less(right_last, left_last)`. -/
def mergeBRev : Nat → List α → List α → List α
  | _, [], ys => ys
  | _, xs, [] => xs
  | 0, xs, ys => xs ++ ys
  | f + 1, x :: xs, y :: ys =>
    if less y x then x :: mergeBRev f xs (y :: ys) else y :: mergeBRev f (x :: xs) ys

def mergeB (l r : List α) : List α :=
  (mergeBRev less (l.length + r.length) l.reverse r.reverse).reverse

/-- Split into chunks of `k` (the last shorter). -/
def chunks (k : Nat) (xs : List α) (fuel : Nat := xs.length + 1) : List (List α) :=
  match fuel with
  | 0 => []
  | f + 1 => if xs.isEmpty then [] else xs.take k :: chunks k (xs.drop k) f

/-- One `__merge_sort_loop` pass: merge consecutive pairs of runs. -/
def mergePass : List (List α) → List (List α)
  | a :: b :: rest => mergeF less a b :: mergePass rest
  | rs => rs

def mergeAll (rs : List (List α)) : Nat → List α
  | 0 => rs.flatten
  | f + 1 => match rs with
    | [] => []
    | [r] => r
    | _ => mergeAll (mergePass less rs) f

/-- `__merge_sort_with_buffer`: `__chunk_insertion_sort` with `_S_chunk_size` = 7, then merge passes
until one run (an extra pass over a single run is a copy). -/
def mergeSortWithBuffer (xs : List α) : List α :=
  mergeAll less ((chunks 7 xs).map (insertionSort less)) (xs.length + 1)

/-- `std::stable_sort` (`__stable_sort` with a buffer of (n+1)/2, `__stable_sort_adaptive`). -/
def stableSort (xs : List α) : List α :=
  if xs.isEmpty then xs else
  let m := (xs.length + 1) / 2
  let l := mergeSortWithBuffer less (xs.take m)
  let r := mergeSortWithBuffer less (xs.drop m)
  -- `__merge_adaptive`: len1 <= len2 forward, else backward
  if m ≤ xs.length - m then mergeF less l r else mergeB less l r

end Std

/-! ## Java's TimSort for n < 32 (`countRunAndMakeAscending`, `binarySort`) -/

section Tim
variable {α : Type} [Inhabited α] (cmp : α → α → Int)

/-- Length of the ascending run at the start (`>= 0` steps). -/
def ascRun : List α → Nat
  | a :: b :: rest => if cmp b a ≥ 0 then ascRun (b :: rest) + 1 else 1
  | [_] => 1
  | [] => 0

/-- Length of the strictly descending run at the start (`< 0` steps). -/
def descRun : List α → Nat
  | a :: b :: rest => if cmp b a < 0 then descRun (b :: rest) + 1 else 1
  | [_] => 1
  | [] => 0

/-- `countRunAndMakeAscending`: the run's length, and the array with a descending run reversed. -/
def countRun (xs : List α) : Nat × List α :=
  match xs with
  | a :: b :: _ =>
    if cmp b a < 0 then
      let k := descRun cmp xs
      (k, (xs.take k).reverse ++ xs.drop k)
    else (ascRun cmp xs, xs)
  | _ => (xs.length, xs)

/-- `binarySort`'s search: the first index in [left, right) where `cmp(pivot, a[mid]) < 0` sends
the search left; the pivot is inserted at `left`. -/
def binSearch (a : Array α) (pivot : α) (left right : Nat) : Nat → Nat
  | 0 => left
  | f + 1 =>
    if left < right then
      let mid := (left + right) / 2
      if cmp pivot a[mid]! < 0 then binSearch a pivot left mid f
      else binSearch a pivot (mid + 1) right f
    else left

def insertAt (a : Array α) (i : Nat) (v : α) : Array α :=
  (a.toList.take i ++ [v] ++ a.toList.drop i).toArray

/-- `binarySort(a, 0, n, start)`: insert a[start..n) one by one into the sorted prefix. -/
def binarySort (prefix_ : Array α) : List α → Array α
  | [] => prefix_
  | p :: ps =>
    let i := binSearch cmp prefix_ p 0 prefix_.size (prefix_.size + 1)
    binarySort (insertAt prefix_ i p) ps

/-- `TimSort.sort` for n < 32: `none` for n >= 32 (not replicated). -/
def timSortSmall (xs : List α) : Option (List α) :=
  if xs.length < 2 then some xs
  else if xs.length ≥ 32 then none
  else
    let (k, ys) := countRun cmp xs
    some (binarySort cmp (ys.take k).toArray (ys.drop k)).toList

end Tim

/-! ## The two sorts on a comparator -/

def jankSort (c : Option Comp) (xs : List El) : List El :=
  match c with
  | none => stableSort jankLessDefault xs
  | some c => stableSort (jankLess c) xs

/-- Clojure: `(sort coll)` is `(sort compare coll)`; `compare`'s result is an Integer. -/
def cljSort (c : Option Comp) (xs : List El) : Option (List El) :=
  match c with
  | none => timSortSmall (fun x y => numCompare x.key y.key) xs
  | some c => timSortSmall (cljCmp c) xs

def Key.code : Key → String
  | .num v => toString v
  | .nan => "##NaN"

def keysCode (xs : List El) : String := "(" ++ " ".intercalate (xs.map (·.key.code)) ++ ")"
def tagsCode (xs : List El) : String := "[" ++ " ".intercalate (xs.map (toString ·.tag)) ++ "]"

/-- Elements from keys, tagged by position. -/
def mk (ks : List Key) : List El := (ks.zipIdx).map fun (k, i) => ⟨k, i⟩

/-! ## Facts (kernel-checked) -/

/-- `(sort [3 ##NaN 1 2])`: Clojure keeps the input (one ascending run under NaN's zeros); jank
merges the halves [3 NaN] and [1 2]. -/
theorem sort_nan_example :
    (jankSort none (mk [.num 3, .nan, .num 1, .num 2])).map (·.key) = [.num 1, .num 2, .num 3, .nan] ∧
    ((cljSort none (mk [.num 3, .nan, .num 1, .num 2])).getD []).map (·.key)
      = [.num 3, .nan, .num 1, .num 2] := by
  decide +kernel

/-- `(sort #(- %1 %2) [4294967296 0])`: Clojure's intValue of -2^32 is 0, so the two stay; jank's
`to_int` sees -2^32 < 0. -/
theorem sort_minus_example :
    (jankSort (some .minus) (mk [.num 4294967296, .num 0])).map (·.key) = [.num 0, .num 4294967296] ∧
    ((cljSort (some .minus) (mk [.num 4294967296, .num 0])).getD []).map (·.key)
      = [.num 4294967296, .num 0] := by
  decide +kernel

/-- ★ For every long `d` in the int range, `intValue` is `d` itself. -/
theorem intValue_id_in_int_range (d : Int) (h1 : -2 ^ 31 ≤ d) (h2 : d < 2 ^ 31) : intValue d = d :=
  Int32.toInt_ofInt_of_le h1 h2

/-- ★ So a comparator returning `(- a b)` sorts alike in both whenever the difference fits in 32
bits: for every two keys, jank's `less` is Clojure's `compare < 0` (and the reverse comparison too). -/
theorem minus_agree_in_int_range (a b : Int) (t u : Nat) (h1 : -2 ^ 31 ≤ a - b) (h2 : a - b < 2 ^ 31) :
    jankLess .minus ⟨.num a, t⟩ ⟨.num b, u⟩ = decide (cljCmp .minus ⟨.num a, t⟩ ⟨.num b, u⟩ < 0) := by
  simp only [jankLess, cljCmp, Comp.call, intValue_id_in_int_range (a - b) h1 h2]

/-- Outside it the sign can differ: -2^32's low 32 bits are 0 (Clojure: equal; jank: less), 2^31's are
-2^31 (Clojure: less; jank: greater). -/
theorem intValue_sign_flips : intValue (-4294967296) = 0 ∧ intValue 2147483648 = -2147483648 := by
  decide

/-- The replica's `intValue` is the same truncation. -/
theorem intValue_examples : intValue (-4294967296) = 0 ∧ intValue 2147483648 = -2147483648 ∧
    intValue 5 = 5 := by decide

end Jank.R9.Seq.Sort

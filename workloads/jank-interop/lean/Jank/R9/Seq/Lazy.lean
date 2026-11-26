/-!
# Round 9, area Seq: how many elements an expression realizes (jank 94d32623 against Clojure 1.12.3)

Each model counts what a program's side effects see: calls of the fn a lazy sequence maps, or
elements of a lazy source realized. The functions follow the code paths named in their comments;
the theorems hold for every length.

1. **Chunks (T9-3).** core.jank's `map`, `filter`, `keep`, `map-indexed`, `keep-indexed` and `for`
   (2885-3045, 3864-3892, 3615-3700) are Clojure's code: over a `chunked-seq?` source they apply
   `f` to a whole chunk (`dotimes` over `chunk-first`) before the first element is seen. Which
   sources are chunked differs. Clojure: a vector's seq (PersistentVector.ChunkedSeq, 32-element
   leaves), `(range n)` (LongRange, chunks of 32), a real `range` (Range). jank: only `range` over
   reals (range.hpp 70-73; chunked_cons) is `behavior::chunkable`; `integer_range` has the
   chunkable members commented out (integer_range.hpp 64-67, 89-91) and persistent_vector_sequence
   has none, so `(range n)` and a vector's seq take the one-element branch. (jank's real `range` is
   R119: chunk_cons seqs its rest at once, seq.cpp 1066.)
2. **`iterate` (T9-4).** jank's iterator (iterator.cpp 35-48): `first` is the current value,
   `next` calls `f` at once (and caches the next node). Clojure's Iterate (Iterate.java 47-59):
   `next` makes an unrealized node; its `first` calls `f`. `take`'s `(rest s)` therefore calls `f`
   in jank, one value ahead of what Clojure computes.
3. **`apply` (T9-5).** jank (core/call.cpp 18-22): `args.fresh_seq()`, then
   `sequence_length(s, max_params + 1)` (seq.cpp 842-873, `max_params` 10): the loop realizes up to
   12 elements before the fn is called. Clojure (`apply`, RestFn.applyTo, AFn.applyToHelper,
   RT.boundedLength): `(seq args)` and `boundedLength(args, requiredArity)` for a variadic fn
   (r + 2 elements: the loop's `c.next()` runs before its test); for a fixed-arity fn
   `boundedLength(args, 20)` and, past 20, `RT.seqToArray` of the rest (every element). So `(mapcat f coll)` = `(apply concat (apply map f colls))` calls
   `f` on 12 elements in jank and 4 in Clojure (concat's required arity is 2).
4. **`dedupe` (T9-6).** jank (core.jank 3926-3933): a hand-written lazy-seq whose step destructures
   `[x & more]` (`(seq xs)`, then `(next s)`): 2 elements for the first output. Clojure (core.clj
   7863): `(sequence (dedupe) coll)` = `RT.chunkIteratorSeq(TransformerIterator)`: one output is
   pulled when the seq is made, and the first `seq` fills a 32-element chunk and asks `hasNext` for
   a 33rd output, so the source is realized up to the input that gives the 33rd output.
-/

namespace Jank.R9.Seq.Lazy

/-! ## 1. Chunks -/

/-- A source's seq as `map` sees it: unchunked, or chunked with `size`-element chunks. -/
inductive Src where
  | plain (n : Nat)
  | chunked (size : Nat) (n : Nat)
  deriving DecidableEq, Repr

inductive Impl where
  | jank | clj
  deriving DecidableEq, Repr

/-- The sources a program writes. -/
inductive Source where
  /-- `(range n)`: jank integer_range, Clojure LongRange. -/
  | intRange (n : Nat)
  /-- `(vec (range n))` or a vector literal: its seq. -/
  | vector (n : Nat)
  /-- `(list ...)`: a list. -/
  | list (n : Nat)
  deriving DecidableEq, Repr

/-- What `(seq src)` is in each implementation. -/
def Source.seqOf : Impl → Source → Src
  | .jank, .intRange n => .plain n   -- integer_range.hpp 64-67: not chunkable
  | .jank, .vector n => .plain n     -- persistent_vector_sequence: not chunkable
  | .jank, .list n => .plain n
  | .clj, .intRange n => .chunked 32 n  -- LongRange.chunkedFirst: CHUNK_SIZE 32
  | .clj, .vector n => .chunked 32 n    -- PersistentVector.ChunkedSeq: the 32-element leaves
  | .clj, .list n => .plain n

/-- `(doall (take k (map f s)))` (or `filter`/`keep` with a pred that keeps everything): the number
of `f` calls. `map`'s lazy-seq body (core.jank 2901-2911): on a chunked seq, `f` on each element
of `chunk-first`, then `(chunk-cons (chunk b) (map f (chunk-rest s)))`, whose rest is realized only
when `take` walks past the chunk; else `(cons (f (first s)) (map f (rest s)))`. `take` realizes
nodes 0..k-1 (core.jank 3065-3069: `(when (pos? n) ...)` stops before the k-th). -/
def mapTakeCalls : Src → Nat → Nat
  | _, 0 => 0
  | .plain 0, _ => 0
  | .plain (n + 1), k + 1 => 1 + mapTakeCalls (.plain n) k
  | .chunked c n, k + 1 =>
    if n = 0 ∨ c = 0 then 0 else
    let m := min c n
    m + mapTakeCalls (.chunked c (n - m)) (k + 1 - m)
termination_by s k => (match s with | .plain n => n | .chunked _ n => n) + k
decreasing_by all_goals simp_wf; omega

def calls (i : Impl) (s : Source) (k : Nat) : Nat := mapTakeCalls (s.seqOf i) k

/-- ★ jank: realizing k elements of `(map f s)` over an integer range, a vector or a list calls `f`
exactly min(k, n) times, for every n and k. -/
theorem jank_plain_calls (n k : Nat) : mapTakeCalls (.plain n) k = min k n := by
  induction n generalizing k with
  | zero => cases k <;> simp [mapTakeCalls]
  | succ n ih =>
    cases k with
    | zero => simp [mapTakeCalls]
    | succ k => simp [mapTakeCalls, ih]; omega

theorem jank_calls (s : Source) (n k : Nat)
    (hs : s = .intRange n ∨ s = .vector n ∨ s = .list n) : calls .jank s k = min k n := by
  rcases hs with rfl | rfl | rfl <;> simp [calls, Source.seqOf, jank_plain_calls]

/-- ★ Clojure: `(first (map f s))` over `(range n)` or a vector of n ≥ 1 elements calls `f`
min(n, 32) times (the first chunk), for every n. -/
theorem clj_first_calls (n : Nat) (h : 0 < n) :
    mapTakeCalls (.chunked 32 n) 1 = min 32 n := by
  rw [mapTakeCalls]
  have : ¬ (n = 0 ∨ (32 : Nat) = 0) := by omega
  simp only [this, ite_false]
  have h1 : 1 - min 32 n = 0 := by omega
  rw [Nat.zero_add, h1]
  cases hn : n - min 32 n <;> simp [mapTakeCalls]

/-- ★ So for every n ≥ 2, `(first (map f (range n)))` and `(first (map f (vec (range n))))` call
`f` once in jank and min(n, 32) times in Clojure: they differ. -/
theorem first_map_differs (n : Nat) (h : 2 ≤ n) (s : Source) (hs : s = .intRange n ∨ s = .vector n) :
    calls .jank s 1 = 1 ∧ calls .clj s 1 = min 32 n ∧ calls .jank s 1 ≠ calls .clj s 1 := by
  have hj : calls .jank s 1 = 1 := by
    rw [jank_calls s n 1 (by rcases hs with h | h <;> simp [h])]; omega
  have hc : calls .clj s 1 = min 32 n := by
    rcases hs with rfl | rfl <;> simp only [calls, Source.seqOf] <;> exact clj_first_calls n (by omega)
  refine ⟨hj, hc, ?_⟩
  rw [hj, hc]; omega

/-- A list is unchunked in both: the control. -/
theorem list_agrees (n k : Nat) : calls .jank (.list n) k = calls .clj (.list n) k := rfl

/-! ## 2. `iterate` -/

/-- Clojure's Iterate node (Iterate.java): the previous seed and, once realized, its own. -/
structure INode where
  prev : Int
  seed : Option Int

/-- `Iterate.first`: realize the seed with one call of `f`. Returns the value, the node, calls. -/
def iFirst (f : Int → Int) (nd : INode) : Int × INode × Nat :=
  match nd.seed with
  | some v => (v, nd, 0)
  | none => (f nd.prev, { nd with seed := some (f nd.prev) }, 1)

/-- `(doall (take k (iterate f x)))` in Clojure from a node: `take`'s body is
`(cons (first s) (take (dec n) (rest s)))`; `rest` is `next()`: `new Iterate(f, first(), UNREALIZED)`
(no call: the node's own seed is already realized by the `first` just before). -/
def cljTake (f : Int → Int) : Nat → INode → List Int × Nat
  | 0, _ => ([], 0)
  | k + 1, nd =>
    let (v, _, c) := iFirst f nd
    let (vs, c') := cljTake f k { prev := v, seed := none }
    (v :: vs, c + c')

/-- jank's iterator (iterator.cpp): `first` is `current`; `rest` → `next()` calls `f` (no node
caches it yet on this walk). -/
def jankTake (f : Int → Int) : Nat → Int → List Int × Nat
  | 0, _ => ([], 0)
  | k + 1, cur =>
    -- (cons (first s) (take (dec n) (rest s))): `rest` is evaluated as an argument: one call
    let (vs, c') := jankTake f k (f cur)
    (cur :: vs, 1 + c')

/-- `(take k (iterate f x))`'s values: x, f x, ... -/
def iterVals (f : Int → Int) : Nat → Int → List Int
  | 0, _ => []
  | k + 1, x => x :: iterVals f k (f x)

theorem cljTake_succ (f : Int → Int) (k : Nat) (nd : INode) :
    cljTake f (k + 1) nd =
      ((iFirst f nd).1 :: (cljTake f k { prev := (iFirst f nd).1, seed := none }).1,
       (iFirst f nd).2.2 + (cljTake f k { prev := (iFirst f nd).1, seed := none }).2) := rfl

theorem cljTake_unrealized (f : Int → Int) (k : Nat) (p : Int) :
    cljTake f k { prev := p, seed := none } = (iterVals f k (f p), k) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [cljTake_succ, ih]
    simp only [iFirst, iterVals]
    congr 1; omega

/-- ★ Clojure: `(doall (take k (iterate f x)))` calls `f` k - 1 times, for every f, x and k ≥ 1. -/
theorem clj_iterate_take (f : Int → Int) (x : Int) (k : Nat) :
    cljTake f (k + 1) { prev := 0, seed := some x } = (iterVals f (k + 1) x, k) := by
  rw [cljTake_succ, cljTake_unrealized]
  simp only [iFirst, iterVals]
  congr 1; omega

/-- ★ jank: the same values with k calls, for every f, x and k: one more than Clojure. -/
theorem jank_iterate_take (f : Int → Int) (x : Int) (k : Nat) :
    jankTake f k x = (iterVals f k x, k) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [jankTake, ih, iterVals]; omega

/-! ## 3. `apply` -/

/-- A lazy argument list of length `len`; `seq` realizes node 1 and each `next` the following one.
Clojure's `RT.boundedLength(list, limit)`:
`for(c = list; c != null && i <= limit; c = c.next()) i++` from node `pos` (1-based) realized:
returns the highest node realized. -/
def boundedLengthRealized (len limit : Nat) : Nat → Nat → Nat → Nat
  | 0, _, realized => realized
  | fuel + 1, i, realized =>
    -- c is node i+1 (exists iff i < len); test `c != null && i <= limit`
    if i < len ∧ i ≤ limit then
      -- i++, then c = c.next(): realizes node i+2 (if any)
      boundedLengthRealized len limit fuel (i + 1) (max realized (min len (i + 2)))
    else realized

/-- Clojure `(apply f args)`: `(seq args)` realizes node 1; `RestFn.applyTo` (RestFn.java 132-136)
calls `boundedLength(args, requiredArity)` and passes the rest unrealized; a fixed-arity fn
(`AFn.applyToHelper`, AFn.java 147-424) switches on `boundedLength(args, 20)`, and past 20 arguments
its default case calls `RT.seqToArray` on the rest: every element. -/
def cljApplyRealized (len : Nat) (variadicRequired : Option Nat) : Nat :=
  if len = 0 then 0 else
  match variadicRequired with
  | some r => boundedLengthRealized len r (len + 2) 0 1
  | none =>
    let b := boundedLengthRealized len 20 (len + 2) 0 1
    if b > 21 then len else b

/-- jank `apply_to` (core/call.cpp 18-22): `fresh_seq` realizes node 1; `sequence_length(s, 11)`:
`for(i = begin; i != end && length < max; ++i) ++length;` (each `++i` is a `next`). -/
def seqLengthRealized (len mx : Nat) : Nat → Nat → Nat → Nat
  | 0, _, realized => realized
  | fuel + 1, length, realized =>
    -- i is node length+1; test `i != end && length < max`
    if length < len ∧ length < mx then
      -- ++length; ++i realizes node length+2
      seqLengthRealized len mx fuel (length + 1) (max realized (min len (length + 2)))
    else realized

def jankApplyRealized (len : Nat) : Nat :=
  if len = 0 then 0 else seqLengthRealized len 11 (len + 2) 0 1

/-- The values: `(first (mapcat f coll))` over a 15-element list: jank 12, Clojure 4 (concat's
required arity 2); a fixed-arity fn over 30 elements: Clojure all 30. -/
theorem apply_examples :
    jankApplyRealized 15 = 12 ∧ cljApplyRealized 15 (some 2) = 4 ∧ cljApplyRealized 30 none = 30 ∧
    jankApplyRealized 3 = 3 ∧ cljApplyRealized 3 (some 2) = 3 := by decide +kernel

theorem seqLength_spec (len mx fuel length : Nat) (hl : length ≤ len) (hm : length ≤ mx)
    (hf : len - length < fuel) :
    seqLengthRealized len mx fuel length (min len (length + 1)) = min len (mx + 1) := by
  induction fuel generalizing length with
  | zero => omega
  | succ fuel ih =>
    rw [seqLengthRealized]
    split
    · rename_i h
      have e : max (min len (length + 1)) (min len (length + 2)) = min len (length + 1 + 1) := by omega
      rw [e]
      exact ih (length + 1) (by omega) (by omega) (by omega)
    · omega

theorem bounded_spec (len limit fuel i : Nat) (hl : i ≤ len) (hm : i ≤ limit + 1)
    (hf : len - i < fuel) :
    boundedLengthRealized len limit fuel i (min len (i + 1)) = min len (limit + 2) := by
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
    rw [boundedLengthRealized]
    split
    · rename_i h
      have e : max (min len (i + 1)) (min len (i + 2)) = min len (i + 1 + 1) := by omega
      rw [e]
      exact ih (i + 1) (by omega) (by omega) (by omega)
    · omega

/-- ★ jank's `apply` realizes min(len, 12) elements of its argument seq, for every length ≥ 1. -/
theorem jank_apply_realized (len : Nat) (h : 0 < len) : jankApplyRealized len = min len 12 := by
  unfold jankApplyRealized
  split
  · omega
  · have := seqLength_spec len 11 (len + 2) 0 (by omega) (by omega) (by omega)
    simpa [show min len 1 = 1 by omega] using this

/-- ★ Clojure's `apply` of a variadic fn with r required parameters realizes min(len, r + 2)
elements, for every length ≥ 1. -/
theorem clj_apply_realized (len : Nat) (h : 0 < len) (r : Nat) :
    cljApplyRealized len (some r) = min len (r + 2) := by
  unfold cljApplyRealized
  split
  · omega
  · have := bounded_spec len r (len + 2) 0 (by omega) (by omega) (by omega)
    simpa [show min len 1 = 1 by omega] using this

/-- ★ ... and of a fixed-arity fn every element, for every length. -/
theorem clj_apply_fixed_realized (len : Nat) : cljApplyRealized len none = len := by
  unfold cljApplyRealized
  split
  · omega
  · have := bounded_spec len 20 (len + 2) 0 (by omega) (by omega) (by omega)
    simp only [show min len (0 + 1) = 1 by omega] at this
    simp only [this]
    split <;> omega

/-- ★ Hence `(first (mapcat f coll))` (concat: r = 2) calls `f` on min(len, 12) elements in jank
and min(len, 4) in Clojure: they differ for every length ≥ 5. -/
theorem mapcat_first_differs (len : Nat) (h : 5 ≤ len) :
    jankApplyRealized len ≠ cljApplyRealized len (some 2) := by
  rw [jank_apply_realized len (by omega), clj_apply_realized len (by omega)]
  simp; omega

/-! ## 4. `dedupe` -/

/-- jank's `(first (dedupe s))`: `(seq xs)` realizes node 1, `[x & more]` takes `(next s)`: node 2. -/
def jankDedupeFirstRealized (xs : List Int) : Nat := min xs.length 2

/-- Clojure's `(first (dedupe s))` (`sequence` = chunkIteratorSeq over a TransformerIterator over a
SeqIterator): inputs are pulled one by one (SeqIterator.hasNext realizes the next node; the end is
seen by realizing it) until 33 outputs are buffered or the source ends; `dedupe`'s step outputs an
input that differs from the previous one (the first always). `outs` counts the outputs so far;
the result is the number of input nodes realized. -/
def cljDedupeGo : List Int → Option Int → Nat → Nat
  | [], _, _ => 0
  | x :: xs, prior, outs =>
    if outs ≥ 33 then 0
    else 1 + cljDedupeGo xs (some x) (if prior != some x then outs + 1 else outs)

def cljDedupeFirstRealized (xs : List Int) : Nat := cljDedupeGo xs none 0

/-- Up to 33 inputs are all realized, whatever the duplicates. -/
theorem cljDedupeGo_short (xs : List Int) (p : Option Int) (o : Nat) (h : o + xs.length ≤ 33) :
    cljDedupeGo xs p o = xs.length := by
  induction xs generalizing p o with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at h
    rw [cljDedupeGo, List.length_cons]
    split
    · omega
    · split
      · rw [ih _ _ (by omega)]; omega
      · rw [ih _ _ (by omega)]; omega

/-- ★ For every list of 2..33 elements, `(first (dedupe s))` realizes all of them in Clojure and 2
in jank: they differ whenever the list has 3 to 33 elements. -/
theorem dedupe_first_differs (xs : List Int) (h1 : 3 ≤ xs.length) (h2 : xs.length ≤ 33) :
    jankDedupeFirstRealized xs = 2 ∧ cljDedupeFirstRealized xs = xs.length := by
  refine ⟨by simp [jankDedupeFirstRealized]; omega, ?_⟩
  exact cljDedupeGo_short xs none 0 (by omega)

theorem dedupe_examples :
    jankDedupeFirstRealized [1, 2, 3, 4, 5] = 2 ∧ cljDedupeFirstRealized [1, 2, 3, 4, 5] = 5 ∧
    jankDedupeFirstRealized [1, 1, 2, 2, 3, 3] = 2 ∧ cljDedupeFirstRealized [1, 1, 2, 2, 3, 3] = 6 := by
  decide

end Jank.R9.Seq.Lazy

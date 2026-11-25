import Jank.R4.Core.Value

/-!
# Round 4: `clojure.data/diff`

**jank** (src/jank/clojure/data.jank at 7135b7708). The file ports Clojure's helpers
(`atom-diff` 16, `vectorize` 22, `diff-associative-key` 32, `diff-associative` 48,
`diff-sequential` 59) but replaces the two protocols with plain functions:

```clojure
(defn- equality-partition [o] :atom)          ; data.jank 66
(defn- diff-similar [lhs rhs] (atom-diff lhs rhs))   ; data.jank 69
```

so `diff` (data.jank 72–89) is `(if (= a b) [nil nil a] [a b nil])` for every pair: maps and
sequential collections are never subdiffed, although its own docstring (copied from Clojure)
says they are.

**Clojure** (clojure/data.clj, 1.12): `EqualityPartition` gives `:atom` (nil, strings, numbers,
keywords…), `:set` (java.util.Set), `:sequential` (java.util.List: vectors, lists, seqs, map
entries; arrays too), `:map` (java.util.Map). `diff-similar` subdiffs maps by keys, sequential
things by index (results as vectors), and sets by difference/intersection.
-/

namespace Jank.R4.Core.Diff

open Jank.R4.Core

/-- Clojure's equality partition (data.clj extend-protocol EqualityPartition). -/
inductive Part where
  | atom | set | sequential | map
  deriving BEq, Repr, DecidableEq

def partOf : V → Part
  | .set _ => .set
  | .vec _ | .entry .. | .list _ | .seq _ | .arr _ => .sequential
  | .map _ => .map
  | _ => .atom

def elemsOf : V → List V
  | .vec xs | .list xs | .seq xs | .arr xs => xs
  | .entry k v => [k, v]
  | _ => []

/-- A diff result: three optional values (nil is `.nil`). -/
abbrev Triple := V × V × V

def triple (t : Triple) : V := .vec [t.1, t.2.1, t.2.2]

def atomDiff (a b : V) : Triple := if V.eq a b then (.nil, .nil, a) else (a, b, .nil)

def notEmpty : List V → V
  | [] => .nil
  | xs => .set xs

def isNil : V → Bool | .nil => true | _ => false

/-- `{k v}` when `cond`, else nil, as an optional map. -/
def single (cond : Bool) (k v : V) : Option (List (V × V)) := if cond then some [(k, v)] else none

def optMap : Option (List (V × V)) → V
  | none => .nil
  | some kvs => .map kvs

/-- `vectorize` (data.clj): a map from indices to values into a vector, nil where missing. -/
def vectorize (m : Option (List (V × V))) : V :=
  match m with
  | none => .nil
  | some [] => .nil
  | some kvs =>
    let idx := kvs.filterMap fun (k, _) => match k with | .int i => some i.toNat | _ => none
    let mx := idx.foldl max 0
    let base : List V := List.replicate mx .nil
    let out := kvs.foldl (fun (acc : List V) (k, v) =>
      match k with
      | .int i => if i.toNat < acc.length then acc.set i.toNat v else acc ++ [v]
      | _ => acc) base
    .vec out

def elemsOfSet : V → List V
  | .set xs => xs
  | _ => []

def keysOf : V → List V
  | .map kvs => kvs.map (·.1)
  | _ => []

mutual
/-- Clojure's `diff` with fuel (data.clj). -/
def cljDiffF : Nat → V → V → Triple
  | 0, a, b => atomDiff a b
  | n + 1, a, b =>
    if V.eq a b then (.nil, .nil, a)
    else if partOf a == partOf b then
      match partOf a with
      | .atom => atomDiff a b
      | .set =>
        let xs := elemsOfSet a
        let ys := elemsOfSet b
        (notEmpty (xs.filter fun x => !ys.any (V.eq x)),
         notEmpty (ys.filter fun y => !xs.any (V.eq y)),
         notEmpty (xs.filter fun x => ys.any (V.eq x)))
      | .sequential =>
        let xs := elemsOf a
        let ys := elemsOf b
        let ks := (List.range (max xs.length ys.length)).map fun (i : Nat) => V.int (i : Int)
        let (p, q, r) := diffAssocF n (.vec xs) (.vec ys) ks
        (vectorize p, vectorize q, vectorize r)
      | .map =>
        let ka := keysOf a
        let kb := keysOf b
        let (p, q, r) := diffAssocF n a b (ka ++ kb.filter fun k => !ka.any (V.eq k))
        (optMap p, optMap q, optMap r)
    else atomDiff a b

/-- `diff-associative` over keys `ks`: per-key triples merged component-wise. -/
def diffAssocF : Nat → V → V → List V →
    Option (List (V × V)) × Option (List (V × V)) × Option (List (V × V))
  | 0, _, _, _ => (none, none, none)
  | n + 1, a, b, ks =>
    ks.foldl (fun (acc : Option (List (V × V)) × Option (List (V × V)) × Option (List (V × V))) k =>
      let va := V.get a k
      let vb := V.get b k
      let (a', b', ab) := cljDiffF n va vb
      let inA := V.containsKey a k
      let inB := V.containsKey b k
      let same := inA && inB && (!isNil ab || (isNil va && isNil vb))
      let d1 := single (inA && (!isNil a' || !same)) k a'
      let d2 := single (inB && (!isNil b' || !same)) k b'
      let d3 := single same k ab
      (V.mergeMaps acc.1 d1, V.mergeMaps acc.2.1 d2, V.mergeMaps acc.2.2 d3)) (none, none, none)

end

def cljDiff (a b : V) : Triple := cljDiffF V.fuel a b

/-- jank's `diff` (data.jank 72–89 with `equality-partition` 66 and `diff-similar` 69): both
sides always fall in `:atom`, so `diff-similar` is `atom-diff`. -/
def jankEqualityPartition (_ : V) : Part := .atom

def jankDiff (a b : V) : Triple :=
  if V.eq a b then (.nil, .nil, a)
  else if jankEqualityPartition a == jankEqualityPartition b then atomDiff a b
  else atomDiff a b

/-- jank's `diff` is `atom-diff` on every pair. -/
theorem jankDiff_is_atomDiff (a b : V) : jankDiff a b = atomDiff a b := by
  unfold jankDiff atomDiff jankEqualityPartition
  by_cases h : V.eq a b <;> simp [h]

def sameTriple (x y : Triple) : Bool := V.eq (triple x) (triple y)

end Jank.R4.Core.Diff

import Jank.R9.Seq.Sort

/-!
# Round 9, area Seq: complete searches of `sort` (jank's std::stable_sort vs Clojure's TimSort)

Every key list of length 1..L over a small domain, for each comparator family; a case is a
disagreement when the sorted tags differ (so a reordering of equal keys counts). Families:

- `compare` over {0, 1, 2, ##NaN} (`(sort coll)`): NaN compares 0 with every number;
- `<` and `>` over {0, 1, 2, ##NaN}: boolean; with NaN neither is true, so AFunction.compare gives 0;
- `<=`, `>=`, `(constantly true)`, `(constantly false)` over {0, 1, 2} (and `<=`, `(constantly true)`
  over {0, 1} to length 14): boolean, not strict;
- `#(- %1 %2)` over {0, 1, 2^31, 3·10^9, 2^32}: a long result outside the int range;
- controls, total preorders: `compare`, `<`, `>` over {0, 1, 2} and `#(- %1 %2)` over {0, 1, 5}.

It also writes validation cases (`emitCases`): each line is a comparator, the keys, jank's predicted
tag order and Clojure's, checked by g++-15's std::stable_sort (.r9-scratch/seq/cc/stable.cpp) and by
Clojure 1.12.3 (.r9-scratch/seq/clj/sortcheck.clj).
-/

namespace Jank.R9.Seq.SortSearch
open Jank.R9.Seq.Sort

/-- Every list of length `n` over `dom`. -/
def lists (dom : List Key) : Nat → List (List Key)
  | 0 => [[]]
  | n + 1 => (lists dom n).flatMap fun l => dom.map (· :: l)

structure Family where
  name : String
  comp : Option Comp
  dom : List Key
  maxLen : Nat
  /-- A total preorder: no disagreement expected. -/
  control : Bool

def families : List Family := [
  ⟨"compare with NaN", none, [.num 0, .num 1, .num 2, .nan], 8, false⟩,
  ⟨"< with NaN", some .lt, [.num 0, .num 1, .num 2, .nan], 8, false⟩,
  ⟨"> with NaN", some .gt, [.num 0, .num 1, .num 2, .nan], 8, false⟩,
  ⟨"<=", some .le, [.num 0, .num 1, .num 2], 8, false⟩,
  ⟨"<= two keys", some .le, [.num 0, .num 1], 14, false⟩,
  ⟨"(constantly true) two keys", some .constT, [.num 0, .num 1], 14, false⟩,
  ⟨">=", some .ge, [.num 0, .num 1, .num 2], 8, false⟩,
  ⟨"(constantly true)", some .constT, [.num 0, .num 1, .num 2], 8, false⟩,
  ⟨"(constantly false)", some .constF, [.num 0, .num 1, .num 2], 8, false⟩,
  ⟨"#(- %1 %2) wide", some .minus,
    [.num 0, .num 1, .num 2147483648, .num 3000000000, .num 4294967296], 6, false⟩,
  ⟨"control compare", none, [.num 0, .num 1, .num 2], 8, true⟩,
  ⟨"control compare fn", some .compare, [.num 0, .num 1, .num 2], 8, true⟩,
  ⟨"control <", some .lt, [.num 0, .num 1, .num 2], 8, true⟩,
  ⟨"control >", some .gt, [.num 0, .num 1, .num 2], 8, true⟩,
  ⟨"control #(- %1 %2) narrow", some .minus, [.num 0, .num 1, .num 5], 8, true⟩]

def tags (xs : List El) : List Nat := xs.map (·.tag)

structure Tally where
  total : Nat := 0
  differ : Nat := 0
  first : Option String := none

def runFamily (f : Family) (len : Nat) : Tally := Id.run do
  let mut t : Tally := {}
  for ks in lists f.dom len do
    let xs := mk ks
    let j := jankSort f.comp xs
    match cljSort f.comp xs with
    | none => pure ()
    | some c =>
      t := { t with total := t.total + 1 }
      if tags j != tags c then
        t := { t with differ := t.differ + 1 }
        if t.first.isNone then
          t := { t with first := some s!"{keysCode xs}: Clojure {keysCode c} {tagsCode c}, jank {keysCode j} {tagsCode j}" }
  return t

def compCode : Option Comp → String
  | none => "sort"
  | some c => match c with
    | .compare => "compare" | .le => "le" | .lt => "lt" | .ge => "ge" | .gt => "gt"
    | .constT => "constT" | .constF => "constF" | .minus => "minus"

def keyTok : Key → String
  | .num v => toString v
  | .nan => "N"

/-- A validation line: `comp n k1 .. kn | jank tags | Clojure tags`. -/
def caseLine (c : Option Comp) (ks : List Key) : Option String :=
  let xs := mk ks
  match cljSort c xs with
  | none => none
  | some cl =>
    some s!"{compCode c} {ks.length} {" ".intercalate (ks.map keyTok)} | {" ".intercalate ((tags (jankSort c xs)).map toString)} | {" ".intercalate ((tags cl).map toString)}"

/-- A small LCG (the cases only need variety; the seed is fixed). -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616

def randomLists (dom : List Key) (count maxLen : Nat) (seed : Nat) : List (List Key) := Id.run do
  let mut s := seed
  let mut out := []
  for _ in [0:count] do
    s := lcg s
    let n := 2 + (s / 65536) % (maxLen - 1)
    let mut l := []
    for _ in [0:n] do
      s := lcg s
      l := dom[(s / 65536) % dom.length]! :: l
    out := l :: out
  return out

/-- Every case of length <= 5 of every family, and 300 random cases of length 2..31 per family. -/
def emitCases : List String := Id.run do
  let mut out := []
  for f in families do
    for n in [1:6] do
      for ks in lists f.dom n do
        if let some l := caseLine f.comp ks then out := l :: out
    for ks in randomLists f.dom 300 31 (f.name.length * 7919 + 17) do
      if let some l := caseLine f.comp ks then out := l :: out
  return out.reverse

/-- Every total preorder on `n` elements, as every list over {0, .., n-1} of length `n` (a list's
sort behavior under a consistent comparator depends only on the order pattern of its keys, and every
pattern of n elements uses at most n distinct values), sorted by `compare` in both. Counts the lists
whose sorted tags differ (expected 0: both are stable sorts). -/
def preorderCensus (n : Nat) (lo : Nat := 0) (hi : Nat := n ^ n) : Nat × Nat := Id.run do
  let mut tot := 0
  let mut dif := 0
  for code in [lo:hi] do
    -- the list whose base-n digits are `code`'s
    let mut c := code
    let mut ks : List Key := []
    for _ in [0:n] do
      ks := Key.num (Int.ofNat (c % n)) :: ks
      c := c / n
    let xs := mk ks
    tot := tot + 1
    match cljSort none xs with
    | some cl => if tags (jankSort none xs) != tags cl then dif := dif + 1
    | none => pure ()
  return (tot, dif)

/-- Random lists of length 2..31 over 2..32 values (no NaN), `count` of them from `seed`. -/
def randomPreorders (count seed : Nat) : Nat × Nat := Id.run do
  let mut s := seed
  let mut tot := 0
  let mut dif := 0
  for _ in [0:count] do
    s := lcg s
    let n := 2 + (s / 65536) % 30
    s := lcg s
    let k := 2 + (s / 65536) % 31
    let mut ks : List Key := []
    for _ in [0:n] do
      s := lcg s
      ks := Key.num (Int.ofNat ((s / 65536) % k)) :: ks
    let xs := mk ks
    tot := tot + 1
    match cljSort none xs with
    | some cl => if tags (jankSort none xs) != tags cl then dif := dif + 1
    | none => pure ()
  return (tot, dif)

end Jank.R9.Seq.SortSearch

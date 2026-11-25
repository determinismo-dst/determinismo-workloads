import Std.Tactic.BVDecide
import Determinismo

/-!
# `compare` and `sort`: jank's C++ beside Clojure's `Util.compare` and `Arrays.sort`

jank (commit 7135b7708; of the files below only core/seq.cpp changed since f3d82d654: `sort` moved
and now returns `()` for any empty input, which this model already gave):

- core.jank `compare` (line 5064) → `cpp/jank.runtime.compare` → core/equal.cpp `compare(l, r)`
  (line 24): `if(l.is_some() && r.is_nil()) return 1; return l.compare(r);`
- `object_ref::compare` (oref.hpp 830–884): two tagged small integers or reals are compared
  inline with `(r < l) - (l < r)`; otherwise the virtual `object::compare(object const &)` of the
  left operand runs (object.hpp 529), whose default (object.cpp 228) throws
  `runtime_unsupported_behavior` (lists, maps, sets, fns...).
- each type's `compare(object const &)`:
  - `nil::compare` (nil.cpp 39): 0 against nil, else -1;
  - numbers (number.cpp 139 `integer`, 228 `small_integer`, 342 `real`, 460 `small_real`;
    big_decimal.cpp 182; ratio.cpp 149; big_integer.cpp 177): `visit_number_like` on the right
    operand (visit.hpp 463: integer, small_integer, big_integer, big_decimal, real, small_real,
    ratio — not boolean), `(o < this) - (this < o)`; a non-number throws;
  - `boolean::compare` (number.cpp 56): the same `visit_number_like` on the right operand: a
    boolean is not number-like, so two booleans throw, and a boolean against a number compares
    the bool as 0/1;
  - `persistent_string::compare` (persistent_string.cpp 63), `character::compare`
    (character.cpp 94): `try_object` (rtti.hpp 22, throws on another type), then bytewise
    (jtl immutable_string.hpp 576);
  - `keyword::compare` (keyword.cpp 50): `expect_object<keyword>` (rtti.hpp 50), whose type check
    is only a `jank_debug_assert` (jtl/assert.hpp: compiled out under NDEBUG,
    jtl/primitive.hpp 3): a non-keyword is reinterpreted as a keyword and its bytes read as the
    `sym` pointer (keyword.hpp 50);
  - `symbol::compare` (symbol.cpp 83/95): `dyn_cast`, throws on another type; then ns and name;
  - `persistent_vector::compare` (persistent_vector.cpp 120/132): a vector only; count first,
    then elementwise with `runtime::compare`.
- core/seq.cpp `sort(coll)` (1098) / `sort(comp, coll)` (1131): copies into a vector and calls
  `std::stable_sort` with `compare(a, b) < 0`, or with `comp(a, b)` coerced: `jank_true` → less,
  `jank_false` → not less, else `to_int(o) < 0` (math.hpp 1411: `o.to_integer()`, an i64).

Clojure 1.12: `Util.compare` (Util.java 144): identical → 0; k2 null → 1; a Number →
`Numbers.compare` (lt both ways through the combined ops: long/long exact, with a double:
doubles, long/BigDecimal: BigDecimal, BigDecimal/double: doubles); otherwise
`((Comparable) k1).compareTo(k2)` (a ClassCastException for a non-Comparable or a mismatched
type); k1 null → -1. `sort` (core.clj): `java.util.Arrays.sort(a, comp)` = TimSort, which below
32 elements is `countRunAndMakeAscending` + `binarySort`. A fn used as a comparator goes through
`AFunction.compare` (AFunction.java 52): true → -1, false → `(f b a)` true → 1 else 0, a Number
→ `intValue()`, anything else (nil included) → an exception.
-/

namespace Jank.Compare

open Determinismo

/-- A double literal: its value, and its exact value as num / den (den a power of two). -/
structure Dbl where
  f : Float
  num : Int
  den : Nat
  code : String

instance : Inhabited Dbl := ⟨{ f := 0.0, num := 0, den := 1, code := "0.0" }⟩

/-- The values `compare` dispatches on. -/
inductive CV where
  | nil
  | bool (b : Bool)
  /-- small_integer / integer: a long. -/
  | long (v : Int)
  | dbl (d : Dbl)
  /-- big_decimal: n / 10^scale, exactly. -/
  | dec (n : Int) (scale : Nat)
  /-- ASCII strings only (UTF-16 vs UTF-8 order is the strings area's). -/
  | str (s : String)
  | char (c : Char)
  | kw (ns : String) (name : String)
  | sym (ns : String) (name : String)
  | vec (xs : List CV)
  /-- A value with no `compare` in jank and not `Comparable` in Clojure (a list, a map, a fn),
  with its identity: the same id is the same object. -/
  | other (id : Nat) (code : String)
  deriving Inhabited

partial def CV.code : CV → String
  | .nil => "nil"
  | .bool b => toString b
  | .long v => toString v
  | .dbl d => d.code
  | .dec n s => if s == 0 then s!"{n}M" else
      let a := n.natAbs; let p := 10 ^ s
      let frac := toString (a % p); let frac := String.ofList (List.replicate (s - frac.length) '0') ++ frac
      s!"{if n < 0 then "-" else ""}{a / p}.{frac}M"
  | .str s => s!"\"{s}\""
  | .char c => s!"\\{c}"
  | .kw ns n => if ns.isEmpty then s!":{n}" else s!":{ns}/{n}"
  | .sym ns n => if ns.isEmpty then s!"'{n}" else s!"'{ns}/{n}"
  | .vec xs => "[" ++ " ".intercalate (xs.map CV.code) ++ "]"
  | .other _ c => c

instance : Repr CV where reprPrec v _ := v.code

/-- How a comparison ended. -/
inductive Cmp where
  /-- A result, normalized to its sign. -/
  | ok (sign : Int)
  /-- A catchable exception. -/
  | throws (why : String)
  /-- Undefined behavior: an assertion abort in a debug build, an unchecked downcast in a release
  build (garbage read as a pointer: typically SIGSEGV). Never a catchable exception. -/
  | ub (why : String)
  deriving Repr, Inhabited

def Cmp.same : Cmp → Cmp → Bool
  | .ok a, .ok b => a == b
  | .throws _, .throws _ => true
  | _, _ => false

def signOf (lt gt : Bool) : Int := if lt then -1 else if gt then 1 else 0

def CV.isNumber : CV → Bool
  | .long _ | .dbl _ | .dec .. => true
  | _ => false

/-- `(o < this) - (this < o)` with C++ comparisons: a double against anything number-like via
the double (`i64 → f64` rounding as C++ and Java both do), NaN comparing false both ways; a
long against a long or a decimal exactly; a decimal against a double exactly (boost
`cpp_dec_float<100>` holds the double's exact expansion: assumption RC2). -/
def cppNumCmp : CV → CV → Int
  | .long a, .long b => signOf (a < b) (b < a)
  | .long a, .dbl d => signOf (Float.ofInt a < d.f) (d.f < Float.ofInt a)
  | .dbl d, .long b => signOf (d.f < Float.ofInt b) (Float.ofInt b < d.f)
  | .dbl d, .dbl e => signOf (d.f < e.f) (e.f < d.f)
  | .long a, .dec n s => signOf (a * 10 ^ s < n) (n < a * 10 ^ s)
  | .dec n s, .long b => signOf (n < b * 10 ^ s) (b * 10 ^ s < n)
  | .dec n s, .dec m t => signOf (n * 10 ^ t < m * 10 ^ s) (m * 10 ^ s < n * 10 ^ t)
  | .dec n s, .dbl d =>
    if d.f.isNaN then 0 else
    -- n/10^s vs num/den, exactly
    let l := n * d.den; let r := d.num * 10 ^ s
    signOf (l < r) (r < l)
  | .dbl d, .dec n s =>
    if d.f.isNaN then 0 else
    let l := d.num * 10 ^ s; let r := n * d.den
    signOf (l < r) (r < l)
  | _, _ => 0

/-- symbol.cpp `symbol::compare(symbol const &)` (95–118); also Symbol.compareTo. -/
def symCmp (ns n ns' n' : String) : Int :=
  if ns == ns' && n == n' then 0
  else if ns.isEmpty && !ns'.isEmpty then -1
  else if !ns.isEmpty && ns'.isEmpty then 1
  else if !ns.isEmpty && ns != ns' then signOf (ns < ns') (ns' < ns)
  else signOf (n < n') (n' < n)

/-- core/equal.cpp `compare` (24) and the per-type `compare(object const &)` it reaches. -/
def jankCompare : Nat → CV → CV → Cmp
  | 0, _, _ => .throws "fuel"
  | f + 1, l, r =>
    match l, r with
    -- equal.cpp 26: a non-nil left and a nil right.
    | .nil, .nil => .ok 0                                   -- nil.cpp 39
    | .nil, _ => .ok (-1)                                   -- nil.cpp 41
    | _, .nil => .ok 1                                      -- equal.cpp 28
    -- number.cpp 56: visit_number_like(o); a boolean is not number-like (visit.hpp 477–494).
    | .bool b, o =>
      if o.isNumber then .ok (cppNumCmp (.long (if b then 1 else 0)) o)
      else .throws "Objects of type `boolean` are not comparable to `boolean`."
    -- number.cpp 139/228/342/460, big_decimal.cpp 182; oref.hpp 834–866 for the inline cases.
    | .long a, o => if o.isNumber then .ok (cppNumCmp (.long a) o) else .throws "not comparable to `integer`"
    | .dbl d, o => if o.isNumber then .ok (cppNumCmp (.dbl d) o) else .throws "not comparable to `real`"
    | .dec n s, o => if o.isNumber then .ok (cppNumCmp (.dec n s) o) else .throws "not comparable"
    -- persistent_string.cpp 63, character.cpp 94: try_object throws.
    | .str a, .str b => .ok (signOf (a < b) (b < a))
    | .str _, _ => .throws "An object of type `persistent_string` was expected here"
    | .char a, .char b => .ok (signOf (a < b) (b < a))
    | .char _, _ => .throws "An object of type `character` was expected here"
    -- keyword.cpp 50: expect_object<keyword>: no check in a release build.
    | .kw ns n, .kw ns' n' => .ok (symCmp ns n ns' n')
    | .kw _ _, o => .ub s!"keyword::compare reads {o.code} as a keyword (expect_object, keyword.cpp 52)"
    -- symbol.cpp 83: dyn_cast, throws.
    | .sym ns n, .sym ns' n' => .ok (symCmp ns n ns' n')
    | .sym _ _, _ => .throws "The value for comparison must be a `symbol`"
    -- persistent_vector.cpp 120–157.
    | .vec xs, .vec ys =>
      if xs.length < ys.length then .ok (-1)
      else if xs.length > ys.length then .ok 1
      else
        let rec go : List CV → List CV → Cmp
          | [], _ => .ok 0
          | _, [] => .ok 0
          | a :: as, b :: bs => match jankCompare f a b with
            | .ok 0 => go as bs
            | other => other
        go xs ys
    | .vec _, _ => .throws "The value for comparison must be a `persistent_vector`"
    -- object.cpp 228: no compare behavior.
    | .other .., _ => .throws "runtime_unsupported_behavior: compare"

/-- BigDecimal.doubleValue(): the nearest double. -/
def decToFloat (n : Int) (s : Nat) : Float :=
  let m := Float.ofScientific n.natAbs true s
  if n < 0 then -m else m

/-- Numbers.compare (Numbers.java 268): `ops(x).combine(ops(y))`, then `lt` both ways. -/
def cljNumCompare (l r : CV) : Int :=
  let asF : CV → Float := fun
    | .long a => Float.ofInt a
    | .dbl d => d.f
    | .dec n s => decToFloat n s
    | _ => 0
  let isD : CV → Bool := fun | .dbl _ => true | _ => false
  if isD l || isD r then
    -- DoubleOps (any double operand, BigDecimal included: DoubleOps.opsWith(BigDecimalOps) is DOUBLE).
    signOf (asF l < asF r) (asF r < asF l)
  else cppNumCmp l r  -- longs and BigDecimals exactly (LongOps, BigDecimalOps)

/-- Identity, as the JVM has it: the same object. Booleans, keywords, nil and longs in
[-128, 127] (the reader boxes with Long.valueOf) are shared; an `other` by its id. -/
def identical : CV → CV → Bool
  | .nil, .nil => true
  | .bool a, .bool b => a == b
  | .kw a b, .kw c d => a == c && b == d
  | .long a, .long b => a == b && -128 ≤ a && a ≤ 127
  | .other a _, .other b _ => a == b
  | _, _ => false

/-- Util.compare (Util.java 144) and the `compareTo`s it reaches. -/
def cljCompare : Nat → CV → CV → Cmp
  | 0, _, _ => .throws "fuel"
  | f + 1, l, r =>
    if identical l r then .ok 0 else
    match l, r with
    | .nil, _ => .ok (-1)
    | _, .nil => .ok 1
    | l, r =>
      if l.isNumber then
        if r.isNumber then .ok (cljNumCompare l r) else .throws "ClassCastException: not a Number"
      else match l, r with
        | .bool a, .bool b => .ok (signOf (!a && b) (a && !b))       -- Boolean.compareTo
        | .str a, .str b => .ok (signOf (a < b) (b < a))
        | .char a, .char b => .ok (signOf (a < b) (b < a))
        | .kw ns n, .kw ns' n' => .ok (symCmp ns n ns' n')          -- Keyword.compareTo
        | .sym ns n, .sym ns' n' => .ok (symCmp ns n ns' n')        -- Symbol.compareTo
        | .vec xs, .vec ys =>                                        -- APersistentVector.compareTo
          if xs.length < ys.length then .ok (-1)
          else if xs.length > ys.length then .ok 1
          else
            let rec go : List CV → List CV → Cmp
              | [], _ => .ok 0
              | _, [] => .ok 0
              | a :: as, b :: bs => match cljCompare f a b with
                | .ok 0 => go as bs
                | other => other
            go xs ys
        | _, _ => .throws "ClassCastException"

def fuel : Nat := 8

/-! ## sort -/

/-- A comparator's verdict as the sort sees it. -/
inductive Verdict where
  | less | notLess
  | failed (c : Cmp)

/-- jank's `std::stable_sort` on n ≤ 7 elements: libstdc++'s `__insertion_sort` (the chunk
size of `__merge_sort_with_buffer` is 7; libc++ also uses insertion sort for short ranges):
for each i, `comp(*i, *first)` moves it to the front, else `__unguarded_linear_insert`
compares it with its predecessors while `comp(val, *prev)`. -/
def insertionSort {α : Type} [Inhabited α] (less : α → α → Except Cmp Bool) (xs : List α) : Except Cmp (List α) := do
  let mut done : Array α := #[]
  for x in xs do
    if done.isEmpty then done := done.push x
    else if ← less x done[0]! then done := #[x] ++ done
    else
      -- unguarded linear insert: from the back, while comp(val, prev).
      let mut j := done.size
      -- (a monadic test inside `&&` would run before the guard: test separately)
      while j > 0 do
        if ← less x done[j - 1]! then j := j - 1 else break
      done := (done.extract 0 j).push x ++ done.extract j done.size
  return done.toList

/-- TimSort below MIN_MERGE (TimSort.java `sort`, `countRunAndMakeAscending`, `binarySort`),
with `cmp` returning Comparator ints. -/
def timSortSmall {α : Type} [Inhabited α] (cmp : α → α → Except Cmp Int) (xs : List α) : Except Cmp (List α) := do
  let n := xs.length
  if n < 2 then return xs
  let mut a := xs.toArray
  -- countRunAndMakeAscending
  let mut runHi := 1
  if (← cmp a[1]! a[0]!) < 0 then
    runHi := 2
    while runHi < n do
      if (← cmp a[runHi]! a[runHi - 1]!) < 0 then runHi := runHi + 1 else break
    a := (a.extract 0 runHi).reverse ++ a.extract runHi n
  else
    runHi := 2
    while runHi < n do
      if (← cmp a[runHi]! a[runHi - 1]!) ≥ 0 then runHi := runHi + 1 else break
  -- binarySort from start = runHi
  let mut start := runHi
  while start < n do
    let pivot := a[start]!
    let mut left := 0
    let mut right := start
    while left < right do
      let mid := (left + right) / 2
      if (← cmp pivot a[mid]!) < 0 then right := mid else left := mid + 1
    a := ((a.extract 0 left).push pivot ++ a.extract left start) ++ a.extract (start + 1) n
    start := start + 1
  return a.toList

/-- `(sort coll)` in jank: `stable_sort` with `compare(a, b) < 0`. -/
def jankSort (xs : List CV) : Except Cmp (List CV) :=
  insertionSort (fun a b => match jankCompare fuel a b with
    | .ok s => .ok (s < 0)
    | c => .error c) xs

/-- `(sort coll)` in Clojure: TimSort with `compare` (through AFunction.compare: an int). -/
def cljSort (xs : List CV) : Except Cmp (List CV) :=
  timSortSmall (fun a b => match cljCompare fuel a b with
    | .ok s => .ok s
    | c => .error c) xs

/-! ## Comparator functions (`(sort f coll)`) -/

/-- What a comparator fn returns, by kind. -/
inductive FnKind where
  /-- `<`: true or false. -/
  | lt
  /-- `>`. -/
  | gt
  /-- `compare`. -/
  | cmp
  /-- `(fn [a b] (- a b))`: a long, possibly beyond int. -/
  | diff
  /-- `(fn [a b] nil)`. -/
  | retNil
  deriving Repr, BEq, Inhabited

inductive Ret where
  | bool (b : Bool)
  | long (v : Int)
  | nil

def FnKind.call : FnKind → Int → Int → Ret
  | .lt, a, b => .bool (a < b)
  | .gt, a, b => .bool (a > b)
  | .cmp, a, b => .long (signOf (a < b) (b < a))
  | .diff, a, b => .long (a - b)
  | .retNil, _, _ => .nil

def FnKind.code : FnKind → String
  | .lt => "<" | .gt => ">" | .cmp => "compare" | .diff => "(fn [a b] (- a b))" | .retNil => "(fn [a b] nil)"

/-- seq.cpp 1146–1162 (7135b7708): true → less, false → not less, else `to_int(o) < 0` (an i64; nil throws:
`object::to_integer`, object.cpp 263). -/
def jankFnLess (k : FnKind) (a b : Int) : Except Cmp Bool :=
  match k.call a b with
  | .bool t => .ok t
  | .long v => .ok (v < 0)
  | .nil => .error (.throws "nil is not number_like")

/-- AFunction.compare: Boolean true → -1; false → (f b a) ? 1 : 0; Number → intValue() (the low
32 bits); nil → NullPointerException. -/
def cljFnCompare (k : FnKind) (a b : Int) : Except Cmp Int :=
  match k.call a b with
  | .bool true => .ok (-1)
  | .bool false => match k.call b a with
    | .bool true => .ok 1
    | _ => .ok 0
  | .long v => .ok (BitVec.ofInt 32 v).toInt
  | .nil => .error (.throws "NullPointerException")

/-! ## The search -/

def d (f : Float) (num : Int) (den : Nat) (code : String) : CV := .dbl { f, num, den, code }

/-- 0.1 as a double is exactly 3602879701896397 / 2^55. -/
def cvUniverse : List CV :=
  [ .nil, .bool true, .bool false, .long 0, .long 1, .long 9007199254740993,
    d 0.0 0 1 "0.0", d 1.5 3 2 "1.5", d 0.1 3602879701896397 (2 ^ 55) "0.1", d (0.0 / 0.0) 0 1 "##NaN",
    d 9007199254740992.0 9007199254740992 1 "9007199254740992.0",
    .dec 1 1, .dec 1 0, .str "a", .str "b", .char 'a', .kw "" "a", .kw "x" "a", .sym "" "a",
    .vec [.long 1], .vec [.long 1, .long 2], .vec [.kw "" "a"], .other 1 "'(1)", .other 2 "{}" ]

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def showCmp : Cmp → String
  | .ok s => toString s
  | .throws w => s!"throws ({w})"
  | .ub w => s!"undefined behavior ({w})"

def showSort : Except Cmp (List CV) → String
  | .ok xs => "(" ++ " ".intercalate (xs.map CV.code) ++ ")"
  | .error c => showCmp c

/-- `(compare a b)`, the same object when both draws are the same element of the universe. -/
def comparePair : EStateM Stop World Unit := do
  let n := cvUniverse.length
  let i ← decide (σ := World) "compare.a" n
  let j ← decide (σ := World) "compare.b" n
  let a := cvUniverse.getD i .nil
  let b := cvUniverse.getD j .nil
  let jr := jankCompare fuel a b
  let cr := cljCompare fuel a b
  if !jr.same cr then
    violate (σ := World) "compare as Clojure's"
      s!"(compare {a.code} {b.code}): Clojure {showCmp cr}, jank {showCmp jr}"

/-- Atoms for sort inputs. -/
def sortAtoms : List CV :=
  [ .long 1, .long 0, .bool true, .bool false, .kw "" "a", .kw "" "b", .str "a", .nil, d 1.5 3 2 "1.5" ]

def sortVec : EStateM Stop World Unit := do
  let len ← decide (σ := World) "sort.length" 4
  let mut xs : List CV := []
  for _ in List.range len do
    xs := xs ++ [sortAtoms.getD (← decide (σ := World) "sort.elem" sortAtoms.length) .nil]
  let jr := jankSort xs
  let cr := cljSort xs
  let same := match jr, cr with
    | .ok a, .ok b => a.map CV.code == b.map CV.code
    | .error a, .error b => a.same b
    | _, _ => false
  if !same then
    violate (σ := World) "sort as Clojure's"
      s!"(sort [{" ".intercalate (xs.map CV.code)}]): Clojure {showSort cr}, jank {showSort jr}"

def fnKinds : List FnKind := [.lt, .gt, .cmp, .diff, .retNil]
def fnLongs : List Int := [0, 1, 2, 3000000000, -3000000000]

/-- `(sort f [a b c])` with a comparator fn of each kind. -/
def sortFn (exceptNarrowing : Bool) : EStateM Stop World Unit := do
  let k := fnKinds.getD (← decide (σ := World) "sortfn.kind" fnKinds.length) .lt
  let len ← decide (σ := World) "sortfn.length" 4
  let mut xs : List Int := []
  for _ in List.range len do
    xs := xs ++ [fnLongs.getD (← decide (σ := World) "sortfn.elem" fnLongs.length) 0]
  -- Clojure's narrowing of a long comparator result to int is its own quirk (assumption RC4).
  if exceptNarrowing && k == .diff && xs.any (fun a => xs.any fun b => a - b ≥ 2 ^ 31 ∨ a - b < -(2 ^ 31)) then
    return
  let jr := insertionSort (jankFnLess k) xs
  let cr := timSortSmall (cljFnCompare k) xs
  let same := match jr, cr with
    | .ok a, .ok b => a == b
    | .error a, .error b => a.same b
    | _, _ => false
  if !same then
    let shw := fun (r : Except Cmp (List Int)) => match r with
      | .ok l => s!"{l}" | .error c => showCmp c
    violate (σ := World) "sort with a comparator fn as Clojure's"
      s!"(sort {k.code} {xs}): Clojure {shw cr}, jank {shw jr}"

def runBody (body : EStateM Stop World Unit) (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- The full table: every ordered pair of the universe, those that disagree. -/
def pairTable : List (CV × CV × Cmp × Cmp) :=
  cvUniverse.flatMap fun a => cvUniverse.filterMap fun b =>
    let j := jankCompare fuel a b
    let c := cljCompare fuel a b
    if j.same c then none else some (a, b, c, j)

/-! ## Theorems -/

/-- The inline small-integer comparison `(r < l) - (l < r)` (oref.hpp 838) is the sign Clojure's
LongOps gives, for every pair of 64-bit longs. -/
theorem long_compare_matches (l r : BitVec 64) :
    ((if r.slt l then (1 : BitVec 64) else 0) - (if l.slt r then 1 else 0)) =
    (if l.slt r then (-1 : BitVec 64) else if r.slt l then 1 else 0) := by
  bv_decide

/-- Two booleans never compare in jank: `boolean::compare` sends a boolean to
`visit_number_like`, which has no boolean case. -/
theorem bool_bool_throws (a b : Bool) : ∃ w, jankCompare fuel (.bool a) (.bool b) = .throws w := by
  cases a <;> cases b <;> exact ⟨_, rfl⟩

/-- Clojure compares them (Boolean.compareTo). -/
theorem bool_bool_clojure (a b : Bool) :
    cljCompare fuel (.bool a) (.bool b) = .ok (signOf (!a && b) (a && !b)) := by
  cases a <;> cases b <;> rfl

/-- A keyword against any non-keyword, non-nil value is undefined behavior in jank. -/
theorem keyword_vs_other_ub (ns n : String) (o : CV)
    (h1 : ∀ a b, o ≠ .kw a b) (h2 : o ≠ .nil) : ∃ w, jankCompare fuel (.kw ns n) o = .ub w := by
  cases o with
  | nil => exact absurd rfl h2
  | kw a b => exact absurd rfl (h1 a b)
  | _ => exact ⟨_, rfl⟩

end Jank.Compare

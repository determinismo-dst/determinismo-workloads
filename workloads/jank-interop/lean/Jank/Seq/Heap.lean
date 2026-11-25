import Determinismo
import Jank.Seq.IntRange

/-!
# Sequences as heap objects: `seq`, `first`, `next`, `next_in_place`, `fresh_seq`, `doseq`

jank's sequence objects are mutable: `next_in_place()` (object.hpp 553: "if you own the
sequence ... you can mutate it in place") advances `persistent_vector_sequence::index`,
`native_vector_sequence::index`, `persistent_list::data`, `integer_range::start`,
`repeat::count` on the object itself. `doseq` (core.jank 2711) starts from `(fresh-seq coll)`
(an owned copy) and steps with `(next-in-place seq)`. But `cons::next()` (cons.cpp 35) returns
`tail.seq()` and `lazy_sequence` (lazy_sequence.cpp 33) returns its cached `s`: objects the
program still holds. From then on `doseq` mutates them.

Each object here is a heap cell (its identity matters); each C++ member function is a Lean
function on the heap. Elements are integers. The closures lazy sequences run are jank code
written out (`Code`): `concat`'s body (core.jank 2071) and `(lazy-seq r)`.

Clojure: seqs are immutable values; `doseq` visits the elements and changes nothing.
-/

namespace Jank.Seq.Heap

open Determinismo
open Jank.Seq.IntRange (IntRange)

abbrev Ref := Nat

/-- A lazy sequence's body (`(fn* lazy-seq# [] ...)`). -/
inductive Code where
  /-- core.jank 2071, `concat` [x y]: `(let [s (seq x)] (if s (if (chunked-seq? s) ...
  (cons (first s) (concat (rest s) y))) y))`. -/
  | concat (x y : Ref)
  /-- `(lazy-seq r)`. -/
  | ofRef (r : Ref)
  deriving Repr, BEq

/-- A heap object. -/
inductive Obj where
  | nil
  /-- persistent_vector (immutable). -/
  | vector (xs : List Int)
  /-- persistent_vector_sequence: its vector (shared, immutable) and `usize index`. -/
  | vseq (vec : List Int) (index : Nat)
  /-- native_vector_sequence (what `sort` returns): `data`, `usize index`. -/
  | nvseq (data : List Int) (index : Nat)
  /-- persistent_list: `data` (replaced by `next_in_place`). -/
  | plist (data : List Int)
  /-- integer_range (`start` advanced by `next_in_place`). -/
  | irange (r : IntRange)
  /-- repeat with a count (`count` decremented by `next_in_place`). -/
  | repeatN (count : Int) (value : Int)
  /-- obj::cons. -/
  | cons (head : Int) (tail : Ref)
  /-- lazy_sequence: `fn` (none once forced), `sv`, `s`. -/
  | lazy (fn : Option Code) (sv : Ref) (s : Ref)
  deriving Repr, BEq

structure Heap where
  objs : Array Obj := #[.nil]
  deriving Repr

/-- C++ throws and undefined behaviour stop the program. -/
abbrev HM := EStateM String Heap

def alloc (o : Obj) : HM Ref := do
  let h ← get
  set { h with objs := h.objs.push o }
  return h.objs.size

def load (r : Ref) : HM Obj := do
  match (← get).objs[r]? with
  | some o => return o
  | none => throw s!"dangling reference {r}"

def store (r : Ref) (o : Obj) : HM Unit :=
  modify fun h => { h with objs := h.objs.set! r o }

/-- `has_behavior(sequence_like)`: every type here but `persistent_vector`. -/
def sequenceLike : Obj → Bool
  | .vector _ => false
  | _ => true

/-- `std::vector`/immer `operator[]` past the end: undefined behaviour. -/
def atIdx (xs : List Int) (i : Nat) (what : String) : HM Int :=
  match xs[i]? with
  | some v => return v
  | none => throw s!"UB: {what}[{i}] read past the end (size {xs.length})"

mutual
/-- `object_ref::seq()` → each type's `seq()`. -/
def seqOf : Nat → Ref → HM Ref
  | 0, _ => throw "fuel"
  | f + 1, r => do
    match ← load r with
    | .nil => return 0
    -- persistent_vector.cpp:158 `seq()` = `fresh_seq()`: a new sequence (nil when empty)
    | .vector xs => if xs.isEmpty then return 0 else alloc (.vseq xs 0)
    -- persistent_vector_sequence.cpp:108: `this`
    | .vseq .. => return r
    -- native_vector_sequence.cpp:89: `data.empty() ? nil : this`
    | .nvseq d _ => if d.isEmpty then return 0 else return r
    -- persistent_list.cpp:100 `seq()` = `fresh_seq()`: a new box over the same data
    | .plist d => if d.isEmpty then return 0 else alloc (.plist d)
    -- integer_range.cpp:98, repeat.cpp:48, cons.cpp:20: `this`
    | .irange _ | .repeatN .. | .cons .. => return r
    -- lazy_sequence.cpp:33: `realize()`
    | .lazy .. => realize f r
  termination_by structural fuel a1 => fuel

/-- `fresh_seq()` (`.fresh_seq` in core.jank `fresh-seq`). -/
def freshSeq : Nat → Ref → HM Ref
  | 0, _ => throw "fuel"
  | f + 1, r => do
    match ← load r with
    | .nil => return 0
    | .vector xs => if xs.isEmpty then return 0 else alloc (.vseq xs 0)
    -- persistent_vector_sequence.cpp:113: a new box at the same index
    | .vseq v i => alloc (.vseq v i)
    -- native_vector_sequence.cpp:94
    | .nvseq d i => if d.isEmpty then return 0 else alloc (.nvseq d i)
    | .plist d => if d.isEmpty then return 0 else alloc (.plist d)
    -- integer_range.cpp:103
    | .irange ir => alloc (.irange ir)
    -- repeat.cpp:53 (finite)
    | .repeatN c v => alloc (.repeatN c v)
    -- cons.cpp:25: a new cons, the same tail
    | .cons h t => alloc (.cons h t)
    -- lazy_sequence.cpp:39: realize; nil → nil; else a lazy sequence over `s.fresh_seq()`
    | .lazy .. => do
      let s ← realize f r
      if s == 0 then return 0
      let fs ← freshSeq f s
      alloc (.lazy none 0 fs)
  termination_by structural fuel a1 => fuel

/-- `first()` of each type; `none` is nil. -/
def firstV : Nat → Ref → HM (Option Int)
  | 0, _ => throw "fuel"
  | f + 1, r => do
    match ← load r with
    | .nil => return none
    | .vector xs => return xs.head?
    -- persistent_vector_sequence.cpp:119 `vec->data[index]`
    | .vseq v i => return some (← atIdx v i "persistent_vector_sequence data")
    -- native_vector_sequence.cpp:107 `data[index]`
    | .nvseq d i => return some (← atIdx d i "native_vector_sequence data")
    | .plist d => return d.head?
    | .irange ir => return some ir.start.toInt
    | .repeatN _ v => return some v
    | .cons h _ => return some h
    -- lazy_sequence.cpp:53: realize; nil → nil; else `runtime::first(s)`
    | .lazy .. => do
      let s ← realize f r
      if s == 0 then return none
      rtFirst f s
  termination_by structural fuel a1 => fuel

/-- seq.cpp:299 `runtime::first`: `first()` when sequence_like, else `seq().first()`. -/
def rtFirst : Nat → Ref → HM (Option Int)
  | 0, _ => throw "fuel"
  | f + 1, r => do
    let o ← load r
    if sequenceLike o then firstV f r
    else do let s ← seqOf f r; if s == 0 then return none else firstV f s
  termination_by structural fuel a1 => fuel

/-- `next()` of each type. -/
def nextV : Nat → Ref → HM Ref
  | 0, _ => throw "fuel"
  | f + 1, r => do
    match ← load r with
    | .nil => return 0
    | .vector xs => do let s ← seqOf f r; if s == 0 then return 0 else (if xs.length ≤ 1 then return 0 else nextV f s)
    -- persistent_vector_sequence.cpp:124
    | .vseq v i => if i + 1 == v.length then return 0 else alloc (.vseq v (i + 1))
    -- native_vector_sequence.cpp:113
    | .nvseq d i => if i + 1 == d.length then return 0 else alloc (.nvseq d (i + 1))
    -- persistent_list.cpp:136
    | .plist d => if d.length < 2 then return 0 else alloc (.plist d.tail)
    -- integer_range.cpp:113
    | .irange ir => match IntRange.next ir with
      | .error e => throw e
      | .ok none => return 0
      | .ok (some ir') => alloc (.irange ir')
    -- repeat.cpp:67 (finite)
    | .repeatN c v => if c ≤ 1 then return 0 else alloc (.repeatN (c - 1) v)
    -- cons.cpp:35: nil tail → nil, else `tail.seq()`
    | .cons _ t => if t == 0 then return 0 else seqOf f t
    -- lazy_sequence.cpp:65: realize; nil → nil; else `runtime::next(s)`
    | .lazy .. => do
      let s ← realize f r
      if s == 0 then return 0
      rtNext f s
  termination_by structural fuel a1 => fuel

/-- seq.cpp:313 `runtime::next`. -/
def rtNext : Nat → Ref → HM Ref
  | 0, _ => throw "fuel"
  | f + 1, r => do
    let o ← load r
    if sequenceLike o then nextV f r
    else do let s ← seqOf f r; if s == 0 then return 0 else nextV f s
  termination_by structural fuel a1 => fuel

/-- `next_in_place()` of each type (object.cpp:303's default is `next()`). -/
def nextInPlace : Nat → Ref → HM Ref
  | 0, _ => throw "fuel"
  | f + 1, r => do
    match ← load r with
    -- persistent_vector_sequence.cpp:137: `++index`, then nil if `index == size`
    | .vseq v i => do
      store r (.vseq v (i + 1))
      if i + 1 == v.length then return 0 else return r
    -- native_vector_sequence.cpp:126: the same
    | .nvseq d i => do
      store r (.nvseq d (i + 1))
      if i + 1 == d.length then return 0 else return r
    -- persistent_list.cpp:145: nil if `size < 2`, else `data = data.rest()`
    | .plist d => if d.length < 2 then return 0 else do store r (.plist d.tail); return r
    -- integer_range.cpp:122: nil if `count() <= 1`, else `start += step`
    | .irange ir => match IntRange.nextInPlace ir with
      | .error e => throw e
      | .ok none => return 0
      | .ok (some ir') => do store r (.irange ir'); return r
    -- repeat.cpp:80: nil if `count <= 1`, else `count = count - 1`
    | .repeatN c v => if c ≤ 1 then return 0 else do store r (.repeatN (c - 1) v); return r
    -- cons, lazy_sequence, vector: object::next_in_place → `next()`
    | _ => nextV f r
  termination_by structural fuel a1 => fuel

/-- lazy_sequence.cpp:118 `realize()`: `force()` (run `fn` once, keep its value in `sv`), then
when `sv` is set: unwrap nested lazy sequences, `s = sv.seq()`, `sv = nil`. Returns `s`. -/
def realize : Nat → Ref → HM Ref
  | 0, _ => throw "fuel"
  | f + 1, r => do
    let .lazy fn sv s ← load r | throw "realize: not a lazy_sequence"
    -- force()
    let sv ← match fn with
      | some code => do
        let v ← runCode f code
        store r (.lazy none v s)
        pure v
      | none => pure sv
    if sv != 0 then do
      -- `auto ls{ sv }; sv = jank_nil;` before unwrapping (lazy_sequence.cpp:124-125)
      let .lazy _ _ s0 ← load r | throw "realize"
      store r (.lazy none 0 s0)
      let ls ← unwrap f sv
      let s' ← seqOf f ls
      store r (.lazy none 0 s')
      return s'
    else
      let .lazy _ _ s ← load r | throw "realize"
      return s
  termination_by structural fuel a1 => fuel

/-- lazy_sequence.cpp:159 `unwrap`: while a lazy sequence, its `sval()` (force, then `sv` or `s`). -/
def unwrap : Nat → Ref → HM Ref
  | 0, _ => throw "fuel"
  | f + 1, r => do
    match ← load r with
    | .lazy fn sv s => do
      let v ← match fn with
        | some code => do let v ← runCode f code; store r (.lazy none v s); pure v
        | none => pure sv
      let next := if v != 0 then v else s
      if next == 0 then return 0 else unwrap f next
    | _ => return r
  termination_by structural fuel a1 => fuel

/-- The jank code of a lazy sequence's body. -/
def runCode : Nat → Code → HM Ref
  | 0, _ => throw "fuel"
  | _ + 1, .ofRef r => return r
  | f + 1, .concat x y => do
    let s ← seqOf f x
    if s == 0 then return y
    -- (chunked-seq? s): no type here is chunkable (none has `chunked_first`)
    let some hd ← rtFirst f s | throw "concat: first of a non-empty seq is nil"
    let rest ← rtRest f s
    let tl ← alloc (.lazy (some (.concat rest y)) 0 0)
    rtCons f hd tl
  termination_by structural fuel a1 => fuel

/-- seq.cpp:351 `runtime::rest`: nil → (); `seq()` nil → (); `more(seq)` (a cons's tail, else
`next`); nil → (). -/
def rtRest : Nat → Ref → HM Ref
  | 0, _ => throw "fuel"
  | f + 1, r => do
    if r == 0 then return ← alloc (.plist [])
    let s ← seqOf f r
    if s == 0 then return ← alloc (.plist [])
    let m ← match ← load s with
      | .cons _ t => pure t
      | _ => rtNext f s
    if m == 0 then alloc (.plist []) else return m
  termination_by structural fuel a1 => fuel

/-- seq.cpp:371 `runtime::cons(head, tail)`: nil → a one-element list; a sequence_like tail is
kept as it is; otherwise `tail.seq()`. -/
def rtCons : Nat → Int → Ref → HM Ref
  | 0, _, _ => throw "fuel"
  | f + 1, hd, t => do
    if t == 0 then return ← alloc (.plist [hd])
    if sequenceLike (← load t) then alloc (.cons hd t)
    else do let s ← seqOf f t; alloc (.cons hd s)
  termination_by structural fuel a1 a2 => fuel
end

def F : Nat := 200

/-- `doseq` (core.jank 2711) with one binding and a body that records `x`:
`(loop [seq- (fresh-seq v), chunk- nil, count- 0, i- 0] (if (< i- count-) ...
(when-let [seq- (seq seq-)] (if (chunked-seq? seq-) ... (let [x (first seq-)] body
(recur (next-in-place seq-) nil 0 0))))))`. The chunked branch is never taken here. -/
def doseq (v : Ref) (maxIter : Nat) : HM (List Int) := do
  let mut cur ← freshSeq F v
  let mut seen : Array Int := #[]
  for _ in List.range maxIter do
    let s ← seqOf F cur
    if s == 0 then return seen.toList
    let some x ← rtFirst F s | throw "doseq: nil first"
    seen := seen.push x
    cur ← nextInPlace F s
  return seen.toList

/-- The same loop stepping with `next` (no mutation): the fix, for comparison. -/
def doseqWithNext (v : Ref) (maxIter : Nat) : HM (List Int) := do
  let mut cur ← freshSeq F v
  let mut seen : Array Int := #[]
  for _ in List.range maxIter do
    let s ← seqOf F cur
    if s == 0 then return seen.toList
    let some x ← rtFirst F s | throw "doseq: nil first"
    seen := seen.push x
    cur ← rtNext F s
  return seen.toList

/-- What a program reads from `r` without `doseq`: `(vec r)` through first/next. -/
def elems (r : Ref) (maxLen : Nat) : HM (List Int) := do
  let mut cur ← seqOf F r
  let mut out : Array Int := #[]
  for _ in List.range maxLen do
    if cur == 0 then return out.toList
    let some x ← rtFirst F cur | throw "nil first"
    out := out.push x
    cur ← rtNext F cur
  return out.toList

/-- persistent_vector_sequence.cpp:124 / native_vector_sequence.cpp:113 `next()`'s index test:
`++n; if(n == size) nil`. An index already at (or past) the size never meets it. -/
def vseqNextIndex (size i : Nat) : Option Nat := if i + 1 == size then none else some (i + 1)

/-- Past the end, `next()` never returns nil: walking such a sequence (`count`, `vec`, printing)
does not terminate. -/
theorem vseq_past_end_never_ends (size k : Nat) : vseqNextIndex size (size + k) = some (size + k + 1) := by
  unfold vseqNextIndex
  have : (size + k + 1 == size) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp [this]

/-- How `count` ended. -/
inductive Count where
  | n (k : Int)
  /-- More than the bound of `next()` steps without nil: the walk does not end. -/
  | hang
  deriving Repr, BEq, DecidableEq

/-- seq.cpp:842 `sequence_length`: `countable` types answer `count()` (persistent_vector_sequence.cpp:82
`size - index`, a `usize`; native_vector_sequence.cpp:101 the same; persistent_list.cpp:114;
integer_range.cpp:186); others walk `first`/`next` (sequence_range.hpp) until nil. The jank
`count` boxes the `usize` as an i64. -/
def seqLength (r : Ref) (bound : Nat) : HM Count := do
  let usize (k : Int) : Int := (BitVec.ofInt 64 k).toInt
  match ← load r with
  | .nil => return .n 0
  | .vector xs => return .n xs.length
  | .vseq v i => return .n (usize (v.length - i))
  | .nvseq d i => return .n (usize (d.length - i))
  | .plist d => return .n d.length
  | .irange ir => match IntRange.count ir with
    | .ok c => return .n c.toInt
    | .error e => throw e
  | _ => do
    let mut cur ← seqOf F r
    let mut k : Nat := 0
    for _ in List.range bound do
      if cur == 0 then return .n k
      k := k + 1
      cur ← nextV F cur
    return .hang

/-! ## Programs: a held sequence, a wrapper over it, a `doseq` over the wrapper -/

/-- The sequence the program holds. -/
inductive Base where
  /-- `(seq [1 2 3])`. -/
  | vecSeq
  /-- `(rest [0 1 2 3])`. -/
  | vecRest
  /-- `(range 1 4)`. -/
  | range
  /-- `(sort [3 1 2])`. -/
  | sorted
  /-- `(list 1 2 3)`. -/
  | list
  /-- `(repeat 3 7)`. -/
  | repeat
  /-- `[1 2 3]`. -/
  | vector
  deriving Repr, BEq, Inhabited

def Base.code : Base → String
  | .vecSeq => "(seq [1 2 3])" | .vecRest => "(rest [0 1 2 3])" | .range => "(range 1 4)"
  | .sorted => "(sort [3 1 2])" | .list => "(list 1 2 3)" | .repeat => "(repeat 3 7)" | .vector => "[1 2 3]"

def Base.elements : Base → List Int
  | .repeat => [7, 7, 7]
  | _ => [1, 2, 3]

/-- Builds the base the way the jank functions do. -/
def Base.build : Base → HM Ref
  | .vecSeq => do let v ← alloc (.vector [1, 2, 3]); seqOf F v
  | .vecRest => do let v ← alloc (.vector [0, 1, 2, 3]); rtRest F v
  | .range => alloc (.irange ⟨1, 4, 1, .positive⟩)
  -- seq.cpp:1098 `sort`: a native_vector_sequence over the sorted elements
  | .sorted => alloc (.nvseq [1, 2, 3] 0)
  | .list => alloc (.plist [1, 2, 3])
  -- repeat.cpp:39 `create(count, value)`
  | .repeat => alloc (.repeatN 3 7)
  | .vector => alloc (.vector [1, 2, 3])

/-- What `doseq` walks. -/
inductive Wrap where
  | direct
  /-- `(cons 0 b)`. -/
  | cons
  /-- `(concat [0] b)`. -/
  | concat
  /-- `(lazy-seq b)`. -/
  | lazySeq
  /-- `(cons 0 (lazy-seq b))`. -/
  | consLazy
  deriving Repr, BEq, Inhabited

def Wrap.code (w : Wrap) (b : String) : String :=
  match w with
  | .direct => b | .cons => s!"(cons 0 b)" | .concat => s!"(concat [0] b)"
  | .lazySeq => "(lazy-seq b)" | .consLazy => "(cons 0 (lazy-seq b))"

def Wrap.prefix : Wrap → List Int
  | .cons | .concat | .consLazy => [0]
  | _ => []

def Wrap.build (w : Wrap) (b : Ref) : HM Ref :=
  match w with
  | .direct => return b
  | .cons => rtCons F 0 b
  | .concat => do let v ← alloc (.vector [0]); alloc (.lazy (some (.concat v b)) 0 0)
  | .lazySeq => alloc (.lazy (some (.ofRef b)) 0 0)
  | .consLazy => do let l ← alloc (.lazy (some (.ofRef b)) 0 0); rtCons F 0 l

/-- One program: `(let [b <base> w <wrap>] (doseq [x w] (record x)) [recorded (vec b) (vec w)])`,
optionally a second `doseq` over `w`. -/
structure Program where
  base : Base
  wrap : Wrap
  twice : Bool
  deriving Repr

def Program.code (p : Program) : String :=
  s!"(let [b {p.base.code} w {p.wrap.code "b"}] (doseq [x w] (record x)){if p.twice then " (doseq [x w] (record x))" else ""} [(count b) (count w) (vec b) (vec w)])"

/-- What a program observes: the recorded elements, `(count b)`, `(count w)`, then `(vec b)` and
`(vec w)` (an error: a throw or undefined behaviour while reading). -/
structure Seen where
  recorded : List Int
  counts : Count × Count
  vecs : Except String (List Int × List Int)

instance : BEq Seen where
  beq a b := a.recorded == b.recorded && a.counts == b.counts &&
    (match a.vecs, b.vecs with
     | .ok x, .ok y => x == y
     | .error x, .error y => x == y
     | _, _ => false)

/-- jank: the recorded elements, then `b`'s and `w`'s counts and elements read afterwards
(`fixed`: `doseq` stepping with `next`). -/
def Program.jank (p : Program) (fixed : Bool := false) : Except String Seen :=
  let loop := if fixed then doseqWithNext else doseq
  let body : HM Seen := do
    let b ← p.base.build
    let w ← p.wrap.build b
    let mut seen ← loop w 20
    if p.twice then seen := seen ++ (← loop w 20)
    let cb ← seqLength b 1000
    let cw ← seqLength w 1000
    let h ← get
    let vecs := match (do let bs ← elems b 20; let ws ← elems w 20; pure (bs, ws) : HM _).run h with
      | .ok r _ => .ok r
      | .error e _ => .error e
    return { recorded := seen, counts := (cb, cw), vecs }
  match body.run {} with
  | .ok r _ => .ok r
  | .error e _ => .error e

/-- Clojure: values; `doseq` changes nothing. -/
def Program.clj (p : Program) : Seen :=
  let ws := p.wrap.prefix ++ p.base.elements
  { recorded := if p.twice then ws ++ ws else ws,
    counts := (.n p.base.elements.length, .n ws.length),
    vecs := .ok (p.base.elements, ws) }

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def bases : List Base := [.vecSeq, .vecRest, .range, .sorted, .list, .repeat, .vector]
def wraps : List Wrap := [.direct, .cons, .concat, .lazySeq, .consLazy]

def Count.show : Count → String
  | .n k => toString k
  | .hang => "does not terminate"

def Seen.show (s : Seen) : String :=
  let v := match s.vecs with
    | .ok (bs, ws) => s!"{bs} {ws}"
    | .error e => s!"<{e}>"
  s!"recorded {s.recorded}, counts {s.counts.1.show} {s.counts.2.show}, vecs {v}"

def Program.verdict (p : Program) : Option String :=
  let c := p.clj
  match p.jank with
  | .error e => some s!"{p.code}: Clojure {c.show}, jank: {e}"
  | .ok j => if j != c then some s!"{p.code}: Clojure {c.show}, jank {j.show}" else none

def body : EStateM Stop World Unit := do
  let base := (← pick (σ := World) "seq.base" bases).getD .vector
  let wrap := (← pick (σ := World) "seq.wrap" wraps).getD .direct
  let twice := (← decide (σ := World) "seq.doseq_twice" 2) == 1
  let p : Program := { base, wrap, twice }
  if let some d := p.verdict then violate (σ := World) "doseq changes no value" d

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

set_option maxRecDepth 200000 in
/-- `(let [w (cons 0 (range 1 4))] (doseq [x w]) [(count w) (vec w)])`: after the `doseq`, `w`
is `(0 3)` (and the range `(3)`); Clojure: `(0 1 2 3)` and `(1 2 3)`. -/
theorem cons_range_after_doseq :
    (Program.jank { base := .range, wrap := .cons, twice := false }).toOption.map (fun s => (s.counts, s.vecs.toOption)) =
      some ((.n 1, .n 2), some ([3], [0, 3])) := by
  decide

def bodyFixed : EStateM Stop World Unit := do
  let base := (← pick (σ := World) "seq.base" bases).getD .vector
  let wrap := (← pick (σ := World) "seq.wrap" wraps).getD .direct
  let twice := (← decide (σ := World) "seq.doseq_twice" 2) == 1
  let p : Program := { base, wrap, twice }
  match p.jank (fixed := true) with
  | .ok j => if !(j == p.clj) then violate (σ := World) "doseq changes no value" p.code
  | .error e => violate (σ := World) "doseq changes no value" e

def runFixed (source : Source) : Ended :=
  match bodyFixed.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

def allPrograms : List Program :=
  bases.flatMap fun base => wraps.flatMap fun wrap => [false, true].map fun twice => { base, wrap, twice }

end Jank.Seq.Heap

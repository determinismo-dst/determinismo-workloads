import Std.Tactic.BVDecide
import Determinismo

/-!
# `range` over integers: obj/integer_range.cpp, beside Clojure's LongRange / Range

Replica of jank 7135b7708 (integer_range.cpp, range.cpp and core.jank are unchanged from
f3d82d654, so their line numbers hold).

core.jank `range` (core.jank 2827) calls `integer_range::create` when every argument is
`integer?`, else `range::create` (Jank/Seq/Range.lean). The object keeps `start`, `end`, `step`
as `i64` and recomputes `count()` on every `next()` (integer_range.cpp 113); `count()` (186)
computes `end - start` in i64, rejects some ranges with a conservative overflow check, and divides.

jank documents signed overflow as well defined (book at 7135b7708: "Signed integer overflow is
well defined and will wrap"):
the subtraction `end - start` wraps (two's complement, `BitVec 64`). Where C++ would be undefined
(the subtraction or `diff + offset` overflowing) the walk notes it (`ubNotes`).

Clojure (LongRange.java, Range.java): the elements are `start + k*step` while below `end` (above,
for a negative step), computed exactly: when LongRange's count overflows, `LongRange.create`
falls back to `Range`, whose `addP` promotes. So Clojure's answer is the mathematical sequence.
-/

namespace Jank.Seq.IntRange

open Determinismo

abbrev I64 := BitVec 64

def i64Max : I64 := 0x7FFFFFFFFFFFFFFF
def i64Min : I64 := 0x8000000000000000

/-- The `bounds_check_t` stored in the object (never called by any member function). -/
inductive Check where
  | positive | negative
  deriving Repr, BEq, DecidableEq

/-- `obj::integer_range`'s fields (integer_range.hpp 84-87): `start`, `end` (here `finish`),
`step`, `bounds_check`. -/
structure IntRange where
  start : I64
  finish : I64
  step : I64
  boundsCheck : Check
  deriving Repr, BEq, DecidableEq

/-- integer_range.cpp:10 `positive_step_bounds_check(val, end)`: `end <= val`. -/
def positiveStepBoundsCheck (val e : I64) : Bool := e.sle val

/-- integer_range.cpp:15 `negative_step_bounds_check(val, end)`: `val <= end`. -/
def negativeStepBoundsCheck (val e : I64) : Bool := val.sle e

/-- What `create` returns. -/
inductive Created where
  /-- `persistent_list::empty()`. -/
  | emptyList
  /-- `repeat::create(make_box(start))`: infinite. -/
  | repeatInf (v : I64)
  | range (r : IntRange)
  deriving Repr, BEq, DecidableEq

/-- integer_range.cpp:62 `create(i64 end)`. -/
def create1 (e : I64) : Created :=
  if (0 : I64).slt e then .range ⟨0, e, 1, .positive⟩ else .emptyList

/-- integer_range.cpp:79 `create(i64 start, i64 end, i64 step)`. -/
def create3 (s e st : I64) : Created :=
  if ((0 : I64).slt st && e.slt s) || (st.slt 0 && s.slt e) || s == e then .emptyList
  else if st == 0 then .repeatInf s
  else .range ⟨s, e, st, if (0 : I64).slt st then .positive else .negative⟩

/-- integer_range.cpp:74 `create(i64 start, i64 end)` = `create(start, end, 1)`. -/
def create2 (s e : I64) : Created := create3 s e 1

/-- integer_range.cpp:186 `count()`. The `usize` result as its 64 bits (`static_cast<size_t>`
of the i64 quotient). Errors are the two `std::runtime_error`s. -/
def count (r : IntRange) : Except String I64 :=
  let s := r.step
  if s == 0 then .error "integer_range step shouldn't be 0."
  else
    let diff := r.finish - r.start
    let offset : I64 := if (0 : I64).slt s then -1 else 1
    if ((0 : I64).slt s && (i64Max - s + offset).slt diff)
        || (s.slt 0 && diff.slt (i64Min - s + offset)) then
      .error "integer_range overflow occurred in arithmetic."
    else .ok ((diff + offset + s).sdiv s)

/-- Undefined behaviour in `count()` under ISO C++ (signed overflow), wrapping per jank's
documentation: `end - start`, then `diff + offset`. -/
def ubNotes (r : IntRange) : List String :=
  let diff := r.finish - r.start
  let offset : I64 := if (0 : I64).slt r.step then -1 else 1
  (if BitVec.ssubOverflow r.finish r.start then ["signed overflow in `end - start` (integer_range.cpp:194)"] else []) ++
  (if BitVec.saddOverflow diff offset then ["signed overflow in `diff + offset` (integer_range.cpp:203)"] else [])

/-- integer_range.cpp:108 `first()`: `make_box(start)`. -/
def first (r : IntRange) : I64 := r.start

/-- integer_range.cpp:113 `next()`: nil when `count() <= 1` (an unsigned comparison: `usize`),
else a new range from `start + step`. -/
def next (r : IntRange) : Except String (Option IntRange) := do
  let c ← count r
  if c.ule 1 then return none
  return some { r with start := r.start + r.step }

/-- integer_range.cpp:122 `next_in_place()`: the same test, then `start += step` on this object. -/
def nextInPlace (r : IntRange) : Except String (Option IntRange) := next r

/-- seq.cpp:842 `sequence_length` on an integer range: `countable`, so `count()`; the jank
function `count` returns that `usize` boxed through `convert<usize>` as an i64 (the same bits). -/
def seqCount : Created → Except String Int
  | .emptyList => .ok 0
  | .repeatInf _ => .error "hangs: counts an infinite repeat"
  | .range r => (count r).map (·.toInt)

/-! ## Walking a range: what a program sees -/

/-- How a walk ended. -/
inductive Ending where
  | done
  | throws (msg : String)
  /-- Fuel ran out: more elements follow. -/
  | more
  deriving Repr, BEq, DecidableEq

structure Walk where
  xs : List Int
  ending : Ending
  deriving Repr, BEq, DecidableEq

def Ending.show : Ending → String
  | .done => "end"
  | .throws m => s!"then throws \"{m}\""
  | .more => "..."

def Walk.show (w : Walk) : String := s!"{w.xs} {w.ending.show}"

/-- `sequence_range` iteration (sequence_range.hpp: `first()`, then `next()` until nil): what
`vec`, `reduce`, `doall`, printing see, up to `fuel` elements. -/
def walkRange : Nat → IntRange → List Int → Walk
  | 0, _, acc => ⟨acc.reverse, .more⟩
  | f + 1, r, acc =>
    let acc := (first r).toInt :: acc
    match next r with
    | .error e => ⟨acc.reverse, .throws e⟩
    | .ok none => ⟨acc.reverse, .done⟩
    | .ok (some r') => walkRange f r' acc

def walk (fuel : Nat) : Created → Walk
  | .emptyList => ⟨[], .done⟩
  | .repeatInf v => ⟨List.replicate fuel v.toInt, .more⟩
  | .range r => walkRange fuel r []

/-! ## Clojure: LongRange and Range (exact) -/

/-- The elements of `(range start end step)` per LongRange.create / Range.create: exact
`start + k*step` while `< end` (`> end` for a negative step); step 0: empty when start = end,
else `start` forever. Up to `fuel` elements. -/
def cljWalk (start finish step : Int) (fuel : Nat) : Walk :=
  if step == 0 then
    if start == finish then ⟨[], .done⟩ else ⟨List.replicate fuel start, .more⟩
  else
    let inside (v : Int) : Bool := if step > 0 then v < finish else v > finish
    let rec go : Nat → Int → List Int → Walk
      | 0, v, acc => if inside v then ⟨acc.reverse, .more⟩ else ⟨acc.reverse, .done⟩
      | f + 1, v, acc => if inside v then go f (v + step) (v :: acc) else ⟨acc.reverse, .done⟩
    go fuel start []

/-- Clojure's count of a finite range: ceil((end - start) / step), 0 when empty. -/
def cljCount (start finish step : Int) : Option Int :=
  if step == 0 then (if start == finish then some 0 else none)
  else if step > 0 then (if finish ≤ start then some 0 else some ((finish - start + step - 1) / step))
  else (if finish ≥ start then some 0 else some ((start - finish + (-step) - 1) / (-step)))

/-! ## The world: a range drawn, its walk and count judged -/

/-- Values drawn: the i64 extremes, values near them, and small ones. -/
def interesting : List I64 :=
  [i64Min, i64Min + 1, 0xC000000000000000 /- -2^62 -/, 0xBA9E4F6A00000000 /- ≈ -5e18 -/,
   -3, -2, -1, 0, 1, 2, 3, 5,
   0x4000000000000000 /- 2^62 -/, 0x2A5A058FC295ED00 /- ≈ 3.05e18 -/, i64Max - 2, i64Max - 1, i64Max]

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

/-- One question: the arity, the arguments, jank's walk and count, Clojure's. -/
structure Question where
  args : List I64
  deriving Repr

def Question.program (q : Question) : String :=
  s!"(range {" ".intercalate (q.args.map fun a => toString a.toInt)})"

def Question.jank (q : Question) : Created :=
  match q.args with
  | [e] => create1 e
  | [s, e] => create2 s e
  | [s, e, st] => create3 s e st
  | _ => .emptyList

def Question.clj (q : Question) : Int × Int × Int :=
  match q.args with
  | [e] => (0, e.toInt, 1)
  | [s, e] => (s.toInt, e.toInt, 1)
  | [s, e, st] => (s.toInt, e.toInt, st.toInt)
  | _ => (0, 0, 1)

def fuel : Nat := 8

/-- The disagreement, if any: elements (first `fuel`), the ending, the count. -/
def Question.verdict (q : Question) : Option String :=
  let j := q.jank
  let (s, e, st) := q.clj
  let jw := walk fuel j
  let cw := cljWalk s e st fuel
  if jw != cw then
    some s!"{q.program}: Clojure {cw.show}, jank {jw.show}"
  else
    match cljCount s e st, seqCount j with
    | some c, .ok jc => if c != jc then some s!"(count {q.program}): Clojure {c}, jank {jc}" else none
    | some c, .error m => some s!"(count {q.program}): Clojure {c}, jank throws {m}"
    | none, _ => none

def drawQuestion : EStateM Stop World Question := do
  let arity := (← decide (σ := World) "range.arity" 3) + 1
  let mut args := []
  for i in List.range arity do
    let v ← pick (σ := World) s!"range.arg{i}" interesting
    args := args ++ [v.getD 0]
  return { args }

def body : EStateM Stop World Unit := do
  let q ← drawQuestion
  if let some d := q.verdict then violate (σ := World) "range agrees with Clojure" d

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- Every question over the drawn values (for a full table). -/
def allQuestions : List Question :=
  (interesting.map fun e => { args := [e] }) ++
  (interesting.flatMap fun s => interesting.map fun e => { args := [s, e] }) ++
  (interesting.flatMap fun s => interesting.flatMap fun e => interesting.map fun st => { args := [s, e, st] })

/-! ## The same object with an exact count (the fix): nothing found -/

/-- `count()` computed on exact integers (as LongRange's `rangeCount` with Range's fallback). -/
def countExact (r : IntRange) : Int :=
  let d := r.finish.toInt - r.start.toInt
  let s := r.step.toInt
  if s > 0 then (d + s - 1) / s else (-d + (-s) - 1) / (-s)

def walkExact : Nat → IntRange → List Int → Walk
  | 0, _, acc => ⟨acc.reverse, .more⟩
  | f + 1, r, acc =>
    let acc := r.start.toInt :: acc
    if countExact r ≤ 1 then ⟨acc.reverse, .done⟩
    else walkExact f { r with start := r.start + r.step } acc

def Question.fixedAgrees (q : Question) : Bool :=
  let (s, e, st) := q.clj
  let w := match q.jank with
    | .emptyList => ⟨[], .done⟩
    | .repeatInf v => ⟨List.replicate fuel v.toInt, .more⟩
    | .range r => walkExact fuel r []
  w == cljWalk s e st fuel

def bodyFixed : EStateM Stop World Unit := do
  let q ← drawQuestion
  if !q.fixedAgrees then violate (σ := World) "range agrees with Clojure" q.program

def runFixed (source : Source) : Ended :=
  match bodyFixed.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## Theorems -/

/-- A positive step: `count()` throws exactly when `end - start` (wrapped) exceeds
`max - step - 1`, i.e. when `diff + step >= max`: two short of where `diff + step - 1`
would overflow. -/
theorem count_throws_pos (s e st : I64) (h : (0 : I64).slt st) :
    (count ⟨s, e, st, .positive⟩).toBool = false ↔ (i64Max - st - 1).slt (e - s) := by
  have hne : (st == 0) = false := by
    simp only [beq_eq_false_iff_ne]; intro h0; subst h0; simp at h
  unfold count
  simp only [hne, h, Bool.false_eq_true, ite_false, ite_true, Bool.true_and]
  have hneg : st.slt 0 = false := by bv_decide
  simp only [hneg, Bool.false_and, Bool.or_false]
  split <;> simp_all [Except.toBool]
  · bv_decide
  · bv_decide

/-- A positive step with no wrap in `end - start` and no throw: `count()` is Clojure's
`ceil((end - start) / step)` (checked on 64-bit words: `(diff + step - 1) / step`). -/
theorem count_ok_pos (s e st : I64) (h : (0 : I64).slt st) (hlt : s.slt e)
    (hno : BitVec.ssubOverflow e s = false) (hok : ¬ (i64Max - st - 1).slt (e - s)) :
    count ⟨s, e, st, .positive⟩ = .ok ((e - s + -1 + st).sdiv st) := by
  have hne : (st == 0) = false := by
    simp only [beq_eq_false_iff_ne]; intro h0; subst h0; simp at h
  unfold count
  simp only [hne, h, Bool.false_eq_true, ite_false, ite_true, Bool.true_and]
  have hneg : st.slt 0 = false := by bv_decide
  simp only [hneg, Bool.false_and, Bool.or_false]
  have hk : ((i64Max - st + -1).slt (e - s)) = false := by
    simp only [Bool.not_eq_true] at hok; bv_decide
  simp only [hk, Bool.false_eq_true, ite_false]

/-- `(range -9223372036854775808 9223372036854775807 4611686018427387904)`: the subtraction
wraps to -1, `count()` is 0, so `next()` is nil after the first element; Clojure's range has 4. -/
theorem quarter_steps_count :
    count ⟨i64Min, i64Max, 0x4000000000000000, .positive⟩ = .ok 0 ∧
    cljCount i64Min.toInt i64Max.toInt (0x4000000000000000 : I64).toInt = some 4 := by
  constructor
  · rfl
  · rfl

/-- `(range 0 10 9223372036854775807)`: `count()` throws, so the first `next()` throws;
Clojure's range is `(0)`. -/
theorem max_step_throws :
    next ⟨0, 10, i64Max, .positive⟩ = .error "integer_range overflow occurred in arithmetic." := by
  rfl

/-- `(range 9223372036854775807)`: `count()` throws (diff = max > max - 2). -/
theorem range_max_throws :
    create1 i64Max = .range ⟨0, i64Max, 1, .positive⟩ ∧
    next ⟨0, i64Max, 1, .positive⟩ = .error "integer_range overflow occurred in arithmetic." := by
  constructor <;> rfl

end Jank.Seq.IntRange

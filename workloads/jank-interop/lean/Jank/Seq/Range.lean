import Determinismo
import Jank.Numbers

/-!
# `range` with a non-integer argument: obj/range.cpp, array_chunk.cpp, beside Clojure's Range

core.jank `range` (2827) calls `range::create` unless every argument is `integer?`:
`(range 0 2.5)`, `(range 2147483646 2147483649.0)`. The object walks by `add(val, step)`
(core/math.hpp `add`), in chunks of 32 (`force_chunk`, range.cpp 132), stopping when
`bounds_check(val, end)` (`lte(end, val)` for a positive step, `lte(val, end)` otherwise).

`add` of two small integers is a 32-bit `int` addition (round 1, D1; `Jank.Numbers.jankIntOp`):
so a range of small integers whose end is a real past 2^31 wraps instead of ending.

Clojure's Range (Range.java) walks by `Numbers.addP` (exact, promoting), with the same chunking.

Modeled values: integer start and step (jank's small or heap integers), the end an exact
half-integer (`n/2`: the reals used are exact doubles, and `lte` of a double and an integer
converts the integer to double: exact below 2^53, assumption S4).
-/

namespace Jank.Seq.Range

open Determinismo Jank.Numbers

/-- The end: `n/2` (a real such as `2.5` or `2147483649.0`). -/
structure Bound where
  twice : Int
  deriving Repr, BEq, DecidableEq

def Bound.code (b : Bound) : String :=
  if b.twice % 2 == 0 then s!"{b.twice / 2}.0" else s!"{b.twice / 2}.5"

/-- An integer value of the walk (small or heap integer). -/
def ival : JNum → Int
  | .small v => v.toInt
  | .int v => v.toInt
  | .big v => v
  | _ => 0

/-- core/math.hpp `lte(end, val)` with a real `end` and an integer `val`: `end->data <= val->data`
(the integer converted to double; exact here). -/
def lteEndVal (e : Bound) (v : JNum) : Bool := e.twice ≤ 2 * ival v

/-- `lte(val, end)`. -/
def lteValEnd (v : JNum) (e : Bound) : Bool := 2 * ival v ≤ e.twice

inductive Check where
  | positive | negative
  deriving Repr, BEq, DecidableEq

/-- range.cpp:11 `positive_step_bounds_check(val, end)` = `lte(end, val)`;
range.cpp:16 `negative_step_bounds_check(val, end)` = `lte(val, end)`. -/
def boundsCheck : Check → JNum → Bound → Bool
  | .positive, v, e => lteEndVal e v
  | .negative, v, e => lteValEnd v e

/-- math.hpp `is_pos`: `0ll < data`. -/
def isPos (v : JNum) : Bool := 0 < ival v
def isNeg (v : JNum) : Bool := ival v < 0
def isZero (v : JNum) : Bool := ival v == 0

/-- core/math.hpp `add(object_ref, object_ref)` for integer operands (round 1's replica). -/
def add (a b : JNum) : JNum :=
  match jankIntOp .add a b with
  | .ok r => r
  | .error _ => a

/-- What `range::create` returns. -/
inductive Created where
  | emptyList
  | repeatInf (v : JNum)
  | range (start step : JNum) (e : Bound) (c : Check)

/-- range.cpp:99 `create(start, end, step)`: empty when `is_pos(step) && lt(end, start)`, or
`is_neg(step) && lt(start, end)`, or `is_equiv(start, end)`; `repeat` when `is_zero(step)`. -/
def create3 (start : JNum) (e : Bound) (step : JNum) : Created :=
  if (isPos step && e.twice < 2 * ival start) || (isNeg step && 2 * ival start < e.twice)
      || 2 * ival start == e.twice then .emptyList
  else if isZero step then .repeatInf start
  else .range start step e (if isPos step then .positive else .negative)

/-- range.cpp:94 `create(start, end)` = `create(start, end, make_box(1))`. -/
def create2 (start : JNum) (e : Bound) : Created := create3 start e (.small 1)

/-- range.cpp:82 `create(end)`: `is_pos(end)` → a range from `make_box(0)` by `make_box(1)`. -/
def create1 (e : Bound) : Created :=
  if 0 < e.twice then .range (.small 0) (.small 1) e .positive else .emptyList

def chunkSize : Nat := 32

/-- range.cpp:132 `force_chunk()`, its loop: `n` counts down from 32; each round pushes `val`,
steps it with `add`, and returns the chunk at once when `bounds_check(val, end)`. -/
def forceChunkLoop (step : JNum) (e : Bound) (c : Check) : Nat → JNum → List JNum → List JNum × Option JNum
  | 0, val, arr =>
    -- after the loop (range.cpp:155): a full last chunk, or a full chunk and `chunk_next` from val
    if boundsCheck c val e then (arr.reverse, none) else (arr.reverse, some val)
  | k + 1, val, arr =>
    let arr := val :: arr
    let val := add val step
    if boundsCheck c val e then (arr.reverse, none) else forceChunkLoop step e c k val arr

/-- range.cpp:132 `force_chunk()`: up to 32 values from `start`; the chunk, and the start of
`chunk_next` (none: this was the last chunk). -/
def forceChunk (start step : JNum) (e : Bound) (c : Check) : List JNum × Option JNum :=
  forceChunkLoop step e c chunkSize start []

/-- How a walk ended (fuel: more elements follow). -/
inductive Ending where
  | done | more
  deriving Repr, BEq, DecidableEq

/-- The elements `first`/`next` give (range.cpp:126 `first`, :165 `next`: while the chunk has
more than one element, a range over `chunk_next()` of the chunk (array_chunk.cpp:35, the same
buffer from `offset + 1`); then `chunked_next()`, the range from `chunk_next`). `chunks` bounds
the chunks visited, `fuel` the elements. -/
def walkFrom (step : JNum) (e : Bound) (c : Check) : Nat → Nat → Option JNum → List Int × Ending
  | 0, _, cur => ([], if cur.isNone then .done else .more)
  | _ + 1, _, none => ([], .done)
  | k + 1, fuel, some s =>
    let (chunk, nextStart) := forceChunk s step e c
    if fuel < chunk.length then ((chunk.take fuel).map ival, .more)
    else
      let (rest, ending) := walkFrom step e c k (fuel - chunk.length) nextStart
      (chunk.map ival ++ rest, ending)

def walkRange (fuel : Nat) (start step : JNum) (e : Bound) (c : Check) : List Int × Ending :=
  walkFrom step e c (fuel + 1) fuel (some start)

def walk (fuel : Nat) : Created → List Int × Ending
  | .emptyList => ([], .done)
  | .repeatInf v => (List.replicate fuel (ival v), .more)
  | .range s st e c => walkRange fuel s st e c

/-! ## Clojure: Range.java (addP: exact) -/

/-- Range.create and Range's walk: `start + k*step` (exact) while not past `end`. -/
def cljWalk (fuel : Nat) (start step : Int) (e : Bound) : List Int × Ending :=
  if (step > 0 && e.twice < 2 * start) || (step < 0 && 2 * start < e.twice) || 2 * start == e.twice then
    ([], .done)
  else if step == 0 then (List.replicate fuel start, .more)
  else
    let exceeded (v : Int) : Bool := if step > 0 then e.twice ≤ 2 * v else 2 * v ≤ e.twice
    let rec go : Nat → Int → List Int × Ending
      | 0, v => ([], if exceeded v then .done else .more)
      | f + 1, v => if exceeded v then ([], .done) else
          let (rest, ending) := go f (v + step)
          (v :: rest, ending)
    go fuel start

/-! ## The world -/

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

/-- Starts and steps drawn: small integers near the i32 limits, a heap integer. -/
def starts : List Int := [0, 5, 2147483640, 2147483646, 2147483647, -2147483647, -2147483648, 4294967296]
def steps : List Int := [1, 2, 3, -1, -3, 1073741824]
/-- Ends drawn as offsets (in halves) from the start: inside one chunk, across chunk boundaries. -/
def offsets : List Int := [1, 5, 7, 63, 64, 65, 129, -5, -7, -65]

structure Question where
  start : Int
  step : Int
  e : Bound

def Question.program (q : Question) : String := s!"(range {q.start} {q.e.code} {q.step})"

def Question.verdict (q : Question) (fuel : Nat) : Option String :=
  let j := walk fuel (create3 (JNum.ofInt q.start) q.e (JNum.ofInt q.step))
  let c := cljWalk fuel q.start q.step q.e
  let sh := fun (w : List Int × Ending) => s!"{w.1.take 12}{if w.1.length > 12 then " ..." else ""} ({if w.2 == .done then "ends" else s!"more than {fuel}"})"
  if j != c then some s!"{q.program}: Clojure {sh c}, jank {sh j}" else none

def drawQuestion : EStateM Stop World Question := do
  let s := (← pick (σ := World) "range.start" starts).getD 0
  let st := (← pick (σ := World) "range.step" steps).getD 1
  let off := (← pick (σ := World) "range.end_offset" offsets).getD 1
  return { start := s, step := st, e := ⟨2 * s + off⟩ }

def body : EStateM Stop World Unit := do
  let q ← drawQuestion
  if let some d := q.verdict 80 then violate (σ := World) "range agrees with Clojure" d

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-- The same world with Clojure's `addP` in place of `add` (the fix): nothing found. -/
def walkFixed (fuel : Nat) (q : Question) : List Int × Ending :=
  match create3 (JNum.ofInt q.start) q.e (JNum.ofInt q.step) with
  | .emptyList => ([], .done)
  | .repeatInf v => (List.replicate fuel (ival v), .more)
  | .range _ _ _ _ => cljWalk fuel q.start q.step q.e

def bodyFixed : EStateM Stop World Unit := do
  let q ← drawQuestion
  if walkFixed 80 q != cljWalk 80 q.start q.step q.e then violate (σ := World) "range agrees with Clojure" q.program

def runFixed (source : Source) : Ended :=
  match bodyFixed.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

def allQuestions : List Question :=
  starts.flatMap fun s => steps.flatMap fun st => offsets.map fun off => { start := s, step := st, e := ⟨2 * s + off⟩ }

/-- `(range 2147483646 2147483649.0)`: Clojure (2147483646 2147483647 2147483648); jank wraps to
-2147483648 after 2147483647 and never reaches the end (the first 6 elements shown). -/
theorem wraps_past_i32 :
    walk 6 (create2 (JNum.ofInt 2147483646) ⟨4294967298⟩) =
      ([2147483646, 2147483647, -2147483648, -2147483647, -2147483646, -2147483645], .more) ∧
    cljWalk 6 2147483646 1 ⟨4294967298⟩ = ([2147483646, 2147483647, 2147483648], .done) := by
  constructor <;> rfl

end Jank.Seq.Range

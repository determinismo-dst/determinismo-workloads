import Determinismo

/-!
# Chunked sequences: `chunk-cons` realizes its rest (seq.cpp:1066)

core.jank `map` (2901), `filter`, `keep`, `map-indexed`, `concat`, `for` handle a chunked seq by
`(chunk-cons (chunk b) (map f (chunk-rest s)))`. core.jank `chunk-cons` (2058) calls
`runtime::chunk_cons` (seq.cpp:1066): `make_box<obj::chunked_cons>(chunk, seq(rest))`. The
`seq(rest)` realizes the lazy `(map f (chunk-rest s))` at once, which maps the next chunk and
calls `chunk-cons` again: realizing the first element maps every chunk of the source, one nested
realization per chunk. Clojure's `chunk-cons` (core.clj 712) builds `ChunkedCons(chunk, rest)`,
which keeps `rest` unrealized (ChunkedCons.java 22-27): one chunk at a time.

The chunked source here is a range with a non-integer argument (range.cpp: chunks of 32,
`chunked_first`/`chunked_next`), e.g. `(range 0.5 n)`; its elements are counted, not computed.
The mapped function counts its calls (a side effect, as `println` would show).
-/

namespace Jank.Seq.Chunked

open Determinismo

abbrev Ref := Nat

inductive Impl where
  | jank | clj
  deriving Repr, BEq

/-- A lazy sequence's body: core.jank 2901 `map` [f coll] with `f` counting its calls. -/
inductive Code where
  | mapF (coll : Ref)
  deriving Repr, BEq

inductive Obj where
  | nil
  /-- persistent_list::empty(). -/
  | emptyList
  /-- array_chunk: `buffer`, `offset`. -/
  | arrayChunk (buf : List Int) (offset : Nat)
  /-- A chunked range: the element at `start`, `left` elements left (none: no end). -/
  | range (start : Int) (left : Option Nat)
  /-- chunked_cons: an array_chunk head, a tail. -/
  | chunkedCons (chunk : Ref) (tail : Ref)
  | cons (head : Int) (tail : Ref)
  /-- lazy_sequence: fn (none once forced), its value or realized seq. -/
  | lazy (fn : Option Code) (s : Ref)
  deriving Repr, BEq

structure Heap where
  objs : Array Obj := #[.nil]
  /-- Calls of the mapped function so far. -/
  calls : Nat := 0
  deriving Repr

abbrev HM := EStateM String Heap

def alloc (o : Obj) : HM Ref := do
  let h ← get
  set { h with objs := h.objs.push o }
  return h.objs.size

def load (r : Ref) : HM Obj := do
  match (← get).objs[r]? with
  | some o => return o
  | none => throw "dangling"

def store (r : Ref) (o : Obj) : HM Unit := modify fun h => { h with objs := h.objs.set! r o }

def chunkSize : Nat := 32

/-- range.cpp:132 `force_chunk` for a step-1 range: up to 32 values; the rest of the range
(`chunk_next`), none at the end. -/
def rangeChunk (start : Int) (left : Option Nat) : List Int × Option (Int × Option Nat) :=
  let n := match left with | some l => min l chunkSize | none => chunkSize
  let vals := (List.range n).map fun (i : Nat) => start + Int.ofNat i
  let rest := match left with
    | some l => if l ≤ chunkSize then none else some (start + chunkSize, some (l - chunkSize))
    | none => some (start + chunkSize, none)
  (vals, rest)

/-- `f`: one call counted. -/
def callF (x : Int) : HM Int := do
  modify fun h => { h with calls := h.calls + 1 }
  return x + 1

mutual
/-- `seq()`: a lazy sequence realizes (lazy_sequence.cpp:118); the others are their own seq. -/
def seqOf (impl : Impl) : Nat → Ref → HM Ref
  | 0, _ => throw "does not terminate (fuel): one nested realization per chunk"
  | f + 1, r => do
    match ← load r with
    | .nil | .emptyList => return 0
    | .lazy fn s => do
      match fn with
      | some code => do
        let v ← runCode impl f code
        let s' ← seqOf impl f v
        store r (.lazy none s')
        return s'
      | none => return s
    | _ => return r
  termination_by structural fuel _ => fuel

/-- core.jank 2901 `map` [f coll]'s lazy body: `(when-let [s (seq coll)] (if (chunked-seq? s)
(let [c (chunk-first s) size (int (count c)) b (chunk-buffer size)] (dotimes [i size]
(chunk-append b (f (nth c i)))) (chunk-cons (chunk b) (map f (chunk-rest s)))) (cons (f (first s))
(map f (rest s)))))`. -/
def runCode (impl : Impl) : Nat → Code → HM Ref
  | 0, _ => throw "does not terminate (fuel): one nested realization per chunk"
  | f + 1, .mapF coll => do
    let s ← seqOf impl f coll
    if s == 0 then return 0
    match ← load s with
    -- chunked-seq?: range (range.hpp chunked_first) and chunked_cons are chunkable
    | .range start left => do
      let (vals, rest) := rangeChunk start left
      let mut out : Array Int := #[]
      for v in vals do out := out.push (← callF v)
      let c ← alloc (.arrayChunk out.toList 0)
      -- (chunk-rest s): seq.cpp:1042 chunked_next, nil → ()
      let cr ← match rest with
        | some (st, l) => alloc (.range st l)
        | none => alloc .emptyList
      let tl ← alloc (.lazy (some (.mapF cr)) 0)
      chunkCons impl f c tl
    | .chunkedCons ch tail => do
      let .arrayChunk buf off ← load ch | throw "chunk"
      let mut out : Array Int := #[]
      for v in buf.drop off do out := out.push (← callF v)
      let c ← alloc (.arrayChunk out.toList 0)
      let cr ← if tail == 0 then alloc .emptyList else pure tail
      let tl ← alloc (.lazy (some (.mapF cr)) 0)
      chunkCons impl f c tl
    | .cons h t => do
      let y ← callF h
      let rest ← if t == 0 then alloc .emptyList else pure t
      let tl ← alloc (.lazy (some (.mapF rest)) 0)
      alloc (.cons y tl)
    | _ => throw "map: not a seq"
  termination_by structural fuel _ => fuel

/-- core.jank 2058 `chunk-cons`: `(if (empty? chunk) rest (chunk_cons chunk rest))`; jank's
seq.cpp:1066 `make_box<chunked_cons>(chunk, seq(rest))`; Clojure's `ChunkedCons(chunk, rest)`. -/
def chunkCons (impl : Impl) : Nat → Ref → Ref → HM Ref
  | 0, _, _ => throw "does not terminate (fuel): one nested realization per chunk"
  | f + 1, c, rest => do
    let .arrayChunk buf off ← load c | throw "chunk"
    if buf.length - off == 0 then return rest
    match impl with
    | .jank => do let s ← seqOf impl f rest; alloc (.chunkedCons c s)
    | .clj => alloc (.chunkedCons c rest)
  termination_by structural fuel _ _ => fuel
end

def fuel : Nat := 400

/-- The first element (`(first coll)`: seq, then chunked_cons.cpp:43 `first` = `chunk.nth(0)`). -/
def firstOf (impl : Impl) (r : Ref) : HM (Option Int) := do
  let s ← seqOf impl fuel r
  if s == 0 then return none
  match ← load s with
  | .chunkedCons c _ => do
    let .arrayChunk buf off ← load c | throw "chunk"
    return buf[off]?
  | .cons h _ => return some h
  | .range st _ => return some st
  | _ => return none

/-- A source of `total` elements (none: no end), mapped `depth` times; `(first ...)`: the
first element and the mapped function's calls. -/
def program (impl : Impl) (total : Option Nat) (depth : Nat) : Except String (Option Int × Nat) :=
  let body : HM (Option Int) := do
    let mut r ← alloc (.range 0 total)
    for _ in List.range depth do
      r ← alloc (.lazy (some (.mapF r)) 0)
    firstOf impl r
  match body.run {} with
  | .ok v h => .ok (v, h.calls)
  | .error e _ => .error e

def code (total : Option Nat) (depth : Nat) : String :=
  let src := match total with
    | some n => s!"(range 0.0 {n}.0)"
    | none => "(range 0.0 ##Inf)"
  let rec wrap : Nat → String → String
    | 0, s => s
    | k + 1, s => wrap k s!"(map f {s})"
  s!"(first {wrap depth src})"

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def totals : List (Option Nat) := [some 1, some 31, some 32, some 33, some 64, some 100, some 1000, none]

def verdict (total : Option Nat) (depth : Nat) : Option String :=
  let c := program .clj total depth
  let j := program .jank total depth
  let sh := fun (r : Except String (Option Int × Nat)) => match r with
    | .ok (v, n) => s!"{v.getD 0}, f called {n} times"
    | .error e => e
  let same := match j, c with
    | .ok a, .ok b => a == b
    | _, _ => false
  if same then none else some s!"{code total depth}: Clojure {sh c}; jank {sh j}"

def body : EStateM Stop World Unit := do
  let total := (← pick (σ := World) "source.length" totals).getD none
  let depth := (← decide (σ := World) "map.depth" 2) + 1
  if let some d := verdict total depth then violate (σ := World) "(first (map f ...)) maps one chunk" d

def run (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `(first (map f (range 0.0 40.0)))`: Clojure calls `f` 32 times, jank 40 times. -/
theorem first_of_map_maps_everything :
    (program .clj (some 40) 1).toOption = some (some 1, 32) ∧
    (program .jank (some 40) 1).toOption = some (some 1, 40) := by
  constructor <;> decide

end Jank.Seq.Chunked

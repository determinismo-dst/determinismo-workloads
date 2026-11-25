import Determinismo
import Jank.R3.Runtime.Common

/-!
# folly::fbvector with jank's gc_allocator, and jtl::immutable_string's buffer ownership

## fbvector (deps/folly e54ca53d, folly/container/FBVector.h)

jank's `native_vector<T>` is `folly::fbvector<T, gc_allocator<T>>` (type.hpp 39-40). With a
non-`std::allocator`, `usingStdAllocator` is false (FBVector.h 226-227), so:
- storage comes from `gc_allocator::allocate` (`GC_MALLOC`, or `GC_MALLOC_ATOMIC` for the
  pointer-free scalar types) and goes back through `gc_allocator::deallocate` = `GC_FREE`
  (gc_allocator.h): every reallocation frees the old block explicitly;
- relocation copies, never memcpy (`relocate_use_memcpy` and `relocate_use_move` need
  `usingStdAllocator`, 646-654), then destroys the old elements (`relocate_done`, 679-698);
- `goodMallocSize` is the identity (no jemalloc: `FOLLY_ASSUME_NO_JEMALLOC=1`, Malloc.h 388-401);
- an empty vector built with no capacity has `b_ = e_ = z_ = nullptr` (Impl 98-104, `init(0)`
  162-164); `clear()` keeps the block (1146); `shrink_to_fit()` of an empty vector resets to null
  (983-987).

Replicated: `computePushBackCapacity` (1163-1174), `emplace_back`/`push_back` with
`emplace_back_aux` (1103-1236: the new element is constructed in the new block before the old
elements are relocated), `reserve` (960-981), `erase` (1242-1270), `do_real_insert` with
`make_window`/`wrap_frame`/`insert_use_fresh` (1344-1494), `insert(pos, const T&)` (checks
`dataIsInternal`, 1508-1516) and `emplace(pos, args...)` (no check, 1497-1506), `pop_back`,
`clear`, `shrink_to_fit` (its non-xallocx branch copies into a fresh block).

Spec: `std::vector` ([vector.modifiers]; LWG 2164: `v.emplace(p, v[k])` inserts the value `v[k]`
had before the call).

## immutable_string (jtl/immutable_string.hpp)

Small (≤ 23 bytes, inline), large owned (GC_malloc_atomic buffer, `GC_free`d by `destroy()` when
the string dies or is assigned over), large shared (never freed: the GC reclaims it). Replicated:
the constructors from characters (`init_small`/`init_large_owned`), the copy constructor (74-83:
marks both shared), the move constructor (85-89), `operator=(immutable_string const&)` (486-503:
`destroy()` first, then copy, owned → both shared), `operator=(const_pointer_type)` (505-520:
`destroy()` first, then reads the characters), `substr`/the substring constructor (161-192:
shared when the remainder is ≤ 512 bytes, the source marked shared), `c_str()` (225-241: a shared
string becomes owned with a fresh copy), the destructor. Spec: `std::string` values.
-/

namespace Jank.R3.Runtime.Containers

open Determinismo

/-! ## fbvector -/

structure Buf where
  cells : Array Nat
  live : Bool := true
  deriving Repr, Inhabited, BEq

structure Vec where
  bufs : Array Buf := #[]
  /-- the block b_ points to (none: nullptr) -/
  b : Option Nat := none
  size : Nat := 0
  cap : Nat := 0
  /-- GC_FREE calls -/
  frees : Nat := 0
  deriving Repr, Inhabited

/-- sizeof(T) = 8 (object_ref). -/
def sizeofT : Nat := 8

def Vec.get (v : Vec) (i : Nat) : Nat :=
  match v.b with
  | some b => (v.bufs[b]!.cells)[i]!
  | none => 0

def Vec.elems (v : Vec) : List Nat := (List.range v.size).map v.get

/-- FBVector.h 1163-1174 (jemallocMinInPlaceExpandable = 4096). -/
def computePushBackCapacity (cap : Nat) : Nat :=
  if cap == 0 then max (64 / sizeofT) 1
  else if cap < 4096 / sizeofT then cap * 2
  else if cap > 4096 * 32 / sizeofT then cap * 2
  else (cap * 3 + 1) / 2

def computeInsertCapacity (v : Vec) (n : Nat) : Nat := max (computePushBackCapacity v.cap) (v.size + n)

def Vec.allocate (v : Vec) (n : Nat) : Vec × Nat :=
  ({ v with bufs := v.bufs.push { cells := Array.replicate n 0 } }, v.bufs.size)

def Vec.deallocate (v : Vec) (b : Nat) : Vec :=
  { v with bufs := v.bufs.set! b { v.bufs[b]! with live := false }, frees := v.frees + 1 }

def Vec.write (v : Vec) (b i x : Nat) : Vec :=
  { v with bufs := v.bufs.set! b { v.bufs[b]! with cells := (v.bufs[b]!.cells).set! i x } }

/-- A value an argument refers to: a fresh value, or a reference to element k (read when used). -/
inductive Arg where
  | fresh (x : Nat)
  | ref (k : Nat)
  deriving Repr, Inhabited, BEq

/-- Reading a reference: the cell of the block the reference was taken in (references are taken
before the call: block `b0`). A freed block is a use after free. -/
def readArg (v : Vec) (b0 : Option Nat) (a : Arg) : Except String Nat :=
  match a, b0 with
  | .fresh x, _ => .ok x
  | .ref k, some b =>
    if !(v.bufs[b]!).live then .error s!"the argument refers to element {k} of a block already GC_FREE'd"
    else .ok ((v.bufs[b]!.cells)[k]!)
  | .ref _, none => .error "reference into an empty vector"

/-- Copy elements [0, size) of the current block to `nb` at offset `off` from index `from`. -/
def Vec.relocate (v : Vec) (nb : Nat) (fromI toI : Nat) (count : Nat) : Vec :=
  (List.range count).foldl (fun v i => v.write nb (toI + i) (v.get (fromI + i))) v

/-- `emplace_back`/`push_back` (1103-1120, emplace_back_aux 1176-1236). -/
def pushBack (v : Vec) (a : Arg) : Except String Vec := do
  let b0 := v.b
  if v.size < v.cap then
    let x ← readArg v b0 a
    return { v.write v.b.get! v.size x with size := v.size + 1 }
  else
    let sz := computePushBackCapacity v.cap
    let (v, nb) := v.allocate sz
    -- not relocatable && usingStdAllocator: construct the new element first, then relocate
    let x ← readArg v b0 a
    let v := v.write nb v.size x
    let v := v.relocate nb 0 0 v.size
    let v := match b0 with | some b => v.deallocate b | none => v
    return { v with b := some nb, size := v.size + 1, cap := sz }

/-- `reserve(n)` (960-981): goodMallocSize(n * sizeof(T)) / sizeof(T) = n. -/
def reserve (v : Vec) (n : Nat) : Vec :=
  if n ≤ v.cap then v
  else
    let (v', nb) := v.allocate n
    let v' := v'.relocate nb 0 0 v.size
    let v' := match v.b with | some b => v'.deallocate b | none => v'
    { v' with b := some nb, cap := n }

/-- `do_real_insert` of one element at `pos` (1414-1494) for `insert(pos, const T&)`
(`internalCheck := true`) and `emplace(pos, args...)` (`internalCheck := false`). -/
def insertOne (v : Vec) (pos : Nat) (a : Arg) (internalCheck : Bool) : Except String Vec := do
  let b0 := v.b
  let atEnd := pos == v.size
  -- insert_use_fresh (1395-1412)
  let fresh := v.size + 1 > v.cap
  -- dataIsInternal(value) → insert(cpos, T(value)): the copy is taken now
  let a ← if !atEnd && !fresh && internalCheck then
      match a with
      | .ref _ => do let x ← readArg v b0 a; pure (Arg.fresh x)
      | .fresh x => pure (.fresh x)
    else pure a
  if fresh then
    let newCap := computeInsertCapacity v 1
    let (v, nb) := v.allocate newCap
    let x ← readArg v b0 a
    let v := v.write nb pos x
    -- wrap_frame: the left ledge, then the right one
    let v := v.relocate nb 0 0 pos
    let v := v.relocate nb pos (pos + 1) (v.size - pos)
    let v := match b0 with | some b => v.deallocate b | none => v
    return { v with b := some nb, size := v.size + 1, cap := newCap }
  else
    let b := v.b.get!
    let v ← if atEnd then pure v
      else
        -- make_window(position, 1) (1344-1375): tail > n: move-construct the last element one
        -- further, copy_backward the rest, destroy the window's slot
        let tail := v.size - pos
        if tail ≤ 1 then
          pure ((v.relocate b pos (pos + 1) tail))
        else
          let v := v.write b v.size (v.get (v.size - 1))
          pure ((List.range (tail - 1)).foldl (fun v i =>
            let src := v.size - 2 - i
            v.write b (src + 1) (v.get src)) v)
    let x ← readArg v b0 a
    return { v.write b pos x with size := v.size + 1 }

/-- `erase(pos)` (1242-1270): move-assign the tail one left, destroy the last. -/
def erase (v : Vec) (pos : Nat) : Vec :=
  if pos ≥ v.size then v
  else
    let v' := (List.range (v.size - 1 - pos)).foldl (fun w k =>
      let i := pos + k
      w.write v.b.get! i (w.get (i + 1))) v
    { v' with size := v.size - 1 }

def popBack (v : Vec) : Vec := if v.size == 0 then v else { v with size := v.size - 1 }
def clear (v : Vec) : Vec := { v with size := 0 }

/-- `shrink_to_fit` (983-1025): empty → reset (free, null); else a fresh block of size() when
smaller (no xallocx without jemalloc). -/
def shrinkToFit (v : Vec) : Vec :=
  if v.size == 0 then
    let v := match v.b with | some b => v.deallocate b | none => v
    { v with b := none, cap := 0 }
  else if v.size ≥ v.cap then v
  else
    let (v', nb) := v.allocate v.size
    let v' := v'.relocate nb 0 0 v.size
    let v' := v'.deallocate v.b.get!
    { v' with b := some nb, cap := v.size }

inductive VOp where
  | push (a : Arg)
  | insert (pos : Nat) (a : Arg)
  | emplace (pos : Nat) (a : Arg)
  | erase (pos : Nat)
  | pop | clear | shrink
  | reserve (n : Nat)
  deriving Repr, Inhabited, BEq

/-- std::vector: the spec, with LWG 2164 for aliasing arguments. -/
def specStep (xs : List Nat) : VOp → Option (List Nat)
  | .push a => some (xs ++ [argVal xs a])
  | .insert p a => if p ≤ xs.length then some (xs.take p ++ [argVal xs a] ++ xs.drop p) else none
  | .emplace p a => if p ≤ xs.length then some (xs.take p ++ [argVal xs a] ++ xs.drop p) else none
  | .erase p => if p < xs.length then some (xs.eraseIdx p) else none
  | .pop => if xs.isEmpty then none else some xs.dropLast
  | .clear => some []
  | .shrink => some xs
  | .reserve _ => some xs
where
  argVal (xs : List Nat) : Arg → Nat
    | .fresh x => x
    | .ref k => xs.getD k 0

def vstep (v : Vec) : VOp → Except String Vec
  | .push a => pushBack v a
  | .insert p a => insertOne v p a true
  | .emplace p a => insertOne v p a false
  | .erase p => .ok (erase v p)
  | .pop => .ok (popBack v)
  | .clear => .ok (clear v)
  | .shrink => .ok (shrinkToFit v)
  | .reserve n => .ok (reserve v n)

/-- A random/exhaustive sequence of operations (each valid for the current size), checked against
std::vector after each, plus `data() == nullptr ⟺ no block`. -/
def runVec (len : Nat) (emplaceAlias : Bool := true) (source : Source) : Ended :=
  let body : EStateM Stop Decisions Unit := do
    let mut v : Vec := {}
    let mut xs : List Nat := []
    let mut ops : List VOp := []
    for step in [0:len] do
      let n := xs.length
      let k ← dd "vec.op" 8
      let mkArg : EStateM Stop Decisions Arg := do
        if n == 0 then pure (.fresh (100 + step))
        else
          let r ← dd "vec.arg" (n + 1)
          pure (if r == n then .fresh (100 + step) else .ref r)
      let op ← match k with
        | 0 => do pure (VOp.push (← mkArg))
        | 1 => do let p ← dd "vec.pos" (n + 1); pure (VOp.insert p (← mkArg))
        | 2 => do
          let p ← dd "vec.pos" (n + 1)
          let a ← mkArg
          -- the residual search: emplace's arguments never alias an element
          pure (VOp.emplace p (if emplaceAlias then a else match a with | .ref _ => .fresh (100 + step) | x => x))
        | 3 => if n == 0 then pure .clear else do pure (VOp.erase (← dd "vec.pos" n))
        | 4 => pure (if n == 0 then .clear else .pop)
        | 5 => pure .clear
        | 6 => pure .shrink
        | _ => do pure (VOp.reserve ((← dd "vec.reserve" 4) + 1))
      ops := ops ++ [op]
      match vstep v op, specStep xs op with
      | .ok v', some xs' =>
        if v'.elems != xs' then
          throw (.violation "std::vector contents"
            s!"after {reprStr ops}: fbvector holds {v'.elems}, std::vector {xs'}")
        v := v'
        xs := xs'
      | .error e, _ => throw (.violation "no use after GC_FREE" s!"after {reprStr ops}: {e}")
      | .ok _, none => pure ()
  match body.run { source, limit := 1000 } with
  | .ok _ d => { taken := d.taken, violation := none }
  | .error (.violation p d) s => { taken := s.taken, violation := some (p, d) }
  | .error .limit s => { taken := s.taken, violation := none }
where
  dd (name : String) (n : Nat) : EStateM Stop Decisions Nat := fun s =>
    match s.next name (List.replicate n 1) with
    | .ok (v, s') => .ok v s'
    | .error e => .error e s

/-! ## immutable_string -/

inductive Cat | small | owned | shared
  deriving BEq, Repr, Inhabited

/-- A string variable: its category and, for a large one, (buffer, offset); `alive`: in scope. -/
structure IStr where
  cat : Cat := .small
  buf : Nat := 0
  off : Nat := 0
  size : Nat := 0
  /-- the characters it should hold (spec: std::string), as (source id, offset) -/
  content : Nat × Nat := (0, 0)
  deriving BEq, Repr, Inhabited

structure SW where
  vars : Array IStr
  /-- buffers: live, original content id -/
  bufs : Array (Bool × Nat) := #[]
  frees : Nat := 0
  deriving Inhabited

def maxSmall : Nat := 23
def maxSharedDifference : Nat := 512

abbrev SM := EStateM String SW

def newBuf (content : Nat) : SM Nat := do
  let w ← get
  set { w with bufs := w.bufs.push (true, content) }
  return w.bufs.size

/-- Reading `size` bytes at (buf, off): a freed buffer is a use after free. -/
def readChars (s : IStr) (what : String) : SM Unit := do
  if s.cat != .small then
    let w ← get
    if !(w.bufs[s.buf]!).1 then throw s!"{what} reads a buffer already GC_free'd"

/-- `destroy()` (immutable_string.hpp 717-725): GC_free an owned buffer. -/
def destroy (i : Nat) : SM Unit := do
  let w ← get
  let s := w.vars[i]!
  if s.cat == .owned then
    if !(w.bufs[s.buf]!).1 then throw s!"s{i}: GC_free of a buffer already freed"
    set { w with bufs := w.bufs.set! s.buf (false, (w.bufs[s.buf]!).2), frees := w.frees + 1 }

def setVar (i : Nat) (s : IStr) : SM Unit := modify fun w => { w with vars := w.vars.set! i s }

/-- Characters (from a literal or from a string's data) into a string: init_small or
init_large_owned (a fresh GC_malloc_atomic copy). -/
def initFrom (size : Nat) (content : Nat × Nat) : SM IStr := do
  if size ≤ maxSmall then return { cat := .small, size, content }
  else
    let b ← newBuf content.1
    return { cat := .owned, buf := b, off := 0, size, content }

inductive SOp where
  /-- `s_i = immutable_string{"<size chars>"}` (a fresh string, the old one destroyed). -/
  | lit (i size : Nat)
  /-- `immutable_string s_i{ s_j }` (old s_i destroyed first: a new scope). -/
  | copyCtor (i j : Nat)
  | moveCtor (i j : Nat)
  /-- `s_i = s_j` -/
  | assign (i j : Nat)
  /-- `s_i = s_j.c_str()` (`operator=(const_pointer_type)`) -/
  | assignCStr (i j : Nat)
  /-- `s_i = s_j.substr(pos)` -/
  | substr (i j pos : Nat)
  /-- `s_i.c_str()` -/
  | cstr (i : Nat)
  /-- read s_i's characters -/
  | read (i : Nat)
  deriving Repr, Inhabited, BEq

/-- `c_str()` (225-241): a shared string becomes owned with a fresh copy. -/
def cstrOf (i : Nat) : SM Unit := do
  let w ← get
  let s := w.vars[i]!
  if s.cat == .shared then
    readChars s s!"s{i}.c_str()"
    let b ← newBuf s.content.1
    setVar i { s with cat := .owned, buf := b, off := 0 }

def sstep : SOp → SM Unit
  | .lit i size => do
    destroy i
    let id := 1000 + size
    setVar i (← initFrom size (id, 0))
  | .copyCtor i j => do
    if i == j then return
    destroy i
    let w ← get
    let s := w.vars[j]!
    if s.cat == .small then setVar i s
    else
      setVar j { s with cat := .shared }
      setVar i { s with cat := .shared }
  | .moveCtor i j => do
    if i == j then return
    destroy i
    let w ← get
    setVar i w.vars[j]!
    setVar j { cat := .small, size := 0, content := (0, 0) }
  | .assign i j => do
    if i == j then return
    destroy i
    let w ← get
    let s := w.vars[j]!
    if s.cat == .owned then
      setVar j { s with cat := .shared }
      setVar i { s with cat := .shared }
    else setVar i s
  | .assignCStr i j => do
    -- c_str() first (as the argument is evaluated), then operator=: destroy(), then length/copy
    cstrOf j
    let w ← get
    let src := w.vars[j]!
    destroy i
    readChars src s!"s{i} = s{j}.c_str()"
    setVar i (← initFrom src.size src.content)
  | .substr i j pos => do
    let w ← get
    let s := w.vars[j]!
    if pos > s.size then return
    readChars s s!"s{j}.substr({pos})"
    let count := s.size - pos
    let content := (s.content.1, s.content.2 + pos)
    let r ← if count ≤ maxSmall then pure ({ cat := .small, size := count, content } : IStr)
      else if s.size - count > maxSharedDifference then initFrom count content
      else
        -- the source becomes shared; the substring shares its buffer
        setVar j { s with cat := if s.cat == .small then .small else .shared }
        pure { cat := .shared, buf := s.buf, off := s.off + pos, size := count, content }
    destroy i
    setVar i r
  | .cstr i => cstrOf i
  | .read i => do
    readChars (← get).vars[i]! s!"reading s{i}"

def runStr (len : Nat) (selfCStr : Bool := true) (source : Source) : Ended :=
  let body : EStateM Stop Decisions Unit := do
    let mut w : SW := { vars := Array.replicate 2 {} }
    let mut ops : List SOp := []
    for _ in [0:len] do
      let k ← dd "str.op" 8
      let i ← dd "str.var" 2
      let j ← dd "str.var" 2
      let op := match k with
        | 0 => SOp.lit i 30
        | 1 => SOp.lit i 600
        | 2 => SOp.copyCtor i j
        | 3 => SOp.moveCtor i j
        | 4 => SOp.assign i j
        | 5 => if !selfCStr && i == j then SOp.cstr i else SOp.assignCStr i j
        | 6 => SOp.substr i j 1
        | _ => SOp.cstr i
      ops := ops ++ [op, .read 0, .read 1]
      for o in [op, .read 0, .read 1] do
        match (sstep o).run w with
        | .ok _ w' => w := w'
        | .error e _ => throw (.violation "no use after GC_free" s!"{reprStr ops}: {e}")
  match body.run { source, limit := 1000 } with
  | .ok _ d => { taken := d.taken, violation := none }
  | .error (.violation p d) s => { taken := s.taken, violation := some (p, d) }
  | .error .limit s => { taken := s.taken, violation := none }
where
  dd (name : String) (n : Nat) : EStateM Stop Decisions Nat := fun s =>
    match s.next name (List.replicate n 1) with
    | .ok (v, s') => .ok v s'
    | .error e => .error e s

end Jank.R3.Runtime.Containers

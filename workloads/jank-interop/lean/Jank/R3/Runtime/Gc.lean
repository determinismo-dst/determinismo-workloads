import Determinismo
import Jank.R3.Runtime.Common

/-!
# bdwgc as jank configures it (deps/bdwgc 327ef1f8; jank 7135b7708)

Configuration (cmake/dependency/bdwgc.cmake, CMakeLists.txt 111-112, c_api.cpp 1119-1130):
threads on, large config, C++ on, `-DPOINTER_MASK=0x0000FFFFFFFFFFFF` for bdwgc and jank alike,
`GC_set_all_interior_pointers(1)`, `GC_init()`, `GC_allow_register_threads()`, and the typed
descriptor of `persistent_string` built from a bitmap with only `data`'s word set.

What decides reachability, replicated:
- **Candidate words.** Heap objects and roots added with `GC_add_roots` are scanned with
  `FIXUP_POINTER(p)` = `p & POINTER_MASK` (gcconfig.h 3727-3734; mark.c 805-806, 979-980;
  typd_mlc.c 187-188). Stacks and registers try the raw word and the masked one
  (`GC_PUSH_ONE_STACK` with `NEED_FIXUP_POINTER`, gc_pmark.h 346-361). jank's `object_ref` tags a
  pointer with 0xFFFA in the top 16 bits (oref.hpp 106-108), so masking recovers it.
- **Interior pointers.** Any address inside an object, and one past its requested end (EXTRA_BYTES),
  keeps it alive.
- **Object kinds.** `GC_malloc`/`new (UseGC)`/`gc_allocator` of non-pointer-free T: every word;
  `GC_malloc_atomic`/`new (PointerFreeGC)`/`GC_realloc` of an atomic block: no word;
  `GC_malloc_uncollectable`/`new (NoGC)`: every word, and a root; `GC_malloc_explicitly_typed`:
  only the words its descriptor marks (`GC_DS_LENGTH`: a prefix; `GC_DS_BITMAP`: bit 63 is word 0;
  mark.c 789-819), the descriptor made by `GC_make_descriptor` (typd_mlc.c 209-284).
- **Roots.** Static data of the executable and loaded libraries, `GC_add_roots` ranges, registered
  threads' stacks and registers, uncollectable objects.
- **Never scanned.** The malloc heap (`std::allocator`, plain `new`, `std::function` storage,
  `std::thread`'s state, the C++ runtime's exception objects from `__cxa_allocate_exception`,
  emulated-TLS blocks from `-femulated-tls`), atomic objects, untyped words of typed objects,
  unregistered threads' stacks (bdwgc docs gcinterface.md 150-170: "the collector may not trace
  correctly from in-flight exception objects").
- **Collection** may run at any allocation, of any thread (stop-the-world): here a decision
  (`gc.collect`) at each allocation. A collection marks from the roots and frees what is unmarked.
  `GC_free` frees at once.

A later use of an object that Clojure's semantics keep alive, after the replica's collector freed
it, is the violation (`object alive`).
-/

namespace Jank.R3.Runtime.Gc

open Determinismo

def pointerMask : UInt64 := 0x0000FFFFFFFFFFFF
/-- oref.hpp 106: `pointer_nan_tag`. -/
def pointerTag : UInt64 := 0xFFFA000000000000
def tag (a : Nat) : UInt64 := pointerTag ||| (UInt64.ofNat a)
def raw (a : Nat) : UInt64 := UInt64.ofNat a

/-! ## Typed descriptors (typd_mlc.c, gc_mark.h) -/

def gcDsLength : UInt64 := 0
def gcDsBitmap : UInt64 := 1
def gcDsTags : UInt64 := 3
def signb : UInt64 := 0x8000000000000000
def bitmapBits : Nat := 62

/-- The index of the last set bit (`last_set_bit`, typd_mlc.c 232-233). -/
def lastSet (bm : List Bool) : Option Nat :=
  ((List.range bm.length).filter fun i => bm.getD i false).getLast?

/-- `GC_make_descriptor(bm, len)` (typd_mlc.c 209-284) for `len ≤ 62` (the extended-descriptor
branch is not reached by jank's 6-word bitmap). `bm` lists the bit of each word. Written with
structural recursion so the kernel can evaluate it. -/
def makeDescriptor (bm : List Bool) : UInt64 :=
  match lastSet bm with
  | none => 0
  | some last =>
    -- "The initial section contains all pointers; use the length descriptor." (239-255)
    if (List.range last).all (fun i => bm.getD i false) then
      UInt64.ofNat ((last + 1) * 8) ||| gcDsLength
    else
      -- "Build the bitmap descriptor (with the bits reversed)." (256-269)
      let d : UInt64 := (List.range last).reverse.foldl
        (fun (d : UInt64) j => let d := d >>> 1; if bm.getD j false then d ||| signb else d) signb
      d ||| gcDsBitmap

/-- The words of an object of `nwords` words that the mark procedure scans for descriptor `d`
(mark.c: GC_DS_LENGTH scans `d` bytes; GC_DS_BITMAP scans the words whose bit is set, from bit 63). -/
def scannedWords (d : UInt64) (nwords : Nat) : List Nat :=
  if d &&& gcDsTags == gcDsLength then
    (List.range ((d.toNat) / 8)).filter (· < nwords)
  else if d &&& gcDsTags == gcDsBitmap then
    let bits := d &&& ~~~gcDsTags
    (List.range 64).filter fun k => k < nwords && (bits <<< (UInt64.ofNat k)) &&& signb != 0
  else List.range nwords

/-- `persistent_string`'s layout (object.hpp 411-614, persistent_string.hpp, immutable_string.hpp
686-723): vptr 0; `object_type type` (u8) 8; `object_behavior behaviors` (u16) 10; `data` 16:
`storage{ union{ bytes[24]; small[24]; large_storage{ data, size, extra } }; uhash hash (u32) }`,
so `store.large.data` is the word at 16 and the object is 48 bytes, 6 words. -/
def psWords : Nat := 6
def psDataWord : Nat := 2

/-- c_api.cpp 1126-1129: `GC_set_bit(bm, GC_OFFSETOF_IN_PTRS(persistent_string, data))`. -/
def psBitmap : List Bool := (List.range psWords).map (· == psDataWord)
def psDescriptor : UInt64 := makeDescriptor psBitmap

/-! ## The heap -/

inductive Kind where
  | normal
  | atomic
  | uncollectable
  | typed (d : UInt64)
  deriving BEq, Repr, Inhabited

structure Obj where
  name : String
  base : Nat
  words : Array UInt64
  kind : Kind
  live : Bool := true
  deriving Repr, Inhabited

/-- A region of memory outside the GC heap: a thread stack (registered or not), static data, a
`GC_add_roots` range, or malloc memory. -/
structure Region where
  name : String
  words : Array UInt64
  /-- scanned by the collector -/
  scanned : Bool
  /-- a stack or registers (raw and masked candidates) -/
  stack : Bool := false
  deriving Repr, Inhabited

structure W where
  heap : Array Obj := #[]
  regions : Array Region := #[]
  next : Nat := 0x10000
  collections : Nat := 0
  /-- Clojure mode: the region names the JVM would trace (in-flight exceptions...). -/
  jvmRoots : List String := []
  decisions : Decisions := {}
  log : Array String := #[]
  deriving Inhabited

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev GM := EStateM Stop W

def note (s : String) : GM Unit := modify fun w => { w with log := w.log.push s }

/-- The object an address points into (interior pointers on; one past the end counts). -/
def find? (w : W) (a : Nat) : Option Nat :=
  w.heap.findIdx? fun o => o.live && o.base ≤ a && a ≤ o.base + 8 * o.words.size

def candidates (word : UInt64) (stack : Bool) : List Nat :=
  let masked := (word &&& pointerMask).toNat
  if stack then [word.toNat, masked] else [masked]

/-- Mark from the roots (fuel-bounded worklist), then sweep. -/
def collect : GM Unit := do
  let w ← get
  let n := w.heap.size
  let mut marked : Array Bool := Array.replicate n false
  let mut work : List Nat := []
  -- roots: scanned regions (+ JVM roots in Clojure mode), uncollectable objects
  for r in w.regions do
    if r.scanned || w.jvmRoots.contains r.name then
      for word in r.words do
        for a in candidates word r.stack do
          if let some i := find? w a then work := i :: work
  for i in [0:n] do
    if w.heap[i]!.live && w.heap[i]!.kind == .uncollectable then work := i :: work
  let mut fuel := 10 * n + 10
  while fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => fuel := 0
    | i :: rest =>
      work := rest
      if !marked[i]! then
        marked := marked.set! i true
        let o := w.heap[i]!
        let idxs : List Nat := match o.kind with
          | .normal | .uncollectable => List.range o.words.size
          | .atomic => []
          | .typed d => scannedWords d o.words.size
        for k in idxs do
          for a in candidates (o.words[k]!) false do
            if let some j := find? w a then work := j :: work
  let mut heap := w.heap
  let mut freed : List String := []
  for i in [0:n] do
    if heap[i]!.live && !marked[i]! then
      heap := heap.set! i { heap[i]! with live := false }
      freed := freed ++ [heap[i]!.name]
  set { w with heap, collections := w.collections + 1 }
  note s!"collection {w.collections + 1}: freed [{String.intercalate ", " freed}]"

/-- A collection may run at this allocation (any thread's). -/
def maybeCollect (why : String) : GM Unit := do
  if (← decide (σ := W) s!"gc.collect" 2) == 1 then
    note s!"a collection runs at {why}"
    collect

def alloc (name : String) (kind : Kind) (words : Array UInt64) : GM Nat := do
  maybeCollect s!"the allocation of {name}"
  let w ← get
  let a := w.next
  set { w with heap := w.heap.push { name, base := a, words, kind }, next := a + 8 * words.size + 64 }
  note s!"allocate {name} at {a} ({reprStr kind})"
  return a

def gcFree (a : Nat) : GM Unit := do
  let w ← get
  if let some i := find? w a then
    set { w with heap := w.heap.set! i { w.heap[i]! with live := false } }
    note s!"GC_free {w.heap[i]!.name}"

def setWord (a k : Nat) (v : UInt64) : GM Unit := do
  let w ← get
  if let some i := find? w a then
    let o := w.heap[i]!
    set { w with heap := w.heap.set! i { o with words := o.words.set! k v } }

def region (name : String) (words : Array UInt64) (scanned : Bool) (stack : Bool := false) : GM Unit :=
  modify fun w =>
    match w.regions.findIdx? (·.name == name) with
    | some i => { w with regions := w.regions.set! i { name, words, scanned, stack } }
    | none => { w with regions := w.regions.push { name, words, scanned, stack } }

def dropRegion (name : String) : GM Unit :=
  modify fun w => { w with regions := w.regions.filter (·.name != name) }

/-- A use of the object at `a` (what Clojure keeps alive): a violation if it was freed. -/
def use (a : Nat) (what : String) : GM Unit := do
  let w ← get
  match w.heap.find? fun o => o.base ≤ a && a ≤ o.base + 8 * o.words.size with
  | some o =>
    if !o.live then throw (.violation "object alive" s!"{what} reads {o.name}, freed by the collector")
    note s!"use {o.name} ({what})"
  | none => throw (.violation "object alive" s!"{what}: no object at {a}")

def word (a k : Nat) : GM UInt64 := do
  let w ← get
  match w.heap.find? fun o => o.base ≤ a && a < o.base + 8 * o.words.size with
  | some o => return o.words[k]!
  | none => return 0

def run (body : GM Unit) (jvm : Bool) (jvmRoots : List String) (source : Source) : Ended × Array String :=
  let w : W := { decisions := { source, limit := 10000 }, jvmRoots := if jvm then jvmRoots else [] }
  match body.run w with
  | .ok _ w' => ({ taken := w'.decisions.taken, violation := none }, w'.log)
  | .error (.violation p d) w' => ({ taken := w'.decisions.taken, violation := some (p, d) }, w'.log)
  | .error .limit w' => ({ taken := w'.decisions.taken, violation := none }, w'.log)
  | .error (.nodeDown _) w' => ({ taken := w'.decisions.taken, violation := none }, w'.log)

/-! ## Scenarios

Objects under construction are held by the allocating frame (`main stack`, scanned), as the C++
locals that hold them are; each scenario updates that frame as the code does. -/

def frame (name : String) (words : List UInt64) (scanned : Bool := true) : GM Unit :=
  region name words.toArray scanned (stack := true)

/-- main.cpp 255: `__rt_ctx = new(UseGC) runtime::context{}`; the static pointer is a root. The
namespace hangs off the context (its namespaces map). -/
def setupContext : GM (Nat × Nat) := do
  region "static data (__rt_ctx)" #[] true
  let ctx ← alloc "context" .normal #[0]
  region "static data (__rt_ctx)" #[raw ctx] true
  let nsObj ← alloc "ns user" .normal #[0]
  setWord ctx 0 (raw nsObj)
  return (ctx, nsObj)

/-! ## Scenario: a value in flight as a C++ exception -/

/-- jank: `(try (try (boom) (finally <allocations>)) (catch cpp/jank.runtime.object_ref e (ex-data e)))`
with `(defn boom [] (throw (ex-info "boom" {:k (vec (range 3))})))`.

- codegen gen(throw) (cpp_processor.cpp 1024-1050): `throw static_cast<jank::runtime::object_ref>(x)`
  copies the tagged word into the exception object (`__cxa_allocate_exception`: malloc);
- boom's frame is gone once unwinding reaches the try/finally;
- gen(try) (1053-1101): `catch(...) { guard.release(); fin_fn(); throw; }`: the finally body runs
  while the exception is caught, its value only in the C++ runtime's (malloc) storage;
- `throw;` rethrows to `catch(jank::runtime::object_ref e)`, which copies the word to its frame.

`finallyAllocs` allocations in the finally (each may collect); `otherThread`: another thread's
allocations during the unwinding (no finally needed). -/
def exceptionInFlight (finallyAllocs : Nat) (otherThread : Nat) : GM Unit := do
  let _ ← setupContext
  frame "main stack" []
  -- boom's frame builds the data and the ex-info
  let v ← alloc "the vector [0 1 2]" .normal #[0, 1, 2]
  frame "boom stack" [tag v]
  let data ← alloc "ex-data map {:k [0 1 2]}" .normal #[0, tag v]
  frame "boom stack" [tag v, tag data]
  let ex ← alloc "ex-info object" .normal #[0, 0, tag data]
  frame "boom stack" [tag v, tag data, tag ex]
  -- throw: the value goes into the exception object; boom's frame unwinds
  region "C++ exception object (malloc)" #[tag ex] false
  dropRegion "boom stack"
  note "throw: the ex-info is in the C++ exception object; boom's frame is popped"
  for i in [0:otherThread] do
    let _ ← alloc s!"another thread's object {i}" .normal #[]
  -- the finally body (catch(...) { fin_fn(); throw; })
  for i in [0:finallyAllocs] do
    let o ← alloc s!"finally's object {i}" .normal #[]
    frame "main stack" [tag o]
  -- catch(object_ref e): the word copied to the frame
  frame "main stack" [tag ex]
  dropRegion "C++ exception object (malloc)"
  note "catch: e copied from the exception object"
  use ex "(ex-data e)"
  use data "(ex-data e)"
  use v "(:k (ex-data e))"

/-- Control: the same value also held by a var, so it stays reachable. -/
def exceptionFromVar (finallyAllocs : Nat) : GM Unit := do
  let (_, nsObj) ← setupContext
  let v ← alloc "the vector [0 1 2]" .normal #[0, 1, 2]
  frame "main stack" [tag v]
  let data ← alloc "ex-data map {:k [0 1 2]}" .normal #[0, tag v]
  frame "main stack" [tag data]
  let ex ← alloc "ex-info object" .normal #[0, 0, tag data]
  frame "main stack" [tag ex]
  let var ← alloc "var err" .normal #[0, 0, tag ex]
  setWord nsObj 0 (tag var)
  region "C++ exception object (malloc)" #[tag ex] false
  frame "main stack" []
  for i in [0:finallyAllocs] do
    let _ ← alloc s!"finally's object {i}" .normal #[]
  frame "main stack" [tag ex]
  use ex "(ex-data e)"
  use data "(ex-data e)"

/-! ## Scenario: an unbound var's root -/

/-- `(def x)` `(def u @#'x)` `(ns-unmap *ns* 'x)` <allocations> `(str u)`.

- var.cpp 15-21: `root{ make_box<var_unbound_root>(this) }`;
- var.hpp 179-191: `var_unbound_root` has `pointer_free{ true }` and a `var_ref var` member, so
  oref.hpp 3086-3088 allocates it with `new(PointerFreeGC)` (GC_malloc_atomic): its `var` word is
  never scanned;
- `(def u @#'x)`: `var::deref` returns the root object, now u's root;
- ns.cpp 105-115 `unmap`: the ns's vars map no longer holds x;
- `(str u)`: var.cpp 351-354 `var_unbound_root::to_string` calls `var->to_string()`.

The forms are top-level calls, evaluated by evaluate.cpp without JIT, so no lifted var roots x.
Clojure: `Var$Unbound` holds its var in an ordinary field (`rootKind := .normal`). -/
def unboundRoot (allocs : Nat) (unmap : Bool) (rootKind : Kind := .atomic) : GM Unit := do
  let (_, nsObj) ← setupContext
  frame "main stack" []
  let symX ← alloc "symbol x" .normal #[]
  frame "main stack" [tag symX]
  let x ← alloc "var x" .normal #[0, 0, tag nsObj, tag symX, 0]
  frame "main stack" [tag x]
  let r ← alloc "x's var_unbound_root" rootKind #[0, 0, tag x]
  setWord x 4 (tag r)
  let m0 ← alloc "vars map {x}" .normal #[tag symX, tag x]
  setWord nsObj 0 (tag m0)
  frame "main stack" [tag r]
  -- (def u @#'x)
  let symU ← alloc "symbol u" .normal #[]
  frame "main stack" [tag r, tag symU]
  let u ← alloc "var u" .normal #[0, 0, tag nsObj, tag symU, tag r]
  frame "main stack" [tag u]
  let m1 ← alloc "vars map {x, u}" .normal #[tag symX, tag x, tag symU, tag u]
  setWord nsObj 0 (tag m1)
  frame "main stack" []
  if unmap then
    let m2 ← alloc "vars map {u}" .normal #[tag symU, tag u]
    setWord nsObj 0 (tag m2)
    note "(ns-unmap *ns* 'x)"
  for i in [0:allocs] do
    let _ ← alloc s!"object {i}" .normal #[]
  -- (str u)
  frame "main stack" [tag u]
  use u "(str u) reads u's root"
  use r "(str u) reads the unbound root"
  let xv ← word r 2
  use ((xv &&& pointerMask).toNat) "var_unbound_root::to_string reads var->to_string()"

/-! ## Scenario: persistent_string and its typed descriptor -/

/-- A `persistent_string` (make_box with `GC_malloc_explicitly_typed(sizeof, gc_descriptor)`,
oref.hpp 3078-3083) holding a `size`-byte string, `shared` pointing `offset` bytes into its
buffer (a substring sharing another string's buffer, immutable_string.hpp 161-192). Only the stack
refers to the object. `descriptor` is jank's, or 0 (what an object allocated before
`jank_init_base` set it would carry). -/
def persistentString (size offset : Nat) (shared : Bool) (descriptor : UInt64) (allocs : Nat) : GM Unit := do
  frame "main stack" []
  let large := size > 23
  let buf ← if large then alloc "string buffer (GC_malloc_atomic)" .atomic (Array.replicate (size / 8 + 1) 0x6161616161616161)
            else pure 0
  frame "main stack" [raw buf]
  let dataWord : UInt64 := if large then raw (buf + (if shared then offset else 0)) else 0x6161616161616161
  let extra : UInt64 := if large then (if shared then 0x8000000000000000 else 0xC000000000000000) else 0
  let ps ← alloc "persistent_string" (.typed descriptor) #[0x1000, 0x5, dataWord, UInt64.ofNat size, extra, 0]
  frame "main stack" [tag ps]
  for i in [0:allocs] do
    let _ ← alloc s!"object {i}" .normal #[]
  use ps "(count s)"
  if large then use (buf + (if shared then offset else 0)) "(str s) reads the characters"

/-! ## Scenario: a future's thread and its registration -/

/-- core.cpp 1104-1121: the future's thread registers itself (`GC_register_my_thread`) except on
macOS. An object only that thread's stack holds survives a collection triggered elsewhere iff the
thread is registered. -/
def futureStack (registered : Bool) (allocs : Nat) : GM Unit := do
  let _ ← setupContext
  let o ← alloc "a vector only the future's stack holds" .normal #[]
  frame "future thread stack" [tag o] registered
  for i in [0:allocs] do
    let _ ← alloc s!"main's object {i}" .normal #[]
  use o "the future body reads its local"

/-! ## Scenario: lifted globals of a module (GC_add_roots on [first, last + 1)) -/

/-- cpp_processor.cpp 2120-2170: for a compiled module, `GC_add_roots(&first, &last + 1)` over the
lifted constants (one call) and vars (another), "since they're right next to each other", before
they are initialized. They are declared in the map's iteration order; the range covers them all
exactly when the compiler lays them out in that order. `order` is the layout (global i at slot
order[i]). -/
def liftedRoots (order : List Nat) (allocs : Nat) : GM Unit := do
  let n := order.length
  let slotOf (i : Nat) := order.getD i i
  let lo := slotOf 0
  let hi := slotOf (n - 1)
  let inRange (i : Nat) := decide (lo ≤ slotOf i) && decide (slotOf i ≤ hi)
  region "GC_add_roots range" #[] true
  let mut objs : List Nat := []
  for i in [0:n] do
    let o ← alloc s!"lifted constant {i}" .normal #[]
    objs := objs ++ [o]
    -- `new (&ns::c_i) auto(...)`: stored in its global
    region "GC_add_roots range" ((((List.range objs.length).filter inRange).map fun k => tag (objs.getD k 0)).toArray) true
    region "unregistered globals" ((((List.range objs.length).filter (!inRange ·)).map fun k => tag (objs.getD k 0)).toArray) false
  for i in [0:allocs] do
    let _ ← alloc s!"object {i}" .normal #[]
  for i in [0:n] do
    use (objs.getD i 0) s!"the module's code reads lifted constant {i}"

end Jank.R3.Runtime.Gc

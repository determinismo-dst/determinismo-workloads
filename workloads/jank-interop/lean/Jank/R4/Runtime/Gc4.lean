import Determinismo
import Jank.R3.Runtime.Gc

/-!
# Round 4, Runtime: bdwgc's conservative stack scanning (replaces round 3's RTA8)

Round 3's GC replica (`Jank.R3.Runtime.Gc`) treated a popped C++ frame as gone: its words were
never scanned again (assumption RTA8, "no stale stack copies"). bdwgc scans each registered
thread's stack conservatively from the stack pointer it saved to the stack's base
(`GC_push_all_stacks`, deps/bdwgc pthread_stop_world.c 836-947: `lo = GC_approx_sp()` for the
collecting thread, `lo = crtn->stack_ptr` for a stopped one, `hi = crtn->stack_end`,
`GC_push_all_stack_sections(lo, hi, …)`). Every word in that range is a candidate pointer, whether
it belongs to a live local or is a leftover of an earlier, deeper call that the current frames
did not overwrite. The collector itself runs at the bottom of the allocating thread's stack (its
own frames below the allocation call), so the range it scans covers memory that earlier popped
frames used.

What this changes, replicated:

- **A live frame keeps every local it ever wrote** at -O0, jank's default (`-O` sets
  `codegen_optimization_level`, default 0: util/cli.cpp 205-206, 321-337): clang gives each local
  its own stack slot at -O0 and emits no lifetime markers, so no slot is reused while the
  function runs. jank compiles a `try` inline into its function (cpp_processor.cpp gen(try)
  1053-1101), the finally running from `catch(...) { guard.release(); fin(); throw; }` in the same
  frame; `throw` throws a local (gen(throw) 1023-1051: `throw static_cast<object_ref>(<local>)`).
  So when the throw and the finally are in one jank fn, the thrown value stays in a live slot of
  the frame that runs the finally: scanned at every collection.
- **A popped frame's words become stale.** At a collection each stale word that matters is, by a
  decision (`gc.stale`, 3 options): outside the scanned range or not reached yet (0, it stays
  stale), inside the range and intact (1, scanned this time), or overwritten by a later frame
  (2, gone for good). The positions and frame sizes that would decide it are those of
  clang-compiled JIT code and are not replicated, so every outcome is allowed: the replica can
  only say that a value held by stale words alone *may* be freed.
- At -O1 and above a local may live only in a register (`gc.slot`: kept in the frame or not).

Everything else (heap, kinds, roots, marking) is round 3's `Gc`.
-/

namespace Jank.R4.Runtime.Gc4

open Determinismo Jank.R3.Runtime.Gc

/-- The stale words of popped frames, kept in an unscanned region. -/
def staleName : String := "stale words of popped frames"

def staleWords (w : W) : Array UInt64 :=
  match w.regions.find? (·.name == staleName) with
  | some r => r.words
  | none => #[]

/-- Pop part of a frame: its words not in `keep` become stale (an unscanned region). -/
def popFrame (name : String) (keep : List UInt64) : GM Unit := do
  let w ← get
  let old := match w.regions.find? (·.name == name) with | some r => r.words.toList | none => []
  let gone := old.filter (fun x => !keep.contains x)
  region staleName (staleWords w ++ gone.toArray) false (stack := true)
  region name keep.toArray true (stack := true)
  if !gone.isEmpty then note s!"frame {name}: {gone.length} word(s) left behind on the stack"

/-- A frame popped whole. -/
def dropFrame (name : String) : GM Unit := do
  popFrame name []
  dropRegion name

/-- A collection with conservative stale words: each stale word is decided (outside, scanned
intact, overwritten); the scanned ones are pushed as a scanned stack region for this collection. -/
def collect4 : GM Unit := do
  let st := staleWords (← get)
  let mut keep : Array UInt64 := #[]
  let mut scanned : Array UInt64 := #[]
  for x in st do
    match (← decide (σ := W) "gc.stale" 3) with
    | 1 => keep := keep.push x; scanned := scanned.push x
    | 2 => pure ()
    | _ => keep := keep.push x
  region staleName keep false (stack := true)
  region "stale words inside the scanned range" scanned true (stack := true)
  if st.size > 0 then note s!"collection: {scanned.size} of {st.size} stale word(s) inside the scanned range, {st.size - keep.size} overwritten"
  collect
  dropRegion "stale words inside the scanned range"

def maybeCollect4 (why : String) : GM Unit := do
  if (← decide (σ := W) "gc.collect" 2) == 1 then
    note s!"a collection runs at {why}"
    collect4

def alloc4 (name : String) (kind : Kind) (words : Array UInt64) : GM Nat := do
  maybeCollect4 s!"the allocation of {name}"
  let w ← get
  let a := w.next
  set { w with heap := w.heap.push { name, base := a, words, kind }, next := a + 8 * words.size + 64 }
  note s!"allocate {name} at {a} ({reprStr kind})"
  return a

/-- An optimized build: does the frame keep this local in a stack slot? (-O0: always.) -/
def slotKept (opt : Nat) (what : String) : GM Bool := do
  if opt == 0 then return true
  let k ← decide (σ := W) "gc.slot" 2
  if k == 1 then note s!"-O{opt}: {what} lives only in a register" ; return false
  return true

/-! ## The exception in flight, again -/

inductive Shape where
  /-- round 3's test: `(try (try (throw (ex-info …)) (finally …)) (catch …))`, the throw in the
  same jank fn (the deftest's) as the finally. -/
  | sameFn
  /-- round 3's report: `(defn boom [] (throw (ex-info …)))` called from the try. -/
  | separateFn
  deriving BEq, Repr, Inhabited

/-- `finallyAllocs` allocations in the finally body, each of which may collect. While the
locals are live they are roots (in a stack slot or in a register, which bdwgc also scans); what
matters is what is left once the throw has happened. -/
def exceptionInFlight (shape : Shape) (opt : Nat) (finallyAllocs : Nat) : GM Unit := do
  let _ ← setupContext
  frame "F (the fn with the try/finally)" []
  let fr := if shape == .sameFn then "F (the fn with the try/finally)" else "boom"
  if shape == .separateFn then frame "boom" []
  let v ← alloc4 "the vector [0 1 2]" .normal #[0, 1, 2]
  frame fr [tag v]
  let data ← alloc4 "ex-data map {:k [0 1 2]}" .normal #[0, tag v]
  frame fr [tag v, tag data]
  let ex ← alloc4 "ex-info object" .normal #[0, 0, tag data]
  frame fr [tag v, tag data, tag ex]
  -- throw: the value goes into the C++ exception object (malloc, never scanned)
  region "C++ exception object (malloc)" #[tag ex] false
  -- after the throw, which of the locals still sit in a stack slot (-O0: all of them; -O1 and
  -- above: those the register allocator spilled)
  let kv ← slotKept opt "the vector's local"
  let kd ← slotKept opt "the map's local"
  let ke ← slotKept opt "the thrown local"
  let fw := (if kv then [tag v] else []) ++ (if kd then [tag data] else []) ++ (if ke then [tag ex] else [])
  if shape == .separateFn then
    frame "boom" fw
    dropFrame "boom"
    note "throw: boom's frame is popped; its words stay on the stack until overwritten"
  else
    frame fr fw
    note "throw: the thrown local stays in F's frame, which runs the finally"
  for i in [0:finallyAllocs] do
    let o ← alloc4 s!"finally's object {i}" .normal #[]
    frame "finally's frame" [tag o]
  dropFrame "finally's frame"
  -- catch(object_ref e): the word copied to F
  frame "F (the fn with the try/finally)" ((if shape == .sameFn then fw else []) ++ [tag ex])
  dropRegion "C++ exception object (malloc)"
  use ex "(ex-data e)"
  use data "(ex-data e)"
  use v "(:k (ex-data e))"

/-- The same, with the opposite property: a violation when the value survives (to show that both
outcomes are reachable when the replica allows a freed read). -/
def survives (body : GM Unit) : GM Unit := do
  let ok ← tryCatch (do body; pure true) (fun e => match e with
    | .violation _ _ => pure false
    | e => throw e)
  if ok then throw (.violation "value freed" "the value survived every collection of this timeline")

/-! ## The unbound root, again -/

/-- Round 3's `unboundRoot` with the frames that touched the var leaving stale words:
`(def x)` and `(def u @#'x)` at load (evaluate.cpp eval(def) 333-360: locals `var`; eval(call)
376-399: the argument vector holds the var), then in the test fn `(ns-unmap *ns* 'x)` (ns.cpp
105-115), `allocs` allocations, `(str u)` (var.cpp 351-354 reads `var->to_string()`). -/
def unboundRoot (allocs : Nat) (unmap : Bool) (rootKind : Kind := .atomic) : GM Unit := do
  let (_, nsObj) ← setupContext
  frame "loader frames" []
  let symX ← alloc4 "symbol x" .normal #[]
  frame "loader frames" [tag symX]
  let x ← alloc4 "var x" .normal #[0, 0, tag nsObj, tag symX, 0]
  frame "loader frames" [tag x]
  let r ← alloc4 "x's var_unbound_root" rootKind #[0, 0, tag x]
  setWord x 4 (tag r)
  let m0 ← alloc4 "vars map {x}" .normal #[tag symX, tag x]
  setWord nsObj 0 (tag m0)
  frame "loader frames" [tag x, tag r]
  let symU ← alloc4 "symbol u" .normal #[]
  frame "loader frames" [tag x, tag r, tag symU]
  let u ← alloc4 "var u" .normal #[0, 0, tag nsObj, tag symU, tag r]
  frame "loader frames" [tag x, tag r, tag symU, tag u]
  let m1 ← alloc4 "vars map {x, u}" .normal #[tag symX, tag x, tag symU, tag u]
  setWord nsObj 0 (tag m1)
  dropFrame "loader frames"
  frame "test fn" []
  if unmap then
    let m2 ← alloc4 "vars map {u}" .normal #[tag symU, tag u]
    setWord nsObj 0 (tag m2)
    note "(ns-unmap *ns* 'x)"
  for i in [0:allocs] do
    let _ ← alloc4 s!"object {i}" .normal #[]
  frame "test fn" [tag u]
  use u "(str u) reads u's root"
  use r "(str u) reads the unbound root"
  let xv ← word r 2
  use ((xv &&& pointerMask).toNat) "var_unbound_root::to_string reads var->to_string()"

/-! ## The printed form of an unbound root -/

/-- var.cpp 351-354: `util::format_to(buff, "unbound@{} for var {}", this, var->to_string())`;
`{}` of a pointer prints `0x` and its hex digits (fmt). -/
def jankUnboundStr (addrHex : String) (varStr : String) : String :=
  "unbound@0x" ++ addrHex ++ " for var " ++ varStr

/-- Clojure Var.java 42-44: `"Unbound: " + v`, and `Var.toString()` is `#'ns/name`. -/
def cljUnboundStr (varStr : String) : String := "Unbound: " ++ varStr

end Jank.R4.Runtime.Gc4

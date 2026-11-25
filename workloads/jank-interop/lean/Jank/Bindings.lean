import Determinismo

/-!
# Dynamic bindings, futures and OS thread ids (context.cpp, core.cpp `future`, var.cpp)

jank keeps every thread's binding frames in one map keyed by the OS thread id
(context.hpp `folly::Synchronized<native_unordered_map<std::thread::id,
native_list<thread_binding_frame>>> thread_binding_frames`).

- `context::push_thread_bindings(bindings)` (context.cpp): `auto &tbfs{ (*tbfs_map)[thread_id] };
  if(!tbfs.empty()) frame.bindings = tbfs.front().bindings;` then each new binding assoc'ed,
  `tbfs.push_front(frame)`.
- `context::get_thread_bindings()`: the front frame of this thread id's list, else empty.
- `var::deref` (var.cpp): `get_thread_binding()` (the front frame's entry) else the root.
- core.cpp `future(fn)`: captures `__rt_ctx->get_thread_bindings()`, starts a `std::thread`
  whose lambda calls `__rt_ctx->push_thread_bindings(bindings)`, runs `fn`, and returns. Nothing
  pops that frame or erases the thread's entry when the thread ends.

A `std::thread::id` is the pthread_t, which the C library may give again to a new thread once
the old one is joined (POSIX allows it; glibc's cached thread stacks make it the common case).
A new thread with a reused id finds the dead thread's frames in the map, and
`push_thread_bindings` starts its frame from them.

Clojure (core.clj `future-call` → `binding-conveyor-fn` → `Var.resetThreadBindingFrame`): the
new thread's frame is exactly the creator's.
-/

namespace Jank.Bindings

open Determinismo

/-- The value of `*x*` in a frame (`none`: not bound in it). Values: 0 = :root, 1 = :one. -/
abbrev Frame := Option Nat

structure Mem where
  /-- thread_binding_frames: OS thread id → frames, newest first. -/
  frames : List (Nat × List Frame) := []
  /-- OS thread ids in use, and the ones of joined threads (reusable). -/
  live : List Nat := [0]
  joined : List Nat := []
  nextId : Nat := 1
  /-- futures: their OS thread id, conveyed frame, result. -/
  futures : Array (Nat × Frame × Option Nat) := #[]
  clojure : Bool := false
  deriving Inhabited

def Mem.framesOf (m : Mem) (id : Nat) : List Frame := (m.frames.lookup id).getD []

def Mem.setFrames (m : Mem) (id : Nat) (fs : List Frame) : Mem :=
  { m with frames := (id, fs) :: m.frames.filter (·.1 != id) }

/-- `get_thread_bindings()` on thread `id`: the front frame (none: no frame). -/
def Mem.current (m : Mem) (id : Nat) : Frame := ((m.framesOf id).head?).getD none

/-- `push_thread_bindings(b)` on thread `id`: the new frame starts from the front frame. -/
def Mem.push (m : Mem) (id : Nat) (b : Frame) : Mem :=
  let fs := m.framesOf id
  let base := (fs.head?).getD none
  m.setFrames id ((match b with | some v => some v | none => base) :: fs)

def Mem.pop (m : Mem) (id : Nat) : Mem := m.setFrames id ((m.framesOf id).drop 1)

/-- `*x*` read on thread `id` (var.cpp `deref`): its binding, else the root (0). -/
def Mem.readX (m : Mem) (id : Nat) : Nat := (m.current id).getD 0

inductive Role where
  /-- the REPL's thread: runs the script -/
  | main
  /-- a future's thread: (index of the future, its body reads `*x*`) -/
  | future (index : Nat) (readsX : Bool)
  deriving Repr, BEq, Inhabited

structure Loc where
  role : Role
  osId : Nat
  pc : Nat := 0
  deriving Inhabited

abbrev PM := ProcessM Mem Loc

def mem : PM Mem := do pure (← get).memory
def setMem (m : Mem) : PM Unit := modify fun p => { p with memory := m }

/-- `std::thread{...}`: an OS thread id, fresh or a joined thread's (a decision). -/
def spawn (index : Nat) (readsX : Bool) (conveyed : Frame) : PM Unit := do
  let m ← mem
  let choices := m.nextId :: m.joined
  let id := choices.getD (← decide (σ := Process Mem Loc) "os.thread_id" choices.length) m.nextId
  let m := { m with live := id :: m.live, joined := m.joined.erase id,
                    nextId := if id == m.nextId then m.nextId + 1 else m.nextId,
                    futures := m.futures.push (id, conveyed, none) }
  setMem m
  modify fun p => { p with threads := p.threads.push (some { role := .future index readsX, osId := id }),
                           log := p.log.push s!"future {index} starts on OS thread {id}" }

/-- The script of the main thread:

    (def ^:dynamic *x* :root)
    (binding [*x* :one] @(future nil))
    @(future *x*)
-/
def mainStep (l : Loc) : PM (StepResult Loc) := do
  let m ← mem
  match l.pc with
  | 0 => setMem (m.push l.osId (some 1)); pure (.ran { l with pc := 1 })   -- (binding [*x* :one]
  | 1 => spawn 0 false (m.current l.osId); pure (.ran { l with pc := 2 })   -- (future nil)
  | 2 =>                                                                  -- @: join
    match m.futures[0]? with
    | some (id, _, some _) =>
      setMem { m with live := m.live.erase id, joined := id :: m.joined }
      pure (.ran { l with pc := 3 })
    | _ => pure .blocked
  | 3 => setMem (m.pop l.osId); pure (.ran { l with pc := 4 })              -- binding's finally
  | 4 => spawn 1 true (m.current l.osId); pure (.ran { l with pc := 5 })    -- (future *x*)
  | 5 =>
    match m.futures[1]? with
    | some (id, _, some _) =>
      setMem { m with live := m.live.erase id, joined := id :: m.joined }
      pure .done
    | _ => pure .blocked
  | _ => pure .done

def futureStep (l : Loc) (index : Nat) (readsX : Bool) : PM (StepResult Loc) := do
  let m ← mem
  let (_, conveyed, _) := m.futures[index]!
  match l.pc with
  | 0 =>
    -- jank: push_thread_bindings(bindings) on this OS thread id's frame list.
    -- Clojure: resetThreadBindingFrame(frame): exactly the conveyed frame.
    let m := if m.clojure then m.setFrames l.osId [conveyed] else m.push l.osId conveyed
    setMem m
    pure (.ran { l with pc := 1 })
  | 1 =>
    let v := if readsX then m.readX l.osId else 0
    setMem { m with futures := m.futures.set! index (l.osId, conveyed, some v),
                    -- Clojure: the frame is the thread's own and ends with it.
                    frames := if m.clojure then m.frames.filter (·.1 != l.osId) else m.frames }
    -- `.ran`, then `.done`: Threads.interleave retries blocked threads only after a `.ran`.
    pure (.ran { l with pc := 2 })
  | _ => pure .done

def step (_ : Nat) (l : Loc) : PM (StepResult Loc) :=
  match l.role with
  | .main => mainStep l
  | .future i r => futureStep l i r

def run (clojure : Bool) (source : Source) : Ended × Array String :=
  let start : Process Mem Loc := { memory := { clojure }, threads := #[some { role := .main, osId := 0 }] }
  let body : PM Unit := do
    interleave { step := step } 100
    let m ← mem
    match m.futures[1]? with
    | some (id, _, some v) =>
      if v != 0 then
        throw (.violation "a future sees its creator's bindings"
          s!"(binding [*x* :one] @(future nil)) @(future *x*): the second future (OS thread {id}) read *x* = {if v == 1 then ":one" else toString v}, Clojure :root")
    | _ => pure ()
  match runProcess start body source with
  | (.ok _, p) => ({ taken := p.decisions.taken, violation := none }, p.log)
  | (.error (.violation prop d), p) => ({ taken := p.decisions.taken, violation := some (prop, d) }, p.log)
  | (.error .limit, p) => ({ taken := p.decisions.taken, violation := none }, p.log)
  | (.error (.nodeDown _), p) => ({ taken := p.decisions.taken, violation := none }, p.log)

/-! ## `set!` of a conveyed binding inside a future

context.cpp `push_thread_bindings`: a conveyed entry that is already a `var_thread_binding` is
re-boxed: `make_box<var_thread_binding>(..->value, thread_id)` with the **future's** thread id.
var.cpp `var::set`: `if(std::this_thread::get_id() != binding->thread_id) return err(...)`.
Clojure: the future gets the creator's `Frame` with the same `TBox`es (thread = the creator), and
`Var.set` throws "Can't set!: ... from non-binding thread". -/

structure Box where
  value : Nat
  thread : Nat
  deriving Repr, BEq

def jankConvey (b : Box) (futureThread : Nat) : Box := { b with thread := futureThread }
def cljConvey (b : Box) (_ : Nat) : Box := b

/-- `var::set` / `Var.set`: allowed on the binding's own thread. -/
def setAllowed (b : Box) (thread : Nat) : Bool := b.thread == thread

/-- `(binding [*x* 2] @(future (set! *x* 3)))`: jank allows the `set!`, Clojure throws. -/
theorem set_in_future (main fut : Nat) (h : main ≠ fut) :
    setAllowed (jankConvey ⟨2, main⟩ fut) fut = true ∧ setAllowed (cljConvey ⟨2, main⟩ fut) fut = false := by
  simp [setAllowed, jankConvey, cljConvey]
  omega

end Jank.Bindings

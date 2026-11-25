import Determinismo
import Jank.Sync

/-!
# delay, promise, deref with a timeout, in the Threads world

## delay (src/cpp/jank/runtime/obj/delay.cpp)

    object_ref delay::deref()
    {
      std::lock_guard<std::mutex> const lock{ mutex };
      if(val.is_some()) { return val; }
      if(error.is_some()) { throw error; }
      try { val = fn.call(); } catch(...) { error = ...; throw; }
      return val;
    }
    bool delay::is_realized() const { lock; return val.is_some(); }

`val` starts as `object_ref{}`, which is `nil` (oref.hpp: the default `data` is `&_jank_nil`);
`is_some()` is "not nil". A body that returns nil leaves `val` nil: the next deref runs the body
again, and `realized?` stays false. A body that threw stores `error` but `realized?` reads `val`.

Clojure (Delay.java): `realize()` sets `fn = null` and `lock = null` once the body ran (whatever
it returned or threw); `isRealized()` is `lock == null`. The docstring: "will invoke the body
only the first time it is forced".

## promise (src/cpp/jank/runtime/obj/promise.cpp at 7135b7708, core.jank `deliver`)

    object_ref promise::call(object_ref const o) const            // line 24
    {
      auto const locked_state{ state.wlock() };
      if(locked_state->status == promise_status::pending)
      { ...; sync.notify_all(); return runtime::detail::untagged(this); }   // 27–33
      /* Clojure returns nil for deliveries to an already-realized promise. */
      return jank_nil;                                             // 36
    }

Since 7135b7708 the delivering call returns the promise and every later one nil, as Clojure's
`promise` (core.clj): `(when (and (pos? (.getCount d)) (compare-and-set! v d x)) (.countDown d)
this)`. (At f3d82d654 every call returned the promise: D20.)

## deref with a timeout (core.jank `deref`)

    ([ref timeout-ms timeout-val]
     ;(if (instance? clojure.lang.IBlockingDeref ref) ... )
     )

The 3-arity body is empty: it returns nil at once. Clojure: the value if delivered within the
timeout, else `timeout-val`.
-/

namespace Jank.Delay

open Determinismo Jank.Sync

/-! ## delay -/

/-- What the delay's body does when it runs. -/
inductive Body where
  | returnsNil | returnsValue | throws
  deriving Repr, BEq, Inhabited

structure DelayMem where
  mutex : Jank.Sync.Mutex := {}
  /-- jank: `val` (none = nil), `error`. -/
  val : Option Nat := none
  error : Bool := false
  /-- Clojure: `fn == null` once realized. -/
  realized : Bool := false
  /-- How many times the body ran. -/
  runs : Nat := 0
  body : Body := .returnsNil
  clojure : Bool := false
  /-- `realized?` answers seen after a deref returned. -/
  realizedAfter : List Bool := []
  deriving Inhabited

/-- A thread: derefs `n` times, then asks `realized?`. pc 0: lock, 1: check/run, 2: unlock,
3: realized?. -/
structure DLoc where
  pc : Nat := 0
  derefsLeft : Nat
  deriving Inhabited

def bodyResult : Body → Option Nat × Bool
  | .returnsNil => (none, false)
  | .returnsValue => (some 7, false)
  | .throws => (none, true)

def delayStep (t : Nat) (l : DLoc) : ProcessM DelayMem DLoc (StepResult DLoc) := do
  let m := (← get).memory
  let set (m : DelayMem) : ProcessM DelayMem DLoc Unit := modify fun p => { p with memory := m }
  match l.pc with
  | 0 =>
    if l.derefsLeft == 0 then pure (.ran { l with pc := 3 })
    else match m.mutex.lock t with
      | some mx => set { m with mutex := mx }; pure (.ran { l with pc := 1 })
      | none => pure .blocked
  | 1 =>
    if m.clojure then
      -- Delay.realize: run once, whatever the body does.
      if !m.realized then
        set { m with runs := m.runs + 1, realized := true }
      pure (.ran { l with pc := 2 })
    else
      if m.val.isSome then pure (.ran { l with pc := 2 })          -- return val
      else if m.error then pure (.ran { l with pc := 2 })          -- throw error
      else
        let (v, threw) := bodyResult m.body
        set { m with runs := m.runs + 1, val := v, error := threw }  -- val = fn.call()
        pure (.ran { l with pc := 2 })
  | 2 =>
    set { m with mutex := m.mutex.unlock }
    pure (.ran { l with pc := 0, derefsLeft := l.derefsLeft - 1 })
  | 3 =>
    let r := if m.clojure then m.realized else m.val.isSome
    set { m with realizedAfter := m.realizedAfter ++ [r] }
    pure .done
  | _ => pure .done

def runDelay (body : Body) (clojure : Bool) (threads derefs : Nat) (source : Source) : Ended :=
  let start : Process DelayMem DLoc :=
    { memory := { body, clojure }, threads := (List.replicate threads (some { derefsLeft := derefs })).toArray }
  let prog : ProcessM DelayMem DLoc Unit := do
    interleave { step := delayStep } 100
    let m := (← get).memory
    if m.runs > 1 then
      throw (.violation "a delay's body runs once"
        s!"{threads} thread(s), {derefs} deref(s) each, body {reprStr body}: the body ran {m.runs} times")
    if m.realizedAfter.any (· == false) then
      throw (.violation "realized? after a deref"
        s!"body {reprStr body}: (realized? d) is false after @d returned or threw")
  match runProcess start prog source with
  | (.ok _, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.violation prop d), p) => { taken := p.decisions.taken, violation := some (prop, d) }
  | (.error .limit, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.nodeDown _), p) => { taken := p.decisions.taken, violation := none }

/-! ## promise and deliver -/

structure PromiseMem where
  state : SharedMutex := {}
  ready : Bool := false
  val : Nat := 0
  /-- What each deliver returned: true for the promise (truthy), false for nil. -/
  returns : List Bool := []
  /-- What each `(deref p timeout-ms timeout-val)` returned. -/
  timeoutDerefs : List (Option Nat) := []
  clojure : Bool := false
  deriving Inhabited

/-- A thread: `deliver x` (pc 0: wlock, 1: set if pending, 2: unlock and return), or a deref with
a timeout (pc 10). -/
structure PLoc where
  pc : Nat := 0
  x : Nat
  delivers : Bool
  deriving Inhabited

def promiseStep (t : Nat) (l : PLoc) : ProcessM PromiseMem PLoc (StepResult PLoc) := do
  let m := (← get).memory
  let set (m : PromiseMem) : ProcessM PromiseMem PLoc Unit := modify fun p => { p with memory := m }
  if !l.delivers then
    -- core.jank deref, 3-arity: an empty body, nil. Clojure: the value if delivered before
    -- the timeout, else timeout-val (99): both possible, decided by the timing.
    if m.clojure then
      let within ← decide (σ := Process PromiseMem PLoc) "time.within_timeout" 2
      let r := if m.ready && within == 0 then some m.val else some 99
      set { m with timeoutDerefs := m.timeoutDerefs ++ [r] }
    else
      set { m with timeoutDerefs := m.timeoutDerefs ++ [none] }
    return .done
  match l.pc with
  | 0 =>
    let m := { m with state := m.state.announce t }
    match m.state.lock t with
    | some s => set { m with state := s }; pure (.ran { l with pc := 1 })
    | none => set m; pure .blocked
  | 1 =>
    if !m.ready then
      set { m with ready := true, val := l.x, returns := m.returns ++ [true] }
    else
      -- promise.cpp:36 (7135b7708): nil, as Clojure.
      set { m with returns := m.returns ++ [false] }
    pure (.ran { l with pc := 2 })
  | 2 =>
    -- The unlock is a step that ran (Threads.interleave unblocks waiters only after `.ran`).
    set { m with state := m.state.unlock }
    pure (.ran { l with pc := 3 })
  | _ => pure .done

def runPromise (clojure : Bool) (delivers : Nat) (timeoutDerefs : Nat) (source : Source) : Ended :=
  let threads := (List.range delivers).map (fun i => some ({ x := i + 1, delivers := true } : PLoc))
    ++ List.replicate timeoutDerefs (some ({ x := 0, delivers := false } : PLoc))
  let start : Process PromiseMem PLoc := { memory := { clojure }, threads := threads.toArray }
  let prog : ProcessM PromiseMem PLoc Unit := do
    interleave { step := promiseStep } 100
    let m := (← get).memory
    let truthy := (m.returns.filter id).length
    if truthy != 1 && delivers > 0 then
      throw (.violation "exactly one deliver returns the promise"
        s!"{delivers} concurrent (deliver p x): {truthy} returned the promise, {m.returns.length - truthy} nil")
    if m.timeoutDerefs.any (·.isNone) then
      throw (.violation "a deref with a timeout returns the value or timeout-val"
        s!"(deref p 100 :timeout) returned nil")
  match runProcess start prog source with
  | (.ok _, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.violation prop d), p) => { taken := p.decisions.taken, violation := some (prop, d) }
  | (.error .limit, p) => { taken := p.decisions.taken, violation := none }
  | (.error (.nodeDown _), p) => { taken := p.decisions.taken, violation := none }

end Jank.Delay

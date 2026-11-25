import Determinismo
import Jank.R3.Runtime.Common
import Jank.R3.Runtime.Folly

/-!
# jank's locks along code paths reachable from jank programs (jank 7135b7708)

Each jank operation is expanded into the exact sequence of lock acquisitions, releases, reads,
writes and callbacks of its C++ (paths under `upstream-main/compiler+runtime/`). Beside it, the
same operation in Clojure 1.12 (Java semantics: `synchronized` monitors and `ReentrantLock` are
reentrant; `Atom`'s validate and notifyWatches take no lock; `FutureTask` and `CountDownLatch`
never block a canceller).

The jank side (`Mode.jank`):

| operation | C++ | locks, in order |
|---|---|---|
| `swap!` | atom.cpp `swap` 83-95 | load; `validate` = `validator.rlock()` (245) around the validator call; CAS; `notify_watches` = `watches.rlock()` (45) around every watch call |
| `reset!` | atom.cpp 56-63 | `validate`; load; store; `notify_watches` |
| `add-watch`/`remove-watch` | atom.cpp 249-259 | `watches.wlock()` |
| `set-validator!` | atom.cpp 237-242 | calls the new validator on `deref()` with no lock, then `validator.wlock()` |
| `get-validator` | atom.cpp 243-247 | `validator.rlock()` |
| `alter-var-root` | var.cpp 106-112 | `std::lock_guard<folly::SharedMutex>{write_mutex}` (exclusive) around `apply_to(f, ...)` |
| `def` (bind_root) | var.cpp 98-104 | `write_mutex` exclusive |
| `(meta #'v)` | var.cpp `get_meta` → lazy_meta.cpp 30-46 | `state.wlock()`; when a source is pending: `binding_scope` (context.cpp 706-750, `thread_binding_frames.wlock()`), `_jank_eval_str(source)` (jank code), pop (`thread_binding_frames.wlock()`) |
| `reset-meta!` | lazy_meta.cpp 48-53 | `state.wlock()` |
| `@delay` | delay.cpp 19-46 | `std::lock_guard<std::mutex>` around the body |
| `realized?` delay | delay.cpp 48-52 | the same `std::mutex` |
| future body | core.cpp 1091-1170 | `push_thread_bindings` (`thread_binding_frames.wlock()`), body, `state.wlock()` set done, `unregister_future` (`active_futures.wlock()`), thread exit |
| `@future` | future.cpp 12-31 | `thread.wlock()` held across `join()`; then `state.rlock()` |
| `future-cancel` | core.cpp 1174-1185 | `state.rlock()` held while `thread.wlock()` and `pthread_cancel` |
| `future-cancelled?` | core.cpp 1187-1235 | `state.ulock()` held while `thread.wlock()` and `pthread_tryjoin_np`; then `moveFromUpgradeToWrite` |
| `realized?` future | future.cpp 33-47 | `state.rlock()` |
| `deliver` | promise.cpp 24-37 | `state.wlock()`, `notify_all` |
| `@promise` | promise.cpp 10-16 | `state.wlock()`; `sync.wait` releases and re-takes it |
| `require` of a module with a managed load fn | loader_dynamic.cpp 726-736 | `state.lock()` (`std::recursive_mutex`) held while the load fn runs the module |

The Clojure side (`Mode.clojure`): Atom.java/ARef.java (`addWatch`/`removeWatch` synchronized on the
atom, nothing else locked), Var.java (`alterRoot`, `bindRoot`, `meta` synchronized on the var),
Delay.java (a `ReentrantLock` in `realize`; `isRealized` is `lock == null`), FutureTask (`get`
waits for completion, `cancel`/`isCancelled` never block), promise (CountDownLatch), `require`
(no lock). In Clojure a var's metadata is evaluated when it is defined, so `meta` never runs code.

SharedMutexes are the coarse `Folly.CSM` by default (validated against the replica) or the fine
replica (`fine := true`), used to confirm each finding at the atomic level.

Callbacks (validator, watch, `alter-var-root` fn, var meta source, delay body, future body, module
body) are bodies drawn from the same operation alphabet; a body runs at a depth budget, and a body
at depth 0 does nothing, in both modes alike.
-/

namespace Jank.R3.Runtime.Locks

open Determinismo

inductive Mode | jank | clojure
  deriving BEq, Hashable, Repr, Inhabited

/-- The operations, each on the program's single object of its kind (`a` atom, `v` var, `d`
delay, `f` future, `p` promise, `M` module). -/
inductive JOp where
  | swap | reset | addWatch | removeWatch | setValidator | getValidator
  | alterVarRoot | defVar | metaRead | resetMeta
  | derefDelay | realizedDelay
  | derefFuture | cancelFuture | cancelledFuture | realizedFuture
  | deliver | derefPromise | sleep | requireMod | requireOther
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

def JOp.clj : JOp → String
  | .swap => "(swap! a inc)" | .reset => "(reset! a 1)"
  | .addWatch => "(add-watch a :k w)" | .removeWatch => "(remove-watch a :k)"
  | .setValidator => "(set-validator! a vf)" | .getValidator => "(get-validator a)"
  | .alterVarRoot => "(alter-var-root #'v f)" | .defVar => "(def v 1)"
  | .metaRead => "(meta #'v)" | .resetMeta => "(reset-meta! #'v {})"
  | .derefDelay => "@d" | .realizedDelay => "(realized? d)"
  | .derefFuture => "@f" | .cancelFuture => "(future-cancel f)"
  | .cancelledFuture => "(future-cancelled? f)" | .realizedFuture => "(realized? f)"
  | .deliver => "(deliver p 1)" | .derefPromise => "@p" | .sleep => "(sleep)"
  | .requireMod => "(require 'M)"
  | .requireOther => "(require 'N)"

def alphabet : List JOp :=
  [.swap, .reset, .addWatch, .removeWatch, .setValidator, .getValidator,
   .alterVarRoot, .defVar, .metaRead, .resetMeta, .derefDelay, .realizedDelay,
   .derefFuture, .cancelFuture, .cancelledFuture, .realizedFuture,
   .deliver, .derefPromise, .sleep, .requireMod, .requireOther]

/-- The two-thread census's alphabet: the operations that take a lock or run a callback under one
(dropping `reset!`/`remove-watch`/`reset-meta!`/`realized?` of a future, which take the same locks
as `swap!`/`add-watch`/`meta`/`future-cancel`'s first lock, and the promise, sleep and module ops
already covered by the one-thread census). -/
def alphabet2 : List JOp :=
  [.swap, .addWatch, .setValidator, .getValidator, .alterVarRoot, .defVar, .metaRead,
   .derefDelay, .realizedDelay, .derefFuture, .cancelFuture, .cancelledFuture]

/-- Callback slots of the program's objects. -/
inductive Slot where
  | validator | watch | alterFn | metaSrc | delayBody | futureBody | moduleBody
  deriving BEq, Hashable, Repr, Inhabited, DecidableEq

def Slot.idx : Slot → Nat
  | .validator => 0 | .watch => 1 | .alterFn => 2 | .metaSrc => 3 | .delayBody => 4
  | .futureBody => 5 | .moduleBody => 6

def Slot.name : Slot → String
  | .validator => "validator vf" | .watch => "watch w" | .alterFn => "alter-var-root fn f"
  | .metaSrc => "var v's meta expression" | .delayBody => "delay d's body"
  | .futureBody => "future f's body" | .moduleBody => "module M's top level"

/-- SharedMutex ids. -/
def smValidator : Nat := 0
def smWatches : Nat := 1
def smWriteMutex : Nat := 2
def smMeta : Nat := 3
def smFState : Nat := 4
def smFThread : Nat := 5
def smPState : Nat := 6
def smTbfs : Nat := 7
def smFutures : Nat := 8
def numSM : Nat := 9

def smName : Nat → String
  | 0 => "atom validator" | 1 => "atom watches" | 2 => "var write_mutex" | 3 => "var lazy_meta"
  | 4 => "future state" | 5 => "future thread" | 6 => "promise state"
  | 7 => "thread_binding_frames" | 8 => "active_futures" | _ => "?"

/-- Reentrant locks: jank's loader `std::recursive_mutex` (0); Clojure monitors (1 atom, 2 var,
3 delay's ReentrantLock). Non-reentrant `std::mutex`: 0 the delay's. -/
def rLoader : Nat := 0
def rAtom : Nat := 1
def rVar : Nat := 2
def rDelay : Nat := 3

def rName : Nat → String
  | 0 => "loader recursive_mutex" | 1 => "atom monitor" | 2 => "var monitor" | 3 => "delay ReentrantLock" | _ => "?"

/-- One instruction of a thread. -/
inductive I where
  | op (o : JOp) (d : Nat)
  /-- SharedMutex: shared, exclusive (two halves in coarse mode), upgrade, upgrade→exclusive. -/
  | sAcq (m : Nat) | sRel (m : Nat)
  | eAcq (m : Nat) | eAcq2 (m : Nat) | eRel (m : Nat)
  | uAcq (m : Nat) | uRel (m : Nat) | upg (m : Nat) | upg2 (m : Nat)
  /-- std::mutex (non-reentrant). -/
  | mAcq | mRel
  /-- reentrant lock / monitor. -/
  | rAcq (x : Nat) | rRel (x : Nat)
  | call (s : Slot) (d : Nat)
  | callWatches (d : Nat)
  /-- atom: load into the thread's register; CAS from it (retry = re-run the op). -/
  | atomLoad
  | atomCas (o : JOp) (d : Nat)
  | atomStore
  | watchAdd | watchRemove | validatorSet
  | varStore
  /-- lazy_meta::get: if a source is pending, evaluate it. -/
  | metaCheck (d : Nat)
  | metaClear
  /-- delay::deref after taking its lock. -/
  | delayCheck (d : Nat)
  | delaySet
  /-- Clojure: realize only while the fn is set. -/
  | cljDelay (d : Nat)
  /-- future: join (wait for the thread to exit), status checks. -/
  | join
  | cancelCheck
  | cancelSignal
  | cancelledCheck
  | tryJoin
  | afterTryJoin
  | statusSet
  | fCancelled
  /-- the future's own thread: body done, exit. -/
  | fDone
  | fExit
  /-- Clojure: wait until the future is done or cancelled. -/
  | fWait
  | promiseSet
  | promiseWait
  /-- jank: condition_variable_any::wait: registered with the cv (its internal mutex) before the
  lock is released, sleeps until notified, then re-takes the lock. -/
  | cvRegister
  | cvSleep
  | cljDelayInner (d : Nat)
  /-- the future thread's catch handlers (core.cpp 1128-1166): where an exception or a forced
  unwind out of the body lands. -/
  | catchMark
  /-- Clojure: a var's metadata expression run lock-free when first read (its timing is R43's
  business; here only the locks are compared). -/
  | cljMeta (d : Nat)
  | sleepPoint
  deriving BEq, Hashable, Repr, Inhabited

structure Mem where
  mode : Mode
  fine : Bool
  bodies : Array (List JOp)
  /-- whether the slot holds a body (validator set, watch added, meta source pending). -/
  hasValidator : Bool
  hasWatch : Bool
  metaPending : Bool
  atomVal : Nat := 0
  varRoot : Nat := 0
  delayVal : Bool := false
  /-- Clojure: the delay's `fn` and `lock` fields still set. -/
  delayFn : Bool := true
  fStatus : Nat := 0     -- 0 running, 1 done, 2 cancelled
  fExited : Bool := false
  fJoined : Bool := false
  fCancelReq : Bool := false
  fThread : Option Nat := none
  pReady : Bool := false
  cvSleepers : List Nat := []
  sm : Array Folly.CSM
  fm : Folly.FMem
  stdMutex : Option Nat := none
  /-- reentrant: owner and count. -/
  rl : Array (Option (Nat × Nat))
  deriving BEq, Hashable, Repr, Inhabited

structure Loc where
  instrs : List I
  reg : Nat := 0
  /-- coarse exclusive: first half done; fine: the replica's pc. -/
  half : Bool := false
  pc : Option Folly.Pc := none
  toks : List (Nat × Folly.Token) := []
  /-- the thread is waiting on the promise's condition variable. -/
  asleep : Bool := false
  deriving BEq, Hashable, Repr, Inhabited

abbrev PM := ProcessM Mem Loc

def mem : PM Mem := do pure (← get).memory
def setMem (m : Mem) : PM Unit := modify fun p => { p with memory := m }

/-! ## Expansions -/

/-- `validate(next)` (atom.cpp 261-265). -/
def validateJ (d : Nat) : List I := [.sAcq smValidator, .call .validator d, .sRel smValidator]

/-- `notify_watches` (atom.cpp 43-54). -/
def notifyJ (d : Nat) : List I := [.sAcq smWatches, .callWatches d, .sRel smWatches]

def exclusive (m : Nat) : List I := [.eAcq m, .eAcq2 m]

/-- jank's expansion of an operation (one level). -/
def expandJ (o : JOp) (d : Nat) : List I :=
  match o with
  | .swap => [.atomLoad] ++ validateJ d ++ [.atomCas o d]
  | .reset => validateJ d ++ [.atomStore] ++ notifyJ d
  | .addWatch => exclusive smWatches ++ [.watchAdd, .eRel smWatches]
  | .removeWatch => exclusive smWatches ++ [.watchRemove, .eRel smWatches]
  | .setValidator => [.call .validator d] ++ exclusive smValidator ++ [.validatorSet, .eRel smValidator]
  | .getValidator => [.sAcq smValidator, .sRel smValidator]
  | .alterVarRoot => exclusive smWriteMutex ++ [.call .alterFn d, .varStore, .eRel smWriteMutex]
  | .defVar => exclusive smWriteMutex ++ [.varStore, .eRel smWriteMutex]
  | .metaRead => exclusive smMeta ++ [.metaCheck d, .eRel smMeta]
  | .resetMeta => exclusive smMeta ++ [.metaClear, .eRel smMeta]
  | .derefDelay => [.mAcq, .delayCheck d, .mRel]
  | .realizedDelay => [.mAcq, .mRel]
  | .derefFuture => exclusive smFThread ++ [.join, .eRel smFThread, .sAcq smFState, .sRel smFState]
  | .cancelFuture => [.sAcq smFState, .cancelCheck, .sRel smFState]
  | .cancelledFuture => [.uAcq smFState, .cancelledCheck]
  | .realizedFuture => [.sAcq smFState, .sRel smFState]
  | .deliver => exclusive smPState ++ [.promiseSet, .eRel smPState]
  | .derefPromise => exclusive smPState ++ [.promiseWait, .eRel smPState]
  | .sleep => [.sleepPoint]
  | .requireMod => [.rAcq rLoader, .call .moduleBody d, .rRel rLoader]
  -- a module without a managed load fn: loader::load checks the managed fns and finds the file
  -- under state.lock() (loader_dynamic.cpp 726-736, 549-554), then evaluates it unlocked
  | .requireOther => [.rAcq rLoader, .rRel rLoader]

/-- Clojure's expansion. -/
def expandC (o : JOp) (d : Nat) : List I :=
  match o with
  | .swap => [.atomLoad, .call .validator d, .atomCas o d]
  | .reset => [.call .validator d, .atomStore, .callWatches d]
  | .addWatch => [.rAcq rAtom, .watchAdd, .rRel rAtom]
  | .removeWatch => [.rAcq rAtom, .watchRemove, .rRel rAtom]
  | .setValidator => [.call .validator d, .validatorSet]
  | .getValidator => []
  | .alterVarRoot => [.rAcq rVar, .call .alterFn d, .varStore, .rRel rVar]
  | .defVar => [.rAcq rVar, .varStore, .rRel rVar]
  | .metaRead => [.rAcq rVar, .rRel rVar, .cljMeta d]
  | .resetMeta => [.rAcq rVar, .metaClear, .rRel rVar]
  | .derefDelay => [.cljDelay d]
  | .realizedDelay => []
  | .derefFuture => [.fWait]
  | .cancelFuture => [.cancelSignal]
  | .cancelledFuture => []
  | .realizedFuture => []
  | .deliver => [.promiseSet]
  | .derefPromise => [.promiseWait]
  | .sleep => [.sleepPoint]
  | .requireMod => [.call .moduleBody d]
  | .requireOther => []

/-- The future's own thread (core.cpp 1104-1168 / FutureTask.run). -/
def futureThread (mode : Mode) (d : Nat) : List I :=
  match mode with
  | .jank => exclusive smTbfs ++ [.eRel smTbfs, .call .futureBody d, .catchMark] ++ exclusive smFState ++
             [.fDone, .eRel smFState] ++ exclusive smFutures ++ [.eRel smFutures, .fExit]
  | .clojure => [.call .futureBody d, .catchMark, .fDone, .fExit]

def isRelease : I → Bool
  | .sRel _ | .eRel _ | .uRel _ | .mRel | .rRel _ => true
  | _ => false

/-- Unwinding to the future's catch handlers: the guards still held release (LockedPtr,
lock_guard destructors); everything else up to the handlers is skipped. -/
def unwindTo (is : List I) : List I × List I :=
  ((is.takeWhile (· != .catchMark)).filter isRelease, (is.dropWhile (· != .catchMark)).drop 1)

/-! ## Locks -/

def smOp (a : I) : Option (Nat × Folly.Op) :=
  match a with
  | .sAcq m => some (m, .lockShared)
  | .eAcq m => some (m, .lock)
  | .eRel m => some (m, .unlock)
  | .uAcq m => some (m, .lockUpgrade)
  | .uRel m => some (m, .unlockUpgrade)
  | .upg m => some (m, .upgradeToLock)
  | _ => none

/-- A SharedMutex instruction with the fine replica: one atomic step; `none` when it completed. -/
def fineSM (t : Nat) (l : Loc) (m : Nat) (op : Folly.Op) : PM (Option (StepResult Loc)) := do
  let me ← mem
  let op : Folly.Op := match op with
    | .unlockShared _ => .unlockShared ((l.toks.find? (fun (x : Nat × Folly.Token) => x.1 == m)).map (·.2) |>.getD .inline)
    | o => o
  let pc := l.pc.getD op.start
  let (f', r) ← Folly.stepPc (σ := Process Mem Loc) t m 2 me.fm pc
  setMem { me with fm := f' }
  match r with
  | .blocked => return some .blocked
  | .next pc' => return some (.ran { l with pc := some pc' })
  | .done ret =>
    -- holder bookkeeping (for reports): the coarse view of what completed
    let c := (← mem).sm[m]!
    let c' : Folly.CSM := match op with
      | .lockShared => { c with s := t :: c.s }
      | .unlockShared _ => c.unlockShared t
      | .lock | .upgradeToLock => { c with e := some t, u := none, pend := none }
      | .unlock => c.unlock
      | .lockUpgrade => { c with u := some t }
      | .unlockUpgrade => c.unlockUpgrade
    setMem { (← mem) with sm := (← mem).sm.set! m c' }
    let toks := match op, ret with
      | .lockShared, .doneS tok => (m, tok) :: l.toks
      | .unlockShared _, _ =>
        match l.toks.findIdx? (fun (x : Nat × Folly.Token) => x.1 == m) with
        | some i => l.toks.eraseIdx i
        | none => l.toks
      | _, _ => l.toks
    return some (.ran { l with pc := none, toks, instrs := l.instrs.drop 1 })

/-! ## The step -/

def ifBody (me : Mem) (s : Slot) (d : Nat) : List I :=
  if d == 0 then [] else (me.bodies[s.idx]!).map fun o => I.op o (d - 1)

/-- One step of thread `t`. -/
def step (t : Nat) (l : Loc) : PM (StepResult Loc) := do
  match l.instrs with
  | [] => pure .done
  | i :: rest =>
    let me ← mem
    let go (l' : Loc) : PM (StepResult Loc) := pure (.ran l')
    let next : PM (StepResult Loc) := go { l with instrs := rest }
    let push (is : List I) : PM (StepResult Loc) := go { l with instrs := is ++ rest }
    match i with
    | .op o d =>
      Process.note s!"thread {t}: {o.clj}"
      push (match me.mode with | .jank => expandJ o d | .clojure => expandC o d)
    | .call s d =>
      let has := match s with
        | .validator => me.hasValidator | .watch => me.hasWatch | .metaSrc => me.metaPending | _ => true
      if has then push (ifBody me s d) else next
    | .callWatches d => if me.hasWatch then push (ifBody me .watch d) else next
    -- SharedMutex
    | .sAcq m | .eAcq m | .eRel m | .uAcq m | .uRel m | .upg m =>
      if me.fine then
        let op := (smOp i).get!.2
        match ← fineSM t l m op with
        | some r =>
          match r with
          | .ran l' => if l'.pc.isNone then Process.note s!"thread {t}: {smName m} {reprStr op} done"
          | _ => pure ()
          pure r
        | none => pure .blocked
      else
        let c := me.sm[m]!
        let put (c' : Folly.CSM) : PM Unit := setMem { me with sm := me.sm.set! m c' }
        match i with
        | .sAcq _ => match c.lockShared t with
          | some c' => put c'; Process.note s!"thread {t}: {smName m} rlock"; next
          | none => pure .blocked
        | .eAcq _ => match c.lockSet t with
          | some c' => put c'; Process.note s!"thread {t}: {smName m} wlock sets kHasE"; next
          | none => pure .blocked
        | .eRel _ => put c.unlock; Process.note s!"thread {t}: {smName m} unlock"; next
        | .uAcq _ => match c.lockUpgrade t with
          | some c' => put c'; Process.note s!"thread {t}: {smName m} ulock"; next
          | none => pure .blocked
        | .uRel _ => put c.unlockUpgrade; next
        | .upg _ => put (c.upgradeSet t); next
        | _ => next
    | .eAcq2 m | .upg2 m =>
      if me.fine then next
      else
        match me.sm[m]!.lockDrain t with
        | some c' => setMem { me with sm := me.sm.set! m c' }; Process.note s!"thread {t}: {smName m} wlock held"; next
        | none => pure .blocked
    | .sRel m =>
      if me.fine then
        match ← fineSM t l m (.unlockShared .inline) with
        | some r => pure r
        | none => pure .blocked
      else
        setMem { me with sm := me.sm.set! m (me.sm[m]!.unlockShared t) }
        Process.note s!"thread {t}: {smName m} runlock"
        next
    -- std::mutex (delay.cpp): a second lock by its owner never returns
    | .mAcq =>
      if me.stdMutex.isNone then
        setMem { me with stdMutex := some t }; Process.note s!"thread {t}: delay std::mutex lock"; next
      else pure .blocked
    | .mRel => setMem { me with stdMutex := none }; next
    -- reentrant
    | .rAcq x =>
      match me.rl[x]! with
      | none => setMem { me with rl := me.rl.set! x (some (t, 1)) }; Process.note s!"thread {t}: {rName x} lock"; next
      | some (o, n) =>
        if o == t then setMem { me with rl := me.rl.set! x (some (t, n + 1)) }; next
        else pure .blocked
    | .rRel x =>
      match me.rl[x]! with
      | some (o, n) => setMem { me with rl := me.rl.set! x (if n ≤ 1 then none else some (o, n - 1)) }; next
      | none => next
    -- atom
    | .atomLoad => go { l with instrs := rest, reg := me.atomVal }
    | .atomCas o d =>
      if me.atomVal == l.reg then
        setMem { me with atomVal := min 3 (l.reg + 1) }
        match me.mode with
        | .jank => push (notifyJ d)
        | .clojure => push [.callWatches d]
      else
        -- atom.cpp: while(true) { ... } retries from the load
        Process.note s!"thread {t}: CAS failed, retry"
        push [.op o d]
    | .atomStore => setMem { me with atomVal := min 3 (me.atomVal + 1) }; next
    | .watchAdd => setMem { me with hasWatch := true }; next
    | .watchRemove => setMem { me with hasWatch := false }; next
    | .validatorSet => setMem { me with hasValidator := true }; next
    | .varStore => setMem { me with varRoot := min 3 (me.varRoot + 1) }; next
    -- lazy_meta::get with a pending source: binding_scope push, eval, pop, clear
    | .metaCheck d =>
      if me.metaPending then
        push (exclusive smTbfs ++ [.eRel smTbfs, .call .metaSrc d] ++ exclusive smTbfs ++ [.eRel smTbfs, .metaClear])
      else next
    | .metaClear => setMem { me with metaPending := false }; next
    -- delay::deref (jank): cached value, else run the body under the mutex
    | .delayCheck d => if me.delayVal then next else push (ifBody me .delayBody d ++ [.delaySet])
    | .delaySet => setMem { me with delayVal := true, delayFn := false }; next
    -- Delay.deref (Clojure): `if(lock != null) realize()`; realize: lock, run while fn set, clear
    -- fn and lock
    | .cljDelay d =>
      if me.delayFn then push [.rAcq rDelay, .cljDelayInner d, .rRel rDelay] else next
    | .cljDelayInner d =>
      if me.delayFn then push [.call .delayBody d, .delaySet] else next
    -- future
    | .join =>
      if me.fThread == some t && me.mode == .jank then
        -- std::thread::join on itself throws resource_deadlock_would_occur; the body unwinds
        -- to the future's catch(std::exception const &) (core.cpp 1137-1142)
        Process.note s!"thread {t}: joins itself: std::system_error, the body unwinds"
        let (rels, tail) := unwindTo rest
        go { l with instrs := rels ++ tail }
      else if me.fJoined then next
      else if me.fExited then setMem { me with fJoined := true }; Process.note s!"thread {t}: joined the future's thread"; next
      else pure .blocked
    | .cancelCheck =>
      if me.fStatus == 0 then push ([.eAcq smFThread, .eAcq2 smFThread, .cancelSignal, .eRel smFThread]) else next
    | .cancelSignal =>
      -- jank: pthread_cancel; Clojure: FutureTask.cancel(true) makes the task CANCELLED at once
      if me.fStatus == 0 then
        setMem { me with fCancelReq := true, fStatus := if me.mode == .clojure then 2 else me.fStatus }
      Process.note s!"thread {t}: cancel signalled"
      next
    | .cancelledCheck =>
      if me.fStatus != 0 then push [.uRel smFState]
      else push ([.eAcq smFThread, .eAcq2 smFThread, .tryJoin, .eRel smFThread, .afterTryJoin])
    | .tryJoin =>
      -- pthread_tryjoin_np: EBUSY while the thread runs (ESRCH/EINVAL once joined): return false;
      -- 0 when it has exited: joined, then moveFromUpgradeToWrite and record (core.cpp 1210-1235)
      if me.fExited && !me.fJoined then
        setMem { me with fJoined := true }
        go { l with instrs := rest, reg := 1 }
      else go { l with instrs := rest, reg := 0 }
    | .afterTryJoin =>
      if l.reg == 1 then push [.upg smFState, .upg2 smFState, .statusSet, .eRel smFState]
      else push [.uRel smFState]
    | .statusSet => next
    | .catchMark => next
    | .cljMeta d => if me.metaPending then push [.call .metaSrc d, .metaClear] else next
    | .fCancelled => setMem { me with fStatus := 2 }; next
    | .fDone => setMem { me with fStatus := if me.fStatus == 0 then 1 else me.fStatus }; Process.note s!"thread {t}: future done"; next
    | .fExit => setMem { me with fExited := true }; Process.note s!"thread {t}: future thread exits"; next
    | .fWait => if me.fStatus != 0 then next else pure .blocked
    -- promise
    | .promiseSet =>
      setMem { me with pReady := true, cvSleepers := [] }
      Process.note s!"thread {t}: delivered"
      next
    | .promiseWait =>
      if me.pReady then next
      else match me.mode with
        | .clojure => pure .blocked
        | .jank => push ([.cvRegister, .eRel smPState, .cvSleep] ++ exclusive smPState ++ [.promiseWait])
    | .cvRegister => setMem { me with cvSleepers := me.cvSleepers ++ [t] }; next
    | .cvSleep => if me.cvSleepers.contains t then pure .blocked else next
    | .sleepPoint =>
      -- a cancellation point of the future's thread: a requested cancel unwinds it
      if me.fThread == some t && me.fCancelReq then
        match me.mode with
        | .jank =>
          -- forced unwind: catch(abi::__forced_unwind) takes state.wlock, marks cancelled,
          -- rethrows; the scope_exit unregisters the future (core.cpp 1145-1150, 1114-1121)
          Process.note s!"thread {t}: cancelled at a cancellation point"
          let (rels, _) := unwindTo rest
          go { l with instrs := rels ++ exclusive smFState ++ [.fCancelled, .eRel smFState] ++ exclusive smFutures ++ [.eRel smFutures, .fExit] }
        | .clojure =>
          let (rels, _) := unwindTo rest
          go { l with instrs := rels ++ [.fExit] }
      else next

def prog : Program Mem Loc := { step := step }

/-! ## Programs -/

structure Program' where
  threads : List (List JOp)
  bodies : Array (List JOp)
  hasValidator : Bool
  hasWatch : Bool
  metaPending : Bool
  usesFuture : Bool
  depth : Nat
  deriving Repr, Inhabited

def usesFutureOp (o : JOp) : Bool :=
  match o with
  | .derefFuture | .cancelFuture | .cancelledFuture | .realizedFuture => true
  | _ => false

def start (pg : Program') (mode : Mode) (fine : Bool) : Process Mem Loc :=
  let n := pg.threads.length
  let tops : List (Option Loc) := pg.threads.map fun ops => some { instrs := ops.map fun o => I.op o pg.depth }
  let fut : List (Option Loc) := if pg.usesFuture then [some { instrs := futureThread mode pg.depth }] else []
  { memory := { mode, fine, bodies := pg.bodies, hasValidator := pg.hasValidator, hasWatch := pg.hasWatch,
                metaPending := pg.metaPending, fThread := if pg.usesFuture then some n else none,
                fExited := !pg.usesFuture, fStatus := if pg.usesFuture then 0 else 1,
                sm := Array.replicate numSM {}, fm := Folly.FMem.init numSM (n + 1) 2,
                rl := Array.replicate 4 none },
    threads := (tops ++ fut).toArray }

/-- What each blocked thread waits for. -/
def waitsFor (p : Process Mem Loc) (t : Nat) : String :=
  match p.threads[t]! with
  | none => "done"
  | some l => match l.instrs.head? with
    | some (.sAcq m) => s!"{smName m} shared"
    | some (.eAcq m) => s!"{smName m} exclusive (kHasE)"
    | some (.eAcq2 m) => s!"{smName m} exclusive (readers to drain)"
    | some (.upg2 m) => s!"{smName m} upgrade→exclusive (readers to drain)"
    | some (.uAcq m) => s!"{smName m} upgrade"
    | some (.eRel m) | some (.sRel m) | some (.uRel m) | some (.upg m) => s!"{smName m} (fine pc {reprStr l.pc})"
    | some .mAcq => "delay std::mutex"
    | some (.rAcq x) => rName x
    | some .join => "join of the future's thread"
    | some .fWait => "the future to finish"
    | some .promiseWait => "the promise"
    | some .cvSleep => "the promise's condition variable"
    | some i => reprStr i
    | none => "?"

def holds (p : Process Mem Loc) (t : Nat) : List String :=
  let me := p.memory
  let sms := (List.range numSM).filterMap fun m =>
    let c := me.sm[m]!
    if c.s.contains t then some s!"{smName m} shared"
    else if c.e == some t then some s!"{smName m} exclusive"
    else if c.pend == some t then some s!"{smName m} kHasE (draining)"
    else if c.u == some t then some s!"{smName m} upgrade"
    else none
  let mx := if me.stdMutex == some t then ["delay std::mutex"] else []
  let rs := (List.range 4).filterMap fun x => match me.rl[x]! with
    | some (o, _) => if o == t then some (rName x) else none
    | none => none
  sms ++ mx ++ rs

def stuck (p : Process Mem Loc) : String :=
  let ths := (List.range p.threads.size).filterMap fun t =>
    (p.threads[t]!).map fun _ => s!"thread {t} holds [{String.intercalate ", " (holds p t)}] and waits for {waitsFor p t}"
  String.intercalate "; " ths

/-- What keeps thread `t` waiting: the conflicting holds (any thread), the join/cv condition. -/
def blockers (p : Process Mem Loc) (t : Nat) : List String :=
  let me := p.memory
  match p.threads[t]! with
  | none => []
  | some l =>
    let smHolds (m : Nat) (excl : Bool) : List String :=
      let c := me.sm[m]!
      (if c.e.isSome then [s!"{smName m} exclusive"] else []) ++
      (if c.pend.isSome then [s!"{smName m} kHasE"] else []) ++
      (if excl && c.u.isSome then [s!"{smName m} upgrade"] else []) ++
      (if excl && !c.s.isEmpty then [s!"{smName m} shared"] else [])
    match l.instrs.head? with
    | some (.sAcq m) => smHolds m false
    | some (.eAcq m) | some (.uAcq m) => smHolds m true
    | some (.eAcq2 m) | some (.upg2 m) => if me.sm[m]!.s.isEmpty then [] else [s!"{smName m} shared"]
    | some .mAcq => ["delay std::mutex held"]
    | some (.rAcq x) => [s!"{rName x} held"]
    | some .join => ["the future's thread still running"]
    | some .fWait => ["the future not done"]
    | some .cvSleep | some .promiseWait => ["no deliver"]
    | _ => []

/-- A deadlock's class: per blocked thread, what it waits for and what blocks it (thread ids and
unrelated holds dropped), sorted and deduplicated. -/
def deadlockClass (p : Process Mem Loc) : String :=
  let ths := (List.range p.threads.size).filterMap fun t =>
    (p.threads[t]!).map fun _ => s!"{waitsFor p t} ⟂ {String.intercalate "+" (blockers p t)}"
  String.intercalate " | " (ths.mergeSort (· ≤ ·)).eraseDups

/-! ## The program generator (a decision tree: `exhaust` enumerates it) -/

structure Gen where
  bodies : Array (Option (List JOp)) := Array.replicate 7 none
  decisions : Decisions := {}
  deriving Inhabited

instance : Chaotic Gen where
  decisions g := g.decisions
  setDecisions g d := { g with decisions := d }

abbrev GM := EStateM Stop Gen

def slotsOf (o : JOp) : List Slot :=
  match o with
  | .swap | .reset => [.validator, .watch]
  | .setValidator => [.validator]
  | .alterVarRoot => [.alterFn]
  | .metaRead => [.metaSrc]
  | .derefDelay => [.delayBody]
  | .derefFuture | .cancelFuture | .cancelledFuture | .realizedFuture => [.futureBody]
  | .requireMod => [.moduleBody]
  | .addWatch => [.watch]
  | _ => []

/-- Choose a body for every slot `o` uses (lazily, once), bodies of `len` ops at most,
recursively to `depth`. Slot body 0 = empty (none for validator/watch/meta: not set). -/
partial def chooseSlots (alpha : List JOp) (len depth : Nat) (o : JOp) : GM Unit := do
  for s in slotsOf o do
    let g ← get
    if (g.bodies[s.idx]!).isNone then
      -- the body: length then each op
      let n ← decide (σ := Gen) s!"prog.{s.name}.len" (len + 1)
      let mut ops : List JOp := []
      for _ in [0:n] do
        let k ← decide (σ := Gen) s!"prog.{s.name}.op" alpha.length
        ops := ops ++ [alpha.getD k .sleep]
      modify fun g => { g with bodies := g.bodies.set! s.idx (some ops) }
      if depth > 0 then
        for o' in ops do chooseSlots alpha len (depth - 1) o'

/-- A program: `threads` top-level threads of 1..`ops` operations each, callback bodies of at
most `len` operations, nested to `depth`. -/
def genProgram (alpha : List JOp) (threads ops len depth : Nat) : GM Program' := do
  let nt ← decide (σ := Gen) "prog.threads" threads
  let mut ths : List (List JOp) := []
  for _ in [0:nt + 1] do
    let no ← decide (σ := Gen) "prog.ops" ops
    let mut th : List JOp := []
    for _ in [0:no + 1] do
      let k ← decide (σ := Gen) "prog.op" alpha.length
      let o := alpha.getD k .sleep
      th := th ++ [o]
      chooseSlots alpha len depth o
    ths := ths ++ [th]
  let g ← get
  let body (s : Slot) := (g.bodies[s.idx]!).getD []
  let set (s : Slot) := match g.bodies[s.idx]! with | some (_ :: _) => true | _ => false
  let all := ths.flatten ++ (g.bodies.toList.filterMap id).flatten
  return { threads := ths,
           bodies := #[body .validator, body .watch, body .alterFn, body .metaSrc, body .delayBody, body .futureBody, body .moduleBody],
           hasValidator := set .validator, hasWatch := set .watch, metaPending := set .metaSrc,
           usesFuture := all.any usesFutureOp, depth := depth + 1 }

def Program'.describe (pg : Program') : String :=
  let slots : List Slot := [.validator, .watch, .alterFn, .metaSrc, .delayBody, .futureBody, .moduleBody]
  let bs := slots.filterMap fun s =>
    let b := pg.bodies[s.idx]!
    if b.isEmpty then none else some s!"{s.name} = (fn [..] {String.intercalate " " (b.map (·.clj))})"
  let ths := (List.range pg.threads.length).map fun i =>
    s!"thread {i}: {String.intercalate " " ((pg.threads.getD i []).map (·.clj))}"
  String.intercalate "; " (bs ++ ths)

/-- Run one generated program in both modes: a violation when jank can deadlock and Clojure
cannot. The class is jank's deadlock class. -/
def judge (pg : Program') (fine : Bool) (maxStates : Nat) : Option (String × String) :=
  let j := stateSearch prog (start pg .jank fine) (onDeadlock := fun p => some (deadlockClass p)) (maxStates := maxStates)
  match j.violation with
  | some (_, "deadlock", cls) =>
    let c := stateSearch prog (start pg .clojure false) (onDeadlock := fun p => some (deadlockClass p)) (maxStates := maxStates)
    match c.violation with
    | some (_, "deadlock", _) => none
    | _ => if c.complete then some (cls, pg.describe) else some ("(Clojure search stopped) " ++ cls, pg.describe)
  | some _ => none
  | none => if j.complete then none else some ("(search stopped)", pg.describe)

def runGen (alpha : List JOp) (threads ops len depth maxStates : Nat) (exclude : List String) (source : Source) : Ended :=
  let g : Gen := { decisions := { source, limit := 100000 } }
  match (genProgram alpha threads ops len depth).run g with
  | .ok pg g' =>
    match judge pg false maxStates with
    | some (cls, d) =>
      if exclude.any (fun e => (cls.splitOn e).length > 1) then { taken := g'.decisions.taken, violation := none }
      else { taken := g'.decisions.taken, violation := some (cls, d) }
    | none => { taken := g'.decisions.taken, violation := none }
  | .error _ g' => { taken := g'.decisions.taken, violation := none }

end Jank.R3.Runtime.Locks

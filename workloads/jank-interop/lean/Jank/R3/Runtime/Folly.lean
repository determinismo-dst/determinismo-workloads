import Determinismo
import Jank.R3.Runtime.Common

/-!
# folly::SharedMutex, replicated (deps/folly e54ca53d, folly/SharedMutex.h)

jank's `folly::Synchronized<T>` default mutex is `folly::SharedMutex` =
`SharedMutexWritePriority` = `SharedMutexImpl<false>` (SharedMutex.h 1419-1421), with
`SharedMutexPolicyDefault` (no thread-id tracking, TSAN annotations compiled out). This file
replicates that instantiation one atomic operation per step:

- the 32-bit `state_` word with `kHasS` (count in bits 11..31, `kIncrHasS = 1 << 11`),
  `kMayDefer`, `kPrevDefer`, `kHasE`, `kBegunE`, `kHasU`, and the waiter bits `kWaitingNotS`,
  `kWaitingESingle`/`kWaitingEMultiple`, `kWaitingU`, `kWaitingS` (857-938);
- the static `deferredReaders[]` slots shared by every SharedMutex of the process (1027-1030),
  `tls_lastDeferredReaderSlot` per thread (1012-1017), `AccessSpreader::current(n)` as a decision
  (`cpu.slot`: the CPU the thread runs on), `kDeferredSearchDistance = 2` (984);
- `lock_shared(Token&)` = `lockSharedImpl` fast path (1352-1363) and slow path (1482-1604), the
  deferred mode it enters at the second concurrent reader (`kNumSharedToStartDeferring = 2`);
- `unlock_shared(Token&)` (566-588), `tryUnlockSharedDeferred` (1388), `unlockSharedInline`
  (1394-1405);
- `lock()` = `lockExclusiveImpl(kHasSolo)` (434-439, 1034-1110) with `applyDeferredReaders`
  (1261-1337), `unlock()` (468-477);
- `lock_upgrade()` = `lockUpgradeImpl` (1407-1416), `unlock_upgrade()` (674-680),
  `unlock_upgrade_and_lock()` = `lockExclusiveImpl(0)` (682-688);
- `waitForZeroBits` → `futexWaitForZeroBits` (1112-1198) with `futexWait(&state_, expected,
  waitMask)` (sleeps only if `state_ == expected`, atomically) and `wakeRegisteredWaiters`
  (1203-1239) with `futexWake(&state_, n, wakeMask)` (wakes up to n sleepers whose wait mask
  intersects; which one for n = 1 is a decision, `futex.wake`).

Simplifications (recorded as assumptions RTA1-RTA3 in the report):
- the spin and `sched_yield` phases of `waitForZeroBits` (`kMaxSpinCycles`, `yieldWaitForZeroBits`)
  are loads that only delay; they are folded into the futex loop, whose first action is the same
  load;
- the spin phase of `applyDeferredReaders` (wait for each deferred reader to leave, then inline it
  after `kMaxSpinCycles`) is modeled as its forced path: each slot loaded, the slots holding this
  mutex moved inline by CAS;
- `getMaxDeferredReaders()` is a small world parameter (`maxSlots`, 2 or 4), not 2 × cores.

The Synchronized shared lock is `std::shared_lock<SharedMutex>`, which folly specializes to the
tokenful `lock_shared(token)`/`unlock_shared(token)` (SharedMutex.h 1618-1749): tokenful slot
values. The token-less forms are not used by jank.

Beside it, `CSM` is the coarse lock the jank-level searches use: S holders, the writer that has
set `kHasE` and drains (`pend`), the exclusive holder, the upgrade holder. `Run/R3/Runtime` checks,
by state search over every small program, that the fine replica deadlocks exactly when `CSM` does
and that every completed acquisition is one `CSM` allows.
-/

namespace Jank.R3.Runtime.Folly

open Determinismo

abbrev St := UInt32

def kIncrHasS : St := 2048  -- 1 << 11
def kHasS : St := ~~~(kIncrHasS - 1)
def kMayDefer : St := 512  -- 1 << 9
def kPrevDefer : St := 256  -- 1 << 8
def kHasE : St := 128  -- 1 << 7
def kBegunE : St := 64  -- 1 << 6
def kHasU : St := 32  -- 1 << 5
def kHasSolo : St := kHasE ||| kBegunE ||| kHasU
def kWaitingNotS : St := 16  -- 1 << 4
def kWaitingESingle : St := 4  -- 1 << 2
def kWaitingEMultiple : St := 8  -- 1 << 3
def kWaitingE : St := kWaitingESingle ||| kWaitingEMultiple
def kWaitingU : St := 2  -- 1 << 1
def kWaitingS : St := 1
def kNumSharedToStartDeferring : St := 2
def kDeferredSearchDistance : Nat := 2

/-- Slot values: 0 empty; a tokenful lock of mutex m: `2(m+1)` (the pointer); token-less adds
`kTokenless = 1`. -/
def tokenful (m : Nat) : Nat := 2 * (m + 1)
def slotIsThis (m v : Nat) : Bool := v != 0 && v / 2 == m + 1

/-- What `lock_shared(Token&)` leaves in the token. -/
inductive Token where
  | inline
  | deferred (slot : Nat)
  deriving BEq, Hashable, Repr, Inhabited

/-- Where a `waitForZeroBits`, an `unlockSharedInline` or a wake returns to. -/
inductive Ret where
  /-- lockSharedImpl after the kHasE wait: continue at 1493 with the state read. -/
  | lsSlow2
  /-- lockExclusiveImpl after the precondition wait (1050-1053). -/
  | leSlow2 (mask : St)
  /-- lockUpgradeImpl after the kHasSolo wait (1414). -/
  | luCas
  /-- back to lockSharedImpl's loop (1487) with this state, after releasing a slot. -/
  | lsLoop (st : St)
  | doneS (tok : Token)
  | doneE
  | doneU
  | doneUnlock
  deriving BEq, Hashable, Repr, Inhabited

/-- The program counter inside one SharedMutex operation; each constructor performs one atomic
operation (load, CAS, fetch-op, futex call) when it steps. -/
inductive Pc where
  | lsFastLoad
  | lsFastCas (st : St)
  | lsSlow2 (st : St)
  | lsSearch (st : St) (best i : Nat)
  | lsInlineCas (st : St)
  | lsMayDefer (st : St) (slot : Nat)
  | lsTakeSlot (slot : Nat)
  | lsRecheck (got : Bool) (slot : Nat)
  | lsRelease (st : St) (slot : Nat)
  | usDeferred (slot : Nat)
  | usi (ret : Ret)
  | fwLoad (goal mask : St) (ret : Ret)
  | fwCas (goal mask st after : St) (ret : Ret)
  | fwWait (goal mask expected : St) (ret : Ret)
  | fwSleep (goal mask : St) (ret : Ret)
  | wake (st mask : St) (ret : Ret)
  | wakeAnd (st mask : St) (ret : Ret)
  | wakeAll (mask : St) (ret : Ret)
  | leFastLoad (mask : St)
  | leFastCas (mask st : St)
  | leSlow2 (mask st : St)
  | leApply (st : St) (slot moved : Nat)
  | leApplyCas (st : St) (slot v moved : Nat)
  | leAddMoved (moved : Nat)
  | unlockE
  | luCas (st : St)
  | unlockU
  deriving BEq, Hashable, Repr, Inhabited

/-- The futexes and slots: everything the SharedMutexes of a process share. -/
structure FMem where
  /-- `state_` of each mutex. -/
  st : Array St
  /-- `deferredReaders[slot * kDeferredSeparationFactor]`, slot < getMaxDeferredReaders(). -/
  slots : Array Nat
  /-- futex sleepers in the order they slept: (thread, mutex, waitMask). -/
  waiters : List (Nat × Nat × St) := []
  /-- `tls_lastDeferredReaderSlot()` of each thread. -/
  tls : Array Nat
  deriving BEq, Hashable, Repr, Inhabited

def FMem.init (mutexes threads maxSlots : Nat) : FMem :=
  { st := Array.replicate mutexes 0, slots := Array.replicate maxSlots 0,
    tls := Array.replicate threads 0 }

/-- A step's outcome inside an operation. -/
inductive Res where
  | next (pc : Pc)
  | blocked
  | done (r : Ret)
  deriving BEq, Repr, Inhabited

/-! ## Where control goes without an atomic operation -/

/-- lockSharedImpl loop top (1487-1491): wait for kHasE to clear, else continue at 1493. -/
def lsLoop (st : St) : Pc :=
  if st &&& kHasE != 0 then .fwLoad kHasE kWaitingS .lsSlow2 else .lsSlow2 st

/-- lockExclusiveImpl loop top (1049-1054). -/
def leLoop (mask st : St) : Pc :=
  if st &&& mask != 0 then .fwLoad mask kWaitingE (.leSlow2 mask) else .leSlow2 mask st

/-- The drain (1084-1107): wait for kHasS to reach 0. -/
def leDrain (st : St) : Res :=
  if st &&& kHasS != 0 then .next (.fwLoad kHasS kWaitingNotS .doneE) else .done .doneE

def afterApply (st : St) (slot moved maxSlots : Nat) : Res :=
  if slot < maxSlots then .next (.leApply st slot moved)
  else if moved > 0 then .next (.leAddMoved moved)
  else leDrain st

/-- Return from waitForZeroBits with the state read. -/
def afterWait (ret : Ret) (st : St) : Res :=
  match ret with
  | .lsSlow2 => .next (.lsSlow2 st)
  | .leSlow2 mask => .next (.leSlow2 mask st)
  | .luCas => .next (.luCas st)
  | .lsLoop st' => .next (lsLoop st')
  | r => .done r

/-- Return from an unlockSharedInline or a wake. -/
def afterWake (ret : Ret) : Res :=
  match ret with
  | .lsLoop st => .next (lsLoop st)
  | r => .done r

/-- `wakeRegisteredWaiters(state, wakeMask)` (1203-1207). -/
def wakeIf (st mask : St) (ret : Ret) : Res :=
  if st &&& mask != 0 then .next (.wake st mask ret) else afterWake ret

/-- The (state & goal) == 0 test and the wait bits to set (1170-1185). -/
def waitAfter (st mask : St) : St :=
  if mask == kWaitingE then
    if st &&& kWaitingESingle != 0 then st ||| kWaitingEMultiple else st ||| kWaitingESingle
  else st ||| mask

/-! ## The atomic steps -/

section
variable {σ : Type} [Chaotic σ]

/-- `futexWake(&state_, n, wakeMask)`: wake up to `n` sleepers of mutex `m` whose wait mask meets
`wakeMask` (all for n = 0). For n = 1 which one is a decision. Returns the memory and the count. -/
def futexWake (mem : FMem) (m : Nat) (all : Bool) (mask : St) : EStateM Stop σ (FMem × Nat) := do
  let eligible := mem.waiters.filter fun (_, mm, wm) => mm == m && wm &&& mask != 0
  if eligible.isEmpty then return (mem, 0)
  if all then
    return ({ mem with waiters := mem.waiters.filter fun w => !eligible.contains w }, eligible.length)
  else
    let i ← decide (σ := σ) "futex.wake" eligible.length
    let w := eligible.getD i eligible.head!
    return ({ mem with waiters := mem.waiters.erase w }, 1)

/-- One atomic step of thread `t` running operation pc on mutex `m`. -/
def stepPc (t m maxSlots : Nat) (mem : FMem) (pc : Pc) : EStateM Stop σ (FMem × Res) := do
  let s := mem.st[m]!
  let setSt (v : St) : FMem := { mem with st := mem.st.set! m v }
  match pc with
  -- lock_shared fast path (1354-1361)
  | .lsFastLoad =>
    if s &&& (kHasS ||| kMayDefer ||| kHasE) == 0 then return (mem, .next (.lsFastCas s))
    else return (mem, .next (lsLoop s))
  | .lsFastCas st =>
    if s == st then return (setSt (st + kIncrHasS), .done (.doneS .inline))
    else return (mem, .next (lsLoop s))
  -- 1493-1535
  | .lsSlow2 st =>
    let slot := mem.tls[t]!
    let canAlreadyDefer := st &&& kMayDefer != 0
    let aboveDeferThreshold := (st &&& kHasS) ≥ (kNumSharedToStartDeferring - 1) * kIncrHasS
    if canAlreadyDefer || aboveDeferThreshold then
      let v := mem.slots[slot]!
      if v != 0 then
        let best ← decide (σ := σ) "cpu.slot" maxSlots
        return (mem, .next (.lsSearch st best 0))
      else return (mem, .next (.lsMayDefer st slot))
    else
      -- not deferring: the inline CAS (1526)
      if s == st then return (setSt (st + kIncrHasS), .done (.doneS .inline))
      else return (mem, .next (lsLoop s))
  | .lsSearch st best i =>
    let slot := best ^^^ i
    let v := mem.slots[slot]!
    if v == 0 then
      return ({ mem with tls := mem.tls.set! t slot }, .next (.lsMayDefer st slot))
    else if i + 1 < kDeferredSearchDistance then return (mem, .next (.lsSearch st best (i + 1)))
    else return (mem, .next (.lsInlineCas st))
  | .lsInlineCas st =>
    if s == st then return (setSt (st + kIncrHasS), .done (.doneS .inline))
    else return (mem, .next (lsLoop s))
  -- 1538-1547
  | .lsMayDefer st slot =>
    if st &&& kMayDefer == 0 then
      if s == st then return (setSt (st ||| kMayDefer), .next (.lsTakeSlot slot))
      else if s &&& (kHasE ||| kMayDefer) != kMayDefer then return (mem, .next (lsLoop s))
      else return (mem, .next (.lsTakeSlot slot))
    else
      -- the slot CAS (1550) right away
      let got := mem.slots[slot]! == 0
      let mem' := if got then { mem with slots := mem.slots.set! slot (tokenful m) } else mem
      return (mem', .next (.lsRecheck got slot))
  | .lsTakeSlot slot =>
    let got := mem.slots[slot]! == 0
    let mem' := if got then { mem with slots := mem.slots.set! slot (tokenful m) } else mem
    return (mem', .next (.lsRecheck got slot))
  -- 1561-1597
  | .lsRecheck got slot =>
    if !got then return (mem, .next (lsLoop s))
    else if s &&& kMayDefer != 0 then return (mem, .done (.doneS (.deferred slot)))
    else return (mem, .next (.lsRelease s slot))
  | .lsRelease st slot =>
    if mem.slots[slot]! == tokenful m then
      return ({ mem with slots := mem.slots.set! slot 0 }, .next (lsLoop st))
    else return (mem, .next (.usi (.lsLoop st)))
  -- unlock_shared(Token&) deferred: tryUnlockSharedDeferred (1388-1392)
  | .usDeferred slot =>
    if mem.slots[slot]! == tokenful m then
      return ({ mem with slots := mem.slots.set! slot 0 }, .done .doneUnlock)
    else return (mem, .next (.usi .doneUnlock))
  -- unlockSharedInline (1394-1405)
  | .usi ret =>
    let v := s - kIncrHasS
    let mem' := setSt v
    if v &&& kHasS == 0 then return (mem', wakeIf v kWaitingNotS ret)
    else return (mem', afterWake ret)
  -- futexWaitForZeroBits (1170-1197)
  | .fwLoad goal mask ret =>
    if s &&& goal == 0 then return (mem, afterWait ret s)
    else
      let after := waitAfter s mask
      if after != s then return (mem, .next (.fwCas goal mask s after ret))
      else return (mem, .next (.fwWait goal mask after ret))
  | .fwCas goal mask st after ret =>
    if s == st then return (setSt after, .next (.fwWait goal mask after ret))
    else return (mem, .next (.fwLoad goal mask ret))
  | .fwWait goal mask expected ret =>
    if s != expected then return (mem, .next (.fwLoad goal mask ret))
    else return ({ mem with waiters := mem.waiters ++ [(t, m, mask)] }, .next (.fwSleep goal mask ret))
  | .fwSleep goal mask ret =>
    if mem.waiters.any (·.1 == t) then return (mem, .blocked)
    else return (mem, .next (.fwLoad goal mask ret))
  -- wakeRegisteredWaitersImpl (1225-1238)
  | .wake st mask ret =>
    if mask &&& kWaitingE == kWaitingE && st &&& mask == kWaitingE then
      let (mem', n) ← futexWake (σ := σ) mem m false kWaitingE
      if n > 0 then return (mem', afterWake ret)
      else return (mem', .next (.wakeAnd st mask ret))
    else
      -- the fetch_and right away
      let prev := s
      let mem' := setSt (s &&& ~~~mask)
      if prev &&& mask != 0 then return (mem', .next (.wakeAll mask ret))
      else return (mem', afterWake ret)
  | .wakeAnd _ mask ret =>
    let prev := s
    let mem' := setSt (s &&& ~~~mask)
    if prev &&& mask != 0 then return (mem', .next (.wakeAll mask ret))
    else return (mem', afterWake ret)
  | .wakeAll mask ret =>
    let (mem', _) ← futexWake (σ := σ) mem m true mask
    return (mem', afterWake ret)
  -- lockExclusiveImpl (1036-1043)
  | .leFastLoad mask =>
    if s &&& (mask ||| kMayDefer ||| kHasS) == 0 then return (mem, .next (.leFastCas mask s))
    else return (mem, .next (leLoop mask s))
  | .leFastCas mask st =>
    if s == st then return (setSt ((st ||| kHasE) &&& ~~~kHasU), .done .doneE)
    else return (mem, .next (leLoop mask s))
  -- 1056-1083 (write priority: !kReaderPriority)
  | .leSlow2 mask st =>
    let after0 : St := if st &&& kMayDefer == 0 then 0 else kPrevDefer
    let after := after0 ||| ((st ||| kHasE) &&& ~~~(kHasU ||| kMayDefer))
    if s == st then
      let mem' := setSt after
      if st &&& kMayDefer != 0 then return (mem', afterApply after 0 0 maxSlots)
      else return (mem', leDrain after)
    else return (mem, .next (leLoop mask s))
  -- applyDeferredReaders, forced path (1318-1330)
  | .leApply st slot moved =>
    let v := mem.slots[slot]!
    if slotIsThis m v then return (mem, .next (.leApplyCas st slot v moved))
    else return (mem, afterApply st (slot + 1) moved maxSlots)
  | .leApplyCas st slot v moved =>
    if mem.slots[slot]! == v then
      return ({ mem with slots := mem.slots.set! slot 0 }, afterApply st (slot + 1) (moved + 1) maxSlots)
    else return (mem, afterApply st (slot + 1) moved maxSlots)
  | .leAddMoved moved =>
    let v := s + (UInt32.ofNat moved) * kIncrHasS
    return (setSt v, leDrain v)
  -- unlock (474-476)
  | .unlockE =>
    let v := s &&& ~~~(kWaitingNotS ||| kPrevDefer ||| kHasE)
    return (setSt v, wakeIf v (kWaitingE ||| kWaitingU ||| kWaitingS) .doneUnlock)
  -- lockUpgradeImpl CAS (1414)
  | .luCas st =>
    if s == st then return (setSt (st ||| kHasU), .done .doneU)
    else return (mem, .next (.fwLoad kHasSolo kWaitingU .luCas))
  -- unlock_upgrade (677-679)
  | .unlockU =>
    let v := s - kHasU
    return (setSt v, wakeIf v (kWaitingE ||| kWaitingU) .doneUnlock)

end

/-- The operations of the SharedMutex API that jank reaches. -/
inductive Op where
  | lockShared
  | unlockShared (tok : Token)
  | lock
  | unlock
  | lockUpgrade
  | unlockUpgrade
  /-- `unlock_upgrade_and_lock()` (LockedPtr::moveFromUpgradeToWrite). -/
  | upgradeToLock
  deriving BEq, Hashable, Repr, Inhabited

def Op.start : Op → Pc
  | .lockShared => .lsFastLoad
  | .unlockShared .inline => .usi .doneUnlock
  | .unlockShared (.deferred s) => .usDeferred s
  | .lock => .leFastLoad kHasSolo
  | .unlock => .unlockE
  | .lockUpgrade => .fwLoad kHasSolo kWaitingU .luCas
  | .unlockUpgrade => .unlockU
  | .upgradeToLock => .leFastLoad 0

/-! ## The coarse lock (what the fine replica refines) -/

/-- Coarse SharedMutex state: shared holders (with multiplicity), the writer that set kHasE and
drains readers, the exclusive holder, the upgrade holder. -/
structure CSM where
  s : List Nat := []
  pend : Option Nat := none
  e : Option Nat := none
  u : Option Nat := none
  deriving BEq, Hashable, Repr, Inhabited

namespace CSM
/-- lock_shared: waits while kHasE is set (a writer holds it or drains). -/
def lockShared (l : CSM) (t : Nat) : Option CSM :=
  if l.e.isSome || l.pend.isSome then none else some { l with s := t :: l.s }
def unlockShared (l : CSM) (t : Nat) : CSM := { l with s := l.s.erase t }
/-- lock(), first half: waits while any solo bit (E, U) is set, then sets kHasE. -/
def lockSet (l : CSM) (t : Nat) : Option CSM :=
  if l.e.isSome || l.pend.isSome || l.u.isSome then none else some { l with pend := some t }
/-- lock(), second half: waits for the readers to drain. -/
def lockDrain (l : CSM) (t : Nat) : Option CSM :=
  if l.pend == some t && l.s.isEmpty then some { l with pend := none, e := some t } else none
def unlock (l : CSM) : CSM := { l with e := none }
def lockUpgrade (l : CSM) (t : Nat) : Option CSM :=
  if l.e.isSome || l.pend.isSome || l.u.isSome then none else some { l with u := some t }
def unlockUpgrade (l : CSM) : CSM := { l with u := none }
/-- unlock_upgrade_and_lock: sets kHasE (clearing kHasU) at once, then drains. -/
def upgradeSet (l : CSM) (t : Nat) : CSM := { l with u := none, pend := some t }
end CSM

/-! ## Standalone programs: threads running SharedMutex operations

Each thread runs a list of `(mutex, operation)`; a shared unlock uses the token its lock got. The
memory also tracks who holds what, and in coarse mode the coarse lock is the whole state. -/

inductive Act where
  | lockS (m : Nat) | unlockS (m : Nat)
  | lockE (m : Nat) | unlockE (m : Nat)
  | lockU (m : Nat) | unlockU (m : Nat)
  | upgrade (m : Nat)
  deriving BEq, Hashable, Repr, Inhabited

def Act.mutex : Act → Nat
  | .lockS m | .unlockS m | .lockE m | .unlockE m | .lockU m | .unlockU m | .upgrade m => m

instance : Inhabited Determinismo.RwLock := ⟨{}⟩

instance : Hashable Determinismo.RwLock where
  hash l := mixHash (hash l.readers) (mixHash (hash l.writer) (mixHash (hash l.waiting) (hash l.writerPriority)))

structure Mem where
  f : FMem
  /-- coarse locks, one per mutex (coarse mode), and the holders (both modes). -/
  c : Array CSM
  maxSlots : Nat
  coarse : Bool
  /-- `Determinismo.RwLock` (writer priority; round 1's `Jank.Sync.SharedMutex` is the same
  lock): a writer announces itself, and every announced writer keeps new readers out. -/
  lib : Array Determinismo.RwLock := #[]
  useLib : Bool := false
  deriving BEq, Hashable, Inhabited

structure Loc where
  acts : List Act
  pc : Option Pc := none
  /-- tokens held, per mutex (a stack for nested shared holds). -/
  toks : List (Nat × Token) := []
  /-- coarse lock(): the kHasE half done. -/
  set : Bool := false
  deriving BEq, Hashable, Repr, Inhabited

abbrev PM := ProcessM Mem Loc

def holderCheck (c : CSM) (what : String) : Option String :=
  if c.e.isSome && !c.s.isEmpty then some s!"{what}: exclusive held while shared held {c.s}"
  else if c.e.isSome && c.u.isSome then some s!"{what}: exclusive and upgrade held"
  else none

/-- Record a completed acquisition in the holder tracking and check the coarse lock allows it. -/
def acquired (t : Nat) (a : Act) (r : Ret) : PM Unit := do
  let mem := (← get).memory
  let m := a.mutex
  let c := mem.c[m]!
  let c' ← match a, r with
    | .lockS _, .doneS _ =>
      if c.e.isSome || c.pend.isSome then
        throw (.violation "refines coarse" s!"thread {t} got mutex {m} shared while a writer holds or drains")
      pure { c with s := t :: c.s }
    | .lockE _, .doneE =>
      if !c.s.isEmpty || c.e.isSome || c.u.isSome then
        throw (.violation "mutual exclusion" s!"thread {t} got mutex {m} exclusive while held {reprStr c}")
      pure { c with e := some t, pend := none }
    | .upgrade _, .doneE =>
      if !c.s.isEmpty || c.e.isSome then
        throw (.violation "mutual exclusion" s!"thread {t} upgraded mutex {m} while held {reprStr c}")
      pure { c with e := some t, pend := none, u := none }
    | .lockU _, .doneU =>
      if c.e.isSome || c.u.isSome || c.pend.isSome then
        throw (.violation "refines coarse" s!"thread {t} got mutex {m} upgrade while held {reprStr c}")
      pure { c with u := some t }
    | .unlockS _, _ => pure (c.unlockShared t)
    | .unlockE _, _ => pure c.unlock
    | .unlockU _, _ => pure c.unlockUpgrade
    | _, _ => pure c
  modify fun p => { p with memory := { mem with c := mem.c.set! m c' } }

/-- Mark the writer that set kHasE (fine: its successful leSlow2/leFastCas CAS). -/
def notePend (t m : Nat) : PM Unit :=
  modify fun p => { p with memory := { p.memory with c := p.memory.c.modify m fun c => { c with pend := some t } } }

def startPc (l : Loc) (a : Act) : Pc :=
  match a with
  | .lockS _ => Op.lockShared.start
  | .unlockS m =>
    let tok := (l.toks.find? (·.1 == m)).map (·.2) |>.getD .inline
    (Op.unlockShared tok).start
  | .lockE _ => Op.lock.start
  | .unlockE _ => Op.unlock.start
  | .lockU _ => Op.lockUpgrade.start
  | .unlockU _ => Op.unlockUpgrade.start
  | .upgrade _ => Op.upgradeToLock.start

def popTok (l : Loc) (m : Nat) : List (Nat × Token) :=
  match l.toks.findIdx? (·.1 == m) with
  | some i => l.toks.eraseIdx i
  | none => l.toks

/-- The library lock's step (S and E only). -/
def libStep (t : Nat) (l : Loc) : PM (StepResult Loc) := do
  match l.acts with
  | [] => pure .done
  | a :: rest =>
    let mem := (← get).memory
    let m := a.mutex
    let c : Determinismo.RwLock := mem.lib[m]!
    let put (c' : Determinismo.RwLock) : PM Unit := modify fun p => { p with memory := { mem with lib := mem.lib.set! m c' } }
    let fin : PM (StepResult Loc) := pure (if rest.isEmpty then .done else .ran { l with acts := rest, set := false })
    match a with
    | .lockS _ => match c.tryLockShared t with
      | some c' => put c'; fin
      | none => pure .blocked
    | .lockE _ =>
      if !l.set then put (c.announce t); pure (.ran { l with set := true })
      else match c.tryLock t with
        | some c' => put c'; fin
        | none => pure .blocked
    | .unlockS _ => put (c.unlockShared t); fin
    | .unlockE _ => put c.unlock; fin
    | _ => fin

/-- Coarse step: one acquisition or release. -/
def coarseStep (t : Nat) (l : Loc) : PM (StepResult Loc) := do
  match l.acts with
  | [] => pure .done
  | a :: rest =>
    let mem := (← get).memory
    let m := a.mutex
    let c := mem.c[m]!
    let put (c' : CSM) : PM Unit := modify fun p => { p with memory := { mem with c := mem.c.set! m c' } }
    let fin : PM (StepResult Loc) := do
      Process.note s!"thread {t}: {reprStr a}"
      pure (if rest.isEmpty then .done else .ran { l with acts := rest, set := false })
    match a with
    | .lockS _ => match c.lockShared t with
      | some c' => put c'; fin
      | none => pure .blocked
    | .lockE _ =>
      if !l.set then
        match c.lockSet t with
        | some c' => put c'; Process.note s!"thread {t}: lock {m} sets kHasE"; pure (.ran { l with set := true })
        | none => pure .blocked
      else match c.lockDrain t with
        | some c' => put c'; fin
        | none => pure .blocked
    | .upgrade _ =>
      if !l.set then put (c.upgradeSet t); pure (.ran { l with set := true })
      else match c.lockDrain t with
        | some c' => put c'; fin
        | none => pure .blocked
    | .lockU _ => match c.lockUpgrade t with
      | some c' => put c'; fin
      | none => pure .blocked
    | .unlockS _ => put (c.unlockShared t); fin
    | .unlockE _ => put c.unlock; fin
    | .unlockU _ => put c.unlockUpgrade; fin

/-- Fine step: one atomic operation of the replica. -/
def fineStep (t : Nat) (l : Loc) : PM (StepResult Loc) := do
  match l.acts with
  | [] => pure .done
  | a :: rest =>
    let mem := (← get).memory
    let m := a.mutex
    let pc := l.pc.getD (startPc l a)
    let (f', r) ← stepPc (σ := Process Mem Loc) t m mem.maxSlots mem.f pc
    modify fun p => { p with memory := { p.memory with f := f' } }
    -- the writer that set kHasE (for the coarse comparison)
    match pc, r with
    | .leSlow2 _ _, .next _ => if f'.st[m]! &&& kHasE != 0 && mem.f.st[m]! != f'.st[m]! then notePend t m
    | .leSlow2 _ _, .done _ => notePend t m
    | _, _ => pure ()
    -- a release takes effect at its atomic operation (the wake after it is not part of the hold)
    let releasing := match a, pc, r with
      | .unlockS _, .usi .doneUnlock, _ => true
      | .unlockS _, .usDeferred _, .done _ => true
      | .unlockE _, .unlockE, _ => true
      | .unlockU _, .unlockU, _ => true
      | _, _, _ => false
    if releasing then acquired t a .doneUnlock
    match r with
    | .blocked => pure .blocked
    | .next pc' =>
      Process.note s!"thread {t}: {reprStr pc} → {reprStr pc'}"
      pure (.ran { l with pc := some pc' })
    | .done ret =>
      Process.note s!"thread {t}: {reprStr a} done ({reprStr ret})"
      if !releasing then acquired t a ret
      let toks := match a, ret with
        | .lockS m, .doneS tok => (m, tok) :: l.toks
        | .unlockS m, _ => popTok l m
        | _, _ => l.toks
      pure (if rest.isEmpty then .done else .ran { acts := rest, pc := none, toks, set := false })

def prog (coarse : Bool) (useLib : Bool := false) : Program Mem Loc :=
  { step := fun t l => if useLib then libStep t l else if coarse then coarseStep t l else fineStep t l }

def start (threads : List (List Act)) (mutexes maxSlots : Nat) (coarse : Bool) (useLib : Bool := false) : Process Mem Loc :=
  { memory := { f := FMem.init mutexes threads.length maxSlots,
                c := Array.replicate mutexes {}, maxSlots, coarse,
                lib := Array.replicate mutexes {}, useLib },
    threads := (threads.map fun acts => some ({ acts } : Loc)).toArray }

/-- The invariant at every state (both modes): exclusive excludes shared and upgrade. -/
def invariant (p : Process Mem Loc) : Option (String × String) := Id.run do
  for i in [0:p.memory.c.size] do
    if let some d := holderCheck p.memory.c[i]! s!"mutex {i}" then return some ("mutual exclusion", d)
  return none

/-- What each blocked thread waits for, for a deadlock report. -/
def stuckDetail (p : Process Mem Loc) : String :=
  let ths := (List.range p.threads.size).filterMap fun i => (p.threads[i]!).map fun l =>
    s!"thread {i} at {reprStr (l.acts.head?)} pc {reprStr l.pc}"
  s!"every live thread blocked: {String.intercalate "; " ths}; coarse {reprStr p.memory.c}; state {reprStr p.memory.f.st}; sleepers {reprStr p.memory.f.waiters}"

/-! ## Program families for the refinement table -/

/-- One thread's bracketed acquisitions of mutex 0: outer kind, optional nested kind. -/
inductive Kind | s | e | u | ue
  deriving BEq, Repr, Inhabited

def Kind.acq (k : Kind) (m : Nat) : List Act :=
  match k with
  | .s => [.lockS m] | .e => [.lockE m] | .u => [.lockU m] | .ue => [.lockU m, .upgrade m]
def Kind.rel (k : Kind) (m : Nat) : List Act :=
  match k with
  | .s => [.unlockS m] | .e => [.unlockE m] | .u => [.unlockU m] | .ue => [.unlockE m]

def bracket (outer : Kind) (inner : Option (Kind × Nat)) : List Act :=
  match inner with
  | none => outer.acq 0 ++ outer.rel 0
  | some (k, m) => outer.acq 0 ++ k.acq m ++ k.rel m ++ outer.rel 0

def kinds : List Kind := [.s, .e, .u, .ue]

/-- Every thread shape: one acquisition of mutex 0, or one with a nested acquisition of mutex 0
or 1. -/
def shapes : List (List Act) :=
  (kinds.map fun k => bracket k none) ++
  (kinds.flatMap fun k => kinds.flatMap fun k2 => [bracket k (some (k2, 0)), bracket k (some (k2, 1))])

end Jank.R3.Runtime.Folly

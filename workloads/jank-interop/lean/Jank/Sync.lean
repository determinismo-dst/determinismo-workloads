import Determinismo

/-!
# Locks for the Threads world (what `Determinismo.Threads` leaves to the program)

`Determinismo.Threads` gives atomic steps, a decision for the next thread, and blocking. The
locks jank's C++ uses are built here as data in the shared memory, each acquisition one step that
either takes the lock or blocks:

- `SharedMutex`: folly's `SharedMutex` = `SharedMutexWritePriority` (folly/SharedMutex.h:
  `using SharedMutex = SharedMutexWritePriority`), the default mutex of `folly::Synchronized`
  (Synchronized.h `template <class T, class Mutex = SharedMutex>`). `rlock()` takes it shared,
  `wlock()` exclusive. Write priority: a shared acquisition waits while a writer waits. It is not
  reentrant: an exclusive acquisition by a thread holding it shared waits for itself.
- `Mutex`: `std::mutex` (non-recursive).

A thread that wants exclusive access first announces itself (`waiting`), then acquires when
there are no holders: the two steps of folly's writer path that matter (a waiting writer blocks
new readers).
-/

namespace Jank.Sync

structure SharedMutex where
  readers : List Nat := []
  writer : Option Nat := none
  waiting : List Nat := []
  deriving Repr, BEq, Inhabited

namespace SharedMutex

/-- `lock_shared` by thread `t`: none if it must wait (a writer holds or waits). -/
def lockShared (m : SharedMutex) (t : Nat) : Option SharedMutex :=
  if m.writer.isNone && m.waiting.isEmpty then some { m with readers := t :: m.readers } else none

def unlockShared (m : SharedMutex) (t : Nat) : SharedMutex :=
  { m with readers := m.readers.erase t }

/-- The writer's announcement (it then blocks new readers). -/
def announce (m : SharedMutex) (t : Nat) : SharedMutex :=
  if m.waiting.contains t then m else { m with waiting := m.waiting ++ [t] }

/-- `lock` by thread `t` once announced: none while anyone holds it. -/
def lock (m : SharedMutex) (t : Nat) : Option SharedMutex :=
  if m.writer.isNone && m.readers.isEmpty then
    some { m with writer := some t, waiting := m.waiting.erase t }
  else none

def unlock (m : SharedMutex) : SharedMutex := { m with writer := none }

end SharedMutex

structure Mutex where
  owner : Option Nat := none
  deriving Repr, BEq, Inhabited

def Mutex.lock (m : Mutex) (t : Nat) : Option Mutex :=
  if m.owner.isNone then some { owner := some t } else none

def Mutex.unlock (_ : Mutex) : Mutex := {}

end Jank.Sync

/-
  Round 3: the pipeline's worker threads under real interleavings,
  transcribed from flecs v4.2.0 src/addons/pipeline/worker.c (the whole
  synchronization protocol: flecs_worker 34-74, flecs_sync_worker 13-31,
  flecs_wait_for_workers 117-135, flecs_wait_for_sync 138-159,
  flecs_signal_workers 162-174) and src/addons/pipeline/pipeline.c 545-675
  (flecs_run_pipeline_ops and the op loop of flecs_run_pipeline).

  The main thread (stage 0) and the worker threads share the world's
  `sync_mutex`, `worker_cond`, `sync_cond`, `workers_waiting` and
  `workers_running`, and the pipeline state (`pq->cur_op`, `pq->cur_i`).
  Each step is atomic at the granularity of a mutex operation or a read or
  write of the shared state.  A condition variable wait releases the mutex
  and joins the waiters in one step (pthread_cond_wait); a signal or
  broadcast removes waiters; a woken thread then reacquires the mutex.

  `ecs_os_cond_wait` is `pthread_cond_wait` (posix_impl.inl 200-208) or
  `SleepConditionVariableCS` (windows_impl.inl 127-132).  Both may return
  without a signal (a spurious wakeup: POSIX pthread_cond_wait, "Spurious
  wakeups ... may occur"; the Windows documentation says the same).  With
  `spurious` > 0 the search may wake a waiting thread without a signal, at
  most that many times per timeline.

  Which thread steps next is determinismo's `thread.next` decision
  (`Determinismo.interleave`), so `exhaust` visits every interleaving within
  the step bound.
-/
import FlecsLean.Search

namespace Flecs.Workers
open Determinismo

/-- An op of the schedule: multi-threaded or not (pipeline.c 263-394). -/
structure POp where
  mt : Bool
  deriving Repr, BEq, Inhabited

/-- Condition variables. -/
def WORKER : Nat := 0
def SYNC : Nat := 1

/-- Program counters.  `wait c ret`: in `cond_wait(c)`, after which the
    thread reacquires the mutex (`reacq ret`) and continues at `ret`. -/
inductive PC
  -- main thread (flecs_workers_progress / flecs_run_pipeline)
  | mWaitWorkers | mUpdate | mOpBegin | mSignal | mRunOwn | mAfterRun
  | mSyncLock | mSyncCheck | mMerge | mMergeEnd
  -- worker thread (flecs_worker)
  | wStart | wStartUnlock | wLoop | wRun | wSyncLock | wSyncUnlock
  -- cond_wait
  | wait (c : Nat) (ret : PC)
  | reacq (ret : PC)
  deriving Repr, BEq, Inhabited

structure Mem where
  stages : Nat
  ops : Array POp
  frames : Nat
  /-- spurious wakeups left -/
  spurious : Nat
  mutex : Option Nat := none
  waiting : Nat := 0
  running : Nat := 0
  condWaiters : Array (List Nat) := #[[], []]
  quit : Bool := false
  /-- `pq->cur_op` (index) and the frame -/
  curOp : Option Nat := none
  frame : Nat := 0
  /-- `ecs_readonly_begin` .. `ecs_readonly_end`: systems may run -/
  readonly : Bool := false
  merging : Bool := false
  /-- system runs this frame: (stage, op) -/
  runs : Array (Nat × Nat) := #[]
  deriving Inhabited

abbrev WM := ProcessM Mem PC

def mem : WM Mem := return (← get).memory
def setMem (m : Mem) : WM Unit := modify fun p => { p with memory := m }
def modMem (f : Mem → Mem) : WM Unit := modify fun p => { p with memory := f p.memory }

/-- `ecs_os_mutex_lock`: `none` when another thread holds it. -/
def tryLock (t : Nat) : WM Bool := do
  let m ← mem
  match m.mutex with
  | some _ => return false
  | none => setMem { m with mutex := some t }; return true

def unlock : WM Unit := modMem fun m => { m with mutex := none }

/-- `cond_wait(c, mutex)`, first half: release the mutex and wait. -/
def condWait (t c : Nat) (ret : PC) : WM (StepResult PC) := do
  modMem fun m => { m with mutex := none, condWaiters := m.condWaiters.modify c (fun l => l ++ [t]) }
  return .ran (.wait c ret)

/-- `cond_signal`: wake the first waiter; `cond_broadcast`: all. -/
def signal (c : Nat) : WM Unit := modMem fun m =>
  { m with condWaiters := m.condWaiters.modify c (fun l => l.drop 1) }
def broadcast (c : Nat) : WM Unit := modMem fun m =>
  { m with condWaiters := m.condWaiters.set! c [] }

def opAt (m : Mem) (i : Nat) : POp := m.ops.getD i default

/-- One atomic step of thread `t` (0 is the main thread). -/
def step (t : Nat) (pc : PC) : WM (StepResult PC) := do
  let m ← mem
  match pc with
  -- cond_wait: woken by a signal (no longer a waiter) or spuriously
  | .wait c ret =>
    if !((m.condWaiters.getD c []).contains t) then return .ran (.reacq ret)
    if m.spurious > 0 then
      if (← decide (σ := Process Mem PC) "cond.spurious" 2) == 1 then
        modMem fun m => { m with spurious := m.spurious - 1, condWaiters := m.condWaiters.modify c (fun l => l.erase t) }
        Process.note s!"thread {t}: spurious wakeup from {if c == WORKER then "worker_cond" else "sync_cond"}"
        return .ran (.reacq ret)
    return .blocked
  | .reacq ret =>
    if (← tryLock t) then return .ran ret else return .blocked
  -- main thread
  | .mWaitWorkers =>
    -- flecs_wait_for_workers (worker.c 117-135): spin until every worker
    -- has started
    if !(← tryLock t) then return .blocked
    let ok := m.running == m.stages - 1
    unlock
    return if ok then .ran .mUpdate else .blocked
  | .mUpdate =>
    -- flecs_pipeline_update(start_of_frame) (pipeline.c 491-519)
    setMem { m with curOp := if m.ops.isEmpty then none else some 0, runs := #[] }
    return .ran .mOpBegin
  | .mOpBegin =>
    match m.curOp with
    | none =>
      let f := m.frame + 1
      setMem { m with frame := f }
      if f < m.frames then return .ran .mWaitWorkers else return .done
    | some c =>
      -- ecs_readonly_begin; pipeline.c 625
      if m.waiting != 0 then
        violate "PP1 no-crash" s!"pipeline.c 625: ecs_assert(world->workers_waiting == 0, ECS_INTERNAL_ERROR) (workers_waiting {m.waiting}, op {c}, frame {m.frame})"
      setMem { m with readonly := true }
      Process.note s!"main: frame {m.frame} op {c} ({if (opAt m c).mt then "multi-threaded" else "single-threaded"}) begins"
      return .ran (if (opAt m c).mt then .mSignal else .mRunOwn)
  | .mSignal =>
    -- flecs_signal_workers (worker.c 162-174)
    if !(← tryLock t) then return .blocked
    broadcast WORKER
    unlock
    return .ran .mRunOwn
  | .mRunOwn =>
    let c := m.curOp.getD 0
    setMem { m with runs := m.runs.push (0, c) }
    return .ran .mAfterRun
  | .mAfterRun =>
    let c := m.curOp.getD 0
    return .ran (if (opAt m c).mt then .mSyncLock else .mMerge)
  | .mSyncLock =>
    -- flecs_wait_for_sync (worker.c 138-159): `if`, not `while`
    if !(← tryLock t) then return .blocked
    if (← mem).waiting != m.stages - 1 then
      Process.note s!"main: waits on sync_cond ({m.waiting} workers waiting)"
      condWait t SYNC .mSyncCheck
    else return .ran .mSyncCheck
  | .mSyncCheck =>
    if m.waiting != m.stages - 1 then
      violate "PP1 no-crash" s!"worker.c 156-157: ecs_assert(world->workers_waiting == (stage_count - 1), ECS_INTERNAL_ERROR) after flecs_wait_for_sync returned ({m.waiting} of {m.stages - 1} workers waiting, frame {m.frame})"
    setMem { m with waiting := 0 }
    unlock
    return .ran .mMerge
  | .mMerge =>
    -- ecs_readonly_end merges the stages' commands
    let c := m.curOp.getD 0
    let stagesThatRun := if (opAt m c).mt then m.stages else 1
    for s in [0:stagesThatRun] do
      let n := (m.runs.filter (· == (s, c))).size
      if n != 1 then
        violate "PW1 each system once per stage" s!"op {c} of frame {m.frame} ran {n} times on stage {s} before its merge (runs {m.runs.toList})"
    setMem { m with merging := true }
    Process.note s!"main: merges op {c}"
    return .ran .mMergeEnd
  | .mMergeEnd =>
    let c := m.curOp.getD 0
    let next := if c + 1 < m.ops.size then some (c + 1) else none
    setMem { m with merging := false, readonly := false, curOp := next }
    return .ran .mOpBegin
  -- worker thread
  | .wStart =>
    if !(← tryLock t) then return .blocked
    let m ← mem
    setMem { m with running := m.running + 1 }
    if !m.quit then condWait t WORKER .wStartUnlock
    else return .ran .wStartUnlock
  | .wStartUnlock => unlock; return .ran .wLoop
  | .wLoop =>
    if m.quit then return .done
    return .ran .wRun
  | .wRun =>
    -- flecs_run_pipeline_ops on the worker's stage (pipeline.c 545-579)
    match m.curOp with
    | none =>
      violate "PP1 no-crash" s!"pipeline.c 553: worker {t} reads pq->cur_op, which is NULL (no op is running): NULL dereference"
    | some c =>
      if !(opAt m c).mt then
        violate "PP1 no-crash" s!"pipeline.c 556: ecs_assert(!stage_index || op->multi_threaded, ECS_INTERNAL_ERROR) on worker {t} (op {c} is single-threaded, frame {m.frame})"
      if !m.readonly || m.merging then
        violate "PW2 no system during a merge" s!"worker {t} runs the systems of op {c} while the main thread {if m.merging then "merges the stages" else "is outside the op"} (frame {m.frame})"
      setMem { m with runs := m.runs.push (t, c) }
      Process.note s!"worker {t}: runs op {c}"
      return .ran .wSyncLock
  | .wSyncLock =>
    -- flecs_sync_worker (worker.c 13-31): no predicate loop around the wait
    if !(← tryLock t) then return .blocked
    let m ← mem
    let w := m.waiting + 1
    setMem { m with waiting := w }
    if w == m.stages - 1 then signal SYNC
    condWait t WORKER .wSyncUnlock
  | .wSyncUnlock => unlock; return .ran .wLoop

def prog : Program Mem PC where
  step := step

structure Cfg where
  stages : Nat := 2
  ops : Array POp := #[{ mt := true }]
  frames : Nat := 1
  spurious : Nat := 0
  maxSteps : Nat := 200
  deriving Repr, Inhabited

/-- One timeline: the threads from `flecs_create_worker_threads`
    (worker.c 77-99, started when the world is created with threads) and the
    main thread running `frames` frames.  A timeline that ends with every
    worker parked in `cond_wait(worker_cond)` after the last frame is the
    normal end; every other "all blocked" state is a deadlock. -/
def timeline (cfg : Cfg) (src : Source) : Ended := Id.run do
  let threads : Array (Option PC) :=
    #[some .mWaitWorkers] ++ (Array.replicate (cfg.stages - 1) (some .wStart))
  let start : Process Mem PC :=
    { memory := { stages := cfg.stages, ops := cfg.ops, frames := cfg.frames,
                  spurious := cfg.spurious }, threads }
  let body : WM Unit := interleave prog cfg.maxSteps (fun p =>
    if (p.threads.getD 0 none).isNone then none
    else some s!"main thread blocked: every thread waits (frame {p.memory.frame}, waiting {p.memory.waiting}, cond waiters {p.memory.condWaiters.toList})")
  let (r, p) := runProcess start body src
  match r with
  | .error (.violation prop detail) =>
    return { taken := p.decisions.taken, violation := some (prop, detail ++ " | story: " ++ " ; ".intercalate p.log.toList) }
  | _ => return { taken := p.decisions.taken, violation := none }

end Flecs.Workers

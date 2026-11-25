/-
  Worker threads, each with its own stage, in multithreaded readonly mode
  (flecs.h 2105-2160: "Each application thread must use its own stage"),
  through determinismo's `Threads`: every interleaving of the threads' calls
  within bounds, then `ecs_readonly_end` merges the stages in order.

  P6 schedule independence: the merged state does not depend on how the
  threads' calls interleaved (each thread's queue is its own; the merge order
  is fixed).
  P5 for threads: it is the state of replaying stage 0's calls, then stage
  1's, on the world (Manual.md "Deferred operations").
-/
import FlecsLean.Search

namespace Flecs
open Determinismo

structure TMem where
  w : World
  rs : Rels

instance {L : Type} : Pick (EStateM Stop (Process TMem L)) where
  pick name n := decide (σ := Process TMem L) name n

/-- A call a worker thread may make in multithreaded readonly mode: no
    ecs_new (flecs.h 2120-2127), only queued calls on its own stage. -/
def genThreadOp {m : Type → Type} [Monad m] [Pick m] (k ents : Nat) : m Op := do
  let e ← Pick.pick "flecs.entity" ents
  let tg := Tgt.stage k
  match (← Pick.pick "flecs.call" 6) with
  | 0 => return .delete tg e
  | 1 => return .add tg e (← pickOf "flecs.id" #[IdS.c0, .c1, .tag, .pair .childOf 0, .pair .delete 1])
  | 2 => return .remove tg e (← pickOf "flecs.id" #[IdS.c0, .c1, .tag])
  | 3 => return .set tg e (← pickOf "flecs.id" #[IdS.c0, .c1]) (← pickOf "flecs.value" #[1, 2])
  | 4 => return .ensure tg e (← pickOf "flecs.id" #[IdS.c0, .c1]) (← pickOf "flecs.value" #[3, 4])
  | _ => return .clear tg e

/-- Run one call on the world held by the process memory. -/
def stepWorld (op : Op) : ProcessM TMem (List Op) Unit := do
  let p ← get
  let ok := match (W.allowed p.memory.rs op).run p.memory.w with
    | .ok (b, _) => b
    | .error _ => false
  if !ok then return
  match (W.runOp p.memory.rs op).run p.memory.w with
  | .ok ((), w') => set { p with memory := { p.memory with w := w' } }
  | .error f =>
    if !allowedFail f then throw (.violation "P1 no-crash" (toString f))

def threadProgram : Program TMem (List Op) where
  step _ ops := do
    match ops with
    | [] => return .done
    | op :: rest =>
      stepWorld op
      Process.note s!"{repr op}"
      return .ran rest

/-- Final state after the threads ran in the order the decisions chose. -/
def runThreads (cfg ents : Nat) (prog : Array (List Op)) (src : Source) (fixedOrder : Bool) :
    Except Stop (Array (Nat × Bool × List Id × List (Id × Nat))) × Array Taken := _root_.Id.run do
  let s : Scenario := { stages := prog.size, cfg, ops := List.replicate ents .new }
  match W.initWorld s false with
  | .error f => return (.error (.violation "init" (toString f)), #[])
  | .ok (w0, rs) =>
    let mut w := w0
    for _ in [0:ents] do
      match (W.runOp rs .new).run w with
      | .ok ((), w') => w := w'
      | .error _ => pure ()
    w := { w with readonly := true, mt := true }
    let body : ProcessM TMem (List Op) Unit := do
      if fixedOrder then
        for k in [0:prog.size] do
          for op in prog.getD k [] do stepWorld op
      else interleave threadProgram 64
      let p ← get
      match W.readonlyEnd.run p.memory.w with
      | .ok ((), w') => set { p with memory := { p.memory with w := w' } }
      | .error f => if !allowedFail f then throw (.violation "P1 no-crash" (toString f))
    let start : Process TMem (List Op) := { memory := { w, rs }, threads := prog.map some }
    let (r, p) := runProcess start body src
    match r with
    | .error e => return (.error e, p.decisions.taken)
    | .ok () => return (.ok (summarize p.memory.w), p.decisions.taken)

/-- One timeline: two threads' programs (decided first), then an
    interleaving; checks P6 against the fixed order and P5 against the
    replay. -/
def threadTimeline (cfg ents len : Nat) (src : Source) : Ended := _root_.Id.run do
  -- the programs are the first decisions
  let gen : EStateM Stop Decisions (Array (List Op)) := do
    let mut prog := #[]
    for k in [0:2] do
      let mut ops := []
      for _ in [0:len] do ops := ops ++ [← genThreadOp k ents]
      prog := prog.push ops
    return prog
  match gen.run { source := src } with
  | .error _ d => return { taken := d.taken, violation := none }
  | .ok prog d =>
    let n := d.taken.size
    let rest : Source := { src with given := src.given.extract n src.given.size }
    let (r, taken) := runThreads cfg ents prog rest false
    let taken := d.taken ++ taken
    match r with
    | .error (.violation p detail) => return { taken, violation := some (p, detail) }
    | .error _ => return { taken, violation := none }
    | .ok st =>
      let (r0, _) := runThreads cfg ents prog (Source.path #[]) true
      match r0 with
      | .ok st0 =>
        if st.toList != st0.toList then
          return { taken, violation := some ("P6 schedule independence",
            s!"interleaved {repr st.toList} vs thread 0 then 1 {repr st0.toList}") }
      | _ => pure ()
      -- reference replay: stage 0's calls then stage 1's, as world calls
      let ref : Scenario := { stages := 2, cfg, ops := List.replicate ents .new ++
        (prog.getD 0 []) ++ (prog.getD 1 []) ++ [.merge 0, .merge 1] }
      let c := runScenario ref false true true
      if c.fail.isNone && c.state.toList != st.toList then
        return { taken, violation := some ("P5 staged = replayed (threads)",
          s!"merged {repr st.toList} vs replayed {repr c.state.toList}") }
      return { taken, violation := none }

end Flecs

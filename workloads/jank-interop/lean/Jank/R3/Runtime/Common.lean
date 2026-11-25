import Determinismo
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Round 3, Runtime: shared helpers

`Determinismo.exhaust` enumerates timelines (paths). For concurrent programs the number of
interleavings grows as the binomial of the steps, while the number of distinct states stays small,
because independent steps commute. This module adds what the library lacks for that case:

- `successors`: every step a `Threads` program can take from a process state, one per live thread
  and per value of the decisions that step itself takes (an exhaustive walk inside the step);
- `stateSearch`: breadth-first search over the reachable states of a `Threads` program, with a
  visited set keyed by (memory, threads), an invariant checked at every state, and a deadlock check
  (live threads, none of which can step). A violation comes back as the shortest path of moves;
- `pathTape` and `pathStory`: the path as determinismo tape lines (`thread.next` = the index of the
  thread among those that could step, then the step's own decisions) and as the story that the
  steps wrote with `Process.note`.

A search is "complete" when the reachable state space was exhausted within `maxStates`.
-/

namespace Jank.R3.Runtime

open Determinismo

/-- One transition: which thread stepped, the decisions its step took, and the index of that
thread among the threads that could step (the `thread.next` value). -/
structure Move where
  thread : Nat
  taken : Array Taken
  index : Nat := 0
  options : Nat := 1
  deriving Inhabited

inductive Succ (M L : Type) where
  | state (p : Process M L)
  | violation (property detail : String)

/-- Every successor of `p`: each live thread's step, each value of the decisions that step takes.
A `.blocked` step has no successor. A step that throws a violation is a violation successor. -/
def successors {M L : Type} (prog : Program M L) (p : Process M L) : Array (Move × Succ M L) := Id.run do
  let mut out : Array (Move × Succ M L) := #[]
  for t in [0:p.threads.size] do
    match p.threads[t]! with
    | none => pure ()
    | some l =>
      let mut path : Array Nat := #[]
      let mut fuel := 4096
      while fuel > 0 do
        fuel := fuel - 1
        let p0 : Process M L := { p with decisions := { source := Source.path path, limit := 1000000 }, log := #[] }
        match (prog.step t l).run p0 with
        | .ok r p1 =>
          let tk := p1.decisions.taken
          match r with
          | .ran l' =>
            out := out.push ({ thread := t, taken := tk },
              .state { p1 with threads := p1.threads.set! t (some l'), steps := p1.steps + 1 })
          | .done =>
            out := out.push ({ thread := t, taken := tk },
              .state { p1 with threads := p1.threads.set! t none, steps := p1.steps + 1 })
          | .blocked => pure ()
          match nextPath tk with
          | some np => path := np
          | none => fuel := 0
        | .error (.violation prop d) p1 =>
          out := out.push ({ thread := t, taken := p1.decisions.taken }, .violation prop d)
          match nextPath p1.decisions.taken with
          | some np => path := np
          | none => fuel := 0
        | .error .limit _ => fuel := 0
        | .error (.nodeDown _) _ => fuel := 0
  -- thread.next: the index of the stepping thread among the threads that could step
  let ready := (out.toList.map (·.1.thread)).eraseDups
  return out.map fun (mv, s) =>
    ({ mv with index := ready.idxOf mv.thread, options := ready.length }, s)

structure SearchResult where
  states : Nat
  transitions : Nat
  /-- The shortest path to a violation: its moves, the property and what was seen. -/
  violation : Option (List Move × String × String)
  /-- Every reachable state was visited. -/
  complete : Bool
  /-- Reachable states where every live thread was blocked (counted, whether or not a violation). -/
  deadlocks : Nat := 0
  deriving Inhabited

/-- Breadth-first search over the reachable states.
- `invariant p`: a violation detail if the state breaks a property;
- `onDeadlock p`: called on a state where live threads exist and none can step; a detail makes it a
  violation (`deadlock`), `none` accepts it (e.g. a deadlock the spec model also has);
- `stopAtFirst`: return at the first violation (else keep counting deadlocks). -/
def stateSearch {M L : Type} [BEq M] [Hashable M] [BEq L] [Hashable L]
    (prog : Program M L) (init : Process M L)
    (invariant : Process M L → Option (String × String) := fun _ => none)
    (onDeadlock : Process M L → Option String := fun _ => some "every live thread blocked")
    (maxStates : Nat := 200000) (stopAtFirst : Bool := true) : SearchResult := Id.run do
  let key (p : Process M L) : M × Array (Option L) := (p.memory, p.threads)
  let mut parent : Std.HashMap (M × Array (Option L)) (Option (M × Array (Option L) × Move)) := {}
  let mut queue : Array (Process M L) := #[init]
  parent := parent.insert (key init) none
  let mut head := 0
  let mut transitions := 0
  let mut deadlocks := 0
  let mut found : Option (M × Array (Option L) × Option Move × String × String) := none
  while head < queue.size do
    if parent.size > maxStates then
      return { states := parent.size, transitions, violation := none, complete := false, deadlocks }
    let some p := queue[head]? | break
    head := head + 1
    if let some (prop, d) := invariant p then
      if found.isNone then found := some ((key p).1, (key p).2, none, prop, d)
      if stopAtFirst then break
    let succs := successors prog p
    transitions := transitions + succs.size
    let live := p.threads.any (·.isSome)
    if succs.isEmpty && live then
      deadlocks := deadlocks + 1
      if let some d := onDeadlock p then
        if found.isNone then found := some ((key p).1, (key p).2, none, "deadlock", d)
        if stopAtFirst then break
    for (mv, s) in succs do
      match s with
      | .violation prop d =>
        if found.isNone then found := some ((key p).1, (key p).2, some mv, prop, d)
      | .state q =>
        let k := key q
        if !parent.contains k then
          parent := parent.insert k (some ((key p).1, (key p).2, mv))
          queue := queue.push q
    if stopAtFirst && found.isSome then break
  match found with
  | none => return { states := parent.size, transitions, violation := none, complete := true, deadlocks }
  | some (m, th, last, prop, d) =>
    -- walk the parents back to the initial state
    let mut moves : List Move := match last with | some mv => [mv] | none => []
    let mut cur : M × Array (Option L) := (m, th)
    let mut fuel := parent.size + 1
    while fuel > 0 do
      fuel := fuel - 1
      match parent.get? cur with
      | some (some (pm, pt, mv)) => moves := mv :: moves; cur := (pm, pt)
      | _ => fuel := 0
    return { states := parent.size, transitions, violation := some (moves, prop, d),
             complete := !stopAtFirst || head ≥ queue.size, deadlocks }

/-- Every reachable state, with a predicate counted (no violation stops it). -/
def stateCount {M L : Type} [BEq M] [Hashable M] [BEq L] [Hashable L]
    (prog : Program M L) (init : Process M L) (maxStates : Nat := 200000) : SearchResult :=
  stateSearch prog init (onDeadlock := fun _ => none) (maxStates := maxStates) (stopAtFirst := false)

/-- Determinismo tape lines for a path found by `stateSearch`. -/
def pathTape (moves : List Move) : String :=
  String.intercalate "\n" <| moves.flatMap fun mv =>
    s!"\{\"name\":\"thread.next\",\"options\":{mv.options},\"value\":{mv.index}}" ::
      (mv.taken.toList.map fun t => s!"\{\"name\":\"{t.name}\",\"options\":{t.options},\"value\":{t.value}}")

/-- The story of a path: each step replayed with its decisions, collecting `Process.note` lines. -/
def pathStory {M L : Type} (prog : Program M L) (init : Process M L) (moves : List Move) : Array String := Id.run do
  let mut p := init
  for mv in moves do
    match p.threads[mv.thread]? with
    | some (some l) =>
      let p0 : Process M L := { p with decisions := { source := Source.path (mv.taken.map (·.value)), limit := 1000000 } }
      match (prog.step mv.thread l).run p0 with
      | .ok r p1 =>
        match r with
        | .ran l' => p := { p1 with threads := p1.threads.set! mv.thread (some l'), steps := p1.steps + 1 }
        | .done => p := { p1 with threads := p1.threads.set! mv.thread none, steps := p1.steps + 1 }
        | .blocked => p := p1
      | .error (.violation prop d) p1 => return p1.log.push s!"violation {prop}: {d}"
      | .error .limit p1 => return p1.log
      | .error (.nodeDown _) p1 => return p1.log
    | _ => pure ()
  return p.log

/-- SplitMix64 finalizer: consecutive seeds give unrelated generators (round 2's `exploreMixed`). -/
def mixSeed (i : Nat) : Nat :=
  let z : UInt64 := (UInt64.ofNat i) + 0x9E3779B97F4A7C15
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31)).toNat

def exploreMixed (run : Source → Ended) (count : Nat) (first : Nat := 0) : Option Counterexample := Id.run do
  for i in [0:count] do
    let o := run { gen := mkStdGen (mixSeed (first + i)) }
    if let some (property, detail) := o.violation then
      return some { taken := o.taken, property, detail, runs := i + 1 }
  return none

/-- A census over every timeline of `run` within `maxRuns`: violations counted per class (the
property name), with the first timeline of each class. Unlike `exhaust` it does not stop at the
first counterexample. -/
structure Census where
  runs : Nat
  complete : Bool
  classes : List (String × Nat × Array Taken × String)
  deriving Inhabited

def census (run : Source → Ended) (maxRuns : Nat) : Census := Id.run do
  let mut path : Array Nat := #[]
  let mut classes : List (String × Nat × Array Taken × String) := []
  for i in [0:maxRuns] do
    let o := run (Source.path path)
    if let some (prop, d) := o.violation then
      match classes.find? (·.1 == prop) with
      | some _ => classes := classes.map fun (c, n, tk, dd) => if c == prop then (c, n + 1, tk, dd) else (c, n, tk, dd)
      | none => classes := classes ++ [(prop, 1, o.taken, d)]
    match nextPath o.taken with
    | none => return { runs := i + 1, complete := true, classes }
    | some p => path := p
  return { runs := maxRuns, complete := false, classes }

end Jank.R3.Runtime

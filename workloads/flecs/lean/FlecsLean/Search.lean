/-
  Search drivers over the generators: seeded random exploration, bounded
  exhaustive enumeration of every choice sequence, and shrinking that keeps
  the failing property.  Every program is reproducible from its tape (the
  list of choices the generator made).
-/
import FlecsLean.Gen
import Determinismo.Search
import Determinismo.Threads

namespace Flecs

/-- A tape-driven chooser: replays `tape`, then draws from a splitmix64
    stream (or 0 when `rng` is none), recording every choice and its bound. -/
structure TapeSt where
  tape : Array Nat
  pos : Nat := 0
  rng : Option UInt64 := none
  taken : Array (Nat × Nat) := #[]   -- (choice, bound)

abbrev TapeM := StateM TapeSt

def splitmix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (s, z ^^^ (z >>> 31))

instance : Pick TapeM where
  pick _ n := do
    let st ← get
    if n == 0 then return 0
    let c ← if h : st.pos < st.tape.size then pure (st.tape[st.pos] % n)
      else match st.rng with
        | some r => do
          let (r', z) := splitmix r
          modify fun st => { st with rng := some r' }
          pure (z.toNat % n)
        | none => pure 0
    modify fun st => { st with pos := st.pos + 1, taken := st.taken.push (c, n) }
    return c

def runGen {α} (g : TapeM α) (tape : Array Nat) (rng : Option UInt64 := none) : α × Array (Nat × Nat) :=
  let (a, st) := g.run { tape, rng }
  (a, st.taken)

/-- Next tape in the odometer order over (choice, bound) lists; none when
    every sequence has been visited. -/
def nextTape (taken : Array (Nat × Nat)) : Option (Array Nat) := _root_.Id.run do
  let mut i := taken.size
  while i > 0 do
    i := i - 1
    let (c, b) := taken[i]!
    if c + 1 < b then
      return some ((taken.extract 0 i).map (·.1) |>.push (c + 1))
  return none

structure Found where
  property : String
  detail : String
  tape : Array Nat
  scenario : Scenario
  deriving Inhabited

structure RunStats where
  programs : Nat := 0
  failures : Nat := 0
  byProperty : List (String × Nat) := []
  first : List Found := []

def bump (xs : List (String × Nat)) (k : String) : List (String × Nat) :=
  if xs.any (·.1 == k) then xs.map (fun (a, n) => if a == k then (a, n + 1) else (a, n))
  else xs ++ [(k, 1)]

/-- A failure's signature: its property and its detail with numbers erased,
    so that failures with the same cause are counted together. -/
def signature (v : Verdict) : String :=
  let d := String.ofList (v.detail.toList.map (fun c => if c.isDigit then '#' else c))
  let d := String.ofList ((d.toList.filter (fun c => c != '#')).take 110)
  v.property ++ " | " ++ d

def record (st : RunStats) (s : Scenario) (tape : Array Nat) (vs : List Verdict) : RunStats :=
  let st := { st with programs := st.programs + 1 }
  if vs.isEmpty then st
  else
    let st := { st with failures := st.failures + 1 }
    vs.foldl (fun st v =>
      let k := signature v
      let first := if st.first.any (·.property == k) then st.first
        else st.first ++ [{ property := k, detail := v.detail, tape, scenario := s }]
      { st with byProperty := bump st.byProperty k, first }) st

/-- Random exploration: `n` programs from seeds `seed, seed+1, ...`. -/
def explore (g : TapeM Scenario) (props : List String) (seed n : Nat) : RunStats := _root_.Id.run do
  let mut st : RunStats := {}
  for i in [0:n] do
    let (s, taken) := runGen g #[] (some (seed + i).toUInt64)
    let vs := (checkAll s).filter (fun v => props.isEmpty || props.any (fun p => v.property.startsWith p))
    st := record st s (taken.map (·.1)) vs
  return st

/-- Exhaustive enumeration of every choice sequence of `g` (bounded by the
    generator's own sizes), at most `limit` programs. -/
def exhaust (g : TapeM Scenario) (props : List String) (limit : Nat) : RunStats × Bool := _root_.Id.run do
  let mut st : RunStats := {}
  let mut tape : Array Nat := #[]
  for _ in [0:limit] do
    let (s, taken) := runGen g tape none
    let vs := (checkAll s).filter (fun v => props.isEmpty || props.any (fun p => v.property.startsWith p))
    st := record st s (taken.map (·.1)) vs
    match nextTape taken with
    | some t => tape := t
    | none => return (st, true)
  return (st, false)

/-- Shrink a failing scenario: drop calls (and reset values/choices) while
    the same property still fails. -/
partial def shrink (s : Scenario) (prop : String) : Scenario :=
  let fails := fun (s : Scenario) => (checkAll s).any (·.property == prop)
  let rec loop (s : Scenario) : Scenario := _root_.Id.run do
    let ops := s.ops.toArray
    for i in [0:ops.size] do
      let cand := { s with ops := (ops.eraseIdx! i).toList }
      if fails cand then return loop cand
    -- drop the hook/observer configuration when it is not needed
    if s.cfg != 0 && fails { s with cfg := 0 } then return loop { s with cfg := 0 }
    if s.stages > 1 && fails { s with stages := 1 } then return loop { s with stages := 1 }
    return s
  loop s

/-! ### Through determinismo's search (`Determinismo.Search`)

The generator's choices are determinismo decisions (`decide`), so a
counterexample is a determinismo tape of named decisions, and the library's
`explore`, `exhaust` and `shrink` drive the search. -/

open Determinismo in
instance : Pick (EStateM Stop Decisions) where
  pick name n := decide (σ := Decisions) name n

open Determinismo in
/-- One timeline: the program the decisions generate, and the first property
    (among `props`, all when empty) it breaks. -/
def timeline (g : EStateM Stop Decisions Scenario) (props : List String) (src : Source) : Ended :=
  match g.run { source := src } with
  | .ok s d =>
    let vs := (checkAll s).filter (fun v => props.isEmpty ||
      props.any (fun p => ((signature v).splitOn p).length > 1))
    { taken := d.taken, violation := vs.head?.map (fun v => (signature v, v.detail)) }
  | .error _ d => { taken := d.taken, violation := none }

open Determinismo in
/-- The scenario a list of decision values generates. -/
def scenarioOf (g : EStateM Stop Decisions Scenario) (values : Array Nat) : Scenario :=
  match g.run { source := Source.path values } with
  | .ok s _ => s
  | .error _ _ => default

/-- Shrink keeping the failure's signature (same cause, not just the same
    property). -/
partial def shrinkSig (s : Scenario) (sig : String) : Scenario :=
  let fails := fun (s : Scenario) => (checkAll s).any (fun v => signature v == sig)
  let rec loop (s : Scenario) : Scenario := _root_.Id.run do
    let ops := s.ops.toArray
    for i in [0:ops.size] do
      let cand := { s with ops := (ops.eraseIdx! i).toList }
      if fails cand then return loop cand
    if s.cfg != 0 && fails { s with cfg := 0 } then return loop { s with cfg := 0 }
    if s.stages > 1 && fails { s with stages := 1 } then return loop { s with stages := 1 }
    return s
  loop s

end Flecs

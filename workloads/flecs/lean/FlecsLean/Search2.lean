/-
  Generic search drivers for round 2's models: the same tape-driven
  generators as round 1 (`TapeM`, `Pick`), over any program type with a check
  that returns the broken properties, plus the adapter to determinismo's
  `explore`/`exhaust`/`shrink` (decisions are named, tapes replay).
-/
import FlecsLean.Search

namespace Flecs

structure GFound (α : Type) where
  sig : String
  detail : String
  tape : Array Nat
  prog : α

structure GStats (α : Type) where
  programs : Nat := 0
  failures : Nat := 0
  byProperty : List (String × Nat) := []
  first : List (GFound α) := []

def gsig (p d : String) : String :=
  signature { ok := false, property := p, detail := d }

def grecord {α} (st : GStats α) (x : α) (tape : Array Nat) (vs : List (String × String)) : GStats α :=
  let st := { st with programs := st.programs + 1 }
  if vs.isEmpty then st
  else
    let st := { st with failures := st.failures + 1 }
    vs.foldl (fun st (p, d) =>
      let k := gsig p d
      let first := if st.first.any (·.sig == k) then st.first
        else st.first ++ [{ sig := k, detail := d, tape, prog := x }]
      { st with byProperty := bump st.byProperty k, first }) st

def gexplore {α} (g : TapeM α) (check : α → List (String × String)) (seed n : Nat) : GStats α := Id.run do
  let mut st : GStats α := {}
  for i in [0:n] do
    let (x, taken) := runGen g #[] (some (seed + i).toUInt64)
    st := grecord st x (taken.map (·.1)) (check x)
  return st

def gexhaust {α} (g : TapeM α) (check : α → List (String × String)) (limit : Nat) : GStats α × Bool := Id.run do
  let mut st : GStats α := {}
  let mut tape : Array Nat := #[]
  for _ in [0:limit] do
    let (x, taken) := runGen g tape none
    st := grecord st x (taken.map (·.1)) (check x)
    match nextTape taken with
    | some t => tape := t
    | none => return (st, true)
  return (st, false)

/-- Shrink by trying smaller candidates while the same signature fails. -/
partial def gshrink {α} (cands : α → List α) (check : α → List (String × String)) (sig : String) (x : α) : α :=
  let fails := fun (y : α) => (check y).any (fun (p, d) => gsig p d == sig)
  match (cands x).find? fails with
  | some y => gshrink cands check sig y
  | none => x

open Determinismo in
instance : Pick (EStateM Stop Decisions) := inferInstance

open Determinismo in
def gtimeline {α} (g : EStateM Stop Decisions α) (check : α → List (String × String))
    (props : List String) (src : Source) : Ended :=
  match g.run { source := src } with
  | .ok x d =>
    let vs := (check x).filter (fun (p, dd) => props.isEmpty ||
      props.any (fun q => ((gsig p dd).splitOn q).length > 1))
    { taken := d.taken, violation := vs.head?.map (fun (p, dd) => (gsig p dd, dd)) }
  | .error _ d => { taken := d.taken, violation := none }

open Determinismo in
def gprogOf {α} [Inhabited α] (g : EStateM Stop Decisions α) (values : Array Nat) : α :=
  match g.run { source := Source.path values } with
  | .ok x _ => x
  | .error _ _ => default

end Flecs

import Replica.Clock
import Replica.Junit
import Replica.Persist
open Replica

/-- Round 2's new areas (round 1's searches are `replica`'s). -/
def main (args : List String) : IO Unit := do
  match args with
  | ["clock", e, n] => let _ ← Clock.searchAll e.toNat! n.toNat!
  | ["junit", e] => let _ ← Junit.searchAll e.toNat!
  | ["persist", e] => let _ ← Persist.searchAll e.toNat!
  | _ => IO.println "usage: replica2 clock <exhaust> <seeds> | junit <exhaust> | persist <exhaust>"

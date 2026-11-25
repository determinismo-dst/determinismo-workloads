import Replica.Resume4
import Replica.Durable
import Replica.Ci4
import Replica.Steer4
import Replica.Clock4
import Replica.Holders4
open Replica

/-- Round 4's areas. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["resume", e, n] => Resume4.searchAll e.toNat! n.toNat!
  | ["resumecensus", n] => Resume4.census n.toNat!
  | ["durable", e, n] => Durable.searchAll e.toNat! n.toNat!
  | ["ci", e, n] => Ci4.searchAll e.toNat! n.toNat!
  | ["steer", e, n] => Steer4.searchAll e.toNat! n.toNat!
  | ["clock", e, n] => Clock4.searchAll e.toNat! n.toNat!
  | ["holders", e, n] => Holders4.searchAll e.toNat! n.toNat!
  | _ => IO.println "usage: replica4 resume|durable|ci|steer|clock|holders <exhaust> <seeds> | resumecensus <seeds>"

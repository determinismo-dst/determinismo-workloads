import Replica.TreeProps
import Replica.Ci
import Replica.Serve3
import Replica.Disk
import Replica.Skew
import Replica.Ce2Drawn
open Replica

/-- Round 3's areas. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["tree", e, n] => Tree.searchTree e.toNat! n.toNat!
  | ["jobs", e, n] => Tree.searchJobs e.toNat! n.toNat!
  | ["treecensus", n] => Tree.treeCensus n.toNat!
  | ["ci", e] => Ci.searchAll e.toNat!
  | ["serve", e] => Serve3.searchAll e.toNat!
  | ["disk", e] => Disk.searchAll e.toNat!
  | ["skew", e, n] => Skew.searchAll e.toNat! n.toNat!
  | ["ce2", n] => Composer.searchCe2 n.toNat!
  | _ => IO.println "usage: replica3 tree <exhaust> <seeds> | jobs <exhaust> <seeds> | ci <exhaust> | serve <exhaust> | disk <exhaust> | skew <exhaust> <seeds> | ce2 <seeds>"

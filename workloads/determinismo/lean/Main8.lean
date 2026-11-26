import Replica.Composer
import Replica.ComposerSearch
import Replica.Junit
import Replica.Persist
import Replica.Verdicts
import Replica.Tape
import Replica.Ci
import Replica.Ci4
import Replica.Ci5
import Replica.Durable
import Replica.Resume4
import Replica.Resume5
import Replica.Clock5
import Replica.Disk5
import Replica.TreeProps
import Replica.Serve3
import Replica.Steer4
import Replica.Holders4
import Replica.Request6
import Replica.Tape6
import Replica.Aimed6
import Replica.Explain7
import Replica.Disk7
open Replica

/-- Round 8: the searches of the models c4f246e changed (their default), with df8f08b's worlds beside them, and the rest as round 7's. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["composer", e, w, d] => discard <| Composer.searchAll e.toNat! w.toNat! d.toNat!
  | ["cworld", p, w, e, n] => Composer.searchWorld p.toNat! w.toNat! e.toNat! n.toNat! 0
  | ["cdrawn", p, n, f] => Composer.searchDrawn p.toNat! n.toNat! f.toNat!
  | ["junit", e] => discard <| Junit.searchAll e.toNat!
  | ["persist", e] => discard <| Persist.searchAll e.toNat!
  | ["verdicts", e] => discard <| Verdicts.searchAll e.toNat!
  | ["tape", e] => discard <| Tape.searchAll e.toNat!
  | ["ci", e, n] => do Ci.searchAll e.toNat!; Ci4.searchAll e.toNat! n.toNat!; Ci5.searchAll e.toNat!
  | ["durable", e, n] => Durable.searchAll e.toNat! n.toNat!
  | ["resume", e] => Resume5.searchAll e.toNat!
  | ["resume4", e, n] => Resume4.searchAll e.toNat! n.toNat!
  | ["resume4census", n] => Resume4.census n.toNat!
  | ["clock", n] => Clock5.searchAll n.toNat!
  | ["disk", e, n] => Disk5.searchAll e.toNat! n.toNat!
  | ["disk7", e, n] => Disk7.searchAll e.toNat! n.toNat!
  | ["tree", e, n] => Tree.searchTree e.toNat! n.toNat!
  | ["treecensus", n] => Tree.treeCensus n.toNat!
  | ["serve", e] => Serve3.searchAll e.toNat!
  | ["steer", e, n] => Steer4.searchAll e.toNat! n.toNat!
  | ["holders", e, n] => Holders4.searchAll e.toNat! n.toNat!
  | ["request", e] => Request6.searchAll e.toNat!
  | ["tape6", e] => Tape6.searchAll e.toNat!
  | ["aimed", e, n] => Aimed6.searchAll e.toNat! n.toNat!
  | ["explain", e] => Explain7.searchAll e.toNat!
  | _ => IO.println "usage: replica8 composer <exhaust> <seeds> <drawn> | cworld <p> <w> <exhaust> <seeds> | cdrawn <p> <n> <f> | junit|persist|verdicts|tape|resume|serve|request|tape6|explain <exhaust> | ci|durable|disk|disk7|resume4|tree|steer|holders|aimed <exhaust> <seeds> | clock|treecensus|resume4census <seeds>"

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
import Replica.Resume5
import Replica.Clock5
import Replica.Disk5
import Replica.Theorems5
open Replica

/-- Round 5: rounds 1 to 4's searches on 62e06e3's code (the models' default), and round 5's. -/
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
  | ["clock", n] => Clock5.searchAll n.toNat!
  | ["disk", e, n] => Disk5.searchAll e.toNat! n.toNat!
  | _ => IO.println "usage: replica5 composer <exhaust> <seeds> <drawn> | cworld <p> <w> <exhaust> <seeds> | junit|persist|verdicts|tape|resume <exhaust> | ci|durable|disk <exhaust> <seeds> | clock <seeds>"

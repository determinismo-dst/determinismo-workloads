import Replica
open Replica

def main (args : List String) : IO Unit := do
  match args with
  | ["composer", e, w, d] => let _ ← Composer.searchAll e.toNat! w.toNat! d.toNat!
  | ["composer", e, w, d, i] => let _ ← Composer.searchAll e.toNat! w.toNat! d.toNat! (some i.toNat!)
  | ["cworld", p, w, e, n, f] => Composer.searchWorld p.toNat! w.toNat! e.toNat! n.toNat! f.toNat!
  | ["cdrawn", p, n, f] => Composer.searchDrawn p.toNat! n.toNat! f.toNat!
  | ["faults", e, w] => let _ ← Faults.searchAll e.toNat! w.toNat!
  | ["verdicts", e] => let _ ← Verdicts.searchAll e.toNat!
  | ["tape", e] => let _ ← Tape.searchAll e.toNat!
  | _ => IO.println "usage: replica composer <exhaust> <world-seeds> <drawn-seeds> | faults <exhaust> <seeds> | verdicts <exhaust> | tape <exhaust>"

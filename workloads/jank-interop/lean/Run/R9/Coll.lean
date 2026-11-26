import Jank.R9.Coll.Order
import Jank.R9.Coll.HashOrder
import Jank.R9.Coll.Lookup
import Jank.R9.Coll.Paths

/-! Round 9, area Coll: the driver. Prints the replicas' predictions for the tests and runs the
complete walks of results/r9-coll-report.txt section 8. -/

open Jank.R9.Coll Jank.R9.Coll.HashOrder Jank.R9.Coll.Order Jank.R9.Coll.Lookup

/-- Every subset of `{0, ..., n-1}` (as int keys), in binary-counter order. -/
def subsets (n : Nat) : List (List Int) :=
  (List.range (2 ^ n)).map fun m => ((List.range n).filter fun i => m.testBit i).map (fun (i : Nat) => (i : Int))

def main : IO Unit := do
  IO.println "Round 9, area Coll."
  -- predictions
  IO.println s!"M9-5 promoted 8-entry map keys (jank): {(jankAssoc (.array range8) 0 99).keys}"
  IO.println s!"M9-5 frequencies [7 6 5 4 3 2 1 0 0] keys (jank): {jankKeys ([7, 6, 5, 4, 3, 2, 1, 0].map (fun (i : Int) => (i, 1)) ++ [(0, 2)])}"
  IO.println s!"M9-6 kwargs 2 :x 1 :y keys (jank): {jankKeys [(2, 0), (1, 1)]}; Clojure: {(cljAsIfByAssoc [(2, 0), (1, 1)]).map Prod.fst}"
  IO.println s!"M9-11 (hash-set 5 9 8): Clojure {cljOrd 7 0 (withHash [5, 9, 8])}, jank {champOrd 7 0 (withHash [5, 9, 8])} (replica {jankKeys [(5, 0), (9, 0), (8, 0)]})"
  let r12 := (List.range 12).map (fun (i : Nat) => (i : Int))
  IO.println s!"M9-11 12 keys 0-11: Clojure {cljOrd 7 0 (withHash r12)}, jank {champOrd 7 0 (withHash r12)}"
  -- walk 1: every subset of {0..N-1}: Clojure's order vs jank's, and champOrd vs the CHAMP replica
  for n in [12, 14] do
    let ss := subsets n
    let mut differ := 0
    let mut replicaMismatch := 0
    let mut firstDiff : Option (List Int) := none
    for s in ss do
      let c := cljOrd 7 0 (withHash s)
      let j := champOrd 7 0 (withHash s)
      if c != j then
        differ := differ + 1
        if firstDiff.isNone then firstDiff := some s
      if j != jankKeys (s.map fun k => (k, 0)) then replicaMismatch := replicaMismatch + 1
    IO.println s!"walk hash-order subsets of 0..{n-1}: complete {ss.length}; Clojure/jank orders differ on {differ}; champOrd vs CHAMP replica mismatches {replicaMismatch}; first differing subset {firstDiff}"
  -- walk 2: vector get over the key window and sizes 0-4
  IO.println s!"walk vector get: complete {5 * keysWindow.length} (size, key) pairs; differ on {vecGetCensus.length}: {repr vecGetCensus}"
  -- walk 3: (range n) for n < 64
  let rs := (List.range 64).filter fun n =>
    let l := (List.range n).map (fun (i : Nat) => (i : Int))
    cljOrd 7 0 (withHash l) != champOrd 7 0 (withHash l)
  IO.println s!"walk (range n), n < 64: complete 64; orders differ for {rs.length} values of n, the first {rs.head?}"

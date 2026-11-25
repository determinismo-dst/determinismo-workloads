import Jank.Core.Destructure
import Jank.R3.Proofs.Lin
import Jank.R3.Proofs.Threads
import Jank.R3.Proofs.AtomLin
import Jank.R3.Proofs.AtomStep
import Jank.R3.Proofs.AtomMain
import Jank.R3.Proofs.AtomDeadlock
import Jank.R3.Proofs.Multi
import Jank.R3.Proofs.Vector
import Jank.R3.Proofs.Delay
import Jank.R3.Proofs.Lex
import Jank.R3.Proofs.Destructure
import Jank.R3.Proofs.Range
import Jank.R3.Proofs.ArrayMap

/-! Round 3 driver: Proofs. The theorems are checked when this exe is built (every module it
imports is elaborated, no `sorry`); the run prints the P1 table (the kwargs conversion with a
trailing empty collection, found while stating the destructuring theorem) and the theorem
inventory. -/

open Jank.Core.Destructure

namespace Run.R3.Proofs

def showR (r : Except String Val) : String :=
  match r with
  | .ok v => v.code
  | .error e => s!"throws ({e})"

/-- `(defn f [& {:as m}] m)` called with every argument list of length ≤ 3 over the round-2
elements plus the empty list and the empty set: where jank's conversion (core.jank 3427–3436 →
base_persistent_map.cpp `conj`) and Clojure's (`PersistentArrayMap/createAsIfByAssoc` →
`APersistentMap.cons`) disagree, by the trailing element's kind. -/
def p1Table : IO Unit := do
  let elems : List Val := [.kw "" "a", .int 1, .map [(.kw "" "b", .int 2)], .nil,
    .vec [.kw "" "c", .int 3], .mapSeq [(.kw "" "d", .int 4)], .list [], .set []]
  let lists := [[]] ++ (elems.map fun a => [a]) ++ (elems.flatMap fun a => elems.map fun b => [a, b]) ++
    (elems.flatMap fun a => elems.flatMap fun b => elems.map fun c => [a, b, c])
  let mut total := 0
  let mut bad : Array (List Val × Except String Val × Except String Val) := #[]
  for args in lists do
    total := total + 1
    let j := kwargs .jank args
    let c := kwargs .clj args
    let same := match j, c with
      | .ok x, .ok y => valEq x y
      | .error _, .error _ => true
      | _, _ => false
    if !same then bad := bad.push (args, c, j)
  IO.println s!"== P1: ((fn [& \{:as m}] m) args…), args ≤ 3 over 8 elements: {total} lists, {bad.size} disagree"
  let kinds : List (String × (Val → Bool)) :=
    [("trailing (seq {:d 4}) (R107)", fun v => match v with | .mapSeq _ => true | _ => false),
     ("trailing () (P1)", fun v => match v with | .list [] => true | _ => false),
     ("trailing #{} (model: Clojure side throws, see note)", fun v => match v with | .set [] => true | _ => false)]
  for (name, isK) in kinds do
    let n := bad.toList.filter fun (args, _, _) => (args.getLast?.map isK).getD false
    IO.println s!"   {name}: {n.length}"
  let other := bad.toList.filter fun (args, _, _) =>
    !(kinds.any fun (_, isK) => (args.getLast?.map isK).getD false)
  IO.println s!"   other: {other.length}"
  for (args, c, j) in bad.toList.take 6 do
    IO.println s!"   ((fn [& \{:as m}] m) {" ".intercalate (args.map Val.code)}): Clojure {showR c}, jank {showR j}"

def inventory : List String := [
  "Lin.linearizable_of_witness: linearization points give a linearizable history (relational definition)",
  "Threads.interleave_inv / interleave_no_deadlock: invariants through every interleaving",
  "AtomLin.linearizable_x86 / linearizable_clojure: every timeline's history is linearizable (strong register)",
  "AtomLin.linearizable_llsc_weak: LL/SC: linearizable against the register with a weak compare-and-set",
  "AtomLin.linearizable_llsc_no_cas: LL/SC without compare-and-set!: linearizable (strong register)",
  "AtomLin.llsc_cas_not_linearizable: round 1's LL/SC tape gives a history no strong-register order explains",
  "AtomLin.no_deadlock: recording watches: the run never reports a deadlock",
  "AtomLin.counter_linearizable / counter2_linearizable / casRace_linearizable_x86: round 1's scenarios",
  "Multi.root_methods_same / agree_of_dominates_agree / jank_prefers_direct",
  "Vector.nth_iff / assoc_none_iff / pop_none_iff / subvec_none_iff / subvec_spec / transient_nth_agrees",
  "Delay.delay_value_runs_once / delay_clojure_runs_once / deliver_once",
  "Lex.mbrtowc_len_pos / symbolStep_next / commentStep_next / stringStep_next / loop_stops / lexSymbol_never_hangs",
  "Destructure.p1_jank_conj_throws / p1_clj_adds_nothing (P1); even_agrees / odd_agrees: the kwargs conversion",
  "Range.fixed_walk_agrees / fixed_walk_agrees2 / fixed_walk_agrees1: integer range with the exact count = Clojure",
  "ArrayMap.transient_keeps_source: after the clone fix, any assoc!/dissoc! sequence on (transient m) leaves m unchanged",
  "Lex.flag_loop_done / symF_spec / charF_spec / comF_spec / defF_spec: every done-flag loop of the lexer ends"]

end Run.R3.Proofs

def main : IO UInt32 := do
  Run.R3.Proofs.p1Table
  IO.println "== theorems (checked at build time)"
  for t in Run.R3.Proofs.inventory do IO.println s!"   {t}"
  return 0

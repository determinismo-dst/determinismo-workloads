import Jank.R9.Champ.Programs
import Jank.R9.Champ.Per
import Jank.R7.Champ.Walk

/-!
Round 9 driver, CHAMP (`jank9-champ show | h91 | seqs CFG N MODE`).

- `show`: H8-1's programs on the replica, stock (round 3's steps) and with the fix (`doAddF`,
  `doAddMutF`), and H9-1 on the abstract non-transitive equality.
- `h91`: H9-1 with round 3's replicas of jank's BigDecimal reader, hash and `=` (round 7's `Vals`,
  `Fix.none`) on the three BigDecimals the C++ search found: their hashes, jank's and Clojure's `=`,
  and the transient chain against its persistent twin, stock and fixed.
- `seqs CFG N MODE`: every sequence of length <= N over the values 0..5 (hash `k / 3`: two groups of
  three, one full hash each, so collision nodes at every length), run as given and with every
  transient step made persistent, from `champ::empty()`, stock and fixed. MODE `pure`: steps
  `add k`/`sub k` once all persistent, once all transient under one owner (12 steps); MODE `mixed`:
  each step persistent or transient (24 steps) against the all-persistent twin. CFG names the
  equality `Equal(stored, query)`:
    `lawful`  x == y (an equivalence);
    `nontrans` |x - y| <= 1 within a group (reflexive, symmetric, NOT transitive: jank's D8);
    `per`     x == y except 5, which equals nothing, itself included (a partial equivalence: NaN, V85);
    `asym`    x == y, or stored 0 accepts the query 1 (not symmetric: R55's string seq and vector).
  Counted: contents differ (as multisets), collision order differs (node by node exactly).
-/

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R7.Champ Jank.R8.Champ Jank.R8.Champ.Programs Jank.R9.Champ
open Jank.R9.Champ.Programs Jank.R7.Champ.Vals Jank.R7.Champ.Walk

/-- `Agree` as a Boolean (`perm`: collision lists compared as multisets). -/
def agreeB (perm : Bool) : Nat → Node Nat → Node Nat → Bool
  | 0, A, B => if perm then A.collisions.isPerm B.collisions else A.collisions == B.collisions
  | r + 1, A, B => (List.range 32).all fun d =>
    match slot A d, slot B d with
    | .empty, .empty => true
    | .data x, .data y => x == y
    | .child a, .child b => agreeB perm r a b
    | _, _ => false

def mkCfg (eq : Nat → Nat → Bool) : Cfg Nat Nat where
  hashT k := k / 3
  hashK k := k / 3
  eqTT := eq
  eqTK := eq

def cfgOf : String → Cfg Nat Nat
  | "nontrans" => mkCfg fun x y => x / 3 == y / 3 && (x == y || x + 1 == y || y + 1 == x)
  | "per" => mkCfg fun x y => x == y && x != 5
  | "asym" => mkCfg fun x y => x == y || (x == 0 && y == 1)
  | _ => mkCfg fun x y => x == y

/-- One step: `kind` 0 = persistent add, 1 = persistent sub, 2 = transient add, 3 = transient sub. -/
def step (fixed : Bool) (cfg : Cfg Nat Nat) (c : Champ Nat) (al : Al) (kind k : Nat) : Champ Nat × Al :=
  match kind with
  | 0 => if fixed then (addRootF cfg c k).run al else (c.add cfg k).run al
  | 1 => (c.sub cfg k).run al
  | 2 => if fixed then (addMutRootF cfg 7 c k).run al else (c.addMut cfg 7 k).run al
  | _ => (c.subMut cfg 7 k).run al

def run (fixed : Bool) (cfg : Cfg Nat Nat) (ops : List (Nat × Nat)) : Champ Nat := Id.run do
  let mut c : Champ Nat := Champ.empty
  let mut al : Al := {}
  for (kind, k) in ops do
    let (c', al') := step fixed cfg c al kind k
    c := c'; al := al'
  return c

def persistK (kind : Nat) : Nat := if kind ≥ 2 then kind - 2 else kind

def opStr : Nat × Nat → String
  | (0, k) => s!"(conj {k})"
  | (1, k) => s!"(disj {k})"
  | (2, k) => s!"(conj! {k})"
  | (_, k) => s!"(disj! {k})"

/-- The `idx`-th sequence of length `len` over `allOps` (base-`allOps.length` digits). -/
def decodeOps (allOps : Array (Nat × Nat)) (len idx : Nat) : List (Nat × Nat) := Id.run do
  let m := allOps.size
  let mut out : List (Nat × Nat) := []
  let mut x := idx
  for _ in List.range len do
    out := allOps[x % m]! :: out
    x := x / m
  return out

def seqs (cname : String) (n : Nat) (mode : String) : IO Unit := do
  let cfg := cfgOf cname
  let kinds := if mode == "mixed" then [0, 1, 2, 3] else [0, 1]
  let allOps : Array (Nat × Nat) := (kinds.flatMap fun kd => (List.range 6).map fun k => (kd, k)).toArray
  let mut total := 0
  let mut cS := 0
  let mut oS := 0
  let mut cF := 0
  let mut oF := 0
  let mut firstC : Option (List (Nat × Nat)) := none
  for len in List.range (n + 1) do
    for idx in List.range (allOps.size ^ len) do
      let ops := decodeOps allOps len idx
      -- `pure`: the transient run is the same steps made transient; `mixed`: the steps as given
      let tOps := if mode == "mixed" then ops else ops.map fun (kd, k) => (kd + 2, k)
      let pOps := ops.map fun (kd, k) => (persistK kd, k)
      total := total + 1
      for fixed in [false, true] do
        let t := run fixed cfg tOps
        let p := run fixed cfg pOps
        let cd := !(p.toList.isPerm t.toList) || p.size != t.size
        let od := !(agreeB false 13 t.root p.root)
        if fixed then
          if cd then cF := cF + 1
          if od then oF := oF + 1
        else
          if cd then
            cS := cS + 1
            if firstC.isNone then firstC := some tOps
          if od then oS := oS + 1
    IO.println s!"{cname} {mode} length <= {len}: sequences {total}; stock: contents differ {cS}, node by node differ {oS}; fixed: contents differ {cF}, node by node differ {oF}"
  match firstC with
  | some ops => IO.println s!"  first stock contents difference: {String.intercalate " " (ops.map opStr)} (twin: every step persistent)"
  | none => pure ()

def show' : IO Unit := do
  IO.println s!"(keys (hash-map 1 :a 7676047846 :a)): {keysOf m0}"
  IO.println s!"(keys (assoc m 1 :b)): stock {keysOf (assocP m0 k1)}, fixed {keysOf (assocF m0 k1 1)}"
  IO.println s!"(keys (assoc m 1 :a)): stock {keysOf ((m0.add mapCfg (k1, 0)).run {}).1}, fixed {keysOf (assocF m0 k1 0)}"
  IO.println s!"(seq (conj (hash-set 1 7676047846) 1)): stock {((s0.add setCfg k1).run {}).1.toList}, fixed {((addRootF setCfg s0 k1).run {}).1.toList}"
  IO.println s!"transient chain / persistent chain keys: stock {keysOf tChain} / {keysOf pChain}, fixed {keysOf tChainF} / {keysOf pChainF}"
  IO.println s!"(assoc! (transient m) 1 :b) keys: stock {keysOf ((m0.addMut mapCfg tokT (k1, 1)).run {}).1}, fixed {keysOf ((addMutRootF mapCfg tokT m0 (k1, 1)).run {}).1}"
  IO.println s!"H9-1 abstract (a=1 q=2 b=3): stock transient {h91T.toList} persistent {h91P.toList}; fixed {h91TF.toList} {h91PF.toList}; control {h91Tc.toList} {h91Pc.toList}"

def h91 : IO Unit := do
  let a := "0.00000000000000000000000002084477"
  let q := "0.00000000000000011000000000687110"
  let b := "0.00000000000000023000000001916567"
  let pool := #[dec a, dec q, dec b]
  let T := Tables.mk' pool false Fix.none
  IO.println s!"jank hashes (round 3's cpp_dec_float replica): a {(jH Fix.none (pool[0]!)).toNat} q {(jH Fix.none (pool[1]!)).toNat} b {(jH Fix.none (pool[2]!)).toNat} (C++ on boost: 3969516785 each)"
  IO.println s!"jank =: (= a q) {T.J 0 1} (= q b) {T.J 1 2} (= a b) {T.J 0 2}; Clojure =: (= a q) {T.C 0 1} (= q b) {T.C 1 2} (= a b) {T.C 0 2}"
  let ops : List (Nat × Nat) := [(2, 0), (2, 2), (2, 0), (3, 1)]
  let cfg := T.cfg
  for fixed in [false, true] do
    let t := run fixed cfg ops
    let p := run fixed cfg (ops.map fun (kd, k) => (persistK kd, k))
    let nm := fun (l : List Nat) => l.map fun i => match i with | 0 => "a" | 1 => "q" | _ => "b"
    IO.println s!"{if fixed then "fixed" else "stock"}: (persistent! (-> (transient #\{}) (conj! a) (conj! b) (conj! a) (disj! q)))) {nm t.toList}; (-> #\{} (conj a) (conj b) (conj a) (disj q)) {nm p.toList}"
  IO.println "Clojure 1.12.3: both #{a b} (its = is exact; .r9-scratch/champ/clj)"

def main (args : List String) : IO Unit := do
  match args with
  | ["show"] => show'
  | ["h91"] => h91
  | ["seqs", c, n, m] => seqs c n.toNat! m
  | _ => IO.println "usage: jank9-champ show | h91 | seqs lawful|nontrans|per|asym N pure|mixed"

import Jank.R8.Champ.Agree
import Jank.R8.Champ.Programs
import Jank.R8.Champ.Seq

/-!
Round 8 driver, CHAMP (`jank8-champ show | seqs N`).

- `show`: H8-1's keys on the replica (jank's long hash, round 3's champ): the two keys' hashes, the
  keys of `(hash-map 1 :a 7676047846 :a)` before and after `(assoc m 1 :b)` and `(assoc m 7676047846 :b)`,
  the transient and persistent chains, and the set forms.
- `seqs N`: every sequence of at most N steps `add k` / `sub k` over the keys 0..5 with the hash
  `k / 2` (three pairs of keys of one full hash, so collision nodes at every length) and `==`, run once
  as persistent steps and once as transient steps under one owner token (`assoc!`/`dissoc!` inside one
  transient), from `champ::empty()`. Counted: sequences whose two results differ in contents (expected
  0: round 7's `buildT_same_keys`), differ node by node up to collision order (`Agree` with permuted
  collision lists; not proved for sequences), and differ node by node exactly (collision order).
-/

open Jank.R3.Immer.Champ Jank.R6.Champ Jank.R8.Champ Jank.R8.Champ.Programs

/-- `Agree` as a Boolean (`perm`: collision lists compared as multisets). -/
def agreeB (perm : Bool) : Nat → Node Nat → Node Nat → Bool
  | 0, A, B => if perm then A.collisions.isPerm B.collisions else A.collisions == B.collisions
  | r + 1, A, B => (List.range 32).all fun d =>
    match slot A d, slot B d with
    | .empty, .empty => true
    | .data x, .data y => x == y
    | .child a, .child b => agreeB perm r a b
    | _, _ => false

def pairCfg : Cfg Nat Nat where
  hashT n := n / 2
  hashK n := n / 2
  eqTT a b := a == b
  eqTK a k := a == k

inductive SOp where
  | add (k : Nat)
  | sub (k : Nat)

def runP (ops : List SOp) : Champ Nat := Id.run do
  let mut c : Champ Nat := Champ.empty
  let mut al : Al := {}
  for op in ops do
    let (c', al') := match op with
      | .add k => (c.add pairCfg k).run al
      | .sub k => (c.sub pairCfg k).run al
    c := c'; al := al'
  return c

def runT (ops : List SOp) : Champ Nat := Id.run do
  let mut c : Champ Nat := Champ.empty
  let mut al : Al := {}
  for op in ops do
    let (c', al') := match op with
      | .add k => (c.addMut pairCfg 7 k).run al
      | .sub k => (c.subMut pairCfg 7 k).run al
    c := c'; al := al'
  return c

def allOps : List SOp := (List.range 6).map SOp.add ++ (List.range 6).map SOp.sub

def opStr : SOp → String
  | .add k => s!"(assoc {k})"
  | .sub k => s!"(dissoc {k})"

def seqs (n : Nat) : IO Unit := do
  let mut total := 0
  let mut contents := 0
  let mut perm := 0
  let mut exact := 0
  let mut firstExact : Option (List SOp) := none
  let mut frontier : List (List SOp) := [[]]
  for len in List.range (n + 1) do
    let mut next : List (List SOp) := []
    for ops in frontier do
      let p := runP ops
      let t := runT ops
      total := total + 1
      if !(p.toList.isPerm t.toList) || p.size != t.size then contents := contents + 1
      if !(agreeB true 13 t.root p.root) then perm := perm + 1
      if !(agreeB false 13 t.root p.root) then
        exact := exact + 1
        if firstExact.isNone then firstExact := some ops
      if len < n then
        for o in allOps do next := (ops ++ [o]) :: next
    frontier := next
    IO.println s!"length <= {len}: sequences {total}, contents differ {contents}, node shape differs (collision order ignored) {perm}, collision order differs {exact}"
  match firstExact with
  | some ops => IO.println s!"first with another collision order: {String.intercalate " " (ops.map opStr)}"
  | none => pure ()

def show' : IO Unit := do
  IO.println s!"jank hash of 1: {hLong k1}; of 7676047846: {hLong k2}"
  IO.println s!"(keys (hash-map 1 :a 7676047846 :a)): {keysOf m0}"
  IO.println s!"(keys (assoc m 1 :b)): {keysOf (assocP m0 k1)}"
  IO.println s!"(keys (assoc m 7676047846 :b)): {keysOf (assocP m0 k2)}"
  IO.println s!"transient chain keys: {keysOf tChain}; persistent chain keys: {keysOf pChain}"
  IO.println s!"(seq (hash-set 1 7676047846)): {s0.toList}"
  IO.println s!"(seq (conj s 1)): {((s0.add setCfg k1).run {}).1.toList}"
  IO.println s!"(seq (conj s 7676047846)): {((s0.add setCfg k2).run {}).1.toList}"
  IO.println s!"(keys (assoc m 1 :a)): {keysOf ((m0.add mapCfg (k1, 0)).run {}).1}"
  IO.println s!"(keys (persistent! (assoc! (transient m) 1 :b))): {keysOf ((m0.addMut mapCfg tokT (k1, 1)).run {}).1}"
  IO.println s!"transient chain before its last assoc!: {keysOf tPrefix}"

def main (args : List String) : IO Unit := do
  match args with
  | ["show"] => show'
  | ["seqs", n] => seqs n.toNat!
  | _ => IO.println "usage: jank8-champ show | seqs N"

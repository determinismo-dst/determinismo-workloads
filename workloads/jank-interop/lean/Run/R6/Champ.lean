import Jank.R6.Champ.Breaks
import Jank.R6.Champ.Mut
import Jank.R3.Immer.Objects

/-!
Round 6 driver, CHAMP (`jank6-champ show | walk N`).

- `show`: the deviations' programs on the replica with round 1's full value model (jank's
  `to_hash` and `equal` per type, `Jank.Equality`), through immer's CHAMP (round 3's replica).
- `walk N`: every sequence of at most `N` operations `conj`/`disj` of a pool value on a hash set
  (from `#{}`), after each step comparing `count`, `(count (seq s))` and `contains?` of every pool
  value with Clojure's set (membership by `Util.equiv`, which starts with identity: each pool value
  is one object, so `##NaN` is identical to itself, as when it comes through a fn parameter).
  Disagreements are classed: `nan` (a self-unequal value: V48's class), `static` (the same miss
  on the one-element set: D12 as round 1 stated it), `path` (found in the one-element set, missed
  here: the law-1 break), `count`.
-/

open Jank.R3.Immer.Champ Jank.R3.Immer.Objects
open Jank.Equality (V)

def pool : Array V := #[.real 0, .real 0x8000000000000000, .real 0x4000000000000000, .real 0x3FF0000000000000,
  .int 1, .big 1, .real 0x7FF8000000000000, .int 3, .list [], .lazy [], .vec []]

def poolName (i : Nat) : String :=
  #["0.0", "-0.0", "2.0", "1.0", "1", "1N", "##NaN", "3", "()", "(lazy-seq nil)", "[]"].getD i "?"

/-- A jank hash set over the replica, and Clojure's set beside it (pool indices). -/
structure St where
  c : Champ V
  al : Al
  clj : List Nat

def cContains (clj : List Nat) (k : Nat) : Bool :=
  clj.any fun i => i == k || cEq (pool.getD i .nil) (pool.getD k .nil)

def cConj (clj : List Nat) (k : Nat) : List Nat := if cContains clj k then clj else clj ++ [k]
def cDisj (clj : List Nat) (k : Nat) : List Nat :=
  clj.filter fun i => !(i == k || cEq (pool.getD i .nil) (pool.getD k .nil))

def jContains (c : Champ V) (k : Nat) : Bool := (c.get setCfg (pool.getD k .nil)).isSome

def single (x : Nat) : Champ V := ((Champ.empty.add setCfg (pool.getD x .nil)).run {}).1

inductive Op where
  | conj (i : Nat)
  | disj (i : Nat)

def Op.code : Op → String
  | .conj i => s!"(conj {poolName i})"
  | .disj i => s!"(disj {poolName i})"

def step (st : St) : Op → St
  | .conj i =>
    let (c, al) := (st.c.add setCfg (pool.getD i .nil)).run st.al
    { c, al, clj := cConj st.clj i }
  | .disj i =>
    let (c, al) := (st.c.sub setCfg (pool.getD i .nil)).run st.al
    { c, al, clj := cDisj st.clj i }

structure Tally where
  states : Nat := 0
  nan : Nat := 0
  static : Nat := 0
  path : Nat := 0
  count : Nat := 0
  countSeq : Nat := 0
  firsts : List String := []

def note (t : Tally) (cls : String) (msg : String) : Tally :=
  let t := match cls with
    | "nan" => { t with nan := t.nan + 1 }
    | "static" => { t with static := t.static + 1 }
    | "path" => { t with path := t.path + 1 }
    | "count" => { t with count := t.count + 1 }
    | _ => { t with countSeq := t.countSeq + 1 }
  if t.firsts.any (·.startsWith (cls ++ ":")) then t else { t with firsts := t.firsts ++ [cls ++ ": " ++ msg] }

def check (t : Tally) (st : St) (trace : String) : Tally := Id.run do
  let mut t := { t with states := t.states + 1 }
  if st.c.size != st.c.toList.length then
    t := note t "count-seq" s!"{trace}: count {st.c.size} vs (count (seq s)) {st.c.toList.length}"
  if st.c.size != st.clj.length then
    let cls := if st.clj.contains 6 then "nan" else "count"
    t := note t cls s!"{trace}: count jank {st.c.size} Clojure {st.clj.length}"
  for k in List.range pool.size do
    let j := jContains st.c k
    let c := cContains st.clj k
    if j != c then
      -- the stored value Clojure finds
      let x? := st.clj.find? fun i => i == k || cEq (pool.getD i .nil) (pool.getD k .nil)
      let cls := if k == 6 then "nan" else
        match x? with
        | some x => if jContains (single x) k then "path" else "static"
        | none => "static"
      t := note t cls s!"{trace} (contains? s {poolName k}): jank {j} Clojure {c}"
  return t

partial def walk (n : Nat) (st : St) (trace : String) (t : Tally) : Tally :=
  let t := check t st trace
  if n == 0 then t else
    let ops := (List.range pool.size).flatMap fun i => [Op.conj i, Op.disj i]
    ops.foldl (fun t op => walk (n - 1) (step st op) (trace ++ " " ++ op.code) t) t

def showAll : IO Unit := do
  let z := pool.getD 0 .nil
  let nz := pool.getD 1 .nil
  let two := pool.getD 2 .nil
  let one := pool.getD 3 .nil
  let nan := pool.getD 6 .nil
  let s1 := ((Champ.empty.add setCfg z).run {}).1
  let s2 := ((s1.add setCfg two).run {}).1
  let s3 := ((s2.sub setCfg two).run {}).1
  let s4 := ((s1.add setCfg one).run {}).1
  IO.println s!"jank hashes: 0.0 {jHash z}, -0.0 {jHash nz}, 2.0 {jHash two}, 1.0 {jHash one}; (= 0.0 -0.0) {jEq z nz}"
  IO.println s!"(contains? #\{0.0} -0.0): {(s1.get setCfg nz).isSome}   Clojure true"
  IO.println s!"(contains? (conj #\{0.0} 2.0) -0.0): {(s2.get setCfg nz).isSome}   Clojure true"
  IO.println s!"(contains? (disj (conj #\{0.0} 2.0) 2.0) -0.0): {(s3.get setCfg nz).isSome}   Clojure true"
  IO.println s!"(contains? (conj #\{0.0} 1.0) -0.0): {(s4.get setCfg nz).isSome}   Clojure true"
  let m1 := ((Champ.empty.add mapCfg (z, .kw "a")).run {}).1
  let m2 := ((m1.add mapCfg (two, .kw "b")).run {}).1
  IO.println s!"(get (hash-map 0.0 :a) -0.0): {((m1.get mapCfg nz).map (fun (p : V × V) => p.2.code))}   Clojure :a"
  IO.println s!"(get (hash-map 0.0 :a 2.0 :b) -0.0): {((m2.get mapCfg nz).map (fun (p : V × V) => p.2.code))}   Clojure :a"
  let n2 := ((((Champ.empty.add setCfg nan).run {}).1.add setCfg nan).run {}).1
  IO.println s!"NaN: (= x x) {jEq nan nan}; (count (hash-set x x)) {n2.size}; (count (seq ...)) {n2.toList.length}; (contains? (hash-set x) x) {((((Champ.empty.add setCfg nan).run {}).1).get setCfg nan).isSome}   Clojure 1 1 true"

def main (args : List String) : IO Unit := do
  match args with
  | ["show"] => showAll
  | ["walk", n] =>
    let t0 ← IO.monoMsNow
    let t := walk n.toNat! { c := Champ.empty, al := {}, clj := [] } "#{}" {}
    let t1 ← IO.monoMsNow
    IO.println s!"walk: every sequence of at most {n} conj/disj over {pool.size} pool values ({2 * pool.size} operations), complete"
    IO.println s!"  states checked {t.states}; disagreements: nan {t.nan}, static {t.static}, path {t.path}, count {t.count}, count-vs-seq {t.countSeq}  ({(t1 - t0) / 1000} s)"
    for f in t.firsts do IO.println s!"  first {f}"
  | _ => IO.println "usage: jank6-champ show | walk N"

import Jank.R7.Champ.Vals
import Jank.R3.Immer.Champ

/-!
# Round 7, CHAMP: every reachable state of a jank hash set or map, beside Clojure's

A state is a jank collection (round 3's replica of immer's champ over pool indices, with jank's
`=` and `hash` from `Vals`, or with chosen known causes fixed) in persistent or transient mode,
beside Clojure's collection (the stored representatives; membership by `Util.equiv`: identity, then
`=`). From `#{}` (or `(hash-map)`), the operations are:

- sets: `conj x`, `disj x`, `transient`; in a transient: `conj! x`, `disj! x`, `persistent!`;
- maps: `assoc k v`, `dissoc k`, `transient`; in a transient: `assoc! k v`, `dissoc! k`, `persistent!`
  (two values `:a`, `:b`);

with every pool value as each operand (each pool value one object: values reach the collection
through a fn parameter). States are merged when equal up to node ids (which only name objects):
the champ's shape and values, its owner marks relative to the live transient's token, and Clojure's
contents. The breadth-first walk is complete to the depth reached; when the frontier empties, every
sequence of every length has been covered.

After every operation: `count` against Clojure's; `(count (seq s))` against `count`; `contains?`
(sets) or `get` (maps) of every pool value; which representatives `seq` yields (S59's class); and for
sets `(= s (apply hash-set (seq clj)))` (jank's persistent_hash_set::equal 55-81: same count, each
element `contains?`'d by the other side), Clojure true.
-/

namespace Jank.R7.Champ.Walk

open Jank.R3.Immer.Champ Jank.R7.Champ.Vals

/-- The pool, its precomputed hashes and equality tables. -/
structure Tables where
  pool : Array W
  isMap : Bool
  fx : Fix
  hash : Array Nat
  jeq : Array (Array Bool)
  ceq : Array (Array Bool)

def Tables.mk' (pool : Array W) (isMap : Bool) (fx : Fix) : Tables :=
  { pool, isMap, fx
    hash := pool.map fun w => (jH fx w).toNat
    jeq := pool.map fun a => pool.map fun b => jEq fx a b
    ceq := pool.map fun a => pool.map fun b => cEq a b }

def Tables.key (T : Tables) (e : Nat) : Nat := if T.isMap then e / 2 else e

def Tables.J (T : Tables) (a b : Nat) : Bool := (T.jeq.getD a #[]).getD b false
def Tables.C (T : Tables) (a b : Nat) : Bool := (T.ceq.getD a #[]).getD b false

/-- immer's `Hash`/`Equal` on stored elements (pool index, or `2·key + value` for maps): `Equal{}(stored,
query)`; with the identity fix, identity first. -/
def Tables.cfg (T : Tables) : Cfg Nat Nat where
  hashT e := T.hash.getD (T.key e) 0
  hashK k := T.hash.getD k 0
  eqTT a b := (T.fx.identity && T.key a == T.key b) || T.J (T.key a) (T.key b)
  eqTK a k := (T.fx.identity && T.key a == k) || T.J (T.key a) k

/-! ## Clojure's side -/

def Tables.cMatch (T : Tables) (e k : Nat) : Bool := T.key e == k || T.C (T.key e) k

def Tables.cFind (T : Tables) (clj : List Nat) (k : Nat) : Option Nat := clj.find? fun e => T.cMatch e k

def Tables.cAdd (T : Tables) (clj : List Nat) (e : Nat) : List Nat :=
  match T.cFind clj (T.key e) with
  | some old =>
    -- a set keeps its element; a map keeps its key and takes the new value
    if T.isMap then clj.map fun x => if x == old then 2 * T.key old + e % 2 else x else clj
  | none => clj ++ [e]

def Tables.cSub (T : Tables) (clj : List Nat) (k : Nat) : List Nat := clj.filter fun e => !T.cMatch e k

/-! ## jank's side -/

structure JS where
  c : Champ Nat
  al : Al
  tok : Option Nat

def JS.empty : JS := { c := Champ.empty, al := {}, tok := none }

inductive Op where
  | add (e : Nat)
  | sub (k : Nat)
  | trans
  | pers

def Tables.opCode (T : Tables) : Op → String
  | .add e =>
    if T.isMap then s!"(assoc {(T.pool.getD (e / 2) .nil).code} {if e % 2 == 0 then ":a" else ":b"})"
    else s!"(conj {(T.pool.getD e .nil).code})"
  | .sub k => if T.isMap then s!"(dissoc {(T.pool.getD k .nil).code})" else s!"(disj {(T.pool.getD k .nil).code})"
  | .trans => "transient"
  | .pers => "persistent!"

def Tables.opCodeT (T : Tables) (inT : Bool) (op : Op) : String :=
  if inT then match op with
    | .add e => if T.isMap then s!"(assoc! {(T.pool.getD (e / 2) .nil).code} {if e % 2 == 0 then ":a" else ":b"})"
                else s!"(conj! {(T.pool.getD e .nil).code})"
    | .sub k => if T.isMap then s!"(dissoc! {(T.pool.getD k .nil).code})" else s!"(disj! {(T.pool.getD k .nil).code})"
    | o => T.opCode o
  else T.opCode op

/-- jank's step (with S59's fix when `keepOld`: an `=` element or key already stored is kept). -/
def Tables.jStep (T : Tables) (s : JS) : Op → JS
  | .trans =>
    let (t, al) := (fresh : M Nat).run s.al
    { s with al, tok := some t }
  | .pers =>
    -- `persistent()` on the transient: the champ is shared, the transient's token replaced
    let (_, al) := (fresh : M Nat).run s.al
    { s with al, tok := none }
  | .add e =>
    let cfg := T.cfg
    let e' := if T.fx.keepOld then
        match s.c.get cfg (T.key e) with
        | some old => if T.isMap then 2 * T.key old + e % 2 else old
        | none => e
      else e
    if T.fx.keepOld && !T.isMap && (s.c.get cfg (T.key e)).isSome then s else
    match s.tok with
    | none => let (c, al) := (s.c.add cfg e').run s.al; { s with c, al }
    | some t => let (c, al) := (s.c.addMut cfg t e').run s.al; { s with c, al }
  | .sub k =>
    let cfg := T.cfg
    match s.tok with
    | none => let (c, al) := (s.c.sub cfg k).run s.al; { s with c, al }
    | some t => let (c, al) := (s.c.subMut cfg t k).run s.al; { s with c, al }

/-! ## State keys -/

partial def serNode (own : Option Nat) : Node Nat → String
  | .collision _ tok xs => "C" ++ (if own == some tok then "o" else "") ++ toString xs
  | n@(.inner _ tok nm dm v cs) =>
    let vm := match v with | some vs => if own == some vs.tok then "o" else "" | none => ""
    "I" ++ (if own == some tok then "o" else "") ++ toString nm ++ "," ++ toString dm ++ vm ++
      toString (n.values.take n.dataCount) ++ "(" ++ ",".intercalate ((cs.take n.childrenCount).map (serNode own)) ++ ")"

def stateKey (s : JS) (clj : List Nat) : String :=
  serNode s.tok s.c.root ++ "|" ++ toString s.c.size ++ "|" ++ (if s.tok.isSome then "T" else "P") ++ "|" ++
    toString (clj.mergeSort (· ≤ ·))

/-! ## Checks -/

structure Tally where
  states : Nat := 0
  count : Nat := 0
  countSeq : Nat := 0
  contains : Nat := 0
  getv : Nat := 0
  repr : Nat := 0
  seteq : Nat := 0
  firsts : Array String := #[]
  /-- Pool keys involved in `contains?`/`get` disagreements: (query, found-by) counts. -/
  pairs : Std.HashMap (Nat × Nat) Nat := {}
  deriving Inhabited

def Tally.total (t : Tally) : Nat := t.count + t.countSeq + t.contains + t.getv + t.repr + t.seteq

def Tally.note (t : Tally) (cls msg : String) : Tally :=
  let t := match cls with
    | "count" => { t with count := t.count + 1 }
    | "count-seq" => { t with countSeq := t.countSeq + 1 }
    | "contains" => { t with contains := t.contains + 1 }
    | "get" => { t with getv := t.getv + 1 }
    | "repr" => { t with repr := t.repr + 1 }
    | _ => { t with seteq := t.seteq + 1 }
  if (t.firsts.filter (·.startsWith (cls ++ ":"))).size ≥ 3 then t else { t with firsts := t.firsts.push (cls ++ ": " ++ msg) }

def Tables.build (T : Tables) (clj : List Nat) : Champ Nat :=
  ((clj.foldlM (fun (c : Champ Nat) e => c.add T.cfg e) (Champ.empty : Champ Nat)).run {}).1

/-- The disagreements of one state: (class, query pool index or none, text after the trace). -/
def Tables.check (T : Tables) (s : JS) (clj : List Nat) : List (String × Option (Nat × Nat) × String) := Id.run do
  let cfg := T.cfg
  let mut out : List (String × Option (Nat × Nat) × String) := []
  let jl := s.c.toList
  if s.c.size != jl.length then
    out := ("count-seq", none, s!": count {s.c.size} vs (count (seq s)) {jl.length}") :: out
  if s.c.size != clj.length then
    out := ("count", none, s!": count jank {s.c.size} Clojure {clj.length}") :: out
  for k in List.range T.pool.size do
    let jg := s.c.get cfg k
    let cg := T.cFind clj k
    if jg.isSome != cg.isSome then
      let partner := match cg with | some e => T.key e | none => match jg with | some e => T.key e | none => k
      out := ("contains", some (k, partner),
        s!" ({if T.isMap then "get m" else "contains? s"} {(T.pool.getD k .nil).code}): jank {if T.isMap then (match jg with | some a => if a % 2 == 0 then ":a" else ":b" | none => "nil") else toString jg.isSome} Clojure {if T.isMap then (match cg with | some a => if a % 2 == 0 then ":a" else ":b" | none => "nil") else toString cg.isSome}") :: out
    else if T.isMap then
      match jg, cg with
      | some a, some b => if a % 2 != b % 2 then
          out := ("get", some (k, T.key b), s!" (get m {(T.pool.getD k .nil).code}): jank {if a % 2 == 0 then ":a" else ":b"} Clojure {if b % 2 == 0 then ":a" else ":b"}") :: out
      | _, _ => pure ()
  let js := (jl.map T.key).mergeSort (· ≤ ·)
  let cs := (clj.map T.key).mergeSort (· ≤ ·)
  if js != cs && jl.length == clj.length then
    out := ("repr", none, s!": (seq s) holds {js.map fun i => (T.pool.getD i .nil).code} Clojure {cs.map fun i => (T.pool.getD i .nil).code}") :: out
  if !T.isMap then
    let fresh := T.build clj
    let eq := s.c.size == fresh.size && jl.all fun e => (fresh.get cfg e).isSome
    if !eq then
      out := ("set=", none, s!": (= s (apply hash-set {cs.map fun i => (T.pool.getD i .nil).code})): jank false Clojure true") :: out
  return out

/-- The operations available in a state. -/
def Tables.ops (T : Tables) (s : JS) : List Op :=
  let n := T.pool.size
  let adds := if T.isMap then (List.range (2 * n)).map Op.add else (List.range n).map Op.add
  let subs := (List.range n).map Op.sub
  adds ++ subs ++ [if s.tok.isSome then Op.pers else Op.trans]

structure Result where
  tally : Tally
  depth : Nat
  completeDepth : Nat
  complete : Bool
  frontier : Nat

def traceOf (T : Tables) (nodes : Array (Nat × Bool × Op)) (root : String) : Nat → Nat → String
  | 0, _ => root
  | fuel + 1, i =>
    if i == 0 then root else
    let (p, inT, op) := nodes.getD i (0, false, .trans)
    traceOf T nodes root fuel p ++ " " ++ T.opCodeT inT op

/-- Breadth-first over distinct states, to depth `maxDepth` or until no new state appears, stopping
at `maxStates` distinct states. Prints each depth as it completes. -/
def Tables.bfs (T : Tables) (maxDepth maxStates : Nat) : IO Result := do
  let s0 := JS.empty
  let root := if T.isMap then "(hash-map)" else "#{}"
  let mut seen : Std.HashSet String := {}
  seen := seen.insert (stateKey s0 [])
  let mut nodes : Array (Nat × Bool × Op) := #[(0, false, .trans)]
  let mut tally : Tally := { states := 1 }
  let mut frontier : Array (JS × List Nat × Nat) := #[(s0, [], 0)]
  let mut depth := 0
  let mut completeDepth := 0
  let mut stopped := false
  while depth < maxDepth && !frontier.isEmpty && !stopped do
    let mut next : Array (JS × List Nat × Nat) := #[]
    for (s, clj, ni) in frontier do
      if !stopped then
      for op in T.ops s do
        if !stopped then
        let s' := T.jStep s op
        let clj' := match op with
          | .add e => T.cAdd clj e
          | .sub k => T.cSub clj k
          | _ => clj
        let sk := stateKey s' clj'
        if !seen.contains sk then
          if seen.size ≥ maxStates then
            stopped := true
          else
            seen := seen.insert sk
            nodes := nodes.push (ni, s.tok.isSome, op)
            let idx := nodes.size - 1
            tally := { tally with states := tally.states + 1 }
            for (cls, pr, msg) in T.check s' clj' do
              let t0 : Tally := match cls with
                | "count" => { tally with count := tally.count + 1 }
                | "count-seq" => { tally with countSeq := tally.countSeq + 1 }
                | "contains" => { tally with contains := tally.contains + 1 }
                | "get" => { tally with getv := tally.getv + 1 }
                | "repr" => { tally with repr := tally.repr + 1 }
                | _ => { tally with seteq := tally.seteq + 1 }
              let t1 : Tally := match pr with
                | some pq => { t0 with pairs := t0.pairs.insert pq ((t0.pairs.getD pq 0) + 1) }
                | none => t0
              let nf : Nat := (t1.firsts.filter (fun (x : String) => x.startsWith (cls ++ ":"))).size
              tally := if nf ≥ 3 then t1
                else { t1 with firsts := t1.firsts.push (cls ++ ": " ++ traceOf T nodes root 10000 idx ++ msg) }
            next := next.push (s', clj', idx)
    frontier := next
    depth := depth + 1
    if !stopped then
      completeDepth := depth
      IO.println s!"    depth {depth} complete: {seen.size} states; frontier {frontier.size}; disagreements so far {tally.total}"
      (← IO.getStdout).flush
  return { tally, depth, completeDepth, complete := frontier.isEmpty && !stopped, frontier := frontier.size }

end Jank.R7.Champ.Walk

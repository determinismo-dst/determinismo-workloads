import Elle.ClosedPredicate
import Elle.Spec
import Elle.GenCP

/-!
# Closed predicate: the DSG under the checker's own reading, from the definitions

Round 1 judged D9 and D10 "under the checker's own version order". This writes that reading
down independently of Elle's edge code (`versions-after`, `version<`, the explainers):

- versions: `:init`'s, then every `:ok` or `:info` transaction's writes in history order, an
  unborn version before a key's first write (closed_predicate.clj:191-218; the namespace
  docstring's universe);
- every `:ok` and `:info` transaction committed (Elle's version order holds their writes);
- a read of `nil` resolved as `resolve-version` says (closed_predicate.clj:300), a predicate
  read's version set as `version-set` infers it (closed_predicate.clj:367): what it read, what
  elimination proves, and unborn when every version matched ("the most charitable
  interpretation", 393-403);
- Adya's edges: ww between successive versions; wr from a version's writer to its reader; rw from
  an item read to the next version's writer; a predicate anti-dependency to the writer of every
  later version that changes the predicate's match (Adya, thesis §3.2.4: "changes the matches";
  unborn precedes every version, 266); a predicate read-dependency from the writer of a version
  in the version set; real-time and process edges as round 1's specification draws them.
-/

namespace Elle.CPSpec

open Elle Elle.ClosedPredicate Elle.Spec

/-- The writer of version `v` of key `k`. -/
def writerOf (h : List Op) (k : Nat) (v : Val) : Option Nat :=
  (possible h).findSome? fun o => if (extWritesOp o).any (fun (k', v') => k' == k && v' == v) then some o.index else none

/-- Versions after `v` in `vs` (unborn precedes every version). -/
def laterThan (vs : List Val) (v : Val) : List Val :=
  if v == .unborn then vs.filter (· != .unborn)
  else match vs.findIdx? (· == v) with
    | some i => vs.drop (i + 1)
    | none => []

/-- The DSG under the checker's reading (`rowItems`: also count a predicate read's rows as item
reads, as Adya's formalism has them). -/
def dsg (h : History) (rowItems : Bool := false) : Graph := Id.run do
  let hl := h.toList
  let av := allVersions hl
  let committed := (possible hl).map (·.index)
  let mut g : Graph := committed.foldl Graph.addVertex {}
  -- ww
  for (k, vs) in av do
    let real := vs.filter (· != .unborn)
    for (a, b) in real.zip (real.drop 1) do
      match writerOf hl k a, writerOf hl k b with
      | some x, some y => if x != y then g := g.link x y Rels.WW
      | _, _ => pure ()
  let itemRead (g : Graph) (t k : Nat) (x : Val) : Graph :=
    let vs := versionsOf av k
    let g := match writerOf hl k x with
      | some w => if w != t then g.link w t Rels.WR else g
      | none => g
    match (laterThan vs x).head? with
    | some n => match writerOf hl k n with
      | some w => if w != t then g.link t w Rels.RW else g
      | none => g
    | none => g
  for o in oks hl do
    if o.f == .init then continue
    for m in o.value do
      match m.f with
      | .r =>
        if let some x := resolveVersion av m.k m.v then g := itemRead g o.index m.k x
      | .rp =>
        for (k, x) in versionSet av m do
          if x != .unborn then
            if let some w := writerOf hl k x then
              if w != o.index then g := g.link w o.index Rels.WRP
          for y in laterThan (versionsOf av k) x do
            if xor' (evalPred m.pred x) (evalPred m.pred y) then
              if let some w := writerOf hl k y then
                if w != o.index then g := g.link o.index w Rels.RWP
          if rowItems && (readMap m).any (·.1 == k) then g := itemRead g o.index k x
      | _ => pure ()
  -- process and real-time edges (round 1's specification)
  let txs := txnViews h
  return orderEdges g txs committed

/-- Cycle phenomena with item and predicate edges kept apart (Adya, thesis §3.2-3.3): G2-item
needs an item anti-dependency; G-single and G2 count either kind. -/
def cyclePhenP (g : Graph) (w d : Rels) (suffix : String) : List String :=
  let anti := Rels.RW ||| Rels.RWP
  let gd := g.project d
  let gall := g.project (d ||| anti)
  let edgesOf (r : Rels) := (g.edges.filter fun (_, _, x) => Rels.inter x r != 0).map fun (a, b, _) => (a, b)
  let g0 := hasCycle (g.project w)
  let g1c := hasCycle gd
  let gsingle := (edgesOf anti).any fun (a, b) => (reach gd b).contains a
  let g2 := (edgesOf anti).any fun (a, b) => (reach gall b).contains a
  let g2item := (edgesOf Rels.RW).any fun (a, b) => (reach gall b).contains a
  let gnonadj := hasCycle (Graph.seqExtension gd (g.project anti))
  (if g0 then ["G0" ++ suffix] else []) ++ (if g1c then ["G1c" ++ suffix] else []) ++
  (if gsingle then ["G-single" ++ suffix] else []) ++ (if g2 then ["G2" ++ suffix] else []) ++
  (if g2item then ["G2-item" ++ suffix] else []) ++
  (if gnonadj then ["G-nonadjacent" ++ suffix] else [])

def phen (h : History) (rowItems : Bool := false) : List String :=
  let g := dsg h rowItems
  let dw := Rels.WW
  let dd := Rels.WW ||| Rels.WR ||| Rels.WRP
  cyclePhenP g dw dd "" ++
  cyclePhenP g (dw ||| Rels.PROCESS) (dd ||| Rels.PROCESS) "-process" ++
  cyclePhenP g (dw ||| Rels.PROCESS ||| Rels.REALTIME) (dd ||| Rels.PROCESS ||| Rels.REALTIME) "-realtime"

/-- Round 1's proscriptions, with repeatable read's G2 as G2-item (Adya's PL-2.99). -/
def proscribedP (m : String) : List String :=
  let ps := (proscribed.lookup m).getD []
  if m == "repeatable-read" then ps.map fun p => if p == "G2" then "G2-item" else p else ps

def violates (h : History) (m : String) (rowItems : Bool := false) : Bool :=
  (phen h rowItems).any (proscribedP m).contains

/-- A step's relation in that DSG. -/
def stepIn (g : Graph) (a b : Nat) (s : Step) : Bool :=
  let r := g.edge a b
  match s.type with
  | "ww" | "wwp" => Rels.inter r Rels.WW != 0
  | "wr" => Rels.inter r Rels.WR != 0
  | "wrp" => Rels.inter r Rels.WRP != 0
  | "rw" => Rels.inter r Rels.RW != 0
  | "rwp" => Rels.inter r Rels.RWP != 0
  | "realtime" => Rels.inter r Rels.REALTIME != 0
  | "process" => Rels.inter r Rels.PROCESS != 0
  | _ => false

/-- The three fixes: `versions-after`'s paren, `version<` (`fixedVersionLt`), and D9's `:w`. -/
structure Fixes where
  versionsAfter : Bool := false
  versionLt : Bool := false
  write : Bool := false

/-- The follow-up's properties on one history: Elle (with fixes `f`) doesn't throw; each step of
each reported cycle is an edge of its kind in the specification's DSG; each model's verdict on
cycles equals the specification's. -/
def check (f : Fixes) (h : History) (models : List String) : Option (String × String) := Id.run do
  let g := dsg h
  for m in models do
    let opts : Opts := { models := some [m] }
    match analyze h (additionalGraphs opts) {} f.versionsAfter f.write [] f.versionLt with
    | .error e => return some ("thrown", s!"{m}: {e}")
    | .ok an =>
      let an := an.filter (·.1 != "predicate-read-miss")
      for (t, cs) in an do
        for c in cs do
          if let .cycle ops steps := c then
            for ((x, y), s) in (ops.zip (ops.drop 1)).zip steps do
              if !stepIn g x y s then
                return some ("explanation", s!"{t}: step {x}->{y} {s.type} key {s.key} is no such edge")
      let ev := (resultMap opts an).valid
      let sv := violates h m
      if ev == .false_ && !sv then return some ("soundness:" ++ m, s!"Elle invalid {(resultMap opts an).anomalyTypes}; no proscribed cycle")
      if ev == .true_ && sv then return some ("completeness:" ++ m, s!"Elle valid; the DSG has {phen h}")
  return none

end Elle.CPSpec

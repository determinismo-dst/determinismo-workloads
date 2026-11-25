import Elle.Model

/-!
# `:not` and `:also-not` against the lattice's definitions

`friendly-boundary` (consistency_model.clj:588-606) of an anomaly set: `impossible` =
`anomalies->impossible-models` (568), `:not` = `weakest-models impossible` (401, `most-models`
with `g/out`, 377), `:also-not` = the rest of `impossible`, each through `friendly-model-name`.
The docstring (588-595): ":not is the weakest set of consistency models invalidated by the given
anomaly, and also-not is the remaining set of stronger models".

`anomalies->impossible-models` is a union over the anomalies (each a reachability set), so every
anomaly set's boundary is a function of the union of its members' impossible sets: the distinct
unions reachable from the anomaly names are all the cases.

Definitions checked, for each such union `U`:
1. `U` is exactly the models that prohibit one of the anomalies (`anomalies-prohibited-by`,
   554: the other direction of the same lattice).
2. `:not` is the minimal elements of `U` under implication (no other model of `U` is implied).
3. `:also-not` is `U` without `:not`, and each of its models implies one of `:not`.
4. Friendly names neither merge two models of `U` nor put one name in both sets.
-/

namespace Elle.Boundary

open Elle Elle.Model

/-- Models strictly implied by `m` (reachable by one or more `g/out` steps). -/
def impliedBy (m : String) : List String := (bfs (dagOut models) [m]).filter (· != m)

/-- The minimal elements of `u`: no other member of `u` is implied by it. -/
def minimal (u : List String) : List String :=
  u.filter fun m => !(impliedBy m).any fun m' => m' != m && u.contains m'

/-- The distinct impossible-model sets of every anomaly set: closure of the singletons' sets
under union. -/
def allUnions (fuel : Nat := 100000) : List (List String) := Id.run do
  let singles := dedup (allAnomalyNames.map fun a => anomaliesToImpossibleModels [a])
  let mut seen : List (List String) := [[]]
  let mut frontier : List (List String) := [[]]
  let mut f := fuel
  while !frontier.isEmpty && f > 0 do
    f := f - 1
    let mut next : List (List String) := []
    for u in frontier do
      for s in singles do
        let v := sortedSet (u ++ s)
        if !seen.contains v && !next.contains v then next := next ++ [v]
    seen := seen ++ next
    frontier := next
  return seen

/-- A failure of a definition on union `u` (by a witness anomaly set), or none. -/
def checkUnion (as : List String) : Option String := Id.run do
  let u := anomaliesToImpossibleModels as
  -- 1. the other direction of the lattice
  let byProhibition := sortedSet ((allModelNames.filter (fun m =>
    (anomaliesProhibitedBy [m]).any as.contains)).map canonicalModelName)
  let uC := sortedSet (u.map canonicalModelName)
  if byProhibition != uC then
    return some s!"impossible {uC} differs from the models prohibiting one of {as}: {byProhibition}"
  -- 2-3. weakest and the rest
  let isNot := weakestModels u
  let mins := minimal u
  if sortedSet isNot != sortedSet mins then
    return some s!"weakest-models {sortedSet isNot} differs from the minimal elements {sortedSet mins}"
  let also := u.filter (!isNot.contains ·)
  for m in also do
    if !(impliedBy m).any isNot.contains then
      return some s!"also-not model {m} implies none of :not {isNot}"
  -- 4. friendly names
  let fr (l : List String) := l.map friendlyModelName
  if (dedup (fr u)).length != (dedup u).length then
    return some s!"friendly names merge models of {u}: {fr u}"
  let (n, a) := friendlyBoundary as
  if n.any a.contains then
    return some s!"a name in both :not {n} and :also-not {a}"
  return none

/-- A witness anomaly set for each union: greedily, the anomalies whose sets it contains. -/
def witness (u : List String) : List String :=
  allAnomalyNames.filter fun a => (anomaliesToImpossibleModels [a]).all u.contains

/-- Every union with its first failure. -/
def checkAll : Nat × List (List String × String) := Id.run do
  let us := allUnions
  let mut bad := []
  for u in us do
    let w := witness u
    if sortedSet (anomaliesToImpossibleModels w) != u then
      bad := bad ++ [(u, "no witness")]
      continue
    if let some e := checkUnion w then bad := bad ++ [(w, e)]
  return (us.length, bad)

end Elle.Boundary

/-
  Round 9: order_by combined with group_by, and `ecs_iter_set_group`,
  transcribed from flecs v4.2.0.

  - `flecs_query_cache_iter_init` (query/cache/cache_iter.c 11-37): with
    an order_by callback it sorts (`flecs_query_cache_sort_tables`,
    order_by.c 228-321: each changed table is sorted in place) and points
    the iterator at `cache->table_slices` (30-33).
  - `flecs_query_cache_build_sorted_tables` (order_by.c 212-222) builds the
    slices group by group: `flecs_query_cache_build_sorted_table_range`
    (91-208) merges the group's sorted tables into runs (`compare(e1, ptr1,
    e2, ptr2) > 0` picks the later table, 189-192).
  - `ecs_iter_set_group` (query/api.c 758-795) then sets `qit->tables =
    &group->tables`: the group's matches in insertion order, each a whole
    table.  The slices are not used, so the rows of the group's tables are
    not merged.

  Documentation: Queries.md "Sorting": "Sorted queries use a two-step
  process to return entities in a sorted order ... This second step is
  necessary to support datasets where ordered results have entities
  interleaved from multiple tables"; flecs.h `ecs_iter_set_group`: "This
  operation limits the results returned by the query to only the selected
  group ID".  flecs's own `GroupBy_group_by_w_sort_reverse_group_creation`
  expects the sorted results group by group.

  Property P-SO1 (new): the results of an order_by query come in order of
  the sorted component, group by group; `ecs_iter_set_group` limits them to
  one group and keeps that order.
-/
import FlecsLean.Search2

namespace Flecs.SortGroup

structure T where
  group : Nat
  vals : List Nat
  deriving Repr, BEq, Inhabited

structure Prog where
  tabs : List T
  setGroup : Option Nat
  deriving Repr, BEq, Inhabited

def insertSorted (v : Nat) : List Nat → List Nat
  | [] => [v]
  | x :: xs => if v < x then v :: x :: xs else x :: insertSorted v xs

def sortNat (l : List Nat) : List Nat := l.foldr insertSorted []

/-- `flecs_query_cache_build_sorted_table_range` for one group: repeatedly
    take the smallest head; ties keep the earlier table. -/
def merge (ts : List (List Nat)) : Nat → List Nat
  | 0 => []
  | f + 1 =>
    let heads := (List.range ts.length).filterMap (fun i => (ts.getD i []).head?.map (fun v => (i, v)))
    match heads with
    | [] => []
    | h :: hs =>
      let (i, v) := hs.foldl (fun (a : Nat × Nat) (b : Nat × Nat) => if a.2 > b.2 then b else a) h
      v :: merge (ts.set i ((ts.getD i []).drop 1)) f

def groupsOf (p : Prog) : List Nat := (p.tabs.map (·.group)).eraseDups

def results (p : Prog) : List Nat :=
  let sorted := p.tabs.map (fun t => { t with vals := sortNat t.vals })
  match p.setGroup with
  | none => (groupsOf p).flatMap (fun g =>
      let ts := (sorted.filter (·.group == g)).map (·.vals)
      merge ts (ts.foldl (· + ·.length) 0))
  | some g => (sorted.filter (·.group == g)).flatMap (·.vals)

def nondecreasing : List Nat → Bool
  | a :: b :: r => a ≤ b && nondecreasing (b :: r)
  | _ => true

def check (p : Prog) : List (String × String) :=
  let rs := results p
  match p.setGroup with
  | some g =>
    let want := sortNat ((p.tabs.filter (·.group == g)).flatMap (·.vals))
    if rs != want then
      [("P-SO1 order_by results in order", s!"after ecs_iter_set_group(group {g}), the order_by query returns {rs}, expected {want}: ecs_iter_set_group iterates the group's tables (query/api.c 787-791), not the sorted slices (cache_iter.c 30-33, order_by.c 212-222), so the group's tables are not merged")]
    else []
  | none =>
    let bad := (groupsOf p).filter (fun g =>
      let ts := ((p.tabs.filter (·.group == g)).map (fun t => sortNat t.vals))
      !nondecreasing (merge ts (ts.foldl (· + ·.length) 0)))
    if bad.isEmpty then [] else [("P-SO1 order_by results in order", s!"groups {bad} out of order")]

section
variable {m : Type → Type} [Monad m] [Pick m]

def genProg (ntabs nvals : Nat) : m Prog := do
  let mut ts := []
  for _ in [0:ntabs] do
    let g ← Pick.pick "sg.group" 2
    let mut vs := []
    for _ in [0:nvals] do vs := vs ++ [← Pick.pick "sg.val" 4]
    ts := ts ++ [{ group := g, vals := vs }]
  let k ← Pick.pick "sg.set" 3
  return { tabs := ts, setGroup := if k == 0 then none else some (k - 1) }

end

def cases : List (String × Prog) := [
  ("query_order_by_set_group_unsorted: group A has [1, 3] and [2, 4]; ecs_iter_set_group(A)",
    { tabs := [{ group := 0, vals := [1, 3] }, { group := 0, vals := [2, 4] }, { group := 1, vals := [0] }], setGroup := some 0 }),
  ("control: the same without ecs_iter_set_group",
    { tabs := [{ group := 0, vals := [1, 3] }, { group := 0, vals := [2, 4] }, { group := 1, vals := [0] }], setGroup := none }),
  ("control: one table in the group",
    { tabs := [{ group := 0, vals := [3, 1] }, { group := 1, vals := [0] }], setGroup := some 0 }) ]

end Flecs.SortGroup

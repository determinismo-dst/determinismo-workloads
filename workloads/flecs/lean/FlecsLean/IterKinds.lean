/-
  Round 7: the iterator a system's callback or run callback receives, and
  the iterator functions that check which one it is, transcribed from flecs
  v4.2.0.

  `flecs_run_system` (addons/system/system.c 22-161):
  - `qit = ecs_query_iter(stage, query)` (80-81): `next = ecs_query_next`;
    `flecs_query_iter_constrain` (query/engine/eval_iter.c 61-155) sets
    `EcsIterTrivialCached` for a cached query whose cache is trivial, with
    no order_by and without `EcsQueryHasChangeDetection` (127-140);
  - with more than one stage and a multi-threaded system,
    `it = ecs_worker_iter(it, stage_index, stage_count)` (97-100):
    `next = ecs_worker_next` (src/iter.c 1008-1034); its private data is the
    worker's, and `ecs_worker_next` copies only the part of the chained
    iterator before `priv_` (1053-1054);
  - with a run callback (109-125): for `qit` with `EcsIterTrivialCached`,
    `it->next = flecs_query_trivial_cached_next` (119-121), then `run(it)`;
  - without (126-151): `qit` is iterated with `flecs_query_trivial_cached_next`
    or `ecs_query_next`, its `next` field left `ecs_query_next`, and the
    callback gets `&qit`; a worker iterator is iterated with
    `ecs_iter_next` and the callback gets it.
  The functions called on that iterator:
  - `ecs_iter_changed` (query/cache/change_detection.c 676-711):
    `ecs_check(it->next == ecs_query_next, ECS_UNSUPPORTED)` (680) — a debug
    build aborts; a release build reads `it->priv_.iter.query.elem` (704-705),
    which for a worker iterator is the field copied when the worker iterator
    was made (`result = *it`, iter.c 1020), before the first result: NULL;
  - `ecs_iter_skip` (714-721): `ecs_assert(it->next == ecs_query_next,
    ECS_INVALID_PARAMETER)`; in a release build the skip flag is set on the
    worker iterator, whose flags `ecs_worker_next` overwrites from the query
    iterator, which never sees it.
  Documented:
  - system.h 55-66 (`ecs_system_desc_t::run`): "When a system is
    multithreaded and/or paged, the iterator can be either a worker or a
    paged iterator ... An implementation can test whether the iterator is a
    query iterator by testing whether the it->next value is equal to
    ecs_query_next()";
  - flecs.h `ecs_iter_changed`: "must be used in combination with a query
    that supports change detection (e.g., is cached)";
  - Queries.md "Change Detection": change detection is enabled with
    `EcsQueryDetectChanges`; "If no changes are made to the iterated table,
    the skip function can be called to prevent marking the matched
    components as dirty"; Systems.md: systems use cached queries.
-/
import FlecsLean.Search2

namespace Flecs.IterKinds

inductive Next | queryNext | trivialCachedNext | workerNext
  deriving Repr, BEq, Inhabited, DecidableEq

def Next.show : Next → String
  | .queryNext => "ecs_query_next" | .trivialCachedNext => "flecs_query_trivial_cached_next"
  | .workerNext => "ecs_worker_next"

inductive Call | iterChanged | iterSkip | testNext
  deriving Repr, BEq, Inhabited, DecidableEq

structure Sys where
  /-- `ecs_set_threads` (1: no workers) -/
  stages : Nat := 1
  multiThreaded : Bool := false
  run : Bool := false
  /-- `EcsQueryDetectChanges` on the system's query -/
  detectChanges : Bool := false
  orderBy : Bool := false
  /-- the system's query has a trivial cache shape (one self term, no
      wildcards, ...) -/
  trivialShape : Bool := true
  call : Call := .iterChanged
  deriving Repr, BEq, Inhabited, DecidableEq

def showSys (s : Sys) : String :=
  s!"{s.stages} stage(s), {if s.multiThreaded then "multi_threaded" else "single-threaded"} system, {if s.run then "run callback" else "callback"}, query {if s.detectChanges then "with EcsQueryDetectChanges" else "without change detection"}{if s.orderBy then ", order_by" else ""}{if s.trivialShape then ", trivial cache shape" else ""}; the callback calls {match s.call with | .iterChanged => "ecs_iter_changed(it)" | .iterSkip => "ecs_iter_skip(it)" | .testNext => "it->next == ecs_query_next"}"

/-- The query's cache is trivial (no change detection: the cache stores
    `ecs_query_triv_cache_match_t`, cache.c): asserted by the change
    detection functions as "query was not created with change detection
    enabled". -/
def trivialCache (s : Sys) : Bool := s.trivialShape && !s.detectChanges && !s.orderBy

/-- `it->next` of the iterator the callback (or run callback) receives. -/
def nextOf (s : Sys) : Next :=
  if s.stages > 1 && s.multiThreaded then .workerNext
  else if s.run && trivialCache s then .trivialCachedNext
  else .queryNext

/-- What the call does: `.ok` result, or an abort message (debug build). -/
def outcome (s : Sys) : Except String String :=
  let n := nextOf s
  match s.call with
  | .testNext => .ok (if n == .queryNext then "true" else "false")
  | .iterChanged =>
    if n != .queryNext then
      .error s!"ecs_iter_changed: ecs_check(it->next == ecs_query_next, ECS_UNSUPPORTED) fails (change_detection.c 680; it->next is {n.show}); a release build reads it->priv_.iter.query.elem, NULL in a worker iterator (iter.c 1020), and dereferences it in flecs_query_check_match_monitor"
    else if trivialCache s then
      .error "precondition: change detection is not enabled on the query"
    else .ok "the change state"
  | .iterSkip =>
    if n != .queryNext then
      .error s!"ecs_iter_skip: ecs_assert(it->next == ecs_query_next, ECS_INVALID_PARAMETER) fails (change_detection.c 718; it->next is {n.show}); {if n == .workerNext then "a release build sets EcsIterSkip on the worker iterator, whose flags ecs_worker_next overwrites from the query iterator (iter.c 1049-1054), which never sees it: the table is marked dirty anyway" else "a release build works: flecs_query_trivial_cached_next reads EcsIterSkip before it clears it (eval_iter.c 640-646)"}"
    else .ok "skipped"

/-- Properties:
  - PI1 (system.h 55-66): a run callback of a system that is neither
    multithreaded nor paged gets a query iterator (`it->next ==
    ecs_query_next`);
  - PI2: `ecs_iter_changed` on the iterator a system gets, for a query with
    change detection enabled (`EcsQueryDetectChanges`, or order_by), does
    not abort;
  - PI3: `ecs_iter_skip` on it does not abort. -/
def check (s : Sys) : List (String × String) :=
  let mt := s.stages > 1 && s.multiThreaded
  match s.call, outcome s with
  | .testNext, .ok r =>
    if s.run && !s.multiThreaded && r == "false" then
      [("PI1 a single-threaded run callback gets a query iterator", s!"{showSys s}: it->next is {(nextOf s).show}, not ecs_query_next (system.c 119-121), though system.h 55-66 says only multithreaded or paged systems get another iterator")]
    else []
  | .iterChanged, .error e =>
    -- the documented precondition: change detection on the query
    -- (EcsQueryDetectChanges, or order_by, which uses it: Queries.md
    -- "Sorting")
    if (e.splitOn "precondition").length > 1 || !(s.detectChanges || s.orderBy) then []
    else [("PI2 ecs_iter_changed works in systems", s!"{showSys s}: {e}")]
  | .iterSkip, .error e => [("PI3 ecs_iter_skip works in systems", s!"{showSys s}: {e}")]
  | _, _ => []

section
variable {m : Type → Type} [Monad m] [Pick m]

def genSys : m Sys := do
  let stages := (← Pick.pick "ik.stages" 2) + 1
  let mtd := (← Pick.pick "ik.mt" 2) == 1
  let run := (← Pick.pick "ik.run" 2) == 1
  let dc := (← Pick.pick "ik.dc" 2) == 1
  let ob := (← Pick.pick "ik.orderby" 2) == 1
  let tr := (← Pick.pick "ik.trivial" 2) == 1
  let call ← pickOf "ik.call" #[Call.iterChanged, .iterSkip, .testNext]
  return { stages, multiThreaded := mtd, run, detectChanges := dc, orderBy := ob, trivialShape := tr, call }

end

def cases : List (String × Sys) := [
  ("iter_changed_multi_threaded_system: 2 stages, multi_threaded, EcsQueryDetectChanges",
    { stages := 2, multiThreaded := true, detectChanges := true, trivialShape := true, call := .iterChanged }),
  ("control: the same system single-threaded",
    { stages := 1, multiThreaded := true, detectChanges := true, trivialShape := true, call := .iterChanged }),
  ("iter_skip_multi_threaded_system",
    { stages := 2, multiThreaded := true, trivialShape := true, call := .iterSkip }),
  ("system_run_trivial_cache_next: run callback, single-threaded, trivial cache",
    { stages := 1, run := true, trivialShape := true, call := .testNext }),
  ("system_run_trivial_cache_next: ecs_iter_skip in that run callback",
    { stages := 1, run := true, trivialShape := true, call := .iterSkip }),
  ("control: the same run callback with EcsQueryDetectChanges",
    { stages := 1, run := true, detectChanges := true, trivialShape := true, call := .iterSkip }) ]

end Flecs.IterKinds

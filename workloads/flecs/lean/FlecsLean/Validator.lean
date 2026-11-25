/-
  Round 4: how a query is split into a cached and an uncached part,
  transcribed from flecs v4.2.0:
  - `flecs_query_finalize_terms` (query/validator.c 965-1312): Or chains
    (982-990), the per-term cacheability decided by `flecs_term_finalize`
    (validator.c 837-859: a term is cacheable when it is matched at table
    level, on `$this`, and is not DontFragment), the Or-chain consistency
    pass (1075-1087), field indices (1089-1093), sparse terms losing
    cacheability after that pass (1234-1238), the trailing-Or check
    (1308-1312), and the query flags `EcsQueryIsCacheable`,
    `EcsQueryHasCacheable`, `EcsQueryCacheWithFilter` (1336-1387);
  - `flecs_query_set_caching_policy` (query/api.c 74-187);
  - `flecs_query_create_cache` (api.c 194-243): the cache's terms and the
    `field_map` (216-232, which compares with `term[-1]`, the previous query
    term);
  - `flecs_query_cache_init` (query/cache/cache.c 700-911): the cache's own
    query is created with `ecs_query_init` from the copied terms, which runs
    `flecs_query_finalize_terms` again; when that fails, `goto error`
    returns NULL with `impl->cache` already set (cache.c 735-736, 750-753);
  - the error path of `flecs_query_init` (api.c 451-457): `ecs_query_fini`,
    then `flecs_query_fini` (api.c 276-334) calls `flecs_query_cache_fini`
    (cache.c 646-698), whose `flecs_query_cache_remove_all_tables`
    (group.c 331-351) and `cache->query->term_count` (cache.c 689)
    dereference the NULL `cache->query`.

  A term is a component of the program's menu (with its storage: table,
  Sparse, or DontFragment) and a source (`$this` self, `$this` up(ChildOf),
  or a fixed entity) and an operator (And, Or, Not, Optional).
-/
import FlecsLean.Search2

namespace Flecs.Val

inductive Storage | table | sparse | dontFragment
  deriving Repr, BEq, Inhabited, DecidableEq

inductive TSrc | self | up | fixed
  deriving Repr, BEq, Inhabited, DecidableEq

inductive TOper | and | or | not | optional
  deriving Repr, BEq, Inhabited, DecidableEq

inductive CacheKind | default_ | auto | all | none
  deriving Repr, BEq, Inhabited, DecidableEq

structure VTerm where
  comp : Nat
  src : TSrc := .self
  oper : TOper := .and
  deriving Repr, BEq, Inhabited, DecidableEq

/-- A finalized term: the flags the validator computes. -/
structure FTerm where
  t : VTerm
  isOr : Bool := false
  cacheable : Bool := false
  fieldIndex : Nat := 0
  deriving Repr, BEq, Inhabited

structure FQuery where
  terms : Array FTerm
  fieldCount : Nat
  isCacheable : Bool
  hasCacheable : Bool
  cacheWithFilter : Bool
  deriving Repr, Inhabited

/-- `flecs_term_finalize`'s `cacheable_term` (validator.c 837-859): matched
    at table level (not DontFragment, validator.c 786-789 and 837-840), on
    `$this` (self or up). -/
def cacheableTerm (st : Array Storage) (t : VTerm) : Bool :=
  st.getD t.comp .table != .dontFragment && t.src != .fixed

/-- `flecs_query_finalize_terms` (validator.c 965-1312), the parts that
    decide Or chains, cacheability and fields.  `Except` carries the
    validator error and its line. -/
def finalizeTerms (st : Array Storage) (ts : Array VTerm) : Except String FQuery := do
  let n := ts.size
  -- 982-990: EcsTermIsOr on both sides of an Or
  let mut fs : Array FTerm := ts.map (fun t => { t })
  for i in [0:n] do
    if (ts.getD i default).oper == .or then
      fs := fs.modify i (fun f => { f with isOr := true })
      if i + 1 != n then fs := fs.modify (i + 1) (fun f => { f with isOr := true })
  let mut fieldCount := 0
  let mut hasChildof := false
  for i in [0:n] do
    let t := ts.getD i default
    let prevIsOr := i > 0 && (ts.getD (i - 1) default).oper == .or
    -- flecs_term_finalize
    fs := fs.modify i (fun f => { f with cacheable := cacheableTerm st t })
    -- 1035-1039
    if prevIsOr && (ts.getD (i - 1) default).src != t.src then
      throw "validator.c 1035-1039: terms in an OR chain must have the same source"
    -- 1058-1063: up(ChildOf) terms with And, Or, Optional or Not
    if t.src == .up then hasChildof := true
    -- 1075-1087: the Or-chain consistency pass
    if (fs.getD i default).cacheable then
      if prevIsOr && !(fs.getD (i - 1) default).cacheable then
        fs := fs.modify i (fun f => { f with cacheable := false })
    else if prevIsOr then
      let mut j := i
      while j > 0 && (ts.getD (j - 1) default).oper == .or do
        fs := fs.modify (j - 1) (fun f => { f with cacheable := false })
        j := j - 1
    -- 1089-1093
    if !prevIsOr then fieldCount := fieldCount + 1
    fs := fs.modify i (fun f => { f with fieldIndex := fieldCount - 1 })
    -- 1227-1231
    if prevIsOr && t.oper != .or && t.oper != .and then
      throw "validator.c 1227-1231: term after OR expression cannot use operators"
    -- 1234-1238: sparse terms (Sparse and DontFragment storage both carry
    -- EcsIdSparse) are not cacheable, after the Or-chain pass
    if st.getD t.comp .table != .table then
      fs := fs.modify i (fun f => { f with cacheable := false })
  -- 1308-1312
  if n > 0 && (ts.getD (n - 1) default).oper == .or then
    throw "validator.c 1308-1312: last term of query can't have OR operator"
  let cacheableTerms := (fs.filter (·.cacheable)).size
  return { terms := fs, fieldCount,
           hasCacheable := cacheableTerms != 0,
           -- 1382-1385 (no order_by in these programs)
           isCacheable := cacheableTerms == n && !hasChildof,
           cacheWithFilter := hasChildof }

/-- `flecs_query_set_caching_policy` (api.c 74-187): the cache kind the
    query ends up with, or the error of api.c 127-131 / 139-146. -/
def cachingPolicy (q : FQuery) (kind : CacheKind) (hasEntity requireCaching : Bool) :
    Except String CacheKind := do
  let mut k := kind
  if k == .default_ then
    k := if hasEntity || requireCaching then .auto else .none
  if k == .none then
    if requireCaching then throw "api.c 127-131: cannot create uncached query with group_by/order_by/change detection"
    return .none
  if kind == .all then
    if q.isCacheable then return .all
    throw "api.c 139-146: cannot enforce QueryCacheAll, query contains uncacheable terms"
  -- k == auto
  if q.isCacheable then
    return if !q.cacheWithFilter then .all else .auto
  if !q.hasCacheable then return .none
  let cacheable := q.terms.filter (·.cacheable)
  let notOpt := (cacheable.filter (fun f => f.t.oper == .not || f.t.oper == .optional)).size
  if requireCaching || cacheable.size != notOpt then return .auto
  return .none

/-- What creating the query does. -/
inductive Outcome
  /-- the query is created; `cacheTerms` is the cache's query, `fieldMap`
      the map of api.c 216-232 -/
  | created (kind : CacheKind) (cacheTerms : Array VTerm) (cacheFields : Nat)
      (fieldMap : Array Nat)
  /-- `ecs_query_init` returns NULL with a validator error -/
  | rejected (msg : String)
  /-- the program crashes -/
  | crash (msg : String)
  deriving Repr, Inhabited

/-- `flecs_query_create_cache` (api.c 194-243) for the Auto case: the
    cache's terms and the field map, as written (dst_field compares with
    `term[-1]`). -/
def autoCacheTerms (q : FQuery) : Array VTerm × Array Nat := Id.run do
  let mut out : Array VTerm := #[]
  let mut fm : Array Nat := Array.replicate 32 0
  let mut dstField := 0
  for i in [0:q.terms.size] do
    let f := q.terms.getD i default
    if f.cacheable then
      out := out.push f.t
      fm := fm.set! dstField f.fieldIndex
      if i > 0 then
        if f.fieldIndex != (q.terms.getD (i - 1) default).fieldIndex then dstField := dstField + 1
      else dstField := dstField + 1
  return (out, fm.extract 0 out.size)

/-- `ecs_query_init` for a program's query. -/
def createQuery (st : Array Storage) (ts : Array VTerm) (kind : CacheKind)
    (hasEntity requireCaching : Bool) : Outcome :=
  match finalizeTerms st ts with
  | .error e => .rejected e
  | .ok q =>
    match cachingPolicy q kind hasEntity requireCaching with
    | .error e => .rejected e
    | .ok .none => .created .none #[] 0 #[]
    | .ok k =>
      let (cts, fm) := if k == .all then (ts, (List.range q.fieldCount).toArray) else autoCacheTerms q
      if cts.isEmpty then .created k #[] 0 #[]
      else
        -- flecs_query_cache_init: ecs_query_init on the cache's terms
        -- (cache_kind None, cache.c 721)
        match finalizeTerms st cts with
        | .error e =>
          .crash s!"cache.c 750-753: the cache's query is rejected ({e}); flecs_query_cache_init returns NULL with impl->cache set, and the error path (api.c 451-457 -> 276-334) runs flecs_query_cache_fini on a cache whose query is NULL: group.c 334 / cache.c 689 dereference cache->query"
        | .ok cq => .created k cts cq.fieldCount fm

/-! ### Properties -/

/-- The Or chains of a term list as lists of term indices. -/
def chains (ts : Array VTerm) : List (List Nat) := Id.run do
  let mut out : List (List Nat) := []
  let mut cur : List Nat := []
  for i in [0:ts.size] do
    cur := cur ++ [i]
    if (ts.getD i default).oper != .or then
      out := out ++ [cur]
      cur := []
  if !cur.isEmpty then out := out ++ [cur]
  return out

structure VProg where
  storage : Array Storage
  terms : Array VTerm
  kind : CacheKind := .auto
  hasEntity : Bool := false
  detect : Bool := false
  deriving Repr, Inhabited

/-- The properties:
  - P1 no crash (Manual.md "Error handling");
    (also ComponentTraits.md "Sparse trait": "ECS operations and queries
    work as expected with sparse components");
  - PV2 (internal): the cache's query holds the cacheable part of the
    query, chain by chain (cache.c 11-17: "It does not contain terms that
    aren't cacheable"), so its Or chains are the query's cacheable chains;
  - PV3 (internal): `field_map` maps each cache field to the query field
    of its terms. -/
def check (p : VProg) : List (String × String) := Id.run do
  let requireCaching := p.detect
  match createQuery p.storage p.terms p.kind p.hasEntity requireCaching with
  | .crash m => return [("P1 no-crash", m)]
  | .rejected _ => return []
  | .created k cts cfields fm =>
    if k != .auto then return []
    let some q := (finalizeTerms p.storage p.terms).toOption | return []
    let mut out := []
    -- PV2
    let qChains := (chains p.terms).filter (fun c => c.all (fun i => (q.terms.getD i default).cacheable))
    let mixed := (chains p.terms).filter (fun c => c.any (fun i => (q.terms.getD i default).cacheable) &&
      !c.all (fun i => (q.terms.getD i default).cacheable))
    let want := qChains.map (fun c => c.map (fun i => p.terms.getD i default))
    let got := (chains cts).map (fun c => c.map (fun i => cts.getD i default))
    if want != got || !mixed.isEmpty then
      out := out ++ [("PV2 cache holds the cacheable chains", s!"the query's chains {(chains p.terms)} are cacheable as {q.terms.toList.map (·.cacheable)} (mixed chains {mixed}); the cache's query has {cfields} field(s) with chains {got.map (fun c => c.map (·.comp))}, expected {want.map (fun c => c.map (·.comp))}")]
    -- PV3
    for f in [0:cfields] do
      let c := (chains cts).getD f []
      let qf := (q.terms.filter (·.cacheable)).getD (c.headD 0) default
      if fm.getD f 99 != qf.fieldIndex then
        out := out ++ [("PV3 field map", s!"cache field {f} maps to query field {fm.getD f 99}, its terms are field {qf.fieldIndex}")]
    return out

/-! ### Generators -/

section
variable {m : Type → Type} [Monad m] [Pick m]

/-- `n` components with drawn storage; `len` terms. -/
def genVProg (ncomp len : Nat) : m VProg := do
  let mut st := #[]
  for _ in [0:ncomp] do st := st.push (← pickOf "val.storage" #[Storage.table, .sparse, .dontFragment])
  let mut ts := #[]
  for _ in [0:len] do
    let comp ← Pick.pick "val.comp" ncomp
    let src ← pickOf "val.src" #[TSrc.self, .up, .fixed]
    let oper ← pickOf "val.oper" #[TOper.and, .or, .not, .optional]
    ts := ts.push { comp, src, oper }
  let kind ← pickOf "val.kind" #[CacheKind.auto, .default_, .all, .none]
  let hasEntity := (← Pick.pick "val.entity" 2) == 1
  let detect := (← Pick.pick "val.detect" 2) == 1
  return { storage := st, terms := ts, kind, hasEntity, detect }

end

def shrinkV (p : VProg) : List VProg := Id.run do
  let mut out := []
  for i in [0:p.terms.size] do
    out := out ++ [{ p with terms := p.terms.eraseIdx! i }]
  for i in [0:p.terms.size] do
    let t := p.terms.getD i default
    if t.oper != .and then out := out ++ [{ p with terms := p.terms.set! i { t with oper := .and } }]
    if t.src != .self then out := out ++ [{ p with terms := p.terms.set! i { t with src := .self } }]
  if p.detect then out := out ++ [{ p with detect := false }]
  if p.hasEntity then out := out ++ [{ p with hasEntity := false }]
  if p.kind != .auto then out := out ++ [{ p with kind := .auto }]
  for i in [0:p.storage.size] do
    if p.storage.getD i .table != .table then out := out ++ [{ p with storage := p.storage.set! i .table }]
  return out

def showV (p : VProg) : String :=
  let st := p.storage.toList.map (fun s => match s with | .table => "table" | .sparse => "Sparse" | .dontFragment => "DontFragment")
  let ts := p.terms.toList.map (fun t =>
    let o := match t.oper with | .and => "" | .or => " ||" | .not => "!" | .optional => "?"
    let pre := if t.oper == .not || t.oper == .optional then o else ""
    let post := if t.oper == .or then o else ""
    let s := match t.src with | .self => "" | .up => "(up)" | .fixed => "(Game)"
    s!"{pre}C{t.comp}{s}{post}")
  s!"components {st}; query [{", ".intercalate ts}] cache_kind={repr p.kind} entity={p.hasEntity} detect_changes={p.detect}"

instance : Repr VProg := ⟨fun p _ => .text (showV p)⟩

/-- The C test's program and variants. -/
def cases : List (String × VProg) := [
  ("query_or_sparse_cache_crash: TagA || Position(Sparse), cached",
    { storage := #[.table, .sparse], terms := #[{ comp := 0, oper := .or }, { comp := 1 }], kind := .auto }),
  ("the same query uncached (control)",
    { storage := #[.table, .sparse], terms := #[{ comp := 0, oper := .or }, { comp := 1 }], kind := .none }),
  ("as a system's query (cache kind default, query entity)",
    { storage := #[.table, .sparse], terms := #[{ comp := 0, oper := .or }, { comp := 1 }], kind := .default_, hasEntity := true }),
  ("TagA || Position(Sparse), TagC: the cache holds TagA || TagC",
    { storage := #[.table, .sparse, .table], terms := #[{ comp := 0, oper := .or }, { comp := 1 }, { comp := 2 }], kind := .auto }),
  ("Position(Sparse) || TagA (sparse first): consistent, no failure",
    { storage := #[.table, .sparse], terms := #[{ comp := 1, oper := .or }, { comp := 0 }], kind := .auto }),
  ("TagA || Position(DontFragment): consistent, no failure",
    { storage := #[.table, .dontFragment], terms := #[{ comp := 0, oper := .or }, { comp := 1 }], kind := .auto }) ]

end Flecs.Val

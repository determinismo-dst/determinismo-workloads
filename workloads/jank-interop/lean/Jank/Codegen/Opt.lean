import Jank.Codegen.Ir

/-!
# IR utilities and passes

Replicas of `src/cpp/jank/ir/{walk,rewrite,util,dominance}.cpp` and
`src/cpp/jank/ir/opt/{hoist_literals,hoist_var_derefs,hoist_scoped_values,remove_nops}.cpp`
(unchanged between f3d82d654 and 7135b7708: the line numbers hold).

The passes mutate instructions shared by pointer; here they rewrite the function's blocks.
`std::unordered_map` iteration is insertion order (assumption C2). Names made by
`munge(__rt_ctx->unique_string())` come from the namespace counter carried in `OptM`.
-/

namespace Jank.Codegen

open Jank.Analyzer

/-- A pass's monad: the namespace counter (for `unique_string`), failures as `.at`/panic. -/
abbrev OptM := StateT Nat (Except String)

def freshName : OptM Ident := do
  let n := (← get) + 1
  set n
  pure (munge (uniqueString "G_" n))

/-! ## walk_references (walk.cpp:500-816) -/

/-- The names an instruction refers to, in the order `walk_references_typed` visits them. Note
`branch_get` refers to its own name, not its shadow; `branch_set`, `loop` and `try`/`catch` never
name a shadow. -/
def Inst.references : Inst → List Ident
  | .def _ _ v _ _ => v.toList
  | .typeErase _ v => [v]
  | .dynamicCall _ fn args => fn :: args
  | .persistentList _ vs m | .persistentVector _ vs m | .persistentHashSet _ vs m => vs ++ m.toList
  | .persistentArrayMap _ kvs m | .persistentHashMap _ kvs m =>
      kvs.flatMap (fun p => [p.1, p.2]) ++ m.toList
  | .closure _ _ _ caps _ _ => caps.map (·.2.1)
  | .setLocal _ _ v => [v]
  | .truthy _ v => [v]
  | .branchGet n _ _ => [n]
  | .branchSet _ _ v => [v]
  | .branch _ c _ _ _ => [c]
  | .loop _ _ _ _ bs => bs.map (·.value)
  | .throw_ _ v => (v.map (·.1)).toList
  | .case_ _ _ _ v _ _ _ => [v]
  | .ret _ _ v => [v]
  | .cppOpaque _ _ _ refs => refs
  | _ => []

/-! ## rewrite_uses (rewrite.cpp) -/

def rw (old new : Ident) (n : Ident) : Ident := if n == old then new else n
def rwO (old new : Ident) (n : Option Ident) : Option Ident := n.map (rw old new)

/-- `rewrite_uses(inst, old, new)` (rewrite.cpp:30-330): the fields each case rewrites. Not
rewritten: a `case_`'s value and default block, a `loop`'s binding-shadow values, a `def`'s meta,
a `closure`'s arities, a `letfn`'s bindings. Returns the instruction and whether it changed. -/
def Inst.rewriteUses (i : Inst) (old new : Ident) : Inst × Bool :=
  let r := rw old new
  let ro := rwO old new
  let i' : Inst := match i with
    | .setLocal n l v => .setLocal n (r l) (r v)
    | .persistentList n vs m => .persistentList n (vs.map r) (ro m)
    | .persistentVector n vs m => .persistentVector n (vs.map r) (ro m)
    | .persistentArrayMap n kvs m => .persistentArrayMap n (kvs.map fun p => (r p.1, r p.2)) (ro m)
    | .persistentHashMap n kvs m => .persistentHashMap n (kvs.map fun p => (r p.1, r p.2)) (ro m)
    | .persistentHashSet n vs m => .persistentHashSet n (vs.map r) (ro m)
    | .closure n c a caps f v => .closure n c a (caps.map fun p => (p.1, (r p.2.1, p.2.2))) f v
    | .def n q v m d => .def n q (ro v) m d
    | .typeErase n v => .typeErase n (r v)
    | .dynamicCall n f a => .dynamicCall n (r f) (a.map r)
    | .namedRecursion n f b a d => .namedRecursion n (r f) b (a.map r) d
    | .truthy n v => .truthy n (r v)
    | .jump n b l => .jump n (r b) l
    | .branchSet n s v => .branchSet n (r s) (r v)
    | .branch n c t e m => .branch n (r c) (r t) (r e) (r m)
    | .loop n lb mb sh bs => .loop n (r lb) (ro mb) (sh.map fun p => (r p.1, p.2)) bs
    | .case_ n s k v cs d m => .case_ n s k v (cs.map fun p => (p.1, r p.2)) d (r m)
    | .try_ n cs m s f => .try_ n (cs.map fun p => (p.1, r p.2)) (r m) (r s) (ro f)
    | .catch_ n t m s f => .catch_ n t (ro m) (ro s) (ro f)
    | .finally n m => .finally n (r m)
    | .throw_ n v => .throw_ n (v.map fun p => (r p.1, p.2))
    | .ret n t v => .ret n t (r v)
    | .cppOpaque k n t refs => .cppOpaque k n t (refs.map r)
    | x => x
  (i', i' != i)

/-- `rewrite_uses(fn, old, new)` (rewrite.cpp:333-346). -/
def IrFn.rewriteUses (f : IrFn) (old new : Ident) : IrFn :=
  { f with blocks := f.blocks.map fun b => { b with insts := b.insts.map fun i => (i.rewriteUses old new).1 } }

/-- `uses_name` (util.cpp:11-14). -/
def Inst.usesName (i : Inst) (n : Ident) : Bool := (i.rewriteUses n n).2

/-- `replace_with_nop` (util.cpp:16-24): the named instruction of the block becomes a `nop` with
a fresh name. -/
def replaceWithNop (f : IrFn) (block : Ident) (name : Ident) : OptM IrFn := do
  let some bi := f.blocks.findIdx? (·.name == block) | throw s!"panic: Unable to find IR block '{block}'."
  let b := f.blocks[bi]!
  let some ii := b.insts.findIdx? (·.name == name) | throw "jank_debug_assert: instruction not found"
  let nn ← freshName
  pure { f with blocks := f.blocks.set! bi { b with insts := b.insts.set! ii (.nop nn) } }

/-! ## walk (walk.cpp:1-497) -/

structure WalkState where
  blockIndex : Nat := 0
  instIndex : Nat := 0
  seen : List Ident := []

/-- `state::enter_block`. -/
def WalkState.enter (f : IrFn) (s : WalkState) (block : Ident) : Except String WalkState := do
  let i ← f.findBlock block
  pure { s with blockIndex := i, instIndex := 0, seen := if s.seen.contains block then s.seen else block :: s.seen }

def WalkState.cur (f : IrFn) (s : WalkState) : Ident := (f.blocks[s.blockIndex]?.map (·.name)).getD ""

def WalkState.inst? (f : IrFn) (s : WalkState) : Option Inst := do
  let b ← f.blocks[s.blockIndex]?
  b.insts[s.instIndex]?

mutual
/-- `walk(instr, f, s)` (walk.cpp:477-480 and every `walk_typed`): visits instructions in the
lexical order code generation emits them, calling `visit acc inst block`. -/
def walkInst {α : Type} (fuel : Nat) (f : IrFn) (visit : α → Inst → Ident → α) (i : Inst)
    (s : WalkState) (acc : α) : Except String (WalkState × α) := do
  match fuel with
  | 0 => throw "walk fuel"
  | fuel + 1 =>
  let s := { s with instIndex := s.instIndex + 1 }
  let acc := visit acc i (s.cur f)
  match i with
  | .jump _ blk _ =>
    -- trailing instructions after the jump (scope closes)
    let mut s := s
    let mut acc := acc
    let mut g := fuel
    while g > 0 do
      g := g - 1
      match s.inst? f with
      | some j => let (s', a') ← walkInst fuel f visit j s acc; s := s'; acc := a'
      | none => break
    if s.seen.contains blk then return (s, acc)
    pure (← s.enter f blk, acc)
  | .branch _ _ t e m =>
    let s ← s.enter f t
    let (s, acc) ← walkUntilJump fuel f visit (some m) s acc
    let s ← s.enter f e
    let (s, acc) ← walkUntilJump fuel f visit (some m) s acc
    pure (← s.enter f m, acc)
  | .loop _ lb mb _ _ =>
    let s ← s.enter f lb
    let (s, acc) ← walkUntilJump fuel f visit mb s acc
    match mb with
    | some m => pure (← s.enter f m, acc)
    | none => pure (s, acc)
  | .try_ _ catches merge _ fin =>
    let mut s := s
    let mut acc := acc
    if let some fb := fin then
      let (ii, bi) := (s.instIndex, s.blockIndex)
      let s1 ← s.enter f fb
      match s1.inst? f with
      | some j =>
        let (s2, a2) ← walkInst fuel f visit j s1 acc
        s := { s2 with instIndex := ii, blockIndex := bi }
        acc := a2
      | none => throw "empty finally block"
    let jb := match fin with | some fb => some fb | none => some merge
    let (s', a') ← walkUntilJump fuel f visit jb s acc
    s := s'; acc := a'
    for (_, cb) in catches do
      s ← s.enter f cb
      match s.inst? f with
      | some j => let (s2, a2) ← walkInst fuel f visit j s acc; s := s2; acc := a2
      | none => throw "empty catch block"
    pure (← s.enter f merge, acc)
  | .catch_ _ _ m _ fin =>
    let jb := match fin with | some fb => some fb | none => m
    walkUntilJump fuel f visit jb s acc
  | .finally _ m => walkUntilJump fuel f visit (some m) s acc
  | .case_ _ _ _ _ cs d m =>
    let mut s := s
    let mut acc := acc
    for (_, cb) in cs do
      s ← s.enter f cb
      let (s', a') ← walkUntilJump fuel f visit (some m) s acc
      s := s'; acc := a'
    s ← s.enter f d
    let (s2, a2) ← walkUntilJump fuel f visit (some m) s acc
    pure (← s2.enter f m, a2)
  | _ => pure (s, acc)

/-- `walk_until_jump` (walk.cpp:35-66). -/
def walkUntilJump {α : Type} (fuel : Nat) (f : IrFn) (visit : α → Inst → Ident → α)
    (jumpBlock : Option Ident) (s : WalkState) (acc : α) : Except String (WalkState × α) := do
  match fuel with
  | 0 => throw "walk fuel"
  | fuel + 1 =>
  let mut s := s
  let mut acc := acc
  let mut g := fuel
  while g > 0 do
    g := g - 1
    let some cur := s.inst? f | break
    match cur with
    | .jump _ blk _ =>
      if s.seen.contains blk then
        let (s', a') ← walkInst fuel f visit cur s acc
        return (s', a')
      let (s', a') ← walkInst fuel f visit cur s acc
      s := s'; acc := a'
      if jumpBlock == some blk then break
    | .ret .. =>
      let (s', a') ← walkInst fuel f visit cur s acc
      s := s'; acc := a'
      break
    | _ =>
      let (s', a') ← walkInst fuel f visit cur s acc
      s := s'; acc := a'
  pure (s, acc)
end

/-- `walk(fn, f)` (walk.cpp:482-497): from block 0 (not entered: not in `seen_blocks`). -/
def walkFn {α : Type} (f : IrFn) (visit : α → Inst → Ident → α) (init : α) (fuel : Nat := 10000) :
    Except String α := do
  let mut s : WalkState := {}
  let mut acc := init
  let mut g := fuel
  while g > 0 do
    g := g - 1
    let some i := s.inst? f | break
    let (s', a') ← walkInst fuel f visit i s acc
    s := s'; acc := a'
  pure acc

/-! ## Dominance (dominance.cpp) -/

def lookupNat (l : List (Ident × Nat)) (k : Ident) : Except String Nat :=
  match (l.find? (·.1 == k)) with
  | some p => .ok p.2
  | none => .error s!"std::out_of_range: rpo_index.at({k})"

def lookupId (l : List (Ident × Ident)) (k : Ident) : Except String Ident :=
  match (l.find? (·.1 == k)) with
  | some p => .ok p.2
  | none => .error s!"std::out_of_range: idom.at({k})"

/-- `lcd(idom, rpo_index, a, b)` (dominance.cpp:6-21). -/
def lcd2 (idom : List (Ident × Ident)) (rpo : List (Ident × Nat)) (a b : Ident) (fuel : Nat := 10000) :
    Except String Ident := do
  let mut a := a
  let mut b := b
  let mut g := fuel
  while a != b && g > 0 do
    g := g - 1
    let mut h := fuel
    while (← lookupNat rpo a) > (← lookupNat rpo b) && h > 0 do
      h := h - 1
      a ← lookupId idom a
    h := fuel
    while (← lookupNat rpo b) > (← lookupNat rpo a) && h > 0 do
      h := h - 1
      b ← lookupId idom b
  if g == 0 then throw "lcd: no common dominator (loops forever)"
  pure a

/-- `lcd(idom, rpo_index, blocks)` (dominance.cpp:23-35). -/
def lcd (idom : List (Ident × Ident)) (rpo : List (Ident × Nat)) (blocks : List Ident) :
    Except String Ident := do
  match blocks with
  | [] => throw "jank_debug_assert: !blocks.empty()"
  | b0 :: rest => rest.foldlM (fun acc b => lcd2 idom rpo acc b) b0

/-- The successors `build_rpo` follows from an instruction (dominance.cpp:55-147). -/
def Inst.rpoSuccessors : Inst → List Ident
  | .jump _ b _ => [b]
  | .branch _ _ t e m => [t, e, m]
  | .loop _ lb mb _ _ => lb :: mb.toList
  | .case_ _ _ _ _ cs d m => cs.map (·.2) ++ [d, m]
  | .try_ _ cs m _ fin => cs.map (·.2) ++ [m] ++ fin.toList
  | _ => []

/-- `build_rpo` (dominance.cpp:42-150): depth first, a block put at the front once finished. -/
def buildRpo (f : IrFn) (fuel : Nat) (b : Block) (rpo : List Ident) (seen : List Ident) :
    Except String (List Ident × List Ident) := do
  match fuel with
  | 0 => throw "rpo fuel"
  | fuel + 1 =>
  if seen.contains b.name then return (rpo, seen)
  let mut seen := b.name :: seen
  let mut rpo := rpo
  for i in b.insts do
    for nb in i.rpoSuccessors do
      let bi ← f.findBlock nb
      let (r, s) ← buildRpo f fuel f.blocks[bi]! rpo seen
      rpo := r; seen := s
  pure (b.name :: rpo, seen)

/-- `build_idom` (dominance.cpp:152-291). A `try`'s catches, merge and finally get, as
predecessor, the first predecessor of the `try`'s own block. -/
def buildIdom (f : IrFn) (rpo : List Ident) : Except String IrFn := do
  let rpoIndex : List (Ident × Nat) := rpo.zipIdx.map fun (n, i) => (n, i)
  let mut preds : List (Ident × List Ident) := f.blocks.toList.map fun b => (b.name, [])
  let addPred := fun (ps : List (Ident × List Ident)) (k v : Ident) =>
    if ps.any (·.1 == k) then ps.map fun p => if p.1 == k then (k, p.2 ++ [v]) else p else ps ++ [(k, [v])]
  for b in f.blocks do
    for i in b.insts do
      match i with
      | .jump _ t _ => preds := addPred preds t b.name
      | .branch _ _ t e m =>
        preds := addPred preds t b.name; preds := addPred preds e b.name
        preds := addPred preds m b.name
      | .loop _ lb mb _ _ =>
        preds := addPred preds lb b.name
        if let some m := mb then preds := addPred preds m b.name
      | .case_ _ _ _ _ cs d m =>
        for (_, c) in cs do preds := addPred preds c b.name
        preds := addPred preds d b.name; preds := addPred preds m b.name
      | .try_ _ cs m _ fin =>
        let some p0 := ((preds.find? (·.1 == b.name)).map (·.2)).bind (·.head?)
          | throw s!"std::out_of_range: preds[{b.name}].at(0)"
        for (_, c) in cs do preds := addPred preds c p0
        preds := addPred preds m p0
        if let some fb := fin then preds := addPred preds fb p0
      | _ => pure ()
  let some entry := rpo.head? | throw "empty rpo"
  let mut idom : List (Ident × Ident) := [(entry, entry)]
  let mut changed := true
  let mut fuel := 1000
  while changed && fuel > 0 do
    fuel := fuel - 1
    changed := false
    for bn in rpo.drop 1 do
      let some bp := (preds.find? (·.1 == bn)).map (·.2) | throw s!"std::out_of_range: preds.at({bn})"
      let some first := bp.find? (fun p => idom.any (·.1 == p)) | continue
      let mut newIdom := first
      for p in bp do
        if p == first || !(idom.any (·.1 == p)) then continue
        newIdom ← lcd2 idom rpoIndex p newIdom
      match idom.find? (·.1 == bn) with
      | some (_, cur) =>
        if cur != newIdom then
          idom := idom.map fun q => if q.1 == bn then (bn, newIdom) else q
          changed := true
      | none =>
        idom := idom ++ [(bn, newIdom)]
        changed := true
  pure { f with immediateDominators := idom, rpo := rpo, blockRpoIndex := rpoIndex }

/-- `build_dominance` (dominance.cpp:293-314). -/
def buildDominance (f : IrFn) : Except String IrFn := do
  let some b0 := f.blocks[0]? | throw "no blocks"
  let (rpo, _) ← buildRpo f 10000 b0 [] []
  buildIdom f rpo

/-! ## hoist_literals (opt/hoist_literals.cpp) and hoist_var_derefs (opt/hoist_var_derefs.cpp) -/

/-- Insert `i` in block `bi` before the first instruction that is not a parameter, capture or
scope open (hoist_literals.cpp:98-105, hoist_var_derefs.cpp:112-119). -/
def insertAtTop (f : IrFn) (bi : Nat) (i : Inst) : IrFn :=
  let b := f.blocks[bi]!
  let pos := (b.insts.toList.takeWhile fun x => match x with
    | .parameter .. | .capture .. | .cppScopeOpen .. => true
    | _ => false).length
  { f with blocks := f.blocks.set! bi { b with insts := b.insts.insertIdxIfInBounds pos i } }

/-- The shared tail of both hoists: occurrences `(block, name)` of one value; the canonical one is
the first in the lowest common dominator block, else a new instruction made by `mk` at that
block's top; every other occurrence's uses are rewritten and it becomes a `nop`. -/
def dedupe (f : IrFn) (occurrences : List (Ident × Ident)) (mk : Ident → Inst) : OptM IrFn := do
  if occurrences.length == 1 then return f
  let target ← liftM (m := Except String) (lcd f.immediateDominators f.blockRpoIndex (occurrences.map (·.1)))
  let ti ← liftM (m := Except String) (f.findBlock target)
  let mut f := f
  let mut canonical : Ident := ""
  for (bn, inn) in occurrences do
    if bn == target then
      canonical := inn
      break
  if canonical.isEmpty then
    canonical ← freshName
    f := insertAtTop f ti (mk canonical)
  for (bn, inn) in occurrences do
    if inn == canonical then continue
    f := f.rewriteUses inn canonical
    f ← replaceWithNop f bn inn
  pure f
where
  liftM {α : Type} {m : Type → Type} [Monad m] (x : Except String α) : OptM α :=
    match x with
    | .ok a => pure a
    | .error e => throw e

/-- `collect_literals` + `hoist_literals` (hoist_literals.cpp:14-141): literals grouped by value
(`very_equal_to_with_meta`, here `same`), in block order. -/
def hoistLiterals (f : IrFn) (same : Obj → Obj → Bool) : OptM IrFn := do
  if f.immediateDominators.isEmpty then throw "jank_debug_assert: dominators built"
  let mut groups : List (Analyzer.Obj × List (Ident × Ident)) := []
  for b in f.blocks do
    for i in b.insts do
      if let .literal n _ o _ := i then
        match groups.findIdx? (fun g => same g.1 o) with
        | some gi => groups := groups.modify gi fun g => (g.1, g.2 ++ [(b.name, n)])
        | none => groups := groups ++ [(o, [(b.name, n)])]
  let mut f := f
  for (_, occ) in groups do
    -- the new instruction copies the first occurrence's type, location, obj and lifted name
    let first := occ.head!
    let some bi := f.blocks.findIdx? (·.name == first.1) | throw "block"
    let some (.literal _ ty o v) := f.blocks[bi]!.insts.find? (·.name == first.2)
      | throw "dynamic_cast to literal failed"
    f ← dedupe f occ fun n => .literal n ty o v
  pure f

/-- `collect_var_derefs` + `hoist_var_derefs` (hoist_var_derefs.cpp:20-153): nothing when the
function has a `loop` (collection stops at the first one) or is a module's load function;
dynamic vars (by their current flag, `isDynamic`) are skipped. -/
def hoistVarDerefs (f : IrFn) (isDynamic : String → Bool) : OptM IrFn := do
  if f.immediateDominators.isEmpty then throw "jank_debug_assert: dominators built"
  if f.name.startsWith "jank_load_" then return f
  let mut groups : List (String × List (Ident × Ident)) := []
  for b in f.blocks do
    for i in b.insts do
      if let .loop .. := i then return f
      if let .varDeref n q := i then
        if isDynamic q then continue
        groups := if groups.any (·.1 == q) then groups.map fun g => if g.1 == q then (q, g.2 ++ [(b.name, n)]) else g
                  else groups ++ [(q, [(b.name, n)])]
  let mut f := f
  for (q, occ) in groups do
    f ← dedupe f occ fun n => .varDeref n q
  pure f

/-- `remove_nops` (opt/remove_nops.cpp). -/
def removeNops (f : IrFn) : IrFn :=
  { f with blocks := f.blocks.map fun b => { b with insts := b.insts.filter fun i => match i with
      | .nop _ => false
      | _ => true } }

/-! ## hoist_scoped_values (opt/hoist_scoped_values.cpp) -/

structure ScopeInfo where
  inst : Inst
  defStack : List Ident
  defBlock : Ident
  lowStack : List Ident := []
  lowBlock : Ident := ""
  deriving Inhabited

/-- `lca_scope` (hoist_scoped_values.cpp:63-82). -/
def lcaScope (lhs rhs : List Ident) : Except String Ident := do
  if lhs.isEmpty || rhs.isEmpty then throw "jank_debug_assert: empty scope stack"
  if lhs.head? != rhs.head? then throw "jank_debug_assert: lhs[0] == rhs[0]"
  for i in List.range lhs.length do
    if rhs.length ≤ i then return lhs[i - 1]!
    if lhs[i]! != rhs[i]! then return lhs[i - 1]!
  return lhs.getLast!

/-- `std::stoi(name.substr(1))`. -/
def scopeNum (n : Ident) : Except String Int :=
  match (String.ofList (n.toList.drop 1)).toInt? with
  | some v => .ok v
  | none => .error s!"std::invalid_argument: stoi({n})"

def lessNested (d l r : List Ident) : Except String Bool := do
  pure ((← scopeNum (← lcaScope d l)) < (← scopeNum (← lcaScope d r)))

def lessNestedOrEqual (d l r : List Ident) : Except String Bool := do
  pure ((← scopeNum (← lcaScope d l)) ≤ (← scopeNum (← lcaScope d r)))

structure Collection where
  info : List (Ident × ScopeInfo) := []
  scopeToBlock : List (Ident × Ident) := []
  stack : List Ident := []
  err : Option String := none
  deriving Inhabited

/-- `collect_locals` (hoist_scoped_values.cpp:106-158). -/
def collectVisit (c : Collection) (i : Inst) (block : Ident) : Collection :=
  if c.err.isSome then c else
  match i with
  | .cppScopeOpen n =>
    let stb := if c.scopeToBlock.any (·.1 == n) then c.scopeToBlock else c.scopeToBlock ++ [(n, block)]
    { c with stack := c.stack ++ [n], scopeToBlock := stb }
  | .cppScopeClose .. => { c with stack := c.stack.dropLast }
  | _ =>
    let c := { c with info := assocSet c.info i.name { inst := i, defStack := c.stack, defBlock := block } }
    i.references.foldl (fun c ref =>
      if c.err.isSome || ref == ":defer" then c else
      match assocGet? c.info ref with
      | none => { c with err := some s!"std::out_of_range: name_to_info.at({ref})" }
      | some loc =>
        let better := !c.stack.isEmpty && (loc.lowStack.isEmpty ||
          (match lessNested loc.defStack c.stack loc.lowStack with
           | .ok b => b
           | .error _ => false))
        if better then
          match assocGet? c.scopeToBlock (c.stack.getLast!) with
          | some lb => { c with info := assocSet c.info ref { loc with lowStack := c.stack, lowBlock := lb } }
          | none => { c with err := some "std::out_of_range: scope_to_block.at" }
        else c) c

/-- `hoist_scoped_values` (hoist_scoped_values.cpp:160-256). -/
def hoistScopedValues (f : IrFn) : OptM IrFn := do
  let col ← match walkFn f collectVisit {} with
    | .ok c => pure c
    | .error e => throw e
  if let some e := col.err then throw e
  let mut f := f
  for (loc, info) in col.info do
    if info.lowStack.isEmpty then continue
    if ← (match lessNestedOrEqual info.defStack info.defStack info.lowStack with
          | .ok b => pure b | .error e => throw e) then continue
    let targetScope ← match lcaScope info.defStack info.lowStack with
      | .ok t => pure t | .error e => throw e
    let some targetBlock := assocGet? col.scopeToBlock targetScope | throw "scope_to_block.at"
    match info.inst with
    | .local_ _ _ =>
      f ← replaceWithNop f info.defBlock loc
      let ti ← match f.findBlock targetBlock with | .ok i => pure i | .error e => throw e
      let tb := f.blocks[ti]!
      let some atI := tb.insts.findIdx? (·.name == targetScope) | throw "jank_debug_assert: scope open"
      let tb := { tb with insts := tb.insts.insertIdxIfInBounds (atI + 1) info.inst }
      f := { f with blocks := f.blocks.set! ti tb }
    | _ =>
      let ti ← match f.findBlock targetBlock with | .ok i => pure i | .error e => throw e
      let tb := f.blocks[ti]!
      let some atI := tb.insts.findIdx? (·.name == targetScope) | throw "jank_debug_assert: scope open"
      let newLocal : Inst := .local_ info.inst.name (nonVoidType info.inst.type)
      let tb := { tb with insts := tb.insts.insertIdxIfInBounds (atI + 1) newLocal }
      f := { f with blocks := f.blocks.set! ti tb }
      let defName ← freshName
      let di ← match f.findBlock info.defBlock with | .ok i => pure i | .error e => throw e
      let db := f.blocks[di]!
      -- the original instruction, found by identity: its current name and kind
      let some ii := db.insts.findIdx? (fun x => x.name == info.inst.name && x.kindName == info.inst.kindName)
        | throw "jank_debug_assert: definition"
      let setName ← freshName
      let setI : Inst := .setLocal setName info.inst.name defName
      let renamed := db.insts[ii]!.setName defName
      let db := { db with insts := (db.insts.insertIdxIfInBounds (ii + 1) setI).set! ii renamed }
      f := { f with blocks := f.blocks.set! di db }
  pure f

/-- The pass pipeline of `ir::create` (processor.cpp:1016-1036 in 7135b7708) for one function. -/
def runPasses (f : IrFn) (hoistLit hoistVar removeN : Bool) (same : Obj → Obj → Bool)
    (isDynamic : String → Bool) : OptM IrFn := do
  let mut f ← match buildDominance f with | .ok g => pure g | .error e => throw e
  if hoistLit then f ← hoistLiterals f same
  if hoistVar then f ← hoistVarDerefs f isDynamic
  f ← hoistScopedValues f
  if removeN then f := removeNops f
  pure f

end Jank.Codegen

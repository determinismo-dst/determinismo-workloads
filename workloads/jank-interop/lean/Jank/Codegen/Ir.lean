import Jank.Analyzer.Expr
import Jank.Codegen.Fmt

/-!
# jank's IR: instructions, blocks, functions, modules, and the builder

Replicas (jank 7135b7708; the IR files' line numbers did not change from f3d82d654 except
`ir/processor.cpp` from line 520 on, +1) of `include/cpp/jank/ir/{instruction,processor,builder}.hpp`,
`src/cpp/jank/ir/instruction.cpp` (constructors' types, `is_terminator`),
`src/cpp/jank/ir/builder.cpp` (every builder method) and the block/function helpers of
`src/cpp/jank/ir/processor.cpp` (`function::add_block`, `remove_block`, `find_block`,
`block::has_terminator`). Paths are under `upstream/compiler+runtime/`.

Layout. C++ instructions are heap objects shared by `jtl::ref`, renamed in place by passes; here a
block is an `Array Inst` and a pass that renames writes the instruction back. `std::unordered_map`
fields are association lists in insertion order (C++ iteration order is unspecified: assumption
C2 of the report). The interop instructions (`cpp_*`), owned by the interop agent, are one opaque
constructor carrying what the passes need (the names it references).
-/

namespace Jank.Codegen

open Jank.Analyzer

abbrev Ident := String

/-! ## C++ types the code generator names (`jtl::ptr<void>` from Clang, by spelling) -/

namespace Ty
def objectRef : CppType := .named "jank::runtime::object_ref"
def bool : CppType := .named "bool"
def void : CppType := .named "void"
def varRef : CppType := .named "jank::runtime::var_ref"
def nilRef : CppType := .named "jank::runtime::obj::nil_ref"
def obj (n : String) : CppType := .named s!"jank::runtime::obj::{n}_ref"
end Ty

def _root_.Jank.Analyzer.CppType.spelling : CppType → String
  | .null => ""
  | .named s => s

/-- `cpp_util::is_untyped_object` (cpp_util.cpp:969). -/
def isUntypedObject (t : CppType) : Bool := t == Ty.objectRef

/-- `cpp_util::is_typed_object_ref` (cpp_util.cpp:1002; `is_typed_object` before 7135b7708, same
body): a specialization of `oref` other than `object_ref`: every `jank::runtime::obj::*_ref` and
`var_ref`. -/
def isTypedObject (t : CppType) : Bool :=
  match t with
  | .named s => !isUntypedObject t &&
      ((s.startsWith "jank::runtime::obj::" && s.endsWith "_ref") || s == "jank::runtime::var_ref")
  | .null => false

/-- `cpp_util::is_any_object` (cpp_util.cpp:1012). -/
def isAnyObject (t : CppType) : Bool := isUntypedObject t || isTypedObject t

/-- `cpp_util::mutable_type` (cpp_util.cpp:1064), for the types non-interop code has: a typed
object becomes `object_ref`; `void` becomes `object_ref`; other types are kept. -/
def mutableType (t : CppType) : CppType :=
  if isTypedObject t then Ty.objectRef else if t == Ty.void then Ty.objectRef else t

/-- `cpp_util::non_void_type` (cpp_util.cpp:1157). -/
def nonVoidType (t : CppType) : CppType := if t == Ty.void then Ty.nilRef else t

/-- `cpp_util::literal_type(o, true)` (cpp_util.cpp:603-861), boxed: the typed ref of each
object type it names, `object_ref` for the others. -/
def literalTypeBoxed (o : Obj) : CppType :=
  match o.type with
  | .nil => Ty.nilRef
  | .boolean => Ty.obj "boolean"
  | .integer => Ty.obj "integer"
  | .smallInteger => Ty.obj "small_integer"
  | .character => Ty.obj "character"
  | .real => Ty.obj "real"
  | .smallReal => Ty.obj "small_real"
  | .symbol => Ty.obj "symbol"
  | .keyword => Ty.obj "keyword"
  | .persistentString => Ty.obj "persistent_string"
  | .persistentList => Ty.obj "persistent_list"
  | .persistentVector => Ty.obj "persistent_vector"
  | .persistentHashSet => Ty.obj "persistent_hash_set"
  | .persistentArrayMap => Ty.obj "persistent_array_map"
  | .persistentHashMap => Ty.obj "persistent_hash_map"
  | .rePattern => Ty.obj "re_pattern"
  | .var => Ty.varRef
  | _ => Ty.objectRef

/-- `native_array_map::max_size` (native_array_map.hpp:30). -/
def arrayMapMaxSize : Nat := 8

/-- `cpp_util::literal_codegen_type(o, is_boxed)` (cpp_util.cpp:864-900): an `integer` whose value
fits `i32` is declared `small_integer_ref`; a hash map of at most 8 entries is declared
`persistent_array_map_ref`. -/
def literalCodegenTypeBoxed (o : Obj) : CppType :=
  match o with
  | .integer v => if (v.toInt ≥ -2147483648 ∧ v.toInt ≤ 2147483647) then Ty.obj "small_integer"
                  else Ty.obj "integer"
  | .persistentHashMap _ kvs => if kvs.length ≤ arrayMapMaxSize then Ty.obj "persistent_array_map"
                                else Ty.obj "persistent_hash_map"
  | o => literalTypeBoxed o

/-- `cpp_util::find_branch_common_type(then, else, has_recur)` (cpp_util.cpp:1907-1995, new in
7135b7708; `analyze_if` and `analyze_case` use it), for branches whose types are jank objects
(every type the drawn programs have): the same type when both have it, else `object_ref`; each
side needs a conversion exactly when the types differ. For objects: every object type is trait
convertible; `is_implicitly_assignable` and `get_common_type` make the pair compatible when one
is `object_ref` (a typed ref converts to it) or both are the same; with `is_else_object` true the
"needs conversion" conditions reduce to "not the same type", and the final types are then both
`object_ref`. Returns the type and whether either side needs a conversion. -/
def findBranchCommonType (thenType : CppType) (elseType : Option CppType) : CppType × Bool :=
  let e := elseType.getD Ty.objectRef
  if thenType == e then (thenType, false) else (Ty.objectRef, true)

/-! ## Instructions (instruction.hpp) -/

/-- `inst::loop::binding_shadow_details`. -/
structure LoopShadow where
  name : Ident
  value : Ident
  type : CppType
  deriving Repr, BEq, Inhabited

/-- `instruction_kind` (instruction.hpp:35-87), the interop kinds kept by name. -/
inductive Inst where
  | nop (name : Ident)
  | parameter (name : Ident) (type : CppType)
  | capture (name : Ident) (type : CppType) (value : String)
  | literal (name : Ident) (type : CppType) (obj : Obj) (value : Ident)
  | persistentList (name : Ident) (values : List Ident) (mta : Option Ident)
  | persistentVector (name : Ident) (values : List Ident) (mta : Option Ident)
  | persistentArrayMap (name : Ident) (values : List (Ident × Ident)) (mta : Option Ident)
  | persistentHashMap (name : Ident) (values : List (Ident × Ident)) (mta : Option Ident)
  | persistentHashSet (name : Ident) (values : List Ident) (mta : Option Ident)
  /-- `arities`: `unordered_map<u8, immutable_string>` (param count → C function name). -/
  | function (name : Ident) (arities : List (Nat × String)) (arityFlags : Nat) (isVariadic : Bool)
  | closure (name : Ident) (context : String) (arities : List (Nat × String))
      (captures : List (String × (Ident × CppType))) (arityFlags : Nat) (isVariadic : Bool)
  | letfn (name : Ident) (bindings : List String)
  | local_ (name : Ident) (type : CppType)
  | setLocal (name : Ident) (loc value : Ident)
  | def (name : Ident) (qualifiedVar : String) (value : Option Ident) (mta : Obj)
      (isDynamic : Bool)
  | varDeref (name : Ident) (qualifiedVar : String)
  | varRef (name : Ident) (qualifiedVar : String)
  | typeErase (name : Ident) (value : Ident)
  | dynamicCall (name : Ident) (fn : Ident) (args : List Ident)
  | namedRecursion (name : Ident) (fn : Ident) (fnBaseName : String) (args : List Ident)
      (needsDynamicCall : Bool)
  | recursionReference (name : Ident)
  | truthy (name : Ident) (value : Ident)
  | jump (name : Ident) (block : Ident) (loop : Bool)
  | branchSet (name : Ident) (shadow value : Ident)
  | branchGet (name : Ident) (shadow : Ident) (type : CppType)
  | branch (name : Ident) (condition thenBlock elseBlock mergeBlock : Ident)
  | loop (name : Ident) (loopBlock : Ident) (mergeBlock : Option Ident)
      (shadow : Option (Ident × CppType)) (bindingShadows : List LoopShadow)
  | case_ (name : Ident) (shift mask : Int) (value : Ident) (caseBlocks : List (Int × Ident))
      (defaultBlock mergeBlock : Ident)
  | try_ (name : Ident) (catches : List (CppType × Ident)) (mergeBlock shadow : Ident)
      (finallyBlock : Option Ident)
  | catch_ (name : Ident) (type : CppType) (mergeBlock shadow finallyBlock : Option Ident)
  | finally (name : Ident) (mergeBlock : Ident)
  | throw_ (name : Ident) (value : Option (Ident × CppType))
  | ret (name : Ident) (type : CppType) (value : Ident)
  | cppScopeOpen (name : Ident)
  | cppScopeClose (name : Ident) (scope : Ident)
  /-- Any `cpp_*` instruction (interop agent): its kind, name, type, the names it references. -/
  | cppOpaque (kind : String) (name : Ident) (type : CppType) (refs : List Ident)
  deriving Repr, BEq, Inhabited

namespace Inst

def name : Inst → Ident
  | nop n | parameter n _ | capture n _ _ | literal n _ _ _ | persistentList n _ _
  | persistentVector n _ _ | persistentArrayMap n _ _ | persistentHashMap n _ _
  | persistentHashSet n _ _ | function n _ _ _ | closure n _ _ _ _ _ | letfn n _ | local_ n _
  | setLocal n _ _ | .def n _ _ _ _ | varDeref n _ | varRef n _ | typeErase n _ | dynamicCall n _ _
  | namedRecursion n _ _ _ _ | recursionReference n | truthy n _ | jump n _ _ | branchSet n _ _
  | branchGet n _ _ | branch n _ _ _ _ | loop n _ _ _ _ | case_ n _ _ _ _ _ _ | try_ n _ _ _ _
  | catch_ n _ _ _ _ | .finally n _ | throw_ n _ | ret n _ _ | cppScopeOpen n | cppScopeClose n _
  | cppOpaque _ n _ _ => n

def setName (i : Inst) (n : Ident) : Inst :=
  match i with
  | nop _ => nop n | parameter _ t => parameter n t | capture _ t v => capture n t v
  | literal _ t o v => literal n t o v | persistentList _ v m => persistentList n v m
  | persistentVector _ v m => persistentVector n v m
  | persistentArrayMap _ v m => persistentArrayMap n v m
  | persistentHashMap _ v m => persistentHashMap n v m
  | persistentHashSet _ v m => persistentHashSet n v m
  | function _ a f v => function n a f v | closure _ c a cs f v => closure n c a cs f v
  | letfn _ b => letfn n b | local_ _ t => local_ n t | setLocal _ l v => setLocal n l v
  | .def _ q v m d => .def n q v m d | varDeref _ q => varDeref n q | varRef _ q => varRef n q
  | typeErase _ v => typeErase n v | dynamicCall _ f a => dynamicCall n f a
  | namedRecursion _ f b a d => namedRecursion n f b a d
  | recursionReference _ => recursionReference n | truthy _ v => truthy n v
  | jump _ b l => jump n b l | branchSet _ s v => branchSet n s v
  | branchGet _ s t => branchGet n s t | branch _ c t e m => branch n c t e m
  | loop _ l m s b => loop n l m s b | case_ _ s k v c d m => case_ n s k v c d m
  | try_ _ c m s f => try_ n c m s f | catch_ _ t m s f => catch_ n t m s f
  | .finally _ m => .finally n m | throw_ _ v => throw_ n v | ret _ t v => ret n t v
  | cppScopeOpen _ => cppScopeOpen n | cppScopeClose _ s => cppScopeClose n s
  | cppOpaque k _ t r => cppOpaque k n t r

/-- The `type` each constructor passes to `instruction{ kind, name, type }` (instruction.cpp). -/
def type : Inst → CppType
  | nop _ => Ty.void
  | parameter _ t | capture _ t _ | literal _ t _ _ | local_ _ t | branchGet _ _ t
  | ret _ t _ | catch_ _ t _ _ _ | cppOpaque _ _ t _ => t
  | persistentList .. => Ty.obj "persistent_list"
  | persistentVector .. => Ty.obj "persistent_vector"
  | persistentArrayMap .. => Ty.obj "persistent_array_map"
  | persistentHashMap .. => Ty.obj "persistent_hash_map"
  | persistentHashSet .. => Ty.obj "persistent_hash_set"
  | function .. => Ty.obj "jit_function"
  | closure .. => Ty.obj "jit_closure"
  | .def .. | varRef .. => Ty.varRef
  | varDeref .. | typeErase .. | dynamicCall .. | namedRecursion .. | recursionReference .. =>
      Ty.objectRef
  | truthy .. => Ty.bool
  | _ => Ty.void

/-- `is_terminator` (instruction.cpp: jump, branch, loop, case_, ret; everything else false). -/
def isTerminator : Inst → Bool
  | jump .. | branch .. | loop .. | case_ .. | ret .. => true
  | _ => false

def isScopeClose : Inst → Bool
  | cppScopeClose .. => true
  | _ => false

def kindName : Inst → String
  | nop .. => "nop" | parameter .. => "parameter" | capture .. => "capture" | literal .. => "literal"
  | persistentList .. => "persistent-list" | persistentVector .. => "persistent-vector"
  | persistentArrayMap .. => "persistent-array-map" | persistentHashMap .. => "persistent-hash-map"
  | persistentHashSet .. => "persistent-hash-set" | function .. => "function"
  | closure .. => "closure" | letfn .. => "letfn" | local_ .. => "local" | setLocal .. => "set-local"
  | .def .. => "def" | varDeref .. => "var-deref" | varRef .. => "var-ref"
  | typeErase .. => "type-erase" | dynamicCall .. => "dynamic-call"
  | namedRecursion .. => "named-recursion" | recursionReference .. => "recursion-reference"
  | truthy .. => "truthy" | jump .. => "jump" | branchSet .. => "branch-set"
  | branchGet .. => "branch-get" | branch .. => "branch" | loop .. => "loop" | case_ .. => "case"
  | try_ .. => "try" | catch_ .. => "catch" | .finally .. => "finally" | throw_ .. => "throw"
  | ret .. => "ret" | cppScopeOpen .. => "cpp/scope-open" | cppScopeClose .. => "cpp/scope-close"
  | cppOpaque k .. => k

end Inst

/-- `ir::block` (processor.hpp:30). -/
structure Block where
  index : Nat
  name : Ident
  insts : Array Inst := #[]
  deriving Repr, Inhabited

/-- `block::has_terminator` (processor.cpp:60-78): scope closes may follow a terminator. -/
def Block.hasTerminator (b : Block) : Bool := Id.run do
  if b.insts.isEmpty then return false
  for i in b.insts.toList.reverse do
    if i.isScopeClose then continue
    return i.isTerminator
  return false

/-- What the IR function keeps of `jtl::ref<analyze::expr::function_arity>`, as the code generator
reads it (cpp_processor.cpp:1939-2040). -/
structure ArityInfo where
  /-- Each parameter's symbol name and type (`fn.arity->params`). -/
  params : List (String × CppType)
  /-- `fn.arity->frame->captures`: name and the capture's binding type. -/
  captures : List (String × CppType)
  /-- `fn.arity->fn_ctx->fn->name`, `unique_name`. -/
  fnName : String
  fnUniqueName : String
  /-- `fn.arity->fn_ctx->param_count`. -/
  paramCount : Nat
  /-- `fn.arity->body->values.empty()`. -/
  bodyEmpty : Bool
  fnCtx : FnCtxId
  deriving Repr, Inhabited

/-- `ir::function` (processor.hpp:41). -/
structure IrFn where
  index : Nat
  arity : ArityInfo
  name : Ident := ""
  blocks : Array Block := #[]
  immediateDominators : List (Ident × Ident) := []
  rpo : List Ident := []
  blockRpoIndex : List (Ident × Nat) := []
  deriving Repr, Inhabited

/-- `function::add_block` (processor.cpp:32-37). -/
def IrFn.addBlock (f : IrFn) (name : Ident) : IrFn × Nat :=
  let index := f.blocks.size
  ({ f with blocks := f.blocks.push { index, name } }, index)

/-- `function::remove_block` (processor.cpp:39-46): later blocks' `index` decremented. -/
def IrFn.removeBlock (f : IrFn) (index : Nat) : IrFn :=
  let bs := f.blocks.eraseIdxIfInBounds index
  { f with blocks := bs.mapIdx fun i b => if i ≥ index then { b with index := b.index - 1 } else b }

/-- `function::find_block` (processor.cpp:48-58): `jank_panic` when missing. -/
def IrFn.findBlock (f : IrFn) (name : Ident) : Except String Nat :=
  match f.blocks.findIdx? (·.name == name) with
  | some i => .ok i
  | none => .error s!"panic: Unable to find IR block '{name}'."

/-- `codegen::compilation_target` (cpp_processor.hpp:19). -/
inductive Target where
  | module | moduleFunction | eval
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `module::lifted_var`. -/
structure LiftedVar where
  name : Ident
  owned : Bool
  deriving Repr, BEq, Inhabited

/-- `ir::module` (processor.hpp:75-101). The two constant maps are keyed by
`very_equal_to_with_meta` / `very_equal_to` with `std::hash<object_ref>`; `Global.constKey` decides
when a key is found. -/
structure Module where
  name : String
  target : Target
  arityFlags : Nat
  rootFn : ExprId
  entryPoints : List String
  functions : Array IrFn := #[]
  liftedConstants : List (Obj × Ident) := []
  liftedCppConstants : List (Obj × Ident) := []
  liftedVars : List (String × LiftedVar) := []
  deriving Repr, Inhabited

/-! ## Builder state (builder.hpp:35-175) -/

/-- The per-function builder (`ir::builder`): one per `gen_arity`, on the C++ stack. -/
structure Builder where
  fnIndex : Nat := 0
  blockIndex : Nat := 0
  identCount : Nat := 0
  /-- `unordered_map<immutable_string, identifier>`. -/
  locals : List (String × Ident) := []
  localToLoopShadow : List (String × Ident) := []
  allowedDefers : List String := []
  usedIdentifiers : List Ident := []
  loopRecurTarget : Option Nat := none
  fnRecurTarget : Option Nat := none
  deriving Repr, Inhabited

/-- What every builder shares: the module, the analyzer's arena (expressions are mutated by
`propagate_position`), the namespace's symbol counter (`unique_string`), and how constants
compare (`very_equal_to_with_meta` and the hash, supplied by the caller). -/
structure Global where
  mod : Module
  arena : Arena
  counter : Nat := 0
  /-- `true` when two objects land on the same key of the lifted-constant map. -/
  constKey : Obj → Obj → Bool := fun a b => a == b
  deriving Inhabited

structure GenState where
  g : Global
  b : Builder

abbrev GenM := StateT GenState (Except String)

/-- `context::unique_string(prefix)` (context.cpp:380-384): `prefix_N`, N the incremented counter. -/
def uniqueStr (pfx : String) : GenM String := do
  let s ← get
  let n := s.g.counter + 1
  set { s with g := { s.g with counter := n } }
  pure (uniqueString pfx n)

/-- `unique_string()` (prefix `G_`). -/
def uniqueStr0 : GenM String := uniqueStr "G_"

def assocGet? (l : List (String × α)) (k : String) : Option α := (l.find? (·.1 == k)).map (·.2)

def assocSet (l : List (String × α)) (k : String) (v : α) : List (String × α) :=
  if l.any (·.1 == k) then l.map fun p => if p.1 == k then (k, v) else p else l ++ [(k, v)]

def curFn : GenM IrFn := do
  let s ← get
  match s.g.mod.functions[s.b.fnIndex]? with
  | some f => pure f
  | none => throw "no current function"

def setCurFn (f : IrFn) : GenM Unit :=
  modify fun s => { s with g := { s.g with mod := { s.g.mod with
    functions := s.g.mod.functions.set! s.b.fnIndex f } } }

/-- `current_function()->blocks[block_index].instructions.emplace_back(...)`. -/
def emit (i : Inst) : GenM Unit := do
  let f ← curFn
  let bi := (← get).b.blockIndex
  match f.blocks[bi]? with
  | some blk => setCurFn { f with blocks := f.blocks.set! bi { blk with insts := blk.insts.push i } }
  | none => throw "no current block"

/-- `builder::next_ident(prefix)` (builder.cpp:17-27). -/
def nextIdentP (pfx : String) : GenM Ident := do
  let mut fuel := 100000
  let mut ret := ""
  repeat
    let s ← get
    ret := pfx ++ toString s.b.identCount
    set { s with b := { s.b with identCount := s.b.identCount + 1 } }
    fuel := fuel - 1
    if !(s.b.usedIdentifiers.contains ret) || fuel == 0 then break
  modify fun s => { s with b := { s.b with usedIdentifiers := s.b.usedIdentifiers ++ [ret] } }
  pure ret

/-- `builder::next_ident()` (builder.cpp:12-15). -/
def nextIdent : GenM Ident := nextIdentP "v"

/-- `builder::next_shadow()` (builder.cpp:29-32). -/
def nextShadow : GenM Ident := nextIdentP "s"

/-- `builder::current_block()` (builder.cpp:39-42). -/
def curBlock : GenM Block := do
  let f ← curFn
  match f.blocks[(← get).b.blockIndex]? with
  | some b => pure b
  | none => throw "no current block"

/-- `builder::block(name)` (builder.cpp:44-47). -/
def newBlock (name : Ident) : GenM Nat := do
  let f ← curFn
  let (f, i) := f.addBlock name
  setCurFn f
  pure i

/-- `builder::block_name(index)` (builder.cpp:49-52). -/
def blockName (i : Nat) : GenM Ident := do
  match (← curFn).blocks[i]? with
  | some b => pure b.name
  | none => throw s!"no block {i}"

/-- `builder::remove_block(index)` (builder.cpp:54-63). -/
def removeBlockB (i : Nat) : GenM Unit := do
  setCurFn ((← curFn).removeBlock i)
  modify fun s => { s with b := { s.b with
    blockIndex := if s.b.blockIndex ≥ i then s.b.blockIndex - 1 else s.b.blockIndex } }

/-- `builder::enter_block(index)` (builder.cpp:65-68). -/
def enterBlock (i : Nat) : GenM Unit := modify fun s => { s with b := { s.b with blockIndex := i } }

/-- The tail-position epilogue every value-producing builder method ends with:
`if(pos == tail) return ret(name, type); return name;`. -/
def tailRet (pos : ExprPosition) (name : Ident) (type : CppType) : GenM Ident := do
  if pos == .tail then
    let n ← nextIdent
    emit (.ret n type name)
    pure n
  else pure name

/-- `builder::ret` (builder.cpp:522-528). -/
def bRet (value : Ident) (type : CppType) : GenM Ident := do
  let n ← nextIdent
  emit (.ret n type value)
  pure n

/-- `builder::parameter` (builder.cpp:70-83): the instruction is named `munge(value)`, which is
added to `used_identifiers`. -/
def bParameter (pos : ExprPosition) (type : CppType) (value : String) : GenM Ident := do
  let name := munge value
  modify fun s => { s with b := { s.b with usedIdentifiers := s.b.usedIdentifiers ++ [name] } }
  emit (.parameter name type)
  tailRet pos name type

/-- `builder::capture` (builder.cpp:85-97). -/
def bCapture (pos : ExprPosition) (type : CppType) (value : String) : GenM Ident := do
  let name ← nextIdent
  emit (.capture name type value)
  tailRet pos name type

/-- The key lookup of `mod->lifted_constants.find(value)`. -/
def findConst (l : List (Obj × Ident)) (eq : Obj → Obj → Bool) (o : Obj) : Option Ident :=
  (l.find? fun p => eq p.1 o).map (·.2)

/-- `builder::literal` (builder.cpp:99-123): the lifted constant is found by
`very_equal_to_with_meta`, else named `munge(unique_string("const"))`. -/
def bLiteral (pos : ExprPosition) (value : Obj) : GenM Ident := do
  let type := literalCodegenTypeBoxed value
  let s ← get
  let lifted ← match findConst s.g.mod.liftedConstants s.g.constKey value with
    | some n => pure n
    | none => do
      let n := munge (← uniqueStr "const")
      modify fun s => { s with g := { s.g with mod := { s.g.mod with
        liftedConstants := s.g.mod.liftedConstants ++ [(value, n)] } } }
      pure n
  let name ← nextIdent
  emit (.literal name type value lifted)
  tailRet pos name type

/-- `builder::persistent_list` .. `persistent_hash_set` (builder.cpp:125-194). -/
def bColl (pos : ExprPosition) (mk : Ident → Inst) : GenM Ident := do
  let name ← nextIdent
  let i := mk name
  emit i
  tailRet pos name i.type

/-- `builder::function` (builder.cpp:196-209). -/
def bFunction (pos : ExprPosition) (arities : List (Nat × String)) (flags : Nat) (variadic : Bool) :
    GenM Ident := bColl pos fun n => .function n arities flags variadic

/-- `builder::closure` (builder.cpp:211-233). -/
def bClosure (pos : ExprPosition) (ctx : String) (arities : List (Nat × String))
    (captures : List (String × (Ident × CppType))) (flags : Nat) (variadic : Bool) : GenM Ident :=
  bColl pos fun n => .closure n ctx arities captures flags variadic

/-- `builder::letfn` (builder.cpp:235-241). -/
def bLetfn (bindings : List String) : GenM Ident := do
  let n ← nextIdent
  emit (.letfn n bindings)
  pure n

/-- `builder::local` (builder.cpp:243-249). -/
def bLocal (type : CppType) : GenM Ident := do
  let n ← nextIdent
  emit (.local_ n type)
  pure n

/-- `builder::set_local` (builder.cpp:251-257). -/
def bSetLocal (loc value : Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.setLocal n loc value)
  pure n

/-- `builder::def` (builder.cpp:259-274). -/
def bDef (pos : ExprPosition) (qv : String) (value : Option Ident) (mta : Obj) (dyn : Bool) :
    GenM Ident := do
  let n ← nextIdent
  emit (.def n qv value mta dyn)
  tailRet pos n Ty.varRef

/-- `builder::var_deref` (builder.cpp:276-301): `unique_string(qualified_var)` is called first
(it bumps the counter even when the var is already lifted); a new lifted var is named
`munge_and_replace(us, "\\.", "_")`. -/
def bVarDeref (pos : ExprPosition) (qv : String) : GenM Ident := do
  let name ← nextIdent
  let us ← uniqueStr qv
  let s ← get
  if (assocGet? s.g.mod.liftedVars qv).isNone then
    modify fun s => { s with g := { s.g with mod := { s.g.mod with
      liftedVars := s.g.mod.liftedVars ++ [(qv, { name := mungeAndReplaceDots us, owned := false })] } } }
  emit (.varDeref name qv)
  tailRet pos name Ty.objectRef

/-- `builder::var_ref` (builder.cpp:303-319): `lifted_vars.emplace` (no overwrite). -/
def bVarRef (pos : ExprPosition) (qv : String) : GenM Ident := do
  let us ← uniqueStr qv
  let s ← get
  if (assocGet? s.g.mod.liftedVars qv).isNone then
    modify fun s => { s with g := { s.g with mod := { s.g.mod with
      liftedVars := s.g.mod.liftedVars ++ [(qv, { name := mungeAndReplaceDots us, owned := false })] } } }
  let name ← nextIdent
  emit (.varRef name qv)
  tailRet pos name Ty.varRef

/-- `builder::type_erase` (builder.cpp:321-332). -/
def bTypeErase (pos : ExprPosition) (value : Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.typeErase n value)
  tailRet pos n Ty.objectRef

/-- `builder::dynamic_call` (builder.cpp:334-347). -/
def bDynamicCall (pos : ExprPosition) (fn : Ident) (args : List Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.dynamicCall n fn args)
  tailRet pos n Ty.objectRef

/-- `builder::named_recursion` (builder.cpp:349-370). -/
def bNamedRecursion (pos : ExprPosition) (fn : Ident) (base : String) (args : List Ident)
    (needsDyn : Bool) : GenM Ident := do
  let n ← nextIdent
  emit (.namedRecursion n fn base args needsDyn)
  tailRet pos n Ty.objectRef

/-- `builder::recursion_reference` (builder.cpp:372-383). -/
def bRecursionReference (pos : ExprPosition) : GenM Ident := do
  let n ← nextIdent
  emit (.recursionReference n)
  tailRet pos n Ty.objectRef

/-- `builder::truthy` (builder.cpp:385-391). -/
def bTruthy (value : Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.truthy n value)
  pure n

/-- `builder::jump(index[, loop])` (builder.cpp:393-409). -/
def bJump (index : Nat) (loop : Bool := false) : GenM Ident := do
  let n ← nextIdent
  let blk ← blockName index
  emit (.jump n blk loop)
  pure n

/-- `builder::branch_set` (builder.cpp:411-417). -/
def bBranchSet (shadow value : Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.branchSet n shadow value)
  pure n

/-- `builder::branch_get` (builder.cpp:419-427). -/
def bBranchGet (shadow : Ident) (type : CppType) : GenM Ident := do
  let n ← nextIdent
  emit (.branchGet n shadow type)
  pure n

/-- `builder::branch` (builder.cpp:429-438). -/
def bBranch (c t e m : Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.branch n c t e m)
  pure n

/-- `builder::loop` (builder.cpp:440-449). -/
def bLoop (lb : Ident) (mb : Option Ident) (shadow : Option (Ident × CppType))
    (shadows : List LoopShadow) : GenM Ident := do
  let n ← nextIdent
  emit (.loop n lb mb shadow shadows)
  pure n

/-- `builder::case_` (builder.cpp:451-469). -/
def bCase (shift mask : Int) (value : Ident) (cases : List (Int × Ident)) (d m : Ident) :
    GenM Ident := do
  let n ← nextIdent
  emit (.case_ n shift mask value cases d m)
  pure n

/-- `builder::try_` (builder.cpp:471-485). -/
def bTry (catches : List (CppType × Ident)) (merge shadow : Ident) (fin : Option Ident) :
    GenM Ident := do
  let n ← nextIdent
  emit (.try_ n catches merge shadow fin)
  pure n

/-- `builder::catch_` (builder.cpp:487-496). -/
def bCatch (type : CppType) (merge shadow fin : Option Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.catch_ n type merge shadow fin)
  pure n

/-- `builder::finally` (builder.cpp:498-504). -/
def bFinally (merge : Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.finally n merge)
  pure n

/-- `builder::throw_()` / `throw_(value, type)` (builder.cpp:506-520). -/
def bThrow (value : Option (Ident × CppType)) : GenM Ident := do
  let n ← nextIdent
  emit (.throw_ n value)
  pure n

/-- `builder::cpp_scope_open` (builder.cpp:530-536): named with the `s` prefix. -/
def bScopeOpen : GenM Ident := do
  let n ← nextIdentP "s"
  emit (.cppScopeOpen n)
  pure n

/-- `builder::cpp_scope_close` (builder.cpp:538-544). -/
def bScopeClose (scope : Ident) : GenM Ident := do
  let n ← nextIdent
  emit (.cppScopeClose n scope)
  pure n

/-- Every `builder::cpp_*` method (builder.cpp:546-753), opaque: a named instruction of the
expression's type, then the tail epilogue. -/
def bCppOpaque (kind : String) (pos : ExprPosition) (type : CppType) (refs : List Ident) :
    GenM Ident := do
  let n ← nextIdent
  emit (.cppOpaque kind n type refs)
  tailRet pos n type

end Jank.Codegen

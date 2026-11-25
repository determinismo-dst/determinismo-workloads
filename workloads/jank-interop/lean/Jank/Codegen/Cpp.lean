import Jank.Codegen.Ir
import Jank.Codegen.Float

/-!
# IR to C++: `src/cpp/jank/codegen/cpp_processor.cpp` (jank 7135b7708)

7135b7708 changed cpp_processor.cpp in place (no line moved): `lift_constant` tests
`is_typed_object_ref` (line 172, the renamed `is_typed_object`), `gen(cpp_into_object)` declares
its result `auto &&` (line 1321), `gen(cpp_call)` tests `is_any_object_ref` (interop).

One Lean definition per C++ function of cpp_processor.cpp except the `cpp_*` instruction cases
(interop agent), which are opaque here (`gen(cpp_opaque)` writes a declaration of the right name
whose value is unknown). Text is built exactly with `util::format`'s `{}` rules (`formatTo`).

The process-wide caches `global_constants` / `global_vars` (cpp_processor.cpp:123-129) and the
runtime heap they point into are `Heap`: an object's address is its index in `objs` (as
`0x%llx`, string_builder.cpp:152-163), a var's address is `varBase` + its index.
-/

namespace Jank.Codegen

open Jank.Analyzer

/-- The JIT process: objects the analyzer created (constants live at an address), interned vars,
and cpp_processor.cpp's two process-wide caches. -/
structure Heap where
  objs : Array Obj := #[]
  vars : Array String := #[]
  globalConstants : List (Obj × String) := []
  globalVars : List (String × String) := []
  deriving Inhabited

def varBase : Nat := 0x10000000

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- An object's address: interned on first use. -/
def Heap.addr (h : Heap) (o : Obj) : Heap × Nat :=
  match h.objs.findIdx? (· == o) with
  | some i => (h, 0x1000 + i * 16)
  | none => ({ h with objs := h.objs.push o }, 0x1000 + h.objs.size * 16)

def Heap.varAddr (h : Heap) (q : String) : Heap × Nat :=
  match h.vars.findIdx? (· == q) with
  | some i => (h, varBase + i * 16)
  | none => ({ h with vars := h.vars.push q }, varBase + h.vars.size * 16)

/-- `get_qualified_type_name(type)`: the type's spelling. -/
def typeName (t : CppType) : String := t.spelling

/-! ## gen_constant (cpp_processor.cpp:253-488) -/

def utf8 (s : String) : List UInt8 := s.toUTF8.toList
def bytesOfString (s : String) : List UInt8 := utf8 s

/-- Bytes to text for code (invalid UTF-8 is not drawn by the program search). -/
def textOf (bs : List UInt8) : String :=
  match String.fromUTF8? (ByteArray.mk bs.toArray) with
  | some s => s
  | none => String.ofList (bs.map fun b => Char.ofNat b.toNat)

/-- `persistent_string::to_code_string` (persistent_string.cpp:52-56): `"` + `escape(data)` + `"`. -/
def stringCode (data : List UInt8) : List UInt8 := [34] ++ escape data ++ [34]

/-- Numbers of `native_big_integer` print in decimal (`d.str()`, string_builder.cpp:235-238). -/
def bigStr (i : Int) : String := toString i

/-- Text for an object's `to_code_string()` where gen_constant needs it for metadata (symbols and
collections with metadata): a simplified printer, adequate for the metadata the search draws. -/
partial def codeString : Obj → String
  | .nil => "nil"
  | .boolean b => sbBool b
  | .integer v => sbI64 v
  | .smallInteger v => sbI32 v
  | .bigInteger v => bigStr v ++ "N"
  | .real b | .smallReal b => Float.sbF64 b
  | .ratio n d => s!"{n}/{d}"
  | .persistentString s => textOf (stringCode (utf8 s))
  | .keyword ns n => ":" ++ (if ns.isEmpty then n else ns ++ "/" ++ n)
  | .symbol _ ns n => if ns.isEmpty then n else ns ++ "/" ++ n
  | .character d => "\\" ++ (match d with
      | "\n" => "newline" | " " => "space" | "\t" => "tab" | "\x08" => "backspace"
      | "\x0c" => "formfeed" | "\r" => "return" | _ => d)
  | .persistentList _ xs | .lazySequence _ xs => "(" ++ " ".intercalate (xs.map codeString) ++ ")"
  | .persistentVector _ xs => "[" ++ " ".intercalate (xs.map codeString) ++ "]"
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs =>
      "{" ++ ", ".intercalate (kvs.map fun (k, v) => codeString k ++ " " ++ codeString v) ++ "}"
  | .persistentHashSet _ xs => "#{" ++ " ".intercalate (xs.map codeString) ++ "}"
  | _ => "#<object>"

/-- `should_gen_meta` (cpp_processor.cpp:248-251): present and not empty. -/
def shouldGenMeta : Option Obj → Bool
  | none => false
  | some .nil => false
  | some (.persistentArrayMap _ []) | some (.persistentHashMap _ []) => false
  | some _ => true

def metaOf : Obj → Option Obj
  | .symbol m _ _ | .persistentList m _ | .persistentVector m _ | .persistentArrayMap m _
  | .persistentHashMap m _ | .persistentHashSet m _ | .cons m _ _ | .lazySequence m _
  | .persistentSortedMap m _ | .persistentSortedSet m _ => m
  | _ => none

/-- The elements a seqable object yields (`make_sequence_range`), for the fallback branch. -/
def seqElems : Obj → Option (List Obj)
  | .cons _ f r => (match r with
      | .persistentList _ xs | .persistentVector _ xs => some xs
      | other => seqElems other).map (f :: ·)
  | .lazySequence _ xs | .seqOf _ xs | .persistentSortedSet _ xs => some xs
  | .persistentSortedMap _ kvs => some (kvs.map fun (k, v) => .persistentVector none [k, v])
  | .nil => some []
  | _ => none

/-- `detail::gen_constant(o, buffer, is_boxed)` (cpp_processor.cpp:253-488), as bytes. -/
partial def genConstant (o : Obj) (isBoxed : Bool) : Except String (List UInt8) :=
  let s := bytesOfString
  let metaPart (m : Option Obj) : List UInt8 :=
    if shouldGenMeta m then s "\"" ++ escape (utf8 (codeString m.get!)) ++ s "\"," else []
  let coll (fn : String) (m : Option Obj) (xs : List Obj) : Except String (List UInt8) := do
    let mut out := s (fn ++ "(") ++ metaPart m ++ s (toString xs.length)
    for x in xs do
      out := out ++ s ", " ++ (← genConstant x true) ++ s ".erase()"
    pure (out ++ s ")")
  let mapColl (fn : String) (m : Option Obj) (kvs : List (Obj × Obj)) : Except String (List UInt8) := do
    let mut out := s (fn ++ "(") ++ metaPart m ++ s (toString kvs.length)
    for (k, v) in kvs do
      out := out ++ s ", " ++ (← genConstant k true) ++ s ".erase(), " ++ (← genConstant v true) ++ s ".erase()"
    pure (out ++ s ")")
  match o with
  | .nil => .ok (s "jank::runtime::jank_nil")
  | .boolean b => .ok (s (if !isBoxed then sbBool b else if b then "jank::runtime::jank_true" else "jank::runtime::jank_false"))
  | .integer v =>
    if !isBoxed then .ok (s (sbI64 v))
    -- `static_cast<i32>(typed_o->data) == typed_o->data`
    else if (v.truncate 32).signExtend 64 == v then .ok (s s!"_jank_small_int({sbI64 v})")
    else .ok (s s!"_jank_int({sbI64 v})")
  | .smallInteger v => .ok (s (if !isBoxed then sbI32 v else s!"_jank_small_int({sbI32 v})"))
  | .real b | .smallReal b =>
    .ok (s (if !isBoxed then Float.sbF64 b else s!"_jank_small_real({Float.sbF64 b})"))
  | .bigInteger v => .ok (s s!"jank::runtime::make_box<jank::runtime::obj::big_integer>(\"{bigStr v}\")")
  | .bigDecimal _ _ => .error "big_decimal constants are not modeled (boost cpp_dec_float::str)"
  | .ratio n d => .ok (s s!"jank::runtime::obj::ratio::create({bigStr n}, {bigStr d})")
  | .symbol m ns n => .ok (s "_jank_symbol( " ++ metaPart m ++ s "\"" ++ utf8 ns ++ s "\", \"" ++ utf8 n ++ s "\")")
  | .character d => .ok (s "jank::runtime::make_box<jank::runtime::obj::character>(\"" ++ escape (utf8 d) ++ s "\")")
  | .keyword ns n => .ok (s "_jank_keyword(\"" ++ utf8 ns ++ s "\", \"" ++ utf8 n ++ s "\")")
  | .persistentString str =>
    let d := utf8 str
    if !isBoxed then .ok (stringCode d)
    else if d.isEmpty then .ok (s "_jank_string()")
    else .ok (s "_jank_string(" ++ stringCode d ++ s ")")
  | .persistentVector m xs => coll "_jank_vec" m xs
  | .persistentList m xs => coll "_jank_list" m xs
  | .persistentHashSet m xs => coll "_jank_hset" m xs
  | .persistentArrayMap m kvs => mapColl "_jank_amap" m kvs
  | .persistentHashMap m kvs => mapColl "_jank_hmap" m kvs
  | o =>
    match seqElems o with
    | some xs => do
      -- "_jank_list({}" with sequence_length, then ", " elem ".erase()" each, then ")"
      let mut out := s s!"_jank_list({xs.length}"
      for x in xs do
        out := out ++ s ", " ++ (← genConstant x true) ++ s ".erase()"
      pure (out ++ s ")")
    | none => .error s!"Unimplemented constant codegen: {repr o.type}"

/-! ## The code generator's builder (cpp_processor.cpp:35-118) -/

structure CB where
  fnIdx : Nat
  blockIndex : Nat := 0
  instIndex : Nat := 0
  cppRaw : String := ""
  moduleHeader : String := ""
  deps : String := ""
  header : String := ""
  body : String := ""
  footer : String := ""
  expression : String := ""
  deferred : List (String × String) := []
  seen : List Ident := []
  deriving Inhabited

/-- What code generation reads and writes besides its builder: the module, the JIT heap and the
namespace counter (`unique_string`), the `debug` option (`#line` directives, default on). -/
structure CgEnv where
  mod : Module
  heap : Heap
  counter : Nat
  debug : Bool := false
  /-- `very_equal_to_with_meta` on the global constant cache's keys. -/
  constKey : Obj → Obj → Bool := fun a b => a == b
  deriving Inhabited

abbrev CgM := StateT CgEnv (Except String)

def cgFn (b : CB) : CgM IrFn := do
  match (← get).mod.functions[b.fnIdx]? with
  | some f => pure f
  | none => throw "panic: Unable to find IR function"

/-- `find_function(module, name)` (cpp_processor.cpp:22-33). -/
def findFunction (name : String) : CgM Nat := do
  match (← get).mod.functions.findIdx? (·.name == name) with
  | some i => pure i
  | none => throw s!"panic: Unable to find IR function '{name}'."

/-- `builder::declaration_str` (cpp_processor.cpp:60-74). -/
def CB.declarationStr (b : CB) : String :=
  b.cppRaw ++ b.moduleHeader ++ b.deps ++ b.header ++ b.body ++ b.footer

/-- `builder::enter_block` (cpp_processor.cpp:43-48). -/
def cbEnter (b : CB) (block : Ident) : CgM CB := do
  let f ← cgFn b
  match f.findBlock block with
  | .ok i => pure { b with blockIndex := i, instIndex := 0,
                           seen := if b.seen.contains block then b.seen else block :: b.seen }
  | .error e => throw e

def cbNext (b : CB) : CB := { b with instIndex := b.instIndex + 1 }

def cbInst? (b : CB) : CgM (Option Inst) := do
  let f ← cgFn b
  pure (do let blk ← f.blocks[b.blockIndex]?; blk.insts[b.instIndex]?)

def emitBody (b : CB) (fmt : String) (args : List String) : CB :=
  { b with body := b.body ++ formatTo fmt args }

/-- `lift_constant` (cpp_processor.cpp:131-213; 7135b7708 tests `is_typed_object_ref`, line 172).
In the eval target, a boxed object is written as
its address (or, for a tagged small integer or real, its value), through the process-wide
`global_constants` cache keyed by `very_equal_to_with_meta`; unboxed, as its printed value.
Otherwise the lifted constant's name. -/
def liftConstant (name : Ident) (o : Obj) (isBoxed : Bool) : CgM String := do
  let env ← get
  if env.mod.target != .eval then return name
  if !isBoxed then
    match o with
    | .real b | .smallReal b => return Float.sbF64 b
    | _ => return codeString o
  match env.heap.globalConstants.find? (fun p => env.constKey p.1 o) with
  | some (_, s) => return s
  | none => pure ()
  let ty := literalTypeBoxed o
  let fmt ← match o with
    | .nil => pure "jank::runtime::jank_nil"
    | .smallInteger v =>
      if v.toInt == -2147483648 then
        pure (formatTo "{}{ static_cast<jtl::i32>({}) }" [typeName ty, sbI32 v])
      else pure (formatTo "{}{ {} }" [typeName ty, sbI32 v])
    | .smallReal b => pure (formatTo "{}{ {} }" [typeName ty, Float.sbF64 b])
    | _ =>
      let (h, a) := env.heap.addr o
      set { env with heap := h }
      pure (formatTo "{}{ _jank_codegen{ }, (void*){} }" [typeName ty, hex a])
  modify fun env => { env with heap := { env.heap with
    globalConstants := env.heap.globalConstants ++ [(o, fmt)] } }
  pure fmt

/-- `lift_var` (cpp_processor.cpp:215-242). -/
def liftVar (qv : String) : CgM String := do
  let env ← get
  if env.mod.target == .eval then
    match assocGet? env.heap.globalVars qv with
    | some s => return s
    | none =>
      let (h, a) := env.heap.varAddr qv
      let fmt := formatTo "jank::runtime::var_ref{ reinterpret_cast<jank::runtime::var*>({}) }" [hex a]
      set { env with heap := { h with globalVars := h.globalVars ++ [(qv, fmt)] } }
      return fmt
  match assocGet? env.mod.liftedVars qv with
  | some v => pure v.name
  | none => throw s!"std::out_of_range: lifted_vars.at({qv})"

mutual

/-- `gen(ir::instruction_ref)` (cpp_processor.cpp:1920-1937): `#line` when debugging, then the
typed overload. -/
partial def cgInst (b : CB) (i : Inst) : CgM (CB × Option Ident) := do
  let b := if (← get).debug then { b with body := b.body ++ "\n#line 1 \"NO_SOURCE_PATH\"\n" } else b
  match i with
  | .def n q v m d => do
    let b := cbNext b
    let b := emitBody b "auto const {}(_jank_var_owned(\"{}\"));\n" [n, q]
    match v with
    | none =>
      pure (emitBody b "{}->with_lazy_meta(\"{}\")->set_dynamic({});\n" [n, escapeStr (codeString m), sbBool d], some n)
    | some val =>
      pure (emitBody b "{}->bind_root({})->with_lazy_meta(\"{}\")->set_dynamic({});\n"
        [n, val, escapeStr (codeString m), sbBool d], some n)
  | .varDeref n q => do
    let b := cbNext b
    let lifted ← liftVar q
    pure (emitBody b "auto const {}({}->deref());\n" [n, lifted], some n)
  | .varRef n q => do
    let b := cbNext b
    let lifted ← liftVar q
    pure (emitBody b "auto const {}({});\n" [n, lifted], some n)
  | .typeErase n v =>
    pure (emitBody (cbNext b) "jank::runtime::object_ref const {}({});\n" [n, v], some n)
  | .dynamicCall n fn args => do
    let mut b := emitBody (cbNext b) "auto const {}({}.call(" [n, fn]
    let mut needComma := false
    for a in args do
      if needComma then b := emitBody b "," []
      needComma := true
      b := emitBody b " {}" [a]
    pure (emitBody b "));\n" [], some n)
  | .literal n _ o v => do
    let b := cbNext b
    let lifted ← liftConstant v o true
    pure (emitBody b "auto const {}({});\n" [n, lifted], some n)
  | .persistentList n vs m => pure (cgColl (cbNext b) "_jank_list" n vs m ", ", some n)
  | .persistentVector n vs m => pure (cgColl (cbNext b) "_jank_vec" n vs m ", ", some n)
  | .persistentHashSet n vs m => pure (cgColl (cbNext b) "_jank_hset" n vs m ",", some n)
  | .persistentArrayMap n kvs m => pure (cgMapColl (cbNext b) "_jank_amap" n kvs m, some n)
  | .persistentHashMap n kvs m => pure (cgMapColl (cbNext b) "_jank_hmap" n kvs m, some n)
  | .function n arities flags variadic => do
    let mut b := emitBody (cbNext b) "auto const {}(" [n]
    b := if variadic then emitBody b "_jank_vfn({})" [toString flags] else emitBody b "_jank_fn({})" [toString flags]
    b := emitBody b ");\n" []
    for (k, fname) in arities do
      b := emitBody b "{}->arity_{} = &{};\n" [n, toString k, fname]
      let nested ← cgFunctionByName fname
      b := { b with deps := b.deps ++ nested.declarationStr }
    pure (b, some n)
  | .closure n ctx arities caps flags variadic => do
    let mut b := cbNext b
    b := { b with deps := b.deps ++ formatTo "struct {}{" [ctx] }
    b := emitBody b "auto const {}(jtl::make_ref<struct {}>(" [ctx, ctx]
    let mut needComma := false
    for (cname, (cv, cty)) in caps do
      b := { b with deps := b.deps ++ formatTo "{} {};\n" [typeName cty, munge cname] }
      if needComma then b := emitBody b ", " []
      needComma := true
      if cv == ":defer" then
        b := { b with deferred := b.deferred ++ [(ctx, cname)] }
        b := { b with body := b.body ++ "jank::runtime::jank_nil" }
      else b := { b with body := b.body ++ cv }
    b := { b with deps := b.deps ++ "};\n" }
    b := emitBody b "));\n" []
    b := emitBody b "auto const {}(" [n]
    b := if variadic then emitBody b "_jank_vclosure({}, {}.data)" [toString flags, ctx]
         else emitBody b "_jank_closure({}, {}.data)" [toString flags, ctx]
    b := emitBody b ");\n" []
    for (k, fname) in arities do
      b := emitBody b "{}->arity_{} = &{};\n" [n, toString k, fname]
      let nested ← cgFunctionByName fname
      b := { b with deps := b.deps ++ nested.declarationStr }
    pure (b, some n)
  | .nop _ => pure (cbNext b, none)
  | .parameter n _ => pure (cbNext b, some n)
  | .capture n _ v => do
    let f ← cgFn b
    let closureCtx := munge (f.arity.fnUniqueName ++ "_ctx")
    pure (emitBody (cbNext b) "auto &&{}({}->{});\n" [n, closureCtx, munge v], some n)
  | .recursionReference n => do
    let f ← cgFn b
    pure (emitBody (cbNext b) "auto &&{}({});\n" [n, munge f.arity.fnName], some n)
  | .namedRecursion n fn base args needsDyn => do
    let mut b := cbNext b
    let mut needsComma := false
    if needsDyn then b := emitBody b "auto const {}({}.call(" [n, fn]
    else
      let fnName := formatTo "{}_{}" [base, toString args.length]
      b := emitBody b "auto const {}({}({}" [n, fnName, fn]
      needsComma := true
      b := { b with deps := b.deps ++ formatTo "extern \"C\" jank::runtime::object_ref {}(jank::runtime::object_ref const" [fnName] }
      for _ in args do b := { b with deps := b.deps ++ ", jank::runtime::object_ref" }
      b := { b with deps := b.deps ++ ");\n" }
    for a in args do
      if needsComma then b := emitBody b "," []
      needsComma := true
      b := emitBody b " {}" [a]
    pure (emitBody b "));\n" [], some n)
  | .letfn n bindings => do
    let mut b := cbNext b
    let mut bound : List (String × Ident) := []
    for bnd in bindings do
      let some nx ← cbInst? b | throw "letfn: missing binding instruction"
      let (b', r) ← cgInst b nx
      b := b'
      let some r := r | throw "panic: unwrap of none (letfn binding)"
      bound := assocSet bound bnd r
    for (ctx, field) in b.deferred do
      -- `bindings[deferred.second]`: default-inserted empty when this letfn did not bind it
      let v := (assocGet? bound field).getD ""
      if (assocGet? bound field).isNone then bound := bound ++ [(field, "")]
      b := emitBody b "{}->{} = {};\n" [ctx, field, v]
    pure (b, some n)
  | .local_ n t => do
    -- lvalue reference types lose the reference (cpp_processor.cpp:912-916)
    pure (emitBody (cbNext b) "{} {}{ };\n" [typeName t, n], some n)
  | .setLocal _ l v => pure (emitBody (cbNext b) "{} = std::move({});\n" [l, v], none)
  | .jump _ blk loop => do
    let mut b := cbNext b
    if loop then b := emitBody b "continue;\n" []
    let mut g := 1000
    while g > 0 do
      g := g - 1
      match ← cbInst? b with
      | some j => let (b', _) ← cgInst b j; b := b'
      | none => break
    if b.seen.contains blk then return (b, none)
    pure (← cbEnter b blk, none)
  | .truthy n v => pure (emitBody (cbNext b) "auto const {}(jank::runtime::truthy({}));\n" [n, v], some n)
  | .branchGet n sh _ => pure (emitBody (cbNext b) "auto {}({});\n" [n, sh], some n)
  | .branchSet _ sh v => pure (emitBody (cbNext b) "{} = {};\n" [sh, v], none)
  | .branch _ c t e m => do
    let b := emitBody b "if({}){\n" [c]
    let b ← cbEnter b t
    let b ← cgUntilJump (some m) b
    let b := emitBody b "} else {\n" []
    let b ← cbEnter b e
    let b ← cgUntilJump (some m) b
    let b := emitBody b "}\n" []
    pure (← cbEnter b m, none)
  | .loop _ lb mb _ shadows => do
    let mut b := cbNext b
    for sh in shadows do
      if isAnyObject sh.type then b := emitBody b "jank::runtime::object_ref {}({});\n" [sh.name, sh.value]
      else b := emitBody b "auto {}({});\n" [sh.name, sh.value]
    b := emitBody b "while(true){\n" []
    b ← cbEnter b lb
    b ← cgUntilJump mb b
    b := emitBody b " break; }\n" []
    if let some m := mb then b ← cbEnter b m
    pure (b, none)
  | .throw_ n v => do
    let mut b := cbNext b
    match v with
    | some (val, ty) =>
      if isAnyObject ty then b := emitBody b "throw static_cast<jank::runtime::object_ref>({});\n" [val]
      else b := emitBody b "throw {};\n" [val]
    | none => b := emitBody b "throw;\n" []
    pure (emitBody b "jank::runtime::obj::nil_ref {};\n" [n], some n)
  | .try_ _ catches merge _ fin => do
    let mut b := cbNext b
    let mut guard : Ident := ""
    if let some fb := fin then
      b := emitBody b "{" []
      let (ii, bi) := (b.instIndex, b.blockIndex)
      b ← cbEnter b fb
      let some fi ← cbInst? b | throw "finally block empty"
      guard := fi.name
      let (b', _) ← cgInst b fi
      b := { b' with instIndex := ii, blockIndex := bi }
    b := emitBody b "try {\n" []
    let jb := match fin with | some fb => some fb | none => some merge
    b ← cgUntilJump jb b
    b := emitBody b "}\n" []
    for (_, cb) in catches do
      b ← cbEnter b cb
      let some ci ← cbInst? b | throw "catch block empty"
      let (b', _) ← cgInst b ci
      b := b'
    if fin.isSome then
      let fname := formatTo "{}_fn" [guard]
      b := emitBody b "catch(...) { {}.release(); {}(); throw; } {}.release(); {}(); }\n" [guard, fname, guard, fname]
    pure (← cbEnter b merge, none)
  | .catch_ n ty m _ fin => do
    let mut b := cbNext b
    if ty == Ty.void then
      b := emitBody b "catch(...) {\n" []
      b := emitBody b "jank::runtime::object_ref {};\n" [n]
    else b := emitBody b "catch({} {}) {\n" [typeName ty, n]
    let jb := match fin with | some fb => some fb | none => m
    b ← cgUntilJump jb b
    pure (emitBody b "}\n" [], none)
  | .finally n m => do
    let fname := n ++ "_fn"
    let mut b := emitBody (cbNext b) "auto const {}{ [&](){\n" [fname]
    b ← cgUntilJump (some m) b
    b := emitBody b "} };\n" []
    pure (emitBody b "jank::util::scope_exit {}{ {}, true };\n" [n, fname], none)
  | .case_ _ shift mask v cases d m => do
    let mut b := cbNext b
    b := emitBody b "switch(jank_shift_mask_case_integer(static_cast<jank::runtime::object*>({}.erase().raw()), {}, {})) {\n"
      [v, sbInt shift, sbInt mask]
    for (k, cbk) in cases do
      b := emitBody b "case {}: {\n" [sbInt k]
      b ← cbEnter b cbk
      b ← cgUntilJump (some m) b
      b := emitBody b "break; }" []
    b := emitBody b "default: {\n" []
    b ← cbEnter b d
    b ← cgUntilJump (some m) b
    b := emitBody b "break; }\n" []
    b := emitBody b "}\n" []
    pure (← cbEnter b m, none)
  | .ret _ _ v => pure (emitBody (cbNext b) "return {};\n" [v], none)
  | .cppScopeOpen n =>
    let b := cbNext b
    if n == "s0" then pure (b, none) else pure (emitBody b "{\n" [], none)
  | .cppScopeClose _ sc =>
    let b := cbNext b
    if sc == "s0" then pure (b, none) else pure (emitBody b "}\n" [], none)
  | .cppOpaque k n ty refs =>
    if k.startsWith "cppConversion|" then
      -- `gen(cpp_into_object)` / `gen(cpp_from_object)` (cpp_processor.cpp:1287-1338)
      let parts := k.splitOn "|"
      let policy := parts.getD 1 "from_object"
      let convT := parts.getD 2 ""
      let v := refs.headD ""
      let b := cbNext b
      if convT == "void" then
        pure (emitBody b "auto const {}(jank::runtime::jank_nil);\n" [n], some n)
      else if isUntypedObject ty && isAnyObject (.named convT) then
        pure (emitBody b "auto &&{}({});\n" [n, v], some n)
      else if ty == Ty.obj "integer" then
        pure (emitBody b "auto const {}(jank::runtime::make_box<jank::runtime::obj::integer>({}));\n" [n, v], some n)
      else
        pure (emitBody b "auto &&{}(jank::runtime::convert<{}>::{}({}));\n" [n, convT, policy, v], some n)
    else
    -- interop instructions: a value of unknown meaning named `n`
    pure (emitBody (cbNext b) "auto &&{}(jank_cpp_opaque(\"{}\"{}));\n"
      [n, k, String.join (refs.map (", " ++ ·))], some n)

/-- `cgColl` for list/vector/set (cpp_processor.cpp:616-707): with meta `{}.erase(), ` for lists
and vectors, `{}.erase(),` (no space) for sets and maps. -/
partial def cgColl (b : CB) (fn : String) (n : Ident) (vs : List Ident) (m : Option Ident)
    (metaSep : String) : CB :=
  let b := emitBody b ("auto const {}(" ++ fn ++ "(") [n]
  let b := match m with
    | some mm => emitBody b ("{}.erase()" ++ metaSep) [mm]
    | none => b
  let b := emitBody b "{}" [toString vs.length]
  let b := vs.foldl (fun b v => emitBody b ", {}.erase()" [v]) b
  emitBody b "));\n" []

partial def cgMapColl (b : CB) (fn : String) (n : Ident) (kvs : List (Ident × Ident))
    (m : Option Ident) : CB :=
  let b := emitBody b ("auto const {}(" ++ fn ++ "(") [n]
  let b := match m with
    | some mm => emitBody b "{}.erase()," [mm]
    | none => b
  let b := emitBody b "{}" [toString kvs.length]
  let b := kvs.foldl (fun b (k, v) => emitBody b ", {}.erase(), {}.erase()" [k, v]) b
  emitBody b "));\n" []

/-- `gen_until_jump` (cpp_processor.cpp:493-526). -/
partial def cgUntilJump (jumpBlock : Option Ident) (b : CB) : CgM CB := do
  let mut b := b
  let mut g := 100000
  while g > 0 do
    g := g - 1
    let some cur ← cbInst? b | break
    match cur with
    | .jump _ blk _ =>
      if b.seen.contains blk then
        let (b', _) ← cgInst b cur
        return b'
      let (b', _) ← cgInst b cur
      b := b'
      if jumpBlock == some blk then break
    | .ret .. =>
      let (b', _) ← cgInst b cur
      b := b'
      break
    | _ =>
      let (b', _) ← cgInst b cur
      b := b'
  pure b

/-- `builder nested{ module, name }; gen(*nested.function, nested);` -/
partial def cgFunctionByName (name : String) : CgM CB := do
  let i ← findFunction name
  cgFunction { fnIdx := i }

/-- `gen(ir::function const &, builder &)` (cpp_processor.cpp:1939-2040). -/
partial def cgFunction (b : CB) : CgM CB := do
  let f ← cgFn b
  let a := f.arity
  let mungedFnName := munge a.fnName
  let mungedLinkage := munge a.fnUniqueName
  let closureCtx := munge (a.fnUniqueName ++ "_ctx")
  let paramShadowsFn := a.params.any fun (p, _) => p == a.fnName
  let mut b := emitBody b "\nextern \"C\" jank::runtime::object_ref {}_{}(jank::runtime::object_ref const {}"
    [mungedLinkage, toString a.params.length, if paramShadowsFn then "" else mungedFnName]
  let mut paramNames : List String := []
  for (p, ty) in a.params do
    if isUntypedObject ty then
      let m := munge p
      b := emitBody b ", jank::runtime::object_ref {}" [m]
      paramNames := paramNames ++ [m]
    else
      let n := (← get).counter + 1
      modify fun e => { e with counter := n }
      let m := munge (uniqueString p n)
      b := emitBody b ", jank::runtime::object_ref {}" [m]
      paramNames := paramNames ++ [m]
  b := emitBody b ") {\n" []
  if !a.captures.isEmpty then
    b := emitBody b "auto const * const {}{ static_cast<struct {}*>(static_cast<jank::runtime::obj::jit_closure*>({}.ptr())->context) };\n"
      [closureCtx, closureCtx, mungedFnName]
  let mut pi := 0
  for (p, ty) in a.params do
    if !isUntypedObject ty then
      b := emitBody b "auto &&{}{ jank::runtime::convert<{}>::from_object({}) };" [munge p, typeName ty, paramNames.getD pi ""]
    pi := pi + 1
  b := { b with blockIndex := 0, instIndex := 0 }
  let mut g := 100000
  while g > 0 do
    g := g - 1
    let some i ← cbInst? b | break
    let (b', _) ← cgInst b i
    b := b'
  if a.bodyEmpty then b := emitBody b "return { };\n" []
  pure (emitBody b "}\n" [])

end

/-- `builder::expression_str` (cpp_processor.cpp:76-102): for the eval target, a new `jit_function`
whose arities point at the generated C functions. -/
def expressionStr (b : CB) : CgM (CB × String) := do
  if !b.expression.isEmpty then return (b, b.expression)
  let env ← get
  let n := env.counter + 1
  set { env with counter := n }
  let ret := munge (uniqueString "fnexpr" n)
  let mut e := formatTo "auto const {}(" [ret]
  e := e ++ formatTo "_jank_fn({})" [toString env.mod.arityFlags]
  e := e ++ ");"
  for f in env.mod.functions do
    if env.mod.entryPoints.contains f.name then
      e := e ++ formatTo "{}->arity_{} = &{}_{};" [ret, toString f.arity.paramCount, munge f.arity.fnUniqueName, toString f.arity.paramCount]
  e := e ++ ret
  pure ({ b with expression := e }, e)

/-- `gen_cpp(module)` (cpp_processor.cpp:2042-2195): the declaration and the expression. For the
module target, the namespace header with the lifted constants and vars and the load function. -/
def genCpp (nativeNs loadFn : String) (counterSnapshot : Nat) : CgM (String × String) := do
  let env ← get
  let some e0 := env.mod.entryPoints.head? | throw "no entry point"
  let mut b : CB := { fnIdx := ← findFunction e0 }
  for fnName in env.mod.entryPoints do
    let i ← findFunction fnName
    b := { b with fnIdx := i }
    b ← cgFunction b
    b := { b with seen := [] }
  let mod := (← get).mod
  if mod.target == .module then
    b := { b with moduleHeader := b.moduleHeader ++ formatTo "namespace {} {\n" [nativeNs] }
    for (o, n) in mod.liftedConstants do
      let line := formatTo "{} {}{ _jank_null{ } };\n" [typeName (literalCodegenTypeBoxed o), n]
      b := { b with moduleHeader := b.moduleHeader ++ line }
    for (o, n) in mod.liftedCppConstants do
      let c ← match genConstant o false with | .ok c => pure c | .error e => throw e
      b := { b with moduleHeader := b.moduleHeader ++ formatTo "auto constexpr {}{ " [n] ++ textOf c ++ " };\n" }
    for (_, v) in mod.liftedVars do
      b := { b with moduleHeader := b.moduleHeader ++ formatTo "jank::runtime::var_ref {}{ _jank_null{ } };\n" [v.name] }
    b := { b with footer := b.footer ++ formatTo "extern \"C\" void {}(){" [loadFn] }
    b := { b with footer := b.footer ++ formatTo "jank_ns_intern_c(\"{}\");" [mod.name] }
    b := { b with footer := b.footer ++ formatTo "jank_ns_set_symbol_counter(\"{}\", {});\n" ["user", toString counterSnapshot] }
    for (q, v) in mod.liftedVars do
      if v.owned then
        b := { b with footer := b.footer ++ formatTo "new (&{}::{}) auto(_jank_var_owned(\"{}\"));\n" [nativeNs, v.name, q] }
      else
        b := { b with footer := b.footer ++ formatTo "new (&{}::{}) auto(_jank_var(\"{}\"));\n" [nativeNs, v.name, q] }
    for (o, n) in mod.liftedConstants do
      let c ← match genConstant o true with | .ok c => pure c | .error e => throw e
      b := { b with footer := b.footer ++ formatTo "new (&{}::{}) auto(" [nativeNs, n] ++ textOf c ++ ");\n" }
    let (b', fnTmp) ← expressionStr b
    b := { b' with footer := b'.footer ++ formatTo "{}->call();\n" [fnTmp] }
    b := { b with footer := b.footer ++ "}\n" ++ "}\n" }
  let decl := b.declarationStr
  let (_, expr) ← expressionStr b
  pure (decl, expr)

end Jank.Codegen

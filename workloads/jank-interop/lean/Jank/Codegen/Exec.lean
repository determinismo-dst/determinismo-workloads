import Jank.Codegen.CppAst
import Jank.Codegen.Cpp
import Jank.Codegen.Value
import Jank.Codegen.Float
import Jank.Codegen.Prims

/-!
# Running the emitted C++

An interpreter of the parsed C++ (`Jank.Codegen.CppAst`) with C++'s rules where this subset
exercises them: block scopes and object lifetimes (a `jank::util::scope_exit` runs its function at
the end of its block, when still active, and a throw out of it calls `std::terminate`, since the
destructor is `noexcept`), `try`/`catch` and `throw;`, `while(true)` with `break`/`continue`,
`switch`, `[&]` lambdas, aggregate initialization of closure contexts.

What the emitted calls do is jank's runtime as its C++ defines it: `_jank_vec` and friends
(codegen/api.cpp), `jank::runtime::truthy`, `object_ref::call` (dispatch on the object: a
function's arity, a var's root, a keyword's lookup), vars (`bind_root`, `deref`,
`with_lazy_meta`), `jank_shift_mask_case_integer` (c_api.cpp). The clojure.core functions the
programs call are `Prims`, shared with the spec.
-/

namespace Jank.Codegen.Exec

open Jank.Codegen Jank.Codegen.CppAst
open Jank.Analyzer (Obj)

inductive CV where
  | obj (v : JV)
  | cbool (b : Bool)
  | cint (v : Int)
  | cstr (bytes : List UInt8)
  | ctxRef (id : Nat)
  | ctxPtr (id : Nat)
  | fnPtr (name : String)
  | lam (env : List (List (String × Nat))) (body : List Stmt)
  /-- `jank::util::scope_exit`: the slot of its function, active. -/
  | guard (fnSlot : Nat) (active : Bool)
  | unit
  deriving Inhabited

inductive Exc where
  | thrown (v : CV)
  | terminate (why : String)
  | ub (what : String)
  | err (what : String)
  | fuel
  deriving Inhabited

/-- A jank function object: arity → C function, the closure context. -/
structure FnObj where
  arities : List (Nat × String) := []
  ctx : Option Nat := none
  deriving Inhabited

structure VarCell where
  root : Option JV := none
  /-- `with_lazy_meta(source)`: the code string, read (and, in the dynamic runtime, evaluated)
  at the first `meta`. -/
  metaSrc : Option String := none
  dynamic : Bool := false
  deriving Inhabited

/-- The clojure.core functions programs call: same code on both sides. -/
structure Prims where
  call : String → List JV → (List String) → Except String (JV × List String)

structure M where
  prog : Program
  store : Array CV := #[]
  fns : Array FnObj := #[]
  ctxs : Array (List (String × CV)) := #[]
  vars : List (String × VarCell) := []
  heap : Heap := {}
  out : List String := []
  fuel : Nat := 200000
  /-- The exception being handled (for `throw;`). -/
  current : List CV := []
  /-- Per open block, the `scope_exit` objects declared in it (their slots). -/
  guards : List (List Nat) := []
  /-- The source text's characters are bytes (constants read back byte for byte). -/
  latin1 : Bool := false
  /-- `_jank_eval_str` evaluates (dynamic runtime) or only reads (static). -/
  dynamicRuntime : Bool := true
  /-- Namespace-level variables (module target), visible in every function. -/
  globalScope : List (String × Nat) := []

abbrev XM := EStateM Exc M

def tick : XM Unit := do
  let m ← get
  if m.fuel == 0 then throw .fuel
  set { m with fuel := m.fuel - 1 }

abbrev Env := List (List (String × Nat))

def alloc (v : CV) : XM Nat := do
  let m ← get
  set { m with store := m.store.push v }
  pure m.store.size

def lookup (env : Env) (n : String) : Option Nat :=
  env.findSome? fun sc => (sc.find? (·.1 == n)).map (·.2)

def readSlot (i : Nat) : XM CV := do
  match (← get).store[i]? with
  | some v => pure v
  | none => throw (.err "bad slot")

def writeSlot (i : Nat) (v : CV) : XM Unit := modify fun m => { m with store := m.store.set! i v }

def varCell (q : String) : XM VarCell := do pure ((assocGet? (← get).vars q).getD {})
def setVarCell (q : String) (c : VarCell) : XM Unit :=
  modify fun m => { m with vars := assocSet m.vars q c }

/-- The bytes a C++ narrow string literal holds ([lex.string], [lex.ccon]): simple escapes,
octal (1-3 digits) and hexadecimal (greedy) escapes, other characters as their UTF-8 bytes; the
terminating NUL not included. -/
def decodeStringLiteral (body : List Char) (latin1 : Bool := false) : Except String (List UInt8) := Id.run do
  let mut out : List UInt8 := []
  let mut r := body
  let mut fuel := body.length + 1
  while fuel > 0 do
    fuel := fuel - 1
    match r with
    | [] => break
    | '\\' :: c :: rest =>
      let simple : Option Nat := match c with
        | 'n' => some 10 | 't' => some 9 | 'r' => some 13 | '\\' => some 92 | '"' => some 34
        | '\'' => some 39 | '?' => some 63 | 'a' => some 7 | 'b' => some 8 | 'f' => some 12
        | 'v' => some 11 | _ => none
      match simple with
      | some v => out := out ++ [UInt8.ofNat v]; r := rest
      | none =>
        if c.isDigit && c.toNat < 56 then
          let ds := (c :: rest).takeWhile (fun d => d.isDigit && d.toNat < 56) |>.take 3
          let v := ds.foldl (fun a d => a * 8 + (d.toNat - 48)) 0
          if v > 255 then return .error "octal escape sequence out of range"
          out := out ++ [UInt8.ofNat v]; r := (c :: rest).drop ds.length
        else if c == 'x' then
          let hx := rest.takeWhile fun d => d.isDigit || ('a' ≤ d.toLower && d.toLower ≤ 'f')
          if hx.isEmpty then return .error "\\x used with no following hex digits"
          let v := hx.foldl (fun a d => a * 16 + (if d.isDigit then d.toNat - 48 else d.toLower.toNat - 87)) 0
          if v > 255 then return .error "hex escape sequence out of range"
          out := out ++ [UInt8.ofNat v]; r := rest.drop hx.length
        else return .error s!"unknown escape sequence '\\{c}'"
    | c :: rest =>
      out := out ++ (if latin1 then [UInt8.ofNat c.toNat] else (String.singleton c).toUTF8.toList)
      r := rest
  return .ok out

/-- `strlen`: what a `char const *` parameter sees of a literal. -/
def cString (bs : List UInt8) : List UInt8 := bs.takeWhile (· != 0)

def bytesToString (bs : List UInt8) : String :=
  match String.fromUTF8? (ByteArray.mk bs.toArray) with
  | some s => s
  | none => String.ofList (bs.map fun b => Char.ofNat b.toNat)

/-- The type and value of a C++ decimal integer literal on LP64 (Clang): `int`, `long`, then
`unsigned long long` as Clang's extension (with a warning) for a value above `LONG_MAX`; above
`ULLONG_MAX` it is an error. `signed = false` marks the unsigned type. -/
def intLiteral (s : String) : Except String (Int × Bool) := do
  let digits := s.toList.filter Char.isDigit
  if digits.length != s.length then throw s!"not an integer literal: {s}"
  let v : Nat := digits.foldl (fun a d => a * 10 + (d.toNat - 48)) 0
  if v ≤ 9223372036854775807 then pure (v, true)
  else if v ≤ 18446744073709551615 then pure (v, false)
  else throw s!"integer literal is too large to be represented in any integer type: {s}"

/-- A C++ arithmetic constant: an integer (with its signedness) or a double. -/
inductive Num where
  | i (v : Int) (signed : Bool)
  | d (bits : UInt64)

/-- The value of a numeric constant expression (literal, unary minus, `INFINITY`, `NAN`). -/
partial def numConst : Expr → Except String Num
  | .num s =>
    if s.contains '.' || s.contains 'e' || s.contains 'E' then
      match Float.parseDecimal s.toList with
      | some b => .ok (.d b)
      | none => .error s!"bad floating literal {s}"
    else do let (v, sg) ← intLiteral s; pure (.i v sg)
  | .id "INFINITY" => .ok (.d Float.cInfinity)
  | .id "NAN" => .ok (.d Float.cNan)
  | .neg e => do
    match ← numConst e with
    | .i v true => pure (.i (-v) true)
    | .i v false => pure (.i ((18446744073709551616 - v) % 18446744073709551616) false)
    | .d b => pure (.d (b ^^^ 0x8000000000000000))
  | .cast _ "jtl::i32" [e] => do
    match ← numConst e with
    | .i v _ => pure (.i (BitVec.ofInt 32 v).toInt true)
    | .d _ => .error "cast of a double"
  | _ => .error "not a numeric constant"

/-- Converting an integer constant to `i64`/`i32` (C++20: modulo 2^N). -/
def toI64 (v : Int) : Int := (BitVec.ofInt 64 v).toInt
def toI32 (v : Int) : Int := (BitVec.ofInt 32 v).toInt

def objOf (v : CV) : XM JV :=
  match v with
  | .obj o => pure o
  | .cbool b => pure (.bool b)
  | .cint i => pure (.int i)
  | _ => throw (.ub "an object_ref expected")

def addrOfText (s : String) : Except String Nat :=
  let t := (strDrop s 2).toList
  if s.startsWith "0x" then
    .ok (t.foldl (fun a d => a * 16 + (if d.isDigit then d.toNat - 48 else d.toLower.toNat - 87)) 0)
  else .error "bad address"

/-- The object at a heap address (`(void*)0x…` written by `lift_constant`). -/
def heapObj (a : Nat) : XM JV := do
  let h := (← get).heap
  if a < 0x1000 || (a - 0x1000) % 16 != 0 then throw (.ub "pointer to no object")
  match h.objs[(a - 0x1000) / 16]? with
  | some o => pure (JV.ofObj o)
  | none => throw (.ub "pointer to no object")

def heapVar (a : Nat) : XM String := do
  let h := (← get).heap
  if a < varBase then throw (.ub "pointer to no var")
  match h.vars[(a - varBase) / 16]? with
  | some q => pure q
  | none => throw (.ub "pointer to no var")

def collect (args : List CV) : XM (List JV) := args.mapM objOf

def newFn (ctx : Option Nat) : XM JV := do
  let m ← get
  set { m with fns := m.fns.push { ctx } }
  pure (.fn m.fns.size)

def assocInPlace (kvs : List (JV × JV)) (k v : JV) : List (JV × JV) :=
  if kvs.any (·.1.equiv k) then kvs.map fun p => if p.1.equiv k then (p.1, v) else p else kvs ++ [(k, v)]

/-- `_jank_vec`/`_jank_list`/`_jank_hset`/`_jank_amap`/`_jank_hmap` (codegen/api.cpp:67-426):
an optional meta first (an `object_ref`, or a `char const *` code string), the count, then that
many elements (pairs for maps). Lists keep the element order (api.cpp:80: built from reverse
iterators); maps `assoc_in_place` (a later equal key replaces the value). -/
def jankColl (fn : String) (args : List CV) : XM JV := do
  let (mta, rest) : Option JV × List CV := match args with
    | .cint _ :: _ => (none, args)
    | .obj m :: r => (some m, r)
    | .cstr bs :: r => (readCode (bytesToString (cString bs)), r)  -- code-string meta (lazy_meta)
    | _ => (none, args)
  match rest with
  | .cint n :: elems =>
    let xs ← collect elems
    let count := if fn == "_jank_amap" || fn == "_jank_hmap" then 2 * n.toNat else n.toNat
    if xs.length != count then throw (.ub "va_arg past the arguments")
    match fn with
    | "_jank_vec" => pure (.vec xs mta)
    | "_jank_list" => pure (.list xs mta)
    | "_jank_hset" => pure (.set (xs.foldl (fun acc x => if acc.any (·.equiv x) then acc else acc ++ [x]) []))
    | _ =>
      let rec pairs : List JV → List (JV × JV)
        | k :: v :: r => (k, v) :: pairs r
        | _ => []
      pure (.map ((pairs xs).foldl (fun acc (k, v) => assocInPlace acc k v) []))
  | _ => throw (.err s!"{fn}: no count")


/-- The runtime: whether `_jank_eval_str` evaluates (dynamic runtime) or only reads (static
runtime, api_static.cpp). -/
structure Runtime where
  dynamic : Bool := true
  deriving Repr, Inhabited

/-- Statement outcomes. -/
inductive Sig where
  | normal | brk | cont | ret (v : CV)
  deriving Inhabited

def varRoot (q : String) : XM (Option JV) := do pure (← varCell q).root

/-- `var::get_meta` → `lazy_meta::get` (lazy_meta.cpp:30-46): the code string read and, in the
dynamic runtime, evaluated, at the first access. -/
def varMeta (rt : Runtime) (q : String) : XM JV := do
  let c ← varCell q
  match c.metaSrc with
  | none => pure .nil
  | some src =>
    match readCode src with
    | none => throw (.err s!"unreadable meta {src}")
    | some form =>
      if !rt.dynamic then pure form
      else
        let vars := (← get).vars
        let lookup := fun (q : String) => (assocGet? vars q).bind (·.root)
        match evalForm lookup (← get).out form with
        | .ok (v, o) => modify (fun m => { m with out := o }); pure v
        | .error e => throw (.thrown (.obj (.other e)))

def assocSetNat (l : List (Nat × String)) (k : Nat) (v : String) : List (Nat × String) :=
  if l.any (·.1 == k) then l.map fun p => if p.1 == k then (k, v) else p else l ++ [(k, v)]

mutual

partial def evalE (rt : Runtime) (env : Env) (e : Expr) : XM CV := do
  tick
  match e with
  | .id n =>
    match lookup env n with
    | some i => readSlot i
    | none =>
      if n == "jank::runtime::jank_nil" then return .obj .nil
      if n == "jank::runtime::jank_true" then return .obj (.bool true)
      if n == "jank::runtime::jank_false" then return .obj (.bool false)
      if n == "true" then return .cbool true
      if n == "false" then return .cbool false
      if (← get).prog.fns.any (·.name == n) then return .fnPtr n
      throw (.err s!"unbound identifier {n}")
  | .num s => match numConst (.num s) with
    | .ok (.i v _) => pure (.cint v)
    | .ok (.d b) => pure (.obj (.real b))
    | .error m => throw (.err m)
  | .neg x => match numConst (.neg x) with
    | .ok (.i v _) => pure (.cint v)
    | .ok (.d b) => pure (.obj (.real b))
    | .error m => throw (.err m)
  | .str b => match decodeStringLiteral b (← get).latin1 with
    | .ok bs => pure (.cstr bs)
    | .error m => throw (.err m)
  | .addr n => pure (.fnPtr n)
  | .lambda body => pure (.lam env body)
  | .brace ty args => evalBrace rt env ty args
  | .cast k ty args => evalCast rt env k ty args
  | .dot x m => do
    match ← evalE rt env x with
    | .ctxRef i => if m == "data" then pure (.ctxPtr i) else ctxField i m
    | v => if m == "data" then pure v else throw (.err s!"member {m}")
  | .arrow x m => do
    match ← evalE rt env x with
    | .ctxPtr i => if m == "context" then pure (.ctxPtr i) else ctxField i m
    | .ctxRef i => ctxField i m
    | _ => throw (.err s!"-> {m}")
  | .call f args => evalCall rt env f args

partial def ctxField (i : Nat) (m : String) : XM CV := do
  match (← get).ctxs[i]? with
  | some fs => match fs.find? (·.1 == m) with
    | some (_, v) => pure v
    | none => throw (.err s!"no field {m}")
  | none => throw (.ub "context of a non-closure")

partial def evalBrace (rt : Runtime) (env : Env) (ty : String) (args : List Expr) : XM CV := do
  match args with
  | [] => pure (.obj .nil)
  | [.brace "_jank_codegen" [], .cast "c" "void*" [.num a]] =>
    match addrOfText a with
    | .ok ad => pure (.obj (← heapObj ad))
    | .error m => throw (.err m)
  | [.cast _ "jank::runtime::var*" [.num a]] =>
    match addrOfText a with
    | .ok ad => pure (.obj (.var (← heapVar ad)))
    | .error m => throw (.err m)
  | [x] =>
    match numConst x with
    | .ok (.i v _) =>
      if ty.endsWith "small_integer_ref" then pure (.obj (.int (toI32 v)))
      else if ty.endsWith "integer_ref" then pure (.obj (.int (toI64 v)))
      else pure (.obj (.int v))
    | .ok (.d b) => pure (.obj (.real b))
    | .error _ => evalE rt env x
  | _ => throw (.err s!"brace init of {ty}")

partial def evalCast (rt : Runtime) (env : Env) (k ty : String) (args : List Expr) : XM CV := do
  if k == "make_ref" then
    let vals ← args.mapM (evalE rt env)
    let some (_, fields) := (← get).prog.structs.find? (·.1 == ty) | throw (.err s!"no struct {ty}")
    if vals.length > fields.length then throw (.err "too many initializers")
    let m ← get
    set { m with ctxs := m.ctxs.push (fields.zip (vals ++ List.replicate (fields.length - vals.length) (CV.obj JV.nil))) }
    return .ctxRef m.ctxs.size
  if k.startsWith "convert:" then
    let vals ← args.mapM (evalE rt env)
    let some v := vals.head? | throw (.err "convert")
    if k == "convert:into_object" || ty == "jank::runtime::object_ref" then return v
    -- `convert<T>::from_object` for a typed ref (convert/builtin.hpp:54-73): `try_object<T>`,
    -- which throws `std::runtime_error` (not an object) on another type (rtti.hpp:22-35)
    let o ← objOf v
    let ok := match o with
      | .kw .. => ty.endsWith "::keyword_ref"
      | .str _ => ty.endsWith "::persistent_string_ref"
      | .int _ => ty.endsWith "::small_integer_ref" || ty.endsWith "::integer_ref"
      | .vec .. => ty.endsWith "::persistent_vector_ref"
      | .list .. => ty.endsWith "::persistent_list_ref"
      | .nil => ty.endsWith "::nil_ref"
      | .bool _ => ty.endsWith "::boolean_ref"
      | .real _ => ty.endsWith "real_ref"
      | .sym .. => ty.endsWith "::symbol_ref"
      | .char _ => ty.endsWith "::character_ref"
      | .set _ => ty.endsWith "::persistent_hash_set_ref"
      | .map _ => ty.endsWith "_map_ref"
      | .big _ => ty.endsWith "::big_integer_ref"
      | .ratio .. => ty.endsWith "::ratio_ref"
      | _ => false
    if ok then return .obj o
    throw (.thrown .unit)
  if k == "make_box" then
    let vals ← args.mapM (evalE rt env)
    match ty, vals with
    | "jank::runtime::obj::big_integer", [.cstr bs] =>
      let s := bytesToString (cString bs)
      let s := if s.endsWith "N" then strDropRight s 1 else s
      match s.toInt? with
      | some v => return .obj (.big v)
      | none => throw (.thrown (.unit))
    | "jank::runtime::obj::character", [.cstr bs] => return .obj (.char (bytesToString (cString bs)))
    | _, _ => throw (.err s!"make_box<{ty}>")
  let vals ← args.mapM (evalE rt env)
  match vals with
  | [v] =>
    if ty == "struct " ++ (ty.drop 7) && ty.endsWith "*" then
      -- `static_cast<struct C*>(static_cast<jit_closure*>(fn.ptr())->context)`: handled at `->`
      pure v
    else if ty == "jank::runtime::obj::jit_closure*" then
      match v with
      | .obj (.fn id) =>
        match (← get).fns[id]? with
        | some { ctx := some c, .. } => pure (.ctxPtr c)
        | _ => throw (.ub "static_cast to jit_closure* of a function without a context")
      | _ => throw (.ub "static_cast to jit_closure* of a non-closure object (its .ptr()->context read)")
    else pure v
  | _ => throw (.err s!"cast to {ty}")

partial def evalCall (rt : Runtime) (env : Env) (f : Expr) (args : List Expr) : XM CV := do
  match f with
  | .id n =>
    -- `G.release()`-style calls are `.dot`; here free functions
    if n == "std::move" then return ← evalE rt env args.head!
    match lookup env n with
    | some slot =>
      match ← readSlot slot with
      | .lam lenv body =>
        let sig ← execBlock rt lenv body
        match sig with
        | .ret v => pure v
        | _ => pure .unit
      | _ => throw (.err s!"{n} is not callable")
    | none =>
    let vals ← args.mapM (evalE rt env)
    match n with
    | "_jank_vec" | "_jank_list" | "_jank_hset" | "_jank_amap" | "_jank_hmap" =>
      pure (.obj (← jankColl n vals))
    | "_jank_fn" | "_jank_vfn" => pure (.obj (← newFn none))
    | "_jank_closure" | "_jank_vclosure" =>
      match vals with
      | [_, .ctxPtr c] => pure (.obj (← newFn (some c)))
      | _ => throw (.err "closure")
    | "_jank_var_owned" | "_jank_var" =>
      match vals with
      | [.cstr bs] =>
        let q := bytesToString (cString bs)
        if (assocGet? (← get).vars q).isNone then setVarCell q {}
        pure (.obj (.var q))
      | _ => throw (.err "var")
    | "_jank_small_int" => match vals with
      | [.cint v] => pure (.obj (.int (toI32 v)))
      | _ => throw (.err "small int")
    | "_jank_int" => match vals with
      | [.cint v] => pure (.obj (.int (toI64 v)))
      | _ => throw (.err "int")
    | "_jank_small_real" => match vals with
      | [.obj (.real b)] => pure (.obj (.real b))
      | [.cint v] => pure (.obj (.real (Float.ofRat (v < 0) v.natAbs 1)))
      | _ => throw (.err "real")
    | "_jank_string" => match vals with
      | [] => pure (.obj (.str ""))
      | [.cstr bs] => pure (.obj (.str (bytesToString (cString bs))))
      | _ => throw (.err "string")
    | "_jank_keyword" => match vals with
      | [.cstr a, .cstr b] => pure (.obj (.kw (bytesToString (cString a)) (bytesToString (cString b))))
      | _ => throw (.err "keyword")
    | "_jank_symbol" => match vals with
      | [.cstr a, .cstr b] => pure (.obj (.sym (bytesToString (cString a)) (bytesToString (cString b)) none))
      | [.cstr m, .cstr a, .cstr b] =>
        let mv := (readCode (bytesToString (cString m)))
        pure (.obj (.sym (bytesToString (cString a)) (bytesToString (cString b)) mv))
      | _ => throw (.err "symbol")
    | "jank::runtime::obj::ratio::create" => match args.mapM numConst with
      | .ok [.i n _, .i d _] =>
        -- overload resolution picks `create(i64, i64)` for integer literals: each converted
        let n := toI64 n
        let d := toI64 d
        if d == 0 then throw (.thrown .unit)
        let g := (Int.gcd n d : Int)
        let (n, d) := (n / g, d / g)
        let (n, d) := if d < 0 then (-n, -d) else (n, d)
        if d == 1 then pure (.obj (.int n)) else pure (.obj (.ratio n d))
      | .ok _ => throw (.err "ratio")
      | .error m => throw (.err m)
    | "jank_ns_intern_c" | "jank_ns_set_symbol_counter" => pure .unit
    | "jank::runtime::truthy" => match vals with
      | [v] => pure (.cbool (← objOf v).truthy)
      | _ => throw (.err "truthy")
    | "jank_shift_mask_case_integer" => match vals with
      | [v, .cint s, .cint m] => pure (.cint (shiftMaskCaseInteger (← objOf v) s m))
      | _ => throw (.err "case integer")
    | _ =>
      if (← get).prog.fns.any (·.name == n) then callC rt n vals
      else throw (.err s!"call of unknown function {n}")
  | .dot x "release" =>
    match x with
    | .id g => match lookup env g with
      | some slot => match ← readSlot slot with
        | .guard fs _ => writeSlot slot (.guard fs false); pure .unit
        | _ => throw (.err "release of a non-guard")
      | none => throw (.err "release")
    | _ => throw (.err "release")
  | .dot x m =>
    let xv ← evalE rt env x
    let vals ← args.mapM (evalE rt env)
    match m with
    | "erase" | "raw" | "ptr" => pure xv
    | "call" => pure (.obj (← dynCall rt (← objOf xv) (← vals.mapM objOf)))
    | _ => throw (.err s!".{m}()")
  | .arrow x m =>
    let xv ← evalE rt env x
    let vals ← args.mapM (evalE rt env)
    match xv with
    | .obj (.var q) =>
      match m, vals with
      | "deref", [] =>
        match ← varRoot q with
        | some v => pure (.obj v)
        | none => throw (.thrown (.obj (.other s!"unbound var {q}")))
      | "bind_root", [v] => do
        let c ← varCell q
        setVarCell q { c with root := some (← objOf v) }
        pure xv
      | "with_lazy_meta", [.cstr bs] => do
        let c ← varCell q
        setVarCell q { c with metaSrc := some (bytesToString (cString bs)) }
        pure xv
      | "set_dynamic", [b] => do
        let c ← varCell q
        setVarCell q { c with dynamic := match b with | .cbool t => t | _ => false }
        pure xv
      | _, _ => throw (.err s!"var->{m}")
    | .obj (.fn _) => if m == "call" then pure (.obj (← dynCall rt (← objOf xv) (← vals.mapM objOf))) else throw (.err m)
    | _ => throw (.err s!"->{m}()")
  | _ => throw (.err "call of an expression")

/-- `object_ref::call` (dynamic call): a function's arity, a var's root, a keyword's lookup, a
primitive. -/
partial def dynCall (rt : Runtime) (f : JV) (args : List JV) : XM JV := do
  tick
  match f with
  | .fn id =>
    let some fo := (← get).fns[id]? | throw (.ub "no function")
    match fo.arities.find? (·.1 == args.length) with
    | some (_, cname) => objOf (← callC rt cname (.obj f :: args.map CV.obj))
    | none => throw (.thrown (.obj (.other "wrong number of args")))
  | .var q =>
    match ← varRoot q with
    | some v => dynCall rt v args
    | none => throw (.thrown (.obj (.other s!"unbound var {q}")))
  | .prim "user/meta-of" =>
    match args with
    | [.var q] => varMeta rt q
    | _ => throw (.thrown (.obj (.other "meta-of")))
  | .prim n =>
    match prim n args (← get).out with
    | .ok (v, o) => modify (fun m => { m with out := o }); pure v
    | .error e => throw (.thrown (.obj (.other e)))
  | .kw ns n =>
    match args with
    | [.map kvs] => pure ((kvs.find? (·.1.equiv (.kw ns n))).map (·.2) |>.getD .nil)
    | [_] => pure .nil
    | _ => throw (.thrown (.obj (.other "keyword arity")))
  | _ => throw (.thrown (.obj (.other s!"{f.show} is not callable")))

/-- A C function call: parameters bound, body run; a body ending without `return` is UB. -/
partial def callC (rt : Runtime) (name : String) (args : List CV) : XM CV := do
  tick
  let some fd := (← get).prog.fns.find? (·.name == name) | throw (.err s!"no function {name}")
  if fd.params.length != args.length then throw (.err "argument count")
  let mut sc : List (String × Nat) := []
  for (p, a) in fd.params.zip args do
    let slot ← alloc a
    if p != "" then sc := (p, slot) :: sc
  match ← execBlock rt [sc, (← get).globalScope] fd.body with
  | .ret v => pure v
  | _ => throw (.ub s!"{name}: flowing off the end of a non-void function")

/-- A block: statements in a new scope; at its end, however left, the `scope_exit` objects it
declared run their function (newest first); a throw out of one terminates (the destructor is
implicitly `noexcept`, util/scope_exit.cpp). -/
partial def execBlock (rt : Runtime) (env : Env) (ss : List Stmt) : XM Sig := do
  modify fun m => { m with guards := [] :: m.guards }
  let r ← tryCatch (do let sg ← execList rt (([] : List (String × Nat)) :: env) ss; pure (Except.ok sg))
    (fun e => pure (Except.error e))
  let gs := (← get).guards.head?.getD []
  modify fun m => { m with guards := m.guards.drop 1 }
  for slot in gs do
    match ← readSlot slot with
    | .guard fs true =>
      match ← readSlot fs with
      | .lam lenv body =>
        let ok ← tryCatch (do let _ ← execBlock rt lenv body; pure true)
          (fun e => match e with
            | .thrown _ => throw (.terminate "an exception left ~scope_exit (noexcept)")
            | other => throw other)
        let _ := ok
      | _ => throw (.err "guard function")
    | _ => pure ()
  match r with
  | .ok sg => pure sg
  | .error e => throw e

/-- Statements in order, the environment growing with declarations. -/
partial def execList (rt : Runtime) (env : Env) (ss : List Stmt) : XM Sig := do
  let mut env := env
  for s in ss do
    let (sg, env') ← execStmt rt env s
    env := env'
    match sg with
    | .normal => continue
    | other => return other
  pure .normal

partial def execStmt (rt : Runtime) (env : Env) (s : Stmt) : XM (Sig × Env) := do
  tick
  match s with
  | .decl ty name init =>
    let v ← match init with
      | [] => pure (.obj .nil)
      | [x] => evalE rt env x
      | [.id f, _] =>
        if ty == "jank::util::scope_exit" then
          match lookup env f with
          | some fs => pure (.guard fs true)
          | none => throw (.err "scope_exit function")
        else throw (.err "two initializers")
      | _ => throw (.err "initializers")
    let slot ← alloc v
    if let .guard .. := v then
      modify fun m => { m with guards := match m.guards with
        | g :: rest => (slot :: g) :: rest
        | [] => [[slot]] }
    match env with
    | sc :: rest => pure (.normal, ((name, slot) :: sc) :: rest)
    | [] => pure (.normal, [[(name, slot)]])
  | .assign lhs rhs =>
    let v ← evalE rt env rhs
    match lhs with
    | .id n =>
      match lookup env n with
      | some slot => writeSlot slot v; pure (.normal, env)
      | none => throw (.err s!"assignment to undeclared {n}")
    | .arrow (.id fnv) m =>
      if m.startsWith "arity_" then
        let k := (strDrop m 6).toNat!
        match ← evalE rt env (.id fnv), v with
        | .obj (.fn id), .fnPtr cname =>
          modify fun mm => { mm with fns := mm.fns.modify id fun fo => { fo with arities := assocSetNat fo.arities k cname } }
          pure (.normal, env)
        | _, _ => throw (.err "arity assignment")
      else
        match ← evalE rt env (.id fnv) with
        | .ctxRef i | .ctxPtr i =>
          modify fun mm => { mm with ctxs := mm.ctxs.modify i fun fs => fs.map fun p => if p.1 == m then (m, v) else p }
          pure (.normal, env)
        | _ => throw (.err "field assignment")
    | _ => throw (.err "assignment target")
  | .expr e => let _ ← evalE rt env e; pure (.normal, env)
  | .block ss => pure (← execBlock rt env ss, env)
  | .ifElse c t e =>
    let cv ← evalE rt env c
    let b := match cv with | .cbool b => b | .obj o => o.truthy | _ => false
    pure (← execBlock rt env (if b then t else e), env)
  | .whileTrue body =>
    let mut g := 100000
    while g > 0 do
      g := g - 1
      tick
      match ← execBlock rt env body with
      | .normal | .cont => continue
      | .brk => return (.normal, env)
      | .ret v => return (.ret v, env)
    throw .fuel
  | .brk => pure (.brk, env)
  | .cont => pure (.cont, env)
  | .ret none => throw (.err "return without a value")
  | .ret (some x) =>
    match x with
    | .brace "" [] => pure (.ret (.obj .nil), env)
    | _ => pure (.ret (← evalE rt env x), env)
  | .thr none =>
    match (← get).current.head? with
    | some v => throw (.thrown v)
    | none => throw (.terminate "throw; with no exception being handled")
  | .thr (some x) => throw (.thrown (← evalE rt env x))
  | .tryCatch body hs =>
    let r ← tryCatch (do let sg ← execBlock rt env body; pure (Except.ok sg))
      (fun e => pure (Except.error e))
    match r with
    | .ok sg => pure (sg, env)
    | .error (.thrown v) =>
      let isObj := match v with | .obj _ => true | _ => false
      for (h, hb) in hs do
        match h with
        | none =>
          modify fun mm => { mm with current := v :: mm.current }
          let r ← execBlock rt env hb
          modify fun mm => { mm with current := mm.current.drop 1 }
          return (r, env)
        | some (_, n) =>
          if isObj then
            let slot ← alloc v
            modify fun mm => { mm with current := v :: mm.current }
            let r ← execBlock rt ([(n, slot)] :: env) hb
            modify fun mm => { mm with current := mm.current.drop 1 }
            return (r, env)
      throw (.thrown v)
    | .error e => throw e
  | .switch e cases =>
    let cv ← evalE rt env e
    let some k := (match cv with | .cint k => some k | _ => none) | throw (.err "switch on a non-integer")
    let mut chosen : Option (List Stmt) := none
    for (lbl, body) in cases do
      if let some l := lbl then
        match numConst l with
        | .ok (.i v true) => if toI64 v == k && chosen.isNone then chosen := some body
        | .ok (.i _ false) => throw (.err "case value cannot be narrowed to the switch type")
        | _ => throw (.err "case label")
    if chosen.isNone then
      chosen := (cases.find? (·.1.isNone)).map (·.2)
    match chosen with
    | some body =>
      match ← execBlock rt env body with
      | .brk | .normal => pure (.normal, env)
      | other => pure (other, env)
    | none => pure (.normal, env)

end

end Jank.Codegen.Exec

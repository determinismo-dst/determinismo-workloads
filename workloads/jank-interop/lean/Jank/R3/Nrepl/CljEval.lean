import Jank.R3.Nrepl.JankEval

/-!
# Round 3, nREPL: the spec — Clojure 1.12's REPL over the same code string

clojure.main/repl (clojure-ref src/clj/clojure/main.clj:368), as an nREPL session runs it on a
code string (assumption NA1: nREPL's eval is clojure.main/repl with `:read` from the code string,
`:caught` answering `eval-error`, the session's thread bindings kept between requests):

- each form: read (`Jank.ReadClj.read`, LispReader), evaluated (`Compiler.eval`, Compiler.java:7658:
  `macroexpand` first; a top-level `(do ...)` evaluated form by form, each again through `eval`;
  otherwise analyzed whole (`Jank.Analyzer.cljAnalyze`, which interns a `def`'s var at analysis)
  and run), then `(set! *3 *2) (set! *2 *1) (set! *1 value)`, then printed (`:print`, a `:value`
  reply with the session's `*ns*`); an exception in read, eval or print is `caught` (an `eval-error`
  reply) and `(set! *e e)`, and the loop reads the next form;
- the session's bindings (`*ns*`, `*1`, `*2`, `*3`, `*e`) persist across its requests; the `ns`
  field rebinds `*ns*` for one request.

Mode `loadString` (assumption-free reading of jank's design): the whole string is one input whose
value is the last form's (`load-string`/`Compiler.load`, Compiler.java:8130: forms in order, the
first exception ends it), `*1` shifted once. Searches run both; a deviation that holds in both is
independent of NA1.

The core library as Clojure 1.12 defines it (core.clj): `defn`, `defmacro` (`(do (defn name
[&form &env ...] ...) (. (var name) (setMacro)) (var name))`, here `set-macro!`), `ns` (`(do (in-ns
'name) (with-loading-context (refer 'clojure.core) refs...) ...)`), `in-ns` returning the namespace,
`refer` through Namespace.reference/checkReplacement (an interned mapping is kept), `print` of no
arguments printing nothing, `pr-str` variadic.
-/

namespace Jank.R3.Nrepl

open Jank.Analyzer

structure SW where
  nss : List NsCell
  slots : Slots
  /-- Vars that are macros (`Var.setMacro`). -/
  macros : List VarRef := []
  heap : Heap := {}
  closures : Array CClosure := #[]
  deriving Inhabited

/-- Variants of the spec that adopt one of jank's known behaviors: a residual search turns a found
class's variant on, so that the two processes do not diverge on it and the search goes on past it;
a census labels a mismatch with the variant that explains it. -/
structure Variant where
  /-- N1: a top-level `(do ...)` is analyzed whole (no Compiler.eval split). -/
  noTopDoSplit : Bool := false
  /-- R112: `in-ns` returns nil. -/
  inNsNil : Bool := false
  /-- A namespace prints as its name (`ns::to_code_string`). -/
  nsPrintName : Bool := false
  /-- N6: what printing the value prints is not the client's output. -/
  printOutLost : Bool := false
  deriving Repr, Inhabited, BEq

def Variant.all : List (String × Variant) :=
  [("N1 top-level do analyzed whole", { noTopDoSplit := true }),
   ("R112 in-ns returns nil", { inNsNil := true }),
   ("namespace pr-str is its name", { nsPrintName := true }),
   ("N6 output printed while printing the value is lost", { printOutLost := true })]

def Variant.join (a b : Variant) : Variant :=
  { noTopDoSplit := a.noTopDoSplit || b.noTopDoSplit, inNsNil := a.inNsNil || b.inNsNil,
    nsPrintName := a.nsPrintName || b.nsPrintName, printOutLost := a.printOutLost || b.printOutLost }

structure SS where
  w : SW
  tb : TB
  out : Array OutEv := #[]
  fuel : Nat := 4000
  v : Variant := {}
  deriving Inhabited

abbrev SM := EStateM Fail SS

def stick : SM Unit := do
  let s ← get
  if s.fuel == 0 then throw .fuel
  set { s with fuel := s.fuel - 1 }

def sHeap : SM Heap := do pure (← get).w.heap
def sSetHeap (h : Heap) : SM Unit := modify fun s => { s with w := { s.w with heap := h } }
def sEmit (e : OutEv) : SM Unit := modify fun s => { s with out := s.out.push e }
def sNewEx (msg : String) (data : Obj := .nil) (origin : String := "throw") : SM Obj := do
  let (h, o) := (← sHeap).newEx { msg, data, origin }
  sSetHeap h
  pure o

def sCurNs (s : SS) : String :=
  match s.tb.deref s.w.slots vNs with
  | some o => (s.w.heap.nsName? o).getD "user"
  | none => "user"

def cljFnObj (k : Nat) : Obj := .opaque .jitFunction k

/-! ## Clojure's core macros -/

/-- core.clj `defn`: `(def name (fn name [params] body))` (metadata other than the name's is not
read by any property; `defn-` would add `:private`). -/
def cljDefnMacro : MacroFn
  | _ :: _ :: name :: fdecl0 =>
    let fdecl := match fdecl0 with
      | .persistentString _ :: rest => rest
      | x => x
    let fdecl := match fdecl with
      | (.persistentArrayMap ..) :: rest => rest
      | x => x
    .ok (lst [sym "def", name, lst (qsym "clojure.core" "fn" :: name.setMeta none :: fdecl)])
  | _ => .error "Wrong number of args passed to: defn"

/-- core.clj `defmacro`: `(do (defn name [&form &env ...] ...) (. (var name) (setMacro)) (var name))`. -/
def cljDefmacroMacro : MacroFn
  | _ :: _ :: name :: args =>
    let args := match args with
      | (.persistentString _) :: rest => rest
      | x => x
    let fdecl := match args.headD .nil with
      | .persistentVector .. => [lst args]
      | _ => args
    let addImplicit (fd : Obj) : Obj :=
      match fd.elems with
      | some (.persistentVector _ ps :: body) => lst (vec (sym "&form" :: sym "&env" :: ps) :: body)
      | _ => fd
    .ok (lst [sym "do", lst (qsym "clojure.core" "defn" :: name :: fdecl.map addImplicit),
      lst [qsym "clojure.core" "set-macro!", lst [sym "var", name]], lst [sym "var", name]])
  | _ => .error "Wrong number of args passed to: defmacro"

/-- core.clj `ns`: `(do (in-ns 'name) (with-loading-context (refer 'clojure.core) refs...) ...)`,
the value nil. -/
def cljNsMacro : MacroFn
  | _ :: _ :: name :: refs =>
    let refs := refs.filter fun r => match r with | .persistentString _ => false | _ => true
    let nm := name.setMeta none
    let process (r : Obj) : Obj :=
      match r.elems with
      | some (.keyword _ k :: args) => lst (qsym "clojure.core" k :: args.map quoteO)
      | _ => .nil
    .ok (lst ([sym "do", lst [qsym "clojure.core" "in-ns", quoteO nm],
               lst ([sym "do"] ++ (if nm != sym "clojure.core" then [lst [qsym "clojure.core" "refer", quoteO (sym "clojure.core")]] else [])
                    ++ refs.map process),
               .nil]))
  | _ => .error "Wrong number of args passed to: ns"

def cljMacros : List (String × MacroFn) :=
  [("when", whenMacro), ("let", letMacro), ("loop", loopMacro), ("fn", fnMacro), ("or", orMacro),
   ("and", andMacro), ("defn", cljDefnMacro), ("defmacro", cljDefmacroMacro), ("ns", cljNsMacro),
   ("comment", commentMacro)]

/-- The Clojure process after start-up: the same vars, namespaces and metadata as `jankBase`
(the nREPL server's `user` refers clojure.core). -/
def cljBase : SW :=
  let j := jankBase
  { nss := j.nss, slots := j.slots, heap := j.heap,
    macros := cljMacros.map fun (n, _) => coreRef n }

/-! ## Evaluation (Clojure) -/

mutual

partial def sEval (e : CE) (env : List (Nat × Obj)) : SM Flow := do
  stick
  match e with
  | .const o => pure (.val (.obj o))
  | .local id => match env.lookup id with
    | some v => pure (.val (.obj v))
    | none => throw (.unsupported "unbound local")
  | .var vr =>
    let s ← get
    match s.tb.deref s.w.slots vr with
    | some o => pure (.val (.obj o))
    | none => pure (.val (.obj (.opaque .varUnboundRoot 0)))
  | .theVar vr => pure (.val (.obj (.var vr.ns vr.name)))
  | .if_ c t el =>
    let cv ← sEvalV c env
    if cv.truthy then sEval t env else sEval el env
  | .do_ xs =>
    let mut last : Flow := .val (.obj .nil)
    for x in xs do
      last ← sEval x env
      if let .recur _ := last then return last
    pure last
  | .let_ binds body isLoop =>
    let mut env := env
    for (id, init) in binds do
      env := (id, ← sEvalV init env) :: env
    if !isLoop then return ← sEval body env
    let mut cur := env
    for _ in [0:100000] do
      match ← sEval body cur with
      | .val v => return .val v
      | .recur args =>
        cur := (binds.map (·.1)).zip (args.map Val.toObj) ++ cur
    throw .fuel
  | .recur args =>
    let vs ← args.mapM (sEvalV · env)
    pure (.recur (vs.map Val.obj))
  | .fn self arities =>
    let s ← get
    let k := s.w.closures.size
    set { s with w := { s.w with closures := s.w.closures.push { self, arities, env } } }
    pure (.val (.obj (cljFnObj k)))
  | .letfn binds body =>
    let s ← get
    let base := s.w.closures.size
    let mut env' := env
    let mut idx := 0
    for (id, _) in binds do
      env' := (id, cljFnObj (base + idx)) :: env'
      idx := idx + 1
    for (_, f) in binds do
      match f with
      | .fn self ars => modify fun s => { s with w := { s.w with closures := s.w.closures.push { self, arities := ars, env := env' } } }
      | _ => throw (.unsupported "letfn value")
    sEval body env'
  | .call f args =>
    let fv ← sEvalV f env
    let vs ← args.mapM (sEvalV · env)
    pure (.val (.obj (← sInvoke fv vs)))
  | .def vr value =>
    match value with
    | some v =>
      let x ← sEvalV v env
      modify fun s => { s with w := { s.w with slots := s.w.slots.modify vr fun sl => { sl with root := some x } } }
    | none => pure ()
    pure (.val (.obj (.var vr.ns vr.name)))
  | .throw x =>
    let v ← sEvalV x env
    throw (.thrown v)
  | .vector xs md =>
    let vs ← xs.mapM (sEvalV · env)
    let m ← md.mapM (sEvalV · env)
    pure (.val (.obj (.persistentVector m vs)))
  | .map kvs md =>
    let vs ← kvs.mapM fun (k, v) => do pure (← sEvalV k env, ← sEvalV v env)
    let m ← md.mapM (sEvalV · env)
    pure (.val (.obj (.persistentArrayMap m vs)))
  | .set xs md =>
    let vs ← xs.mapM (sEvalV · env)
    let m ← md.mapM (sEvalV · env)
    pure (.val (.obj (.persistentHashSet m vs)))

partial def sEvalV (e : CE) (env : List (Nat × Obj)) : SM Obj := do
  match ← sEval e env with
  | .val v => pure v.toObj
  | .recur _ => throw (.error "compile" "recur escaped")

partial def sStrOf (o : Obj) : SM String := do
  let o ← sRealize o
  pure (strObj .clj (← sHeap) o)

partial def sPrOf (o : Obj) : SM String := do
  let o ← sRealize o
  pure (prObj (if (← get).v.nsPrintName then .jank else .clj) (← sHeap) o)

partial def sRealize (o : Obj) : SM Obj := do
  match o with
  | .opaque .lazySequence k =>
    let some l := (← sHeap).lazies[k]? | throw (.unsupported "lazy")
    let mut out := []
    for x in l.xs do
      out := out ++ [← sRealize (← sInvoke l.f [x])]
    pure (.persistentList none out)
  | .persistentVector m xs => pure (.persistentVector m (← xs.mapM sRealize))
  | .persistentList m xs => pure (.persistentList m (← xs.mapM sRealize))
  | x => pure x

partial def sInternNs (nm : String) : SM Unit := do
  let s ← get
  if (s.w.nss.find? (·.name == nm)).isNone then
    set { s with w := { s.w with nss := s.w.nss ++ [({ name := nm } : NsCell)] } }

/-- Clojure's core functions (core.clj, RT, Namespace). -/
partial def sBuiltin (n : String) (args : List Obj) : SM Obj := do
  match n, args with
  | "println", xs =>
    let parts ← xs.mapM sStrOf
    sEmit (.out ((" ".intercalate parts) ++ "\n").toUTF8.toList)
    pure .nil
  | "print", xs =>
    let parts ← xs.mapM sStrOf
    sEmit (.out (" ".intercalate parts).toUTF8.toList)
    pure .nil
  | "prn", xs =>
    let parts ← xs.mapM sPrOf
    sEmit (.out ((" ".intercalate parts) ++ "\n").toUTF8.toList)
    pure .nil
  | "pr", xs =>
    let parts ← xs.mapM sPrOf
    sEmit (.out (" ".intercalate parts).toUTF8.toList)
    pure .nil
  | "pr-str", xs =>
    let parts ← xs.mapM sPrOf
    pure (str (" ".intercalate parts))
  | "str", xs =>
    let parts ← xs.mapM fun x => match x with
      | .nil => pure ""
      | x => sStrOf x
    pure (str (String.join parts))
  | "ex-info", [.persistentString m, d] => sNewEx m d
  | "ex-info", _ => throw (.stdex "IllegalArgumentException: ex-info")
  | "ex-message", [.opaque .exceptionInfo k] =>
    pure (match (← sHeap).exs[k]? with
      | some e => str e.msg
      | none => .nil)
  | "ex-message", [_] => pure .nil
  | "ex-data", [.opaque .exceptionInfo k] => pure (((← sHeap).exs[k]?).map (·.data) |>.getD .nil)
  | "ex-data", [_] => pure .nil
  | "in-ns", [.symbol _ "" nm] =>
    -- RT.java in-ns: `CURRENT_NS.set(Namespace.findOrCreate(nsname))`, returns the namespace.
    sInternNs nm
    let (h, o) := (← sHeap).nsObj nm
    sSetHeap h
    let s ← get
    match s.tb.set vNs o with
    | .ok tb => set { s with tb }
    | .error m => throw (.stdex s!"IllegalStateException: {m}")
    if s.v.inNsNil then pure .nil else pure o
  | "in-ns", _ => throw (.stdex "ClassCastException: in-ns")
  | "create-ns", [.symbol _ "" nm] =>
    sInternNs nm
    let (h, o) := (← sHeap).nsObj nm
    sSetHeap h
    pure o
  | "find-ns", [.symbol _ "" nm] =>
    if ((← get).w.nss.find? (·.name == nm)).isSome then
      let (h, o) := (← sHeap).nsObj nm
      sSetHeap h
      pure o
    else pure .nil
  | "the-ns", [x] =>
    match x with
    | .opaque .ns _ => pure x
    | .symbol _ "" nm =>
      if ((← get).w.nss.find? (·.name == nm)).isSome then
        let (h, o) := (← sHeap).nsObj nm
        sSetHeap h
        pure o
      else throw (.thrown (← sNewEx s!"No namespace: {nm} found"))
    | _ => throw (.stdex "ClassCastException: the-ns")
  | "ns-name", [x] =>
    match (← sHeap).nsName? x with
    | some nm => pure (sym nm)
    | none => throw (.stdex "ClassCastException: ns-name")
  | "refer", [.symbol _ "" from_] =>
    -- core.clj refer → Namespace.refer → reference/checkReplacement (Namespace.java:106): an
    -- interned mapping of the current namespace is kept.
    let s ← get
    let cur := sCurNs s
    let some src := s.w.nss.find? (·.name == from_) | throw (.thrown (← sNewEx s!"No namespace: {from_}"))
    let publics := src.mappings.filter fun (_, r) => r.ns == from_ && !(metaGet (s.w.slots.get r).md "private").truthy
    let mut nss := s.w.nss
    for (nm, r) in publics do
      let tgt := (nss.find? (·.name == cur)).getD { name := cur }
      let keep := match tgt.mappings.lookup nm with
        | some found => found.ns == cur && found.name == nm
        | none => false
      if !keep then
        nss := nss.map fun c => if c.name == cur then { c with mappings := (nm, r) :: c.mappings.filter (·.1 != nm) } else c
    modify fun s => { s with w := { s.w with nss } }
    pure .nil
  | "require", specs =>
    for sp in specs do
      match sp with
      | .persistentVector _ [.symbol _ "" lib, .keyword "" "as", .symbol _ "" as_] =>
        discard <| sBuiltin "alias" [sym as_, sym lib]
      | .symbol _ "" lib =>
        if ((← get).w.nss.find? (·.name == lib)).isNone then
          throw (.thrown (← sNewEx s!"Could not locate {lib}"))
      | _ => throw (.unsupported "require spec")
    pure .nil
  | "alias", [.symbol _ "" as_, .symbol _ "" lib] =>
    let s ← get
    let cur := sCurNs s
    if (s.w.nss.find? (·.name == lib)).isNone then throw (.thrown (← sNewEx s!"No namespace: {lib} found"))
    modify fun s => { s with w := { s.w with nss := s.w.nss.map fun c =>
      if c.name == cur then { c with aliases := (as_, lib) :: c.aliases.filter (·.1 != as_) } else c } }
    pure .nil
  | "set-macro!", [.var ns nm] =>
    modify fun s => { s with w := { s.w with macros := ⟨ns, nm⟩ :: s.w.macros } }
    pure .nil
  | "reset-meta!", [.var ns nm, m] =>
    modify fun s => { s with w := { s.w with slots := s.w.slots.modify ⟨ns, nm⟩ fun sl => { sl with md := m } } }
    pure m
  | "reset-meta!", [_, m] => pure m
  | "meta", [.var ns nm] => pure ((← get).w.slots.get ⟨ns, nm⟩).md
  | "meta", [x] => pure (x.getMeta.getD .nil)
  | "assoc", [m, k, v] => pure (m.assoc k v)
  | "conj", [.persistentVector md xs, x] => pure (.persistentVector md (xs ++ [x]))
  | "conj", [.nil, x] => pure (.persistentList none [x])
  | "conj", [.persistentList md xs, x] => pure (.persistentList md (x :: xs))
  | "conj", [.persistentSortedSet md xs, x] => pure (.persistentSortedSet md (if xs.any (·.equiv x) then xs else xs ++ [x]))
  | "deref", [.var ns nm] =>
    let s ← get
    pure ((s.tb.deref s.w.slots ⟨ns, nm⟩).getD (.opaque .varUnboundRoot 0))
  | "deref", [.opaque .atom k] => pure (((← sHeap).atoms[k]?).getD .nil)
  | "var-get", [.var ns nm] =>
    let s ← get
    pure ((s.tb.deref s.w.slots ⟨ns, nm⟩).getD (.opaque .varUnboundRoot 0))
  | "swap!", (.opaque .atom k) :: f :: more =>
    let old := ((← sHeap).atoms[k]?).getD .nil
    let nv ← sInvoke f (old :: more)
    let h ← sHeap
    sSetHeap { h with atoms := h.atoms.set! k nv }
    pure nv
  | "map", [f, coll] =>
    let xs := coll.elems.getD []
    let (h, o) := (← sHeap).newLazy { f, xs }
    sSetHeap h
    pure o
  | "symbol", [.persistentString s] => pure (sym s)
  | "symbol", [x@(.symbol ..)] => pure x
  | "keyword", [.persistentString s] => pure (kw s)
  | "identity", [x] => pure x
  | "hash-map", xs =>
    let rec pairs : List Obj → List (Obj × Obj)
      | k :: v :: rest => (k, v) :: pairs rest
      | _ => []
    pure (.persistentHashMap none (pairs xs))
  | "list*", xs => pure (.persistentList none xs)
  | "seq", [x] => pure (match x.elems with | some [] => .nil | some ys => .persistentList none ys | none => .nil)
  | "vec", [x] => pure (.persistentVector none (x.elems.getD []))
  | "doall", [x] => sRealize x
  | "clojure.string/join", [coll] =>
    let parts ← (coll.elems.getD []).mapM sStrOf
    pure (str (String.join parts))
  | "clojure.string/join", [sep, coll] =>
    let parts ← (coll.elems.getD []).mapM sStrOf
    pure (str ((← sStrOf sep).intercalate parts))
  | "clojure.string/blank?", [x] =>
    match x with
    | .nil => pure (.boolean true)
    | .persistentString s => pure (.boolean (s.all Char.isWhitespace))
    | _ => throw (.stdex "ClassCastException: blank?")
  | "iteration", _ => pure .nil
  | name, xs =>
    match builtin name xs with
    | some (.ok r) => pure r
    | some (.error m) => throw (.stdex m)
    | none => throw (.stdex s!"ArityException: Wrong number of args ({xs.length}) passed to: clojure.core/{name}")

partial def sInvoke (f : Obj) (args : List Obj) : SM Obj := do
  stick
  match f with
  | .opaque .nativeFunctionWrapper k => sBuiltin (jBuiltins.getD k "") args
  | .opaque .jitFunction k =>
    let some c := (← get).w.closures[k]? | throw (.unsupported "closure")
    let n := args.length
    let fixed := c.arities.find? fun (ps, r, _) => r.isNone && ps.length == n
    let variadic := c.arities.find? fun (ps, r, _) => r.isSome && ps.length ≤ n
    let some (ps, r, body) := fixed <|> variadic | throw (.stdex s!"ArityException: Wrong number of args ({n})")
    let selfEnv := match c.self with | some id => [(id, f)] | none => []
    let bind (xs : List Obj) : List (Nat × Obj) :=
      match r with
      | some rid =>
        let restV : Obj := if xs.length > ps.length then .persistentList none (xs.drop ps.length) else .nil
        ps.zip (xs.take ps.length) ++ [(rid, restV)] ++ selfEnv ++ c.env
      | none => ps.zip xs ++ selfEnv ++ c.env
    let mut cur := args
    for _ in [0:10000] do
      match ← sEval body (bind cur) with
      | .val v => return v.toObj
      | .recur vs =>
        let vs := vs.map Val.toObj
        cur := match r with
          | some _ => vs.take ps.length ++ ((vs.drop ps.length).headD .nil |>.elems |>.getD [])
          | none => vs
    throw .fuel
  | .keyword .. =>
    match args with
    | [m] => pure (builtinGet m f)
    | [m, d] => pure (builtinGet m f d)
    | _ => throw (.stdex "ArityException: keyword")
  | .var ns nm =>
    let s ← get
    sInvoke ((s.tb.deref s.w.slots ⟨ns, nm⟩).getD .nil) args
  | _ => throw (.stdex s!"ClassCastException: {prObj .clj (← sHeap) f} cannot be cast to clojure.lang.IFn")

end

/-! ## Analysis (Compiler.analyze) on this process -/

def sClosureMacro (s : SS) (f : Obj) : MacroFn := fun args =>
  match (sInvoke f args).run { s with out := #[], fuel := 2000 } with
  | .ok o _ => .ok o
  | .error e s' => .error (e.show s'.w.heap)

def specRt (s : SS) : Runtime :=
  let cells : List VarCell := s.w.slots.map fun (r, sl) =>
    let isM := s.w.macros.contains r
    let macroFn : Option MacroFn :=
      if !isM then none
      else if r.ns == "clojure.core" then cljMacros.lookup r.name
      else match sl.root with
        | some f => some (sClosureMacro s f)
        | none => none
    { ns := r.ns, name := r.name, isMacro := isM, private_ := (metaGet sl.md "private").truthy
      dynamic := sl.dynamic, macroFn, cljMacroFn := macroFn, bound := sl.root.isSome }
  { namespaces := s.w.nss, vars := cells, currentNs := sCurNs s }

/-- `Compiler.macroexpand1` at the top (no locals: `&env` nil) — `none` when not a macro form. -/
def sMacroexpand1 (s : SS) (form : Obj) : Except String (Option Obj) :=
  match form with
  | .persistentList _ (.symbol _ ns name :: args) =>
    if cljSpecial (.symbol none ns name) then .ok none else
    let rt := specRt s
    let (qns, qname) := rt.qualifySymbol ns name
    match rt.findVar qns qname with
    | none => .ok none
    | some vr => match rt.var? vr with
      | some v =>
        if v.isMacro then
          match v.cljMacroFn with
          | some f => (f (form :: .nil :: args)).map some
          | none => .error "unbound macro"
        else .ok none
      | none => .ok none
  | _ => .ok none

/-- Analyzes and runs one top-level form that is not a `do` (Compiler.eval's last branch): the
`def`'s var is interned first (DefExpr.Parser `lookupVar(sym, true)` runs before its init is
analyzed, so it stays interned when the init fails). -/
def sEvalNonDo (s : SS) (form : Obj) : SS × Except Fail Obj :=
  let s := match form with
    | .persistentList _ [.symbol _ "" "def", .symbol _ "" nm] | .persistentList _ (.symbol _ "" "def" :: .symbol _ "" nm :: _ :: _) =>
      let rt := specRt s
      let (rt', vr) := rt.internOwnedVar rt.currentNs nm
      let slots := if (s.w.slots.lookup vr).isSome then s.w.slots else s.w.slots.set vr {}
      { s with w := { s.w with nss := rt'.namespaces, slots } }
    | _ => s
  let cst : CState := { rt := specRt s }
  match (cljAnalyze form {} .expr).run cst with
  | .error (.compileError m) => (s, .error (.error "compile" m))
  | .error (.thrown m) => (s, .error (.stdex m))
  | .error .fuel => (s, .error .fuel)
  | .error (.ub m) => (s, .error (.ub m))
  | .error (.unsupported m) => (s, .error (.unsupported m))
  | .error (.value _) => (s, .error (.unsupported "value"))
  | .ok (ce, cst') =>
    let slots := cst'.rt.vars.foldl (fun acc c => if (acc.lookup c.ref).isSome then acc else acc.set c.ref {}) s.w.slots
    let s := { s with w := { s.w with nss := cst'.rt.namespaces, slots } }
    match (sEvalV ce []).run s with
    | .ok v s' => (s', .ok v)
    | .error f s' => (s', .error f)

/-- `Compiler.eval` (Compiler.java:7658): macroexpand, then a `do` form by form. -/
partial def sEvalTop (s : SS) (form : Obj) (fuel : Nat := 64) : SS × Except Fail Obj :=
  if fuel == 0 then (s, .error .fuel) else
  -- `form = macroexpand(form)`
  let rec expand (f : Obj) : Nat → Except String Obj
    | 0 => .error "macroexpansion fuel"
    | k + 1 => match sMacroexpand1 s f with
      | .ok (some f') => expand f' k
      | .ok none => .ok f
      | .error e => .error e
  match expand form 64 with
  | .error e => (s, .error (.error "macroexpand" e))
  | .ok form =>
    match form with
    | .persistentList _ (.symbol _ "" "do" :: body) =>
      if s.v.noTopDoSplit then sEvalNonDo s form else
      match body with
      | [] => (s, .ok .nil)
      | _ => Id.run do
        let mut s := s
        let mut last : Obj := .nil
        for b in body do
          let (s', r) := sEvalTop s b (fuel - 1)
          s := s'
          match r with
          | .ok v => last := v
          | .error f => return (s, .error f)
        return (s, .ok last)
    | _ => sEvalNonDo s form

/-- A Clojure session's own state (nREPL session: its thread bindings). -/
structure Session where
  ns : String := "user"
  s1 : Obj := .nil
  s2 : Obj := .nil
  s3 : Obj := .nil
  se : Obj := .nil
  deriving Inhabited

/-- One reply the spec gives for one form (or the whole input in `loadString` mode). -/
inductive SpecItem where
  | value (pr : String) (ns : String)
  | error
  deriving Repr, BEq, Inhabited

/-- How the spec reads code: clojure.main/repl, or one input (load-string). -/
inductive SpecMode where
  | repl
  | loadString
  deriving Repr, BEq, Inhabited

structure SpecEvalOut where
  items : List SpecItem
  out : List UInt8
  /-- The reader hung or the spec left its grammar. -/
  unsupported : Option String := none
  deriving Inhabited

/-- One nREPL `eval` of `code` in session `sess` (namespace `nsOverride` when the request names
one), as clojure.main/repl (or load-string) runs it. -/
def specEval (w : SW) (sess : Session) (code : String) (nsOverride : Option String) (mode : SpecMode)
    (variant : Variant := {}) (restoreNs : Bool := false) : SW × Session × SpecEvalOut := Id.run do
  let startNs := nsOverride.getD sess.ns
  let (h, nso) := w.heap.nsObj startNs
  let tb := ({} : TB).push [(vNs, nso), (v1, sess.s1), (v2, sess.s2), (v3, sess.s3), (vE, sess.se)]
  let mut s : SS := { w := { w with heap := h }, tb, v := variant }
  let units := Jank.ReadClj.toUtf16 (code.toList.map Char.toNat)
  let mut st : Jank.ReadClj.St := { r := { s := units.toArray } }
  let mut items : Array SpecItem := #[]
  let mut out : Array OutEv := #[]
  let mut unsupported : Option String := none
  let mut last : Option Obj := none
  let mut failedLS := false
  for _ in [0:64] do
    let (o, st') := (Jank.ReadClj.read (units.length + 8)).run st
    st := st'
    let setE (s : SS) (f : Fail) : SS :=
      let (h, e) := match f with
        | .thrown o@(.opaque .exceptionInfo _) => (s.w.heap, o)
        | f => s.w.heap.newEx { msg := f.show s.w.heap, origin := "clj" }
      let s := { s with w := { s.w with heap := h } }
      { s with tb := (s.tb.set vE e).toOption.getD s.tb }
    match o with
    | .eof => break
    | .none_ => continue
    | .closer _ | .err _ =>
      s := setE s (.error "read" "reader exception")
      items := items.push .error
      if mode == .loadString then failedLS := true; break
      -- LispReader leaves the reader after the bad character: the loop reads on.
      if let .err m := o then
        if m == "StackOverflowError" || m == "reader loop" then unsupported := some m; break
      continue
    | .ok v =>
      match cljForm v with
      | none => unsupported := some "a value outside the grammar"; break
      | some form =>
        let (s', r) := sEvalTop { s with out := #[] } form
        out := out ++ s'.out
        s := { s' with out := #[] }
        match r with
        | .error (.unsupported m) => unsupported := some m; break
        | .error .fuel => unsupported := some "fuel"; break
        | .error f =>
          s := setE s f
          items := items.push .error
          if mode == .loadString then failedLS := true; break
        | .ok v =>
          if mode == .loadString then last := some v
          else
            let o1 := (s.tb.deref s.w.slots v1).getD .nil
            let o2 := (s.tb.deref s.w.slots v2).getD .nil
            let tb := (s.tb.set v3 o2).toOption.getD s.tb
            let tb := (tb.set v2 o1).toOption.getD tb
            let tb := (tb.set v1 v).toOption.getD tb
            s := { s with tb }
            -- `:print`: an exception printing the value is caught like any other (*1 already set).
            match (sPrOf v).run { s with out := #[] } with
            | .ok txt s' =>
              out := out ++ (if variant.printOutLost then #[] else s'.out)
              s := { s' with out := #[] }
              items := items.push (.value txt (sCurNs s))
            | .error f s' =>
              out := out ++ s'.out
              s := setE { s' with out := #[] } f
              items := items.push .error
  -- `Compiler.load` (load-file) binds `*ns*` for the load: what the file switched to is undone.
  if restoreNs then
    let (h, o) := s.w.heap.nsObj startNs
    s := { s with w := { s.w with heap := h } }
    s := { s with tb := (s.tb.set vNs o).toOption.getD s.tb }
  if mode == .loadString && !failedLS && unsupported.isNone then
    match last with
    | some v =>
      let o1 := (s.tb.deref s.w.slots v1).getD .nil
      let o2 := (s.tb.deref s.w.slots v2).getD .nil
      let tb := (s.tb.set v3 o2).toOption.getD s.tb
      let tb := (tb.set v2 o1).toOption.getD tb
      let tb := (tb.set v1 v).toOption.getD tb
      s := { s with tb }
      match (sPrOf v).run { s with out := #[] } with
      | .ok txt s' =>
        out := out ++ (if variant.printOutLost then #[] else s'.out)
        s := { s' with out := #[] }
        items := items.push (.value txt (sCurNs s))
      | .error f s' =>
        out := out ++ s'.out
        let (h, e) := s'.w.heap.newEx { msg := f.show s'.w.heap, origin := "clj print" }
        s := { s' with out := #[], w := { s'.w with heap := h } }
        s := { s with tb := (s.tb.set vE e).toOption.getD s.tb }
        items := items.push .error
    | none => pure ()
  let g (v : VarRef) := (s.tb.deref s.w.slots v).getD .nil
  let sess' : Session := { ns := sCurNs s, s1 := g v1, s2 := g v2, s3 := g v3, se := g vE }
  return (s.w, sess', { items := items.toList, out := outBytes out.toList, unsupported })

end Jank.R3.Nrepl

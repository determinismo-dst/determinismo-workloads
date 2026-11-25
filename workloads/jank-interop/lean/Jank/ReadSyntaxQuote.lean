import Determinismo

/-!
# Syntax quote: what the expansion evaluates to, jank beside Clojure

jank expands `` ` `` at read time (parse.cpp `syntax_quote`, 1458-1724, with
`syntax_quote_expand_segments` 1320-1392 and `is_special` 1433-1456); Clojure too
(LispReader.java `SyntaxQuoteReader.syntaxQuote`, 1010-1110, `Compiler.resolveSymbol`). The two
build different code (jank `(clojure.core/list ...)`, Clojure `(seq (concat (list ...)))`), so
they are compared by what the code evaluates to, with locals `a`, `b` bound by the search.

Modeled, for jank:
- a symbol: special (`is_special`: `finally`, `catch`, a name starting with `.`, or a name in
  `def fn* recur do let* letfn* loop* if quote var throw try case* ...`) stays as it is; a name
  ending in `#` is a gensym; an unqualified symbol other than `&` becomes `<var's ns>/name` when
  `find_var` finds a var, else `<current ns>/name` (1489-1500); a qualified one goes through
  `qualify_symbol` (aliases; none here);
- `~x` is `x` evaluated; `~@` of a LITERAL vector or set form splices that form's element
  expressions one by one (1358-1371); any other `~@x` splices `x`'s value;
- a vector, list or set is rebuilt from the segments (a set literal of the expressions).

For Clojure: specials (`Compiler.specials`: the same plus `. set! new deftype* reify*
monitor-enter monitor-exit clojure.core/import* &`) stay; `x#` is a gensym; a name ending in `.`
is resolved without the dot and gets it back unqualified; a name starting with `.` stays;
`Compiler.resolveSymbol` leaves a name containing a `.` (not first) as it is, maps a var to its
namespace, anything else to the current namespace; `~@x` splices the VALUE of `x` (a set literal
`#{a b}` is evaluated first: equal values collapse).
-/

namespace Jank.ReadSyntaxQuote

open Determinismo

/-- A form inside a syntax quote. -/
inductive F where
  | sym (ns name : String)
  | num (n : Int)
  | unq (x : F)
  | unqs (x : F)
  | list (xs : List F)
  | vec (xs : List F)
  | set (xs : List F)
  deriving Repr, BEq, Inhabited

/-- A value. Sets are kept sorted (compared as sets). -/
inductive V where
  | sym (ns name : String)
  | num (n : Int)
  | list (xs : List V)
  | vec (xs : List V)
  | set (xs : List V)
  deriving Repr, BEq, Inhabited

partial def V.show : V → String
  | .sym ns n => if ns.isEmpty then n else ns ++ "/" ++ n
  | .num n => toString n
  | .list xs => "(" ++ " ".intercalate (xs.map V.show) ++ ")"
  | .vec xs => "[" ++ " ".intercalate (xs.map V.show) ++ "]"
  | .set xs => "#{" ++ " ".intercalate (xs.map V.show) ++ "}"

partial def F.show : F → String
  | .sym ns n => if ns.isEmpty then n else ns ++ "/" ++ n
  | .num n => toString n
  | .unq x => "~" ++ x.show
  | .unqs x => "~@" ++ x.show
  | .list xs => "(" ++ " ".intercalate (xs.map F.show) ++ ")"
  | .vec xs => "[" ++ " ".intercalate (xs.map F.show) ++ "]"
  | .set xs => "#{" ++ " ".intercalate (xs.map F.show) ++ "}"

/-- A set value: equal values once, in a canonical order. -/
def mkSet (xs : List V) : V :=
  let dedup := xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  .set ((dedup.toArray.qsort fun a b => a.show < b.show).toList)

/-- The runtime: locals and the vars that exist (`map` in clojure.core). -/
structure Env where
  locals : List (String × V)
  vars : List (String × String) := [("map", "clojure.core")]
  ns : String := "user"

/-- Evaluating an unquoted form (`~x`, `~@x`): a local, a number, a literal vector or set of
such (sets collapse equal values), `(list ...)`. -/
partial def evalU (env : Env) : F → Except String V
  | .sym "" n => match env.locals.lookup n with
    | some v => .ok v
    | none => .error s!"unbound {n}"
  | .num n => .ok (.num n)
  | .vec xs => do .ok (.vec (← xs.mapM (evalU env)))
  | .set xs => do .ok (mkSet (← xs.mapM (evalU env)))
  | .list (.sym "" "list" :: xs) => do .ok (.list (← xs.mapM (evalU env)))
  | f => .error s!"cannot evaluate {f.show}"

def elements : V → List V
  | .list xs | .vec xs | .set xs => xs
  | _ => []

def jankSpecials : List String :=
  ["def", "fn*", "recur", "do", "let*", "letfn*", "loop*", "if", "quote", "var", "throw", "try",
   "case*", "cpp/raw", "cpp/dsl", "cpp/value", "cpp/cast", "cpp/unsafe-cast", "cpp/box",
   "cpp/unbox", "cpp/new", "cpp/delete"]

/-- parse.cpp `is_special` (1433-1456) and the symbol branch of `syntax_quote` (1470-1507). -/
def jankQualify (env : Env) (ns name : String) : V :=
  if (ns.isEmpty && (name == "finally" || name == "catch" || name.startsWith ".")) || jankSpecials.contains name then
    .sym ns name
  else if ns.isEmpty && name.endsWith "#" then .sym "" (String.ofList name.toList.dropLast ++ "__auto__")
  else if ns.isEmpty && name != "&" then
    match env.vars.lookup name with
    | some vns => .sym vns name
    | none => .sym env.ns name
  else .sym ns name

def cljSpecials : List String :=
  ["def", "loop*", "recur", "if", "case*", "let*", "letfn*", "do", "fn*", "quote", "var",
   "clojure.core/import*", ".", "set!", "deftype*", "reify*", "try", "throw", "monitor-enter",
   "monitor-exit", "catch", "finally", "new", "&"]

/-- `Compiler.resolveSymbol` for an unqualified symbol (Compiler.java). -/
def cljResolve (env : Env) (name : String) : V :=
  if (name.drop 1).contains '.' then .sym "" name
  else match env.vars.lookup name with
    | some vns => .sym vns name
    | none => .sym env.ns name

/-- `SyntaxQuoteReader.syntaxQuote`'s symbol branch (LispReader.java:1016-1059). -/
def cljQualify (env : Env) (ns name : String) : V :=
  let full := if ns.isEmpty then name else ns ++ "/" ++ name
  if cljSpecials.contains full then .sym ns name
  else if ns.isEmpty && name.endsWith "#" then .sym "" (String.ofList name.toList.dropLast ++ "__auto__")
  else if ns.isEmpty && name.endsWith "." then
    match cljResolve env (String.ofList name.toList.dropLast) with
    | .sym _ n => .sym "" (n ++ ".")
    | v => v
  else if ns.isEmpty && name.startsWith "." then .sym "" name
  else if !ns.isEmpty then .sym ns name
  else cljResolve env name

mutual
/-- What jank's expansion of `` `form `` evaluates to. -/
partial def jankSQ (env : Env) : F → Except String V
  | .sym ns n => .ok (jankQualify env ns n)
  | .num n => .ok (.num n)
  | .unq x => evalU env x
  | .unqs _ => .error "splice outside a collection"
  | .list xs => do .ok (.list (← jankItems env xs))
  | .vec xs => do .ok (.vec (← jankItems env xs))
  | .set xs => do .ok (mkSet (← jankItems env xs))

/-- `syntax_quote_expand_segments` (parse.cpp:1320-1392). -/
partial def jankItems (env : Env) : List F → Except String (List V)
  | [] => .ok []
  | item :: rest => do
    let here ← match item with
      | .unq x => do pure [← evalU env x]
      | .unqs (.vec es) => es.mapM (evalU env)   -- folded: each element expression
      | .unqs (.set es) => do
        -- folded too; the set's iteration order is taken to be Clojure's (canonical) order, so
        -- only what the fold changes is seen: equal values are not collapsed.
        let vs ← es.mapM (evalU env)
        pure (vs.toArray.qsort (fun a b => a.show < b.show)).toList
      | .unqs x => do pure (elements (← evalU env x))
      | f => do pure [← jankSQ env f]
    pure (here ++ (← jankItems env rest))
end

mutual
/-- What Clojure's expansion evaluates to. -/
partial def cljSQ (env : Env) : F → Except String V
  | .sym ns n => .ok (cljQualify env ns n)
  | .num n => .ok (.num n)
  | .unq x => evalU env x
  | .unqs _ => .error "splice not in list"
  | .list xs => do .ok (.list (← cljItems env xs))
  | .vec xs => do .ok (.vec (← cljItems env xs))
  | .set xs => do .ok (mkSet (← cljItems env xs))

partial def cljItems (env : Env) : List F → Except String (List V)
  | [] => .ok []
  | item :: rest => do
    let here ← match item with
      | .unq x => do pure [← evalU env x]
      | .unqs x => do pure (elements (← evalU env x))
      | f => do pure [← cljSQ env f]
    pure (here ++ (← cljItems env rest))
end

/-! ## Search: forms drawn by decisions -/

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev WM := EStateM Stop World

def symbols : List (String × String) :=
  [("", "a"), ("", "foo"), ("", "map"), ("", "if"), ("", "a.b"), ("", "Foo."), ("", ".m"),
   ("", "x#"), ("", "&"), ("", "new"), ("str", "join")]

/-- An unquoted expression. -/
def drawU (depth : Nat) : WM F := do
  match ← decide (σ := World) "sq.unquoted" (if depth == 0 then 1 else 3) with
  | 0 => pure (.sym "" (if (← decide (σ := World) "sq.local" 2) == 0 then "a" else "b"))
  | 1 => do
    let n ← decide (σ := World) "sq.lit.size" 3
    let mut xs := #[]
    for _ in [0:n] do xs := xs.push (.sym "" (if (← decide (σ := World) "sq.local" 2) == 0 then "a" else "b"))
    pure (.vec xs.toList)
  | _ => do
    -- a set literal of distinct locals (a reader-valid set form)
    match ← decide (σ := World) "sq.lit.set" 3 with
    | 0 => pure (.set [.sym "" "a"])
    | 1 => pure (.set [.sym "" "b"])
    | _ => pure (.set [.sym "" "a", .sym "" "b"])

partial def drawF (depth : Nat) (syms : List (String × String) := symbols) : WM F := do
  let k ← decide (σ := World) "sq.kind" (if depth == 0 then 3 else 6)
  match k with
  | 0 => do
    let s ← pick (σ := World) "sq.symbol" syms
    let (ns, n) := s.getD ("", "a")
    pure (.sym ns n)
  | 1 => pure (.num 1)
  | 2 => pure (.unq (← drawU 1))
  | _ => do
    let n ← decide (σ := World) "sq.size" 3
    let mut xs := #[]
    for _ in [0:n] do
      if (← decide (σ := World) "sq.splice" 2) == 1 then xs := xs.push (.unqs (← drawU 1))
      else xs := xs.push (← drawF (depth - 1) syms)
    match k with
    | 3 => pure (.list xs.toList)
    | 4 => pure (.vec xs.toList)
    | _ => pure (.set xs.toList)

def body (syms : List (String × String) := symbols) : WM Unit := do
  let f ← drawF 2 syms
  let a ← decide (σ := World) "sq.a" 2
  let b ← decide (σ := World) "sq.b" 2
  let env : Env := { locals := [("a", .num (Int.ofNat a + 1)), ("b", .num (Int.ofNat b + 1))] }
  let j := jankSQ env f
  let c := cljSQ env f
  let sh := fun (r : Except String V) => match r with | .ok v => v.show | .error e => s!"error ({e})"
  if sh j != sh c then
    violate (σ := World) "syntax quote evaluates as Clojure's"
      s!"(let [a {a + 1} b {b + 1}] `{f.show}): Clojure {sh c}, jank {sh j}"

def runWith (syms : List (String × String)) (source : Source) : Ended :=
  match (body syms).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

def run : Source → Ended := runWith symbols

/-- Without the symbols the first searches find (`a.b`, `Foo.`, and `new`, a Clojure special
form jank does not have). -/
def runNoDots : Source → Ended :=
  runWith (symbols.filter fun (_, n) => (!(n.contains '.') || n.startsWith ".") && n != "new")

end Jank.ReadSyntaxQuote

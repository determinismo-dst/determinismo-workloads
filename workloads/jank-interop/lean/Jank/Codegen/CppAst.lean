import Jank.Codegen.Value
/-!
# The emitted C++, read back: tokens, a parser for the subset jank emits, a scope check

The meaning of the generated text is the C++ one. This module reads the text the code generator
produced (`Jank.Codegen.Cpp`) into a small C++ syntax tree, and checks it the way a C++ compiler
would for the faults this subset can have: a name used outside the block that declares it, a
name declared twice in one block or parameter list, `return;` in a function returning a value,
and anything that does not parse. Its execution is `Jank.Codegen.Exec`.

The grammar covers exactly the statement and expression shapes cpp_processor.cpp writes for the
non-interop instructions.
-/

namespace Jank.Codegen.CppAst

inductive Tok where
  | ident (s : String)   -- qualified names are one token: `jank::runtime::truthy`
  | num (s : String)
  | str (bytes : List Char)  -- raw characters between the quotes
  | punct (s : String)
  deriving Repr, BEq, Inhabited

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c == '$' || c.toNat ≥ 128
def isIdChar (c : Char) : Bool := isIdStart c || c.isDigit

/-- C++ tokens (comments and `#line` directives skipped). -/
def tokenize (s : String) : Except String (Array Tok) := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut out : Array Tok := #[]
  let mut fuel := n * 4 + 16
  while i < n && fuel > 0 do
    fuel := fuel - 1
    let c := cs[i]!
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then i := i + 1
    else if c == '#' then
      -- a preprocessing directive: to the end of the line
      while i < n && cs[i]! != '\n' do i := i + 1
    else if isIdStart c then
      let mut j := i
      let mut done := false
      while !done do
        while j < n && isIdChar cs[j]! do j := j + 1
        if j + 2 < n && cs[j]! == ':' && cs[j+1]! == ':' && isIdStart cs[j+2]! then j := j + 2
        else done := true
      out := out.push (.ident (String.ofList (cs.extract i j).toList))
      i := j
    else if c.isDigit || (c == '.' && i + 1 < n && cs[i+1]!.isDigit) then
      let mut j := i
      while j < n && (isIdChar cs[j]! || cs[j]! == '.' ||
          ((cs[j]! == '+' || cs[j]! == '-') && j > i && (cs[j-1]! == 'e' || cs[j-1]! == 'E'))) do
        j := j + 1
      out := out.push (.num (String.ofList (cs.extract i j).toList))
      i := j
    else if c == '"' then
      let mut j := i + 1
      let mut body : List Char := []
      while j < n && cs[j]! != '"' do
        if cs[j]! == '\n' then return .error "missing terminating '\"' character (a raw newline in a string literal)"
        if cs[j]! == '\\' && j + 1 < n then
          body := body ++ [cs[j]!, cs[j+1]!]
          j := j + 2
        else
          body := body ++ [cs[j]!]
          j := j + 1
      if j ≥ n then return .error "unterminated string literal"
      out := out.push (.str body)
      i := j + 1
    else
      let two := if i + 1 < n then String.ofList [c, cs[i+1]!] else ""
      let three := if i + 2 < n then String.ofList [c, cs[i+1]!, cs[i+2]!] else ""
      if three == "..." then out := out.push (.punct "..."); i := i + 3
      else if two == "->" || two == "&&" || two == "::" then out := out.push (.punct two); i := i + 2
      else out := out.push (.punct (String.singleton c)); i := i + 1
  return .ok out

mutual
inductive Expr where
  | id (n : String)
  | num (s : String)
  | str (body : List Char)
  | neg (e : Expr)
  | call (f : Expr) (args : List Expr)
  | dot (e : Expr) (m : String)
  | arrow (e : Expr) (m : String)
  /-- `T{ args }` -/
  | brace (ty : String) (args : List Expr)
  /-- `static_cast<T>(e)`, `reinterpret_cast<T>(e)`, `(void*)e`, `jtl::make_ref<struct C>(…)` -/
  | cast (kind : String) (ty : String) (args : List Expr)
  | addr (n : String)
  | lambda (body : List Stmt')

/-- Statements. -/
inductive Stmt' where
  | decl (ty : String) (name : String) (init : List Expr)
  | assign (lhs rhs : Expr)
  | expr (e : Expr)
  | block (ss : List Stmt')
  | ifElse (c : Expr) (t e : List Stmt')
  | whileTrue (body : List Stmt')
  | brk
  | cont
  | ret (e : Option Expr)
  | thr (e : Option Expr)
  /-- `catch(T n)` is `some (T, n)`, `catch(...)` is `none`. -/
  | tryCatch (body : List Stmt') (handlers : List (Option (String × String) × List Stmt'))
  | switch (e : Expr) (cases : List (Option Expr × List Stmt'))
end

instance : Inhabited Expr := ⟨.id ""⟩
instance : Inhabited Stmt' := ⟨.brk⟩

abbrev Stmt := Stmt'

/-- A C function: name, parameter names (`""` when unnamed), body. -/
structure FnDef where
  name : String
  params : List String
  body : List Stmt
  deriving Inhabited

structure Program where
  fns : List FnDef := []
  structs : List (String × List String) := []
  /-- Namespace-level variables (module target), by unqualified and qualified name. -/
  globals : List String := []
  /-- The module load function's statements. -/
  load : List Stmt := []
  deriving Inhabited

structure P where
  toks : Array Tok
  pos : Nat := 0

abbrev PM := StateT P (Except String)

def peek : PM Tok := do
  let s ← get
  pure (s.toks[s.pos]?.getD (.punct "<eof>"))

def peekAt (k : Nat) : PM Tok := do
  let s ← get
  pure (s.toks[s.pos + k]?.getD (.punct "<eof>"))

def adv : PM Tok := do
  let t ← peek
  modify fun s => { s with pos := s.pos + 1 }
  pure t

def expectP (p : String) : PM Unit := do
  let t ← adv
  if t != .punct p then throw s!"expected '{p}', got {repr t}"

def expectId : PM String := do
  match ← adv with
  | .ident s => pure s
  | t => throw s!"expected identifier, got {repr t}"

def isP (p : String) : PM Bool := do pure ((← peek) == .punct p)

/-- A type name as the code generator spells it: qualified identifiers, `const`, `*`, `&&`, and
template arguments `<…>`. -/
partial def parseTypeTail (acc : String) : PM String := do
  match ← peek with
  | .ident "const" => let _ ← adv; parseTypeTail (acc ++ " const")
  | .punct "*" => let _ ← adv; parseTypeTail (acc ++ "*")
  | .punct "&&" => let _ ← adv; parseTypeTail (acc ++ "&&")
  | .punct "&" => let _ ← adv; parseTypeTail (acc ++ "&")
  | .punct "<" =>
    let _ ← adv
    let mut depth := 1
    let mut s := acc ++ "<"
    let mut g := 1000
    while depth > 0 && g > 0 do
      g := g - 1
      match ← adv with
      | .punct "<" => depth := depth + 1; s := s ++ "<"
      | .punct ">" => depth := depth - 1; s := s ++ ">"
      | .ident x => s := s ++ x ++ " "
      | .num x => s := s ++ x
      | .punct x => s := s ++ x
      | .str _ => s := s ++ "\"\""
    parseTypeTail s
  | _ => pure acc

mutual
partial def parseArgs (close : String) : PM (List Expr) := do
  if ← isP close then let _ ← adv; return []
  let mut out : List Expr := []
  let mut g := 10000
  while g > 0 do
    g := g - 1
    out := out ++ [← parseExpr]
    match ← adv with
    | .punct "," => continue
    | .punct c => if c == close then break else throw s!"expected ',' or '{close}', got {c}"
    | t => throw s!"bad argument list token {repr t}"
  pure out

partial def parsePrimary : PM Expr := do
  match ← adv with
  | .punct "-" => pure (.neg (← parsePrimary))
  | .punct "&" => pure (.addr (← expectId))
  | .punct "(" =>
    -- `(void*)expr` or a parenthesised expression
    match ← peek with
    | .ident "void" =>
      let _ ← adv
      expectP "*"
      expectP ")"
      pure (.cast "c" "void*" [← parsePostfix])
    | _ =>
      let e ← parseExpr
      expectP ")"
      pure e
  | .punct "[" =>
    expectP "&"; expectP "]"; expectP "("; expectP ")"; expectP "{"
    pure (.lambda (← parseStmts))
  | .num s => pure (.num s)
  | .str b => pure (.str b)
  | .ident "static_cast" | .ident "reinterpret_cast" =>
    let k := "cast"
    expectP "<"
    let ty ← parseTypeName
    expectP ">"
    expectP "("
    pure (.cast k ty (← parseArgs ")"))
  | .ident "jtl::make_ref" =>
    expectP "<"
    let _ ← expectId  -- struct
    let c ← expectId
    expectP ">"
    expectP "("
    pure (.cast "make_ref" c (← parseArgs ")"))
  | .ident n =>
    if ← isP "{" then
      let _ ← adv
      pure (.brace n (← parseArgs "}"))
    else if n == "jank::runtime::convert" && (← isP "<") then
      let _ ← adv
      let ty ← parseTypeName
      expectP ">"
      expectP "::"
      let m ← expectId
      expectP "("
      pure (.cast ("convert:" ++ m) ty (← parseArgs ")"))
    else if n == "jank::runtime::make_box" && (← isP "<") then
      let _ ← adv
      let ty ← parseTypeName
      expectP ">"
      expectP "("
      pure (.cast "make_box" ty (← parseArgs ")"))
    else pure (.id n)
  | t => throw s!"unexpected token in expression: {repr t}"

partial def parsePostfix : PM Expr := do
  let mut e ← parsePrimary
  let mut g := 1000
  while g > 0 do
    g := g - 1
    match ← peek with
    | .punct "(" => let _ ← adv; e := .call e (← parseArgs ")")
    | .punct "." => let _ ← adv; e := .dot e (← expectId)
    | .punct "->" => let _ ← adv; e := .arrow e (← expectId)
    | _ => break
  pure e

partial def parseExpr : PM Expr := parsePostfix

partial def parseTypeName : PM String := do
  let base ← match ← adv with
    | .ident "struct" => pure ("struct " ++ (← expectId))
    | .ident s => pure s
    | t => throw s!"expected a type, got {repr t}"
  parseTypeTail base

/-- A declaration after its type: `name(init)`, `name{ init }`, `name;`. -/
partial def parseDeclRest (ty : String) : PM Stmt := do
  -- `auto &&name(...)`: the `&&` was part of the type
  let name ← expectId
  match ← adv with
  | .punct "(" => let a ← parseArgs ")"; expectP ";"; pure (.decl ty name a)
  | .punct "{" => let a ← parseArgs "}"; expectP ";"; pure (.decl ty name a)
  | .punct ";" => pure (.decl ty name [])
  | t => throw s!"bad declaration of {name}: {repr t}"

partial def parseBlockBody : PM (List Stmt) := do
  expectP "{"
  parseStmts

/-- Statements up to the closing `}` (consumed). -/
partial def parseStmts : PM (List Stmt) := do
  let mut out : List Stmt := []
  let mut g := 100000
  while g > 0 do
    g := g - 1
    match ← peek with
    | .punct "}" => let _ ← adv; return out
    | .punct "<eof>" => throw "unexpected end of input (missing '}')"
    | _ => out := out ++ [← parseStmt]
  throw "statement fuel"

partial def parseStmt : PM Stmt := do
  match ← peek with
  | .punct "{" => let _ ← adv; pure (.block (← parseStmts))
  | .punct ";" => let _ ← adv; pure (.block [])
  | .ident "if" =>
    let _ ← adv; expectP "("
    let c ← parseExpr
    expectP ")"
    let t ← parseBlockBody
    match ← peek with
    | .ident "else" => let _ ← adv; pure (.ifElse c t (← parseBlockBody))
    | _ => pure (.ifElse c t [])
  | .ident "while" =>
    let _ ← adv; expectP "("
    let _ ← adv; expectP ")"
    pure (.whileTrue (← parseBlockBody))
  | .ident "break" => let _ ← adv; expectP ";"; pure .brk
  | .ident "continue" => let _ ← adv; expectP ";"; pure .cont
  | .ident "return" =>
    let _ ← adv
    if ← isP ";" then let _ ← adv; pure (.ret none)
    else if ← isP "{" then
      let _ ← adv; expectP "}"; expectP ";"
      pure (.ret (some (.brace "" [])))
    else
      let e ← parseExpr
      expectP ";"
      pure (.ret (some e))
  | .ident "throw" =>
    let _ ← adv
    if ← isP ";" then let _ ← adv; pure (.thr none)
    else let e ← parseExpr; expectP ";"; pure (.thr (some e))
  | .ident "try" =>
    let _ ← adv
    let body ← parseBlockBody
    let mut hs : List (Option (String × String) × List Stmt) := []
    let mut g := 1000
    while g > 0 do
      g := g - 1
      match ← peek with
      | .ident "catch" =>
        let _ ← adv; expectP "("
        if ← isP "..." then
          let _ ← adv; expectP ")"
          hs := hs ++ [(none, ← parseBlockBody)]
        else
          let ty ← parseTypeName
          let n ← expectId
          expectP ")"
          hs := hs ++ [(some (ty, n), ← parseBlockBody)]
      | _ => break
    -- [except.pre]: a try-block is followed by at least one handler
    if hs.isEmpty then throw "expected 'catch' after a try block"
    pure (.tryCatch body hs)
  | .ident "switch" =>
    let _ ← adv; expectP "("
    let e ← parseExpr
    expectP ")"; expectP "{"
    let mut cases : List (Option Expr × List Stmt) := []
    let mut g := 10000
    while g > 0 do
      g := g - 1
      match ← adv with
      | .ident "case" =>
        let k ← parseExpr
        expectP ":"
        cases := cases ++ [(some k, ← parseBlockBody)]
      | .ident "default" =>
        expectP ":"
        cases := cases ++ [(none, ← parseBlockBody)]
      | .punct "}" => break
      | t => throw s!"bad switch body: {repr t}"
    pure (.switch e cases)
  | .ident "auto" =>
    let ty ← parseTypeName
    parseDeclRest ty
  | .ident "new" =>
    -- `new (&ns::name) auto(expr);`: placement-new of a namespace variable
    let _ ← adv; expectP "("; expectP "&"
    let n ← expectId
    expectP ")"
    let _ ← expectId
    expectP "("
    let e ← parseExpr
    expectP ")"; expectP ";"
    pure (.assign (.id ((n.splitOn "::").getLast!)) e)
  | .ident "GC_add_roots" =>
    let mut g := 1000
    while g > 0 do
      g := g - 1
      if (← adv) == .punct ";" then break
    pure (.block [])
  | .ident n =>
    -- a declaration `T name...` (two identifiers in a row) or an expression statement
    match ← peekAt 1 with
    | .ident _ =>
      let ty ← parseTypeName
      parseDeclRest ty
    | .punct "<" =>
      if n.startsWith "jank::" && !(n.endsWith "_cast") then
        let ty ← parseTypeName
        parseDeclRest ty
      else exprStmt
    | _ => exprStmt
  | _ => exprStmt

partial def exprStmt : PM Stmt := do
  let e ← parseExpr
  if ← isP "=" then
    let _ ← adv
    let r ← parseExpr
    expectP ";"
    pure (.assign e r)
  else
    expectP ";"
    pure (.expr e)
end

/-- `extern "C" jank::runtime::object_ref name(params) { … }`, prototypes, structs, the module
namespace and its variables and load function. -/
partial def parseTop (acc : Program) : PM Program := do
  match ← peek with
  | .punct "<eof>" => pure acc
  | .punct "}" => let _ ← adv; parseTop acc  -- the namespace's closing brace
  | .ident "namespace" => let _ ← adv; let _ ← expectId; expectP "{"; parseTop acc
  | .ident "struct" =>
    let _ ← adv
    let n ← expectId
    expectP "{"
    let mut fields : List String := []
    let mut g := 1000
    while g > 0 do
      g := g - 1
      if ← isP "}" then let _ ← adv; break
      let _ ← parseTypeName
      fields := fields ++ [← expectId]
      expectP ";"
    expectP ";"
    parseTop { acc with structs := acc.structs ++ [(n, fields)] }
  | .ident "extern" =>
    let _ ← adv
    let _ ← adv  -- "C"
    let rty ← parseTypeName
    let name ← expectId
    expectP "("
    let mut params : List String := []
    if ← isP ")" then let _ ← adv
    else
      let mut g := 100
      while g > 0 do
        g := g - 1
        let _ ← parseTypeName
        let pn ← match ← peek with
          | .ident p => let _ ← adv; pure p
          | _ => pure ""
        params := params ++ [pn]
        match ← adv with
        | .punct "," => continue
        | .punct ")" => break
        | t => throw s!"bad parameter list: {repr t}"
    if ← isP ";" then let _ ← adv; parseTop acc
    else
      expectP "{"
      let body ← parseStmts
      if rty == "void" then parseTop { acc with load := acc.load ++ body }
      else parseTop { acc with fns := acc.fns ++ [{ name, params, body }] }
  | .ident _ =>
    -- a namespace-level variable `T name{ _jank_null{ } };` (module target)
    let _ ← parseTypeName
    let n ← expectId
    expectP "{"
    let _ ← parseArgs "}"
    expectP ";"
    parseTop { acc with globals := acc.globals ++ [n] }
  | t => throw s!"unexpected top-level token {repr t}"

def parseProgram (text : String) : Except String Program := do
  let toks ← tokenize text
  match (parseTop {}).run { toks } with
  | .ok (p, _) => pure p
  | .error e => throw s!"C++ parse error: {e}"

/-- The eval target's expression text (`auto const f(...);f->arity_0 = &g;f`): statements, then
the expression after the last `;`. -/
def parseStmtsText (text : String) : Except String (List Stmt × Option Expr) := do
  let parts := text.splitOn ";"
  let last := Jank.Codegen.strTrim (parts.getLast?.getD "")
  let body := ";".intercalate (parts.dropLast) ++ (if parts.length > 1 then ";" else "")
  let toks ← tokenize (body ++ "}")
  let ss ← match parseStmts.run { toks } with
    | .ok (r, _) => pure r
    | .error e => throw s!"C++ parse error: {e}"
  if last.isEmpty then return (ss, none)
  let et ← tokenize last
  match parseExpr.run { toks := et } with
  | .ok (e, _) => pure (ss, some e)
  | .error e => throw s!"C++ parse error: {e}"

/-! ## Scope check: what a C++ compiler rejects in this subset -/

/-- Names the generated code uses that it does not declare: jank's API, macros, keywords. -/
def isKnownGlobal (n : String) : Bool :=
  (n.splitOn "::").length > 1 || n.startsWith "jank::" || n.startsWith "_jank_" || n.startsWith "jtl::" || n.startsWith "std::"
  || n.startsWith "jank_" || n == "INFINITY" || n == "NAN" || n == "true" || n == "false"
  || n == "nullptr" || n == "GC_add_roots" || n == "new"

/-- A `case` label is a converted constant expression of the switch's promoted type (`jank_i64`,
a signed 64-bit type): narrowing is ill-formed ([stmt.switch]/2, [expr.const]/10). A decimal
literal above `LLONG_MAX` has type `unsigned long long` (Clang's extension), and so does its
negation: such a label does not fit. -/
partial def caseLabelFits : Expr → Bool
  | .num s =>
    let v : Nat := s.toList.foldl (fun a d => if d.isDigit then a * 10 + (d.toNat - 48) else a) 0
    v ≤ 9223372036854775807
  | .neg e => caseLabelFits e
  | _ => true

partial def checkExpr (scopes : List (List String)) (fns : List String) : Expr → Except String Unit
  | .id n =>
    if isKnownGlobal n || fns.contains n || scopes.any (·.contains n) then .ok ()
    else .error s!"use of undeclared identifier '{n}'"
  | .num _ | .str _ | .addr _ => .ok ()
  | .neg e => checkExpr scopes fns e
  | .call f args => do checkExpr scopes fns f; for a in args do checkExpr scopes fns a
  | .dot e _ | .arrow e _ => checkExpr scopes fns e
  | .brace _ args | .cast _ _ args => do for a in args do checkExpr scopes fns a
  | .lambda body => do let _ ← checkStmts (([] : List String) :: scopes) fns body; pure ()
where
  checkStmts (scopes : List (List String)) (fns : List String) (ss : List Stmt) :
      Except String (List (List String)) := do
    let mut sc := scopes
    for s in ss do sc ← checkStmt sc fns s
    pure sc
  checkStmt (scopes : List (List String)) (fns : List String) : Stmt → Except String (List (List String))
    | .decl _ name init => do
      for a in init do checkExpr scopes fns a
      match scopes with
      | top :: rest =>
        if top.contains name then throw s!"redefinition of '{name}'"
        pure ((name :: top) :: rest)
      | [] => pure [[name]]
    | .assign l r => do checkExpr scopes fns l; checkExpr scopes fns r; pure scopes
    | .expr e => do checkExpr scopes fns e; pure scopes
    | .block ss => do let _ ← checkStmts ([] :: scopes) fns ss; pure scopes
    | .ifElse c t e => do
      checkExpr scopes fns c
      let _ ← checkStmts ([] :: scopes) fns t
      let _ ← checkStmts ([] :: scopes) fns e
      pure scopes
    | .whileTrue b => do let _ ← checkStmts ([] :: scopes) fns b; pure scopes
    | .brk | .cont => pure scopes
    | .ret none => throw "non-void function should return a value"
    | .ret (some e) => do
      match e with
      | .brace "" [] => pure scopes
      | _ => checkExpr scopes fns e; pure scopes
    | .thr e => do
      if let some x := e then checkExpr scopes fns x
      pure scopes
    | .tryCatch b hs => do
      let _ ← checkStmts ([] :: scopes) fns b
      for (h, body) in hs do
        let sc := match h with | some (_, n) => [n] :: scopes | none => [] :: scopes
        let _ ← checkStmts sc fns body
      pure scopes
    | .switch e cs => do
      checkExpr scopes fns e
      for (lbl, body) in cs do
        if let some l := lbl then
          if !caseLabelFits l then
            throw "case value cannot be narrowed to the switch's type (jank_i64)"
        let _ ← checkStmts ([] :: scopes) fns body
      pure scopes

/-- A function's parameters (duplicates are an error) and body. -/
def checkFn (globals fns : List String) (f : FnDef) : Except String Unit := do
  let named := f.params.filter (· != "")
  if named.length != named.eraseDups.length then
    throw s!"redefinition of parameter in '{f.name}'"
  let _ ← checkExpr.checkStmts [named, globals] fns f.body
  pure ()

def checkProgram (p : Program) : Except String Unit := do
  let fns := p.fns.map (·.name)
  for f in p.fns do checkFn p.globals fns f
  let _ ← checkExpr.checkStmts [p.globals] fns p.load
  pure ()

end Jank.Codegen.CppAst

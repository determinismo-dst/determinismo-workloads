import Jank.Codegen.Value
import Jank.Codegen.Float

/-!
# clojure.core functions the programs call, and code strings read back

`prim` is one implementation for both sides (the Clojure evaluator and the interpreter of
jank's emitted C++), with Clojure's meaning, so that a difference between the sides is the code
generator's. `user/log` appends its argument to the output: it makes evaluation order visible.

`readCode` reads the text `to_code_string` produced for metadata (what `with_lazy_meta` and
`_jank_symbol(meta, …)` store); `evalForm` evaluates such a form the way `_jank_eval_str` does in
the dynamic runtime (codegen/api_dynamic.cpp: `eval(read_string(edn))`), for the forms the search
draws: literals, `quote`, collections, symbols (vars, else "Unable to resolve"), calls.
-/

namespace Jank.Codegen

def numArgs (args : List JV) : Option (List Int) :=
  args.mapM fun a => match a with | .int i => some i | _ => none

/-- The primitives, by var name. Integer arithmetic is exact (Clojure's longs are not exercised
past i64 by the drawn programs). -/
def prim (name : String) (args : List JV) (out : List String) : Except String (JV × List String) :=
  match name, args with
  | "clojure.core/+", _ => match numArgs args with
    | some xs => .ok (.int (xs.foldl (· + ·) 0), out)
    | none => .error "+ of a non-number"
  | "clojure.core/-", [a] => match a with | .int x => .ok (.int (-x), out) | _ => .error "-"
  | "clojure.core/-", _ => match numArgs args with
    | some (x :: xs) => .ok (.int (xs.foldl (· - ·) x), out)
    | _ => .error "- of a non-number"
  | "clojure.core/inc", [.int x] => .ok (.int (x + 1), out)
  | "clojure.core/dec", [.int x] => .ok (.int (x - 1), out)
  | "clojure.core/<", [.int a, .int b] => .ok (.bool (a < b), out)
  | "clojure.core/=", [a, b] => .ok (.bool (a.equiv b), out)
  | "clojure.core/zero?", [.int a] => .ok (.bool (a == 0), out)
  | "clojure.core/pos?", [.int a] => .ok (.bool (a > 0), out)
  | "clojure.core/vector", xs => .ok (.vec xs none, out)
  | "clojure.core/list?", [x] => .ok (.bool (match x with | .list .. => true | _ => false), out)
  | "clojure.core/vector?", [x] => .ok (.bool (match x with | .vec .. => true | _ => false), out)
  | "clojure.core/first", [x] => match x with
    | .vec (y :: _) _ | .list (y :: _) _ => .ok (y, out)
    | .vec [] _ | .list [] _ | .nil => .ok (.nil, out)
    | _ => .error "first"
  | "clojure.core/count", [x] => match x with
    | .vec ys _ | .list ys _ | .set ys => .ok (.int ys.length, out)
    | .map kvs => .ok (.int kvs.length, out)
    | .str s => .ok (.int s.length, out)
    | .nil => .ok (.int 0, out)
    | _ => .error "count"
  | "clojure.core/identity", [x] => .ok (x, out)
  | "user/log", [x] => .ok (x, out ++ [x.show])
  | n, _ => .error s!"no primitive {n} for {args.length} args"

/-! ## Reading code strings -/

inductive RTok where
  | o (c : Char) | c (ch : Char) | atom (s : String) | str (s : String)
  deriving BEq, Inhabited

def rtokenize (s : String) : List RTok := Id.run do
  let cs := s.toList.toArray
  let mut i := 0
  let mut out : List RTok := []
  let mut fuel := cs.size * 2 + 4
  while i < cs.size && fuel > 0 do
    fuel := fuel - 1
    let ch := cs[i]!
    if ch == ' ' || ch == ',' || ch == '\n' then i := i + 1
    else if ch == '(' || ch == '[' || ch == '{' then out := out ++ [.o ch]; i := i + 1
    else if ch == ')' || ch == ']' || ch == '}' then out := out ++ [.c ch]; i := i + 1
    else if ch == '"' then
      let mut j := i + 1
      let mut b : List Char := []
      while j < cs.size && cs[j]! != '"' do
        if cs[j]! == '\\' && j + 1 < cs.size then
          let e := cs[j+1]!
          b := b ++ [if e == 'n' then '\n' else if e == 't' then '\t' else e]
          j := j + 2
        else b := b ++ [cs[j]!]; j := j + 1
      out := out ++ [.str (String.ofList b)]
      i := j + 1
    else
      let mut j := i
      while j < cs.size && !(" ,\n()[]{}\"".toList.contains cs[j]!) do j := j + 1
      out := out ++ [.atom (String.ofList (cs.extract i j).toList)]
      i := j
  return out

def atomValue (a : String) : JV :=
  if a == "nil" then .nil else if a == "true" then .bool true else if a == "false" then .bool false
  else if a.startsWith "\\" then .char (match strDrop a 1 with
    | "newline" => "\n" | "space" => " " | "tab" => "\t" | "backspace" => "\x08"
    | "formfeed" => "\x0c" | "return" => "\r" | c => c)
  else if a.endsWith "N" && (strDropRight a 1).toInt?.isSome then .big (strDropRight a 1).toInt!
  else if (a.contains '.' || a.contains 'e') && (a.toList.headD 'x').isDigit then
    match Float.parseDecimal a.toList with
    | some b => .real b
    | none => .sym "" a none
  else if a.startsWith "-" && (a.contains '.' || a.contains 'e') then
    match Float.parseDecimal (a.toList.drop 1) with
    | some b => .real (b ^^^ 0x8000000000000000)
    | none => .sym "" a none
  else if (match a.splitOn "/" with
           | [n, d] => n.toInt?.isSome && d.toNat?.isSome
           | _ => false) then
    match a.splitOn "/" with
    | [n, d] => .ratio n.toInt! d.toNat!
    | _ => .nil
  else if a.startsWith ":" then
    let b := strDrop a 1
    match b.splitOn "/" with
    | [ns, n] => .kw ns n
    | _ => .kw "" b
  else match a.toInt? with
    | some i => .int i
    | none => match a.splitOn "/" with
      | [ns, n] => if ns.isEmpty || n.isEmpty then .sym "" a none else .sym ns n none
      | _ => .sym "" a none

partial def readForms (ts : List RTok) (close : Option Char) : Option (List JV × List RTok) :=
  match ts with
  | [] => if close.isNone then some ([], []) else none
  | .c ch :: rest => if close == some ch then some ([], rest) else none
  | t :: rest => do
    let (v, rest') ← readOne t rest
    let (vs, rest'') ← readForms rest' close
    pure (v :: vs, rest'')
where
  readOne (t : RTok) (rest : List RTok) : Option (JV × List RTok) :=
    match t with
    | .atom a => some (atomValue a, rest)
    | .str s => some (.str s, rest)
    | .o '(' => (readForms rest (some ')')).map fun (xs, r) => (.list xs none, r)
    | .o '[' => (readForms rest (some ']')).map fun (xs, r) => (.vec xs none, r)
    | .o '{' => (readForms rest (some '}')).map fun (xs, r) =>
        let rec pairs : List JV → List (JV × JV)
          | k :: v :: r => (k, v) :: pairs r
          | _ => []
        (.map (pairs xs), r)
    | _ => none

/-- The reader on a code string: its first form. -/
def readCode (s : String) : Option JV :=
  match readForms (rtokenize s) none with
  | some (v :: _, _) => some v
  | _ => none

/-- Evaluating a read form against vars (`lookup` gives a var's root): literals, `quote`,
collections element-wise, symbols as vars, calls of primitives. Locals do not exist here. -/
partial def evalForm (lookup : String → Option JV) (out : List String) : JV → Except String (JV × List String)
  | .sym ns n _ =>
    let q := if ns.isEmpty then "user/" ++ n else ns ++ "/" ++ n
    match lookup q with
    | some v => .ok (v, out)
    | none => match lookup ("clojure.core/" ++ n) with
      | some v => .ok (v, out)
      | none => .error s!"Unable to resolve symbol: {n}"
  | .list [.sym "" "quote" _, x] _ => .ok (x, out)
  | .list (f :: args) _ => do
    let (fv, out) ← evalForm lookup out f
    let mut out := out
    let mut vs : List JV := []
    for a in args do
      let (v, o) ← evalForm lookup out a
      vs := vs ++ [v]; out := o
    match fv with
    | .prim n => prim n vs out
    | _ => .error "not callable in metadata"
  | .vec xs m => do
    let mut out := out
    let mut vs : List JV := []
    for a in xs do
      let (v, o) ← evalForm lookup out a
      vs := vs ++ [v]; out := o
    pure (.vec vs m, out)
  | .map kvs => do
    let mut out := out
    let mut r : List (JV × JV) := []
    for (k, v) in kvs do
      let (kv, o) ← evalForm lookup out k
      let (vv, o) ← evalForm lookup o v
      r := r ++ [(kv, vv)]; out := o
    pure (.map r, out)
  | x => .ok (x, out)

end Jank.Codegen

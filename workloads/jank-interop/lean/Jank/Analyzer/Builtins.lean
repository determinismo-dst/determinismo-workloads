import Jank.Analyzer.Runtime

/-!
# Runtime functions shared by both sides

The core functions the generated programs call (`=`, `inc`, `+`, `<`, `meta`, `vector`, `str`,
`count`, `first`, `rest`, `nil?`, `pos?`), with Clojure's documented meaning. Both the evaluation
of jank's analyzed tree and the Clojure spec use these same functions, so a disagreement between
the two sides comes from analysis (forms → expressions, types, conversions), not from the
runtime library (which other agents model).

Numbers: a Clojure long is `Obj.integer` (64-bit), jank's small integers are normalized to it
(`Obj.norm`); doubles are `Obj.smallReal` bits.
-/

namespace Jank.Analyzer

def Obj.long (i : Int) : Obj := .integer (BitVec.ofInt 64 i)
def Obj.dbl (f : Float) : Obj := .smallReal f.toBits
def Obj.isLongRange (i : Int) : Bool := -9223372036854775808 ≤ i && i ≤ 9223372036854775807

/-- Integer value of an integral object. -/
def Obj.intVal? : Obj → Option Int
  | .integer v => some v.toInt
  | .smallInteger v => some v.toInt
  | .bigInteger v => some v
  | _ => none

def Obj.dblVal? : Obj → Option Float
  | .smallReal b | .real b => some (Float.ofBits b)
  | _ => none

/-- Normal form for comparing results: small integers as longs, reals as small reals,
metadata dropped. -/
partial def Obj.norm : Obj → Obj
  | .smallInteger v => .integer (v.signExtend 64)
  | .opaque .jitClosure _ | .opaque .jitFunction _ | .opaque .nativeFunctionWrapper _ => .opaque .jitFunction 0
  | .real b => .smallReal b
  | .symbol _ ns n => .symbol none ns n
  | .persistentList _ xs => .persistentList none (xs.map Obj.norm)
  | .cons _ f r => .persistentList none ((Obj.cons none f r).elems.getD [] |>.map Obj.norm)
  | .lazySequence _ xs | .seqOf _ xs => .persistentList none (xs.map Obj.norm)
  | .persistentVector _ xs => .persistentVector none (xs.map Obj.norm)
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
    .persistentArrayMap none (kvs.map fun (k, v) => (k.norm, v.norm))
  | .persistentHashSet _ xs | .persistentSortedSet _ xs => .persistentHashSet none (xs.map Obj.norm)
  | x => x

/-- A double printed as Clojure prints it (the cases the programs produce). -/
def fmtDouble (f : Float) : String :=
  if f.isNaN then "##NaN"
  else if f.isInf then (if f > 0 then "##Inf" else "##-Inf")
  else if f == f.floor && f.abs < 1e15 then s!"{f.toInt64.toInt}.0"
  else
    -- Fixed notation, trailing zeros trimmed (enough for the programs' values).
    let s := toString f
    if s.contains 'e' then s else
      let s := (s.toList.reverse.dropWhile (· == '0')).reverse
      String.mk s

/-- `pr-str`. -/
partial def Obj.pr : Obj → String
  | .nil => "nil"
  | .boolean b => if b then "true" else "false"
  | .integer v => s!"{v.toInt}"
  | .smallInteger v => s!"{v.toInt}"
  | .bigInteger v => s!"{v}N"
  | .bigDecimal u s => s!"{u}E-{s}M"
  | .real b | .smallReal b => fmtDouble (Float.ofBits b)
  | .ratio n d => s!"{n}/{d}"
  | .persistentString s => s!"\"{s}\""
  | .keyword ns n => if ns.isEmpty then s!":{n}" else s!":{ns}/{n}"
  | .symbol _ ns n => if ns.isEmpty then n else s!"{ns}/{n}"
  | .character c => s!"\\{c}"
  | .persistentVector _ xs => "[" ++ " ".intercalate (xs.map Obj.pr) ++ "]"
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
    "{" ++ ", ".intercalate (kvs.map fun (k, v) => k.pr ++ " " ++ v.pr) ++ "}"
  | .persistentHashSet _ xs | .persistentSortedSet _ xs => "#{" ++ " ".intercalate (xs.map Obj.pr) ++ "}"
  | .var ns n => s!"#'{ns}/{n}"
  | .opaque t i => s!"#object[{reprStr t} {i}]"
  | o => "(" ++ " ".intercalate ((o.elems.getD []).map Obj.pr) ++ ")"

/-- Clojure's `=` on the values the programs build (`Util.equiv`: numbers by category, sequential
collections elementwise, maps and sets by content). -/
partial def cljEquals (a b : Obj) : Bool :=
  match a.norm, b.norm with
  | .integer x, .integer y => x == y
  | .smallReal x, .smallReal y => Float.ofBits x == Float.ofBits y
  | .persistentArrayMap _ k1, .persistentArrayMap _ k2 =>
    k1.length == k2.length && k1.all fun (k, v) => k2.any fun (k', v') => cljEquals k k' && cljEquals v v'
  | .persistentHashSet _ x, .persistentHashSet _ y =>
    x.length == y.length && x.all fun e => y.any (cljEquals e ·)
  | x, y =>
    if x.sequential && y.sequential then
      let xs := x.elems.getD []
      let ys := y.elems.getD []
      xs.length == ys.length && (xs.zip ys).all fun (p, q) => cljEquals p q
    else x == y

/-- A runtime function's failure: a thrown exception's message. -/
abbrev Thrown := String

/-- The core functions, by name, on argument objects. -/
def builtin (name : String) (args : List Obj) : Option (Except Thrown Obj) :=
  match name, args with
  | "=", [_] => some (.ok (.boolean true))
  | "=", [a, b] => some (.ok (.boolean (cljEquals a b)))
  | "nil?", [a] => some (.ok (.boolean (a == .nil)))
  | "meta", [a] => some (.ok (a.getMeta.getD .nil))
  | "vector", xs => some (.ok (.persistentVector none xs))
  | "list", xs => some (.ok (.persistentList none xs))
  | "count", [a] => some (match a.elems with
      | some xs => .ok (Obj.long xs.length)
      | none => .error s!"count not supported on this type: {reprStr a.type}")
  | "first", [a] => some (.ok a.first)
  | "rest", [a] => some (.ok a.rest)
  | "str", xs => some (.ok (.persistentString (String.join (xs.map fun
      | .nil => "" | .persistentString s => s | o => o.pr))))
  | "inc", [a] => some (match a.intVal?, a.dblVal? with
      | some i, _ => if Obj.isLongRange (i + 1) then .ok (Obj.long (i + 1)) else .error "integer overflow"
      | _, some f => .ok (Obj.dbl (f + 1.0))
      | _, _ => .error "inc of a non-number")
  | "+", [a, b] => some (match a.intVal?, b.intVal?, a.dblVal?, b.dblVal? with
      | some x, some y, _, _ => if Obj.isLongRange (x + y) then .ok (Obj.long (x + y)) else .error "integer overflow"
      | some x, _, _, some g => .ok (Obj.dbl (Float.ofInt x + g))
      | _, some y, some f, _ => .ok (Obj.dbl (f + Float.ofInt y))
      | _, _, some f, some g => .ok (Obj.dbl (f + g))
      | _, _, _, _ => .error "+ of a non-number")
  | "*", [a, b] => some (match a.intVal?, b.intVal?, a.dblVal?, b.dblVal? with
      | some x, some y, _, _ => if Obj.isLongRange (x * y) then .ok (Obj.long (x * y)) else .error "integer overflow"
      | some x, _, _, some g => .ok (Obj.dbl (Float.ofInt x * g))
      | _, some y, some f, _ => .ok (Obj.dbl (f * Float.ofInt y))
      | _, _, some f, some g => .ok (Obj.dbl (f * g))
      | _, _, _, _ => .error "* of a non-number")
  | "<", [a, b] => some (match a.intVal?, b.intVal?, a.dblVal?, b.dblVal? with
      | some x, some y, _, _ => .ok (.boolean (x < y))
      | some x, _, _, some g => .ok (.boolean (Float.ofInt x < g))
      | _, some y, some f, _ => .ok (.boolean (f < Float.ofInt y))
      | _, _, some f, some g => .ok (.boolean (f < g))
      | _, _, _, _ => .error "< of a non-number")
  | "pos?", [a] => some (match a.intVal?, a.dblVal? with
      | some i, _ => .ok (.boolean (i > 0))
      | _, some f => .ok (.boolean (f > 0.0))
      | _, _ => .error "pos? of a non-number")
  | _, _ => none

/-- `get` (the keyword-call rewrite target). -/
def builtinGet (m k : Obj) (dflt : Obj := .nil) : Obj :=
  match m with
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
    match kvs.find? (fun (k', _) => cljEquals k' k) with
    | some (_, v) => v
    | none => dflt
  | _ => dflt

end Jank.Analyzer

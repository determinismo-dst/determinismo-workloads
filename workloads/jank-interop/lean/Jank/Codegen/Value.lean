import Jank.Analyzer.Expr
import Jank.Hash

/-!
# Runtime values shared by the two sides

`JV` is what a jank object (`object_ref`) or a Clojure value is, for the programs the search
draws: both the Clojure evaluator (the spec) and the interpreter of the emitted C++ produce `JV`s,
and the same primitive functions act on them, so a difference comes from the code generator.
-/

namespace Jank.Codegen

open Jank.Analyzer

/-- `s` without its first `n` characters (a `String`, not a slice). -/
def strDrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
def strDropRight (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))
def strTrim (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

inductive JV where
  | nil
  | bool (b : Bool)
  | int (v : Int)
  | real (bits : UInt64)
  | big (v : Int)
  | ratio (n d : Int)
  | str (s : String)
  | kw (ns n : String)
  | sym (ns n : String) (mta : Option JV)
  | char (s : String)
  | vec (xs : List JV) (mta : Option JV)
  | list (xs : List JV) (mta : Option JV)
  | set (xs : List JV)
  | map (kvs : List (JV × JV))
  /-- A function object: its index in the machine's function table. -/
  | fn (id : Nat)
  | var (q : String)
  /-- A clojure.core function, by name. -/
  | prim (name : String)
  | other (desc : String)
  deriving Repr, BEq, Inhabited

/-- Clojure's `=` on the values the search draws (sequential collections compare by elements,
numbers of one category by value; metadata ignored). -/
partial def JV.equiv : JV → JV → Bool
  | .nil, .nil => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .int a, .big b | .big a, .int b | .big a, .big b => a == b
  | .real a, .real b => a == b || ((a &&& 0x7FFFFFFFFFFFFFFF) == 0 && (b &&& 0x7FFFFFFFFFFFFFFF) == 0)
  | .ratio a b, .ratio c d => a == c && b == d
  | .str a, .str b => a == b
  | .kw a b, .kw c d => a == c && b == d
  | .sym a b _, .sym c d _ => a == c && b == d
  | .char a, .char b => a == b
  | .vec xs _, .vec ys _ | .vec xs _, .list ys _ | .list xs _, .vec ys _ | .list xs _, .list ys _ =>
    xs.length == ys.length && (xs.zip ys).all fun (x, y) => x.equiv y
  | .set xs, .set ys => xs.length == ys.length && xs.all fun x => ys.any (x.equiv ·)
  | .map a, .map b => a.length == b.length && a.all fun (k, v) => b.any fun (k2, v2) => k.equiv k2 && v.equiv v2
  -- function objects of the two sides are not comparable by identity: any two are alike
  | .fn _, .fn _ => true
  | .var a, .var b => a == b
  | .prim a, .prim b => a == b
  | _, _ => false

/-- The same value, type included (a list is not a vector; metadata compared). Used where the
spec is "denotes the same value" (constants). -/
partial def JV.same : JV → JV → Bool
  | .vec xs m, .vec ys n | .list xs m, .list ys n =>
    xs.length == ys.length && (xs.zip ys).all (fun (x, y) => x.same y) && optSame m n
  | .set xs, .set ys => xs.length == ys.length && xs.all fun x => ys.any (x.same ·)
  | .map a, .map b => a.length == b.length && a.all fun (k, v) => b.any fun (k2, v2) => k.same k2 && v.same v2
  | .sym a b m, .sym c d n => a == c && b == d && optSame m n
  | .real a, .real b => a == b || (((a >>> 52) &&& 0x7FF) == 0x7FF && (a &&& 0xFFFFFFFFFFFFF) != 0
                                 && ((b >>> 52) &&& 0x7FF) == 0x7FF && (b &&& 0xFFFFFFFFFFFFF) != 0)
  | a, b => a.equiv b && sameKind a b
where
  optSame : Option JV → Option JV → Bool
    | none, none => true
    | some a, some b => a.same b
    | none, some (.map []) | some (.map []), none => true
    | _, _ => false
  sameKind : JV → JV → Bool
    | .int _, .int _ | .big _, .big _ => true
    | .int _, _ | _, .int _ | .big _, _ | _, .big _ => false
    | _, _ => true

partial def JV.show : JV → String
  | .nil => "nil"
  | .bool b => toString b
  | .int v => toString v
  | .real b => s!"#double[{b}]"
  | .big v => s!"{v}N"
  | .ratio n d => s!"{n}/{d}"
  | .str s => s!"{repr s}"
  | .kw ns n => ":" ++ (if ns.isEmpty then n else ns ++ "/" ++ n)
  | .sym ns n m => (match m with | some mm => "^" ++ mm.show ++ " " | none => "") ++ (if ns.isEmpty then n else ns ++ "/" ++ n)
  | .char s => "\\" ++ s
  | .vec xs m => (match m with | some mm => "^" ++ mm.show ++ " " | none => "") ++ "[" ++ " ".intercalate (xs.map JV.show) ++ "]"
  | .list xs m => (match m with | some mm => "^" ++ mm.show ++ " " | none => "") ++ "(" ++ " ".intercalate (xs.map JV.show) ++ ")"
  | .set xs => "#{" ++ " ".intercalate (xs.map JV.show) ++ "}"
  | .map kvs => "{" ++ ", ".intercalate (kvs.map fun (k, v) => k.show ++ " " ++ v.show) ++ "}"
  | .fn _ => "#<fn>"
  | .var q => s!"#'{q}"
  | .prim n => s!"#<{n}>"
  | .other d => s!"#<{d}>"

def JV.truthy : JV → Bool
  | .nil | .bool false => false
  | _ => true

/-- An analyzer object (a constant) as a runtime value. -/
partial def JV.ofObj : Obj → JV
  | .nil => .nil
  | .boolean b => .bool b
  | .integer v => .int v.toInt
  | .smallInteger v => .int v.toInt
  | .bigInteger v => .big v
  | .bigDecimal u s => .other s!"{u}e-{s}M"
  | .real b | .smallReal b => .real b
  | .ratio n d => .ratio n d
  | .persistentString s => .str s
  | .keyword ns n => .kw ns n
  | .symbol m ns n => .sym ns n (m.map JV.ofObj)
  | .character d => .char d
  | .persistentList m xs => .list (xs.map JV.ofObj) (m.map JV.ofObj)
  | .persistentVector m xs => .vec (xs.map JV.ofObj) (m.map JV.ofObj)
  | .persistentArrayMap _ kvs | .persistentHashMap _ kvs | .persistentSortedMap _ kvs =>
      .map (kvs.map fun (k, v) => (JV.ofObj k, JV.ofObj v))
  | .persistentHashSet _ xs | .persistentSortedSet _ xs => .set (xs.map JV.ofObj)
  | .cons m f r => match JV.ofObj r with
      | .list xs _ => .list (JV.ofObj f :: xs) (m.map JV.ofObj)
      | _ => .list [JV.ofObj f] (m.map JV.ofObj)
  | .lazySequence m xs => .list (xs.map JV.ofObj) (m.map JV.ofObj)
  | .seqOf _ xs => .list (xs.map JV.ofObj) none
  | .var ns n => .var s!"{ns}/{n}"
  | .opaque t i => .other s!"{repr t} {i}"

/-- `hash::integer(i64)` (hash.cpp), from the first round's replica. -/
def hashInteger (v : Int) : UInt32 := Jank.Hash.integer (UInt64.ofInt v)

/-- `to_case_integer_or_hash` (c_api.cpp:991-1012): an integer within `i32` is itself, one
outside is `hash::integer` of it (a `u32`, non-negative as `i64`); other objects their hash. -/
def toCaseIntegerOrHash (v : JV) : Int :=
  match v with
  | .int i => if -2147483648 ≤ i ∧ i ≤ 2147483647 then i else (hashInteger i).toNat
  | .big i => if -2147483648 ≤ i ∧ i ≤ 2147483647 then i else 0x5EED  -- `to_hash`: not drawn
  | .kw ns n => (Jank.Hash.keyword .signed ns.toUTF8.toList n.toUTF8.toList).toNat
  | .nil => 0
  | _ => 0x5EED

/-- C++ `i64 >> s` (arithmetic) and `&`. -/
def shiftMask (x shift mask : Int) : Int :=
  let b := (BitVec.ofInt 64 x).sshiftRight shift.toNat
  (b &&& BitVec.ofInt 64 mask).toInt

/-- `jank_shift_mask_case_integer` (c_api.cpp:1027-1037). -/
def shiftMaskCaseInteger (v : JV) (shift mask : Int) : Int :=
  let i := toCaseIntegerOrHash v
  if mask != 0 then shiftMask i shift mask else i

end Jank.Codegen

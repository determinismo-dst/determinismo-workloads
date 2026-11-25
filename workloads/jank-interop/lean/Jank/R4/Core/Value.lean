/-!
# Round 4, clojure.core functions: the values these functions see

A small value model shared by the round-4 core replicas. Each function that recurses takes fuel
(structural recursion on `Nat`), so every replica is total and the kernel can run it.

- `entry k v` is Clojure's `MapEntry`: a vector to `vector?`, `=` to the 2-vector `[k v]`, what
  `(first {k v})` and `find` return. jank has no entry type: its map seqs yield plain
  `persistent_vector`s (base_persistent_map_sequence.cpp builds a vector per pair), so on the jank
  side `entry` never occurs and `[k v]` stands for both.
- `map` is an array map (insertion order, ≤ 8 entries); `set` holds distinct elements in order.
- `arr` is a native array (`long-array`, `int-array`): `persistent`-free, counted by `alength`.
-/

namespace Jank.R4.Core

inductive V where
  | nil
  | bool (b : Bool)
  | int (i : Int)
  | big (i : Int)
  | dbl (text : String)
  | str (s : String)
  | ch (c : Char)
  | kw (ns n : String)
  | sym (ns n : String)
  | vec (xs : List V)
  | entry (k v : V)
  | list (xs : List V)
  | seq (xs : List V)
  | map (kvs : List (V × V))
  | set (xs : List V)
  | arr (xs : List V)
  deriving Repr, Inhabited

namespace V

/-- Sequential to Clojure's `=` (vectors, entries, lists, seqs; arrays are not). -/
def sequentialElems : V → Option (List V)
  | .vec xs => some xs
  | .entry k v => some [k, v]
  | .list xs => some xs
  | .seq xs => some xs
  | _ => none

/-- Clojure's `=` (Util.equiv) on this model; `fuel` bounds the depth. Longs and BigInts of the
same value are `=` (same category); doubles compare by text; arrays by identity, modeled as never
`=` unless both empty and the same literal list (the search never compares two arrays). -/
def eqF : Nat → V → V → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | .nil, .nil => true
    | .bool x, .bool y => x == y
    | .int x, .int y => x == y
    | .int x, .big y => x == y
    | .big x, .int y => x == y
    | .big x, .big y => x == y
    | .dbl x, .dbl y => x == y
    | .str x, .str y => x == y
    | .ch x, .ch y => x == y
    | .kw a b, .kw c d => a == c && b == d
    | .sym a b, .sym c d => a == c && b == d
    | .map xs, .map ys =>
      xs.length == ys.length &&
        xs.all fun (k, v) => ys.any fun (k', v') => eqF n k k' && eqF n v v'
    | .set xs, .set ys =>
      xs.length == ys.length && xs.all fun x => ys.any fun y => eqF n x y
    | .arr _, .arr _ => false
    | a, b =>
      match a.sequentialElems, b.sequentialElems with
      | some xs, some ys => xs.length == ys.length && (List.zip xs ys).all fun (x, y) => eqF n x y
      | _, _ => false

def fuel : Nat := 12

def eq (a b : V) : Bool := eqF fuel a b

/-- Clojure's printed form (pr-str), enough for reports. -/
def codeF : Nat → V → String
  | 0, _ => "…"
  | n + 1, v =>
    match v with
    | .nil => "nil"
    | .bool b => toString b
    | .int i => toString i
    | .big i => s!"{i}N"
    | .dbl t => t
    | .str s => "\"" ++ s ++ "\""
    | .ch c => "\\" ++ c.toString
    | .kw ns k => if ns.isEmpty then ":" ++ k else ":" ++ ns ++ "/" ++ k
    | .sym ns k => if ns.isEmpty then k else ns ++ "/" ++ k
    | .vec xs => "[" ++ " ".intercalate (xs.map (codeF n)) ++ "]"
    | .entry k w => "[" ++ codeF n k ++ " " ++ codeF n w ++ "]"
    | .list xs => "(" ++ " ".intercalate (xs.map (codeF n)) ++ ")"
    | .seq xs => "(" ++ " ".intercalate (xs.map (codeF n)) ++ ")"
    | .map kvs => "{" ++ ", ".intercalate (kvs.map fun (k, w) => codeF n k ++ " " ++ codeF n w) ++ "}"
    | .set xs => "#{" ++ " ".intercalate (xs.map (codeF n)) ++ "}"
    | .arr xs => "#array[" ++ " ".intercalate (xs.map (codeF n)) ++ "]"

def code (v : V) : String := codeF fuel v

/-- The Clojure source that builds the value (for tests). -/
def src : V → String
  | .list xs => "'" ++ code (.list xs)
  | .seq xs => "(seq " ++ code (.vec xs) ++ ")"
  | .entry k w => "(first {" ++ code k ++ " " ++ code w ++ "})"
  | .arr xs => "(long-array " ++ code (.vec xs) ++ ")"
  | v => code v

/-- `get` on maps (by `=`), vectors (by index); nil otherwise. -/
def get (m k : V) : V :=
  match m with
  | .map kvs => (kvs.find? fun (k', _) => eq k k').map (·.2) |>.getD .nil
  | .vec xs => match k with
    | .int i => if 0 ≤ i ∧ i < xs.length then xs.getD i.toNat .nil else .nil
    | _ => .nil
  | _ => .nil

def containsKey (m k : V) : Bool :=
  match m with
  | .map kvs => kvs.any fun (k', _) => eq k k'
  | .vec xs => match k with
    | .int i => 0 ≤ i ∧ i < xs.length
    | _ => false
  | .set xs => xs.any (eq k)
  | _ => false

/-- `assoc` on an array map: the stored key stays (array maps keep it, native_array_map.cpp
139–162; Clojure PersistentArrayMap.assoc). -/
def assocMap (kvs : List (V × V)) (k v : V) : List (V × V) :=
  if kvs.any (fun (k', _) => eq k k') then kvs.map fun (k', v') => if eq k k' then (k', v) else (k', v')
  else kvs ++ [(k, v)]

/-- `merge` of two maps given as options (nil is `none`). -/
def mergeMaps : Option (List (V × V)) → Option (List (V × V)) → Option (List (V × V))
  | none, none => none
  | some a, none => some a
  | none, some b => some b
  | some a, some b => some (b.foldl (fun acc (k, v) => assocMap acc k v) a)

end V

end Jank.R4.Core

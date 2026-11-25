import Jank.LexBytes

/-!
# What a reader returns, for both sides

Values as the reader builds them, compared across jank and Clojure. Text is code points
(`List Nat`): jank's strings and names are UTF-8 bytes, decoded for the comparison (a jank string
that is not valid UTF-8 keeps its bytes, `Val.bytes`); Clojure's are UTF-16, decoded with
surrogate pairs combined (a lone surrogate stays a code point in 0xD800-0xDFFF).

jank also attaches `{:jank/source {...}}` metadata to every list, vector, map, set and symbol it
reads (parse.cpp `source_to_meta`); that is left out of `Val` and reported on its own (R-meta).
Metadata from `^` is kept (`withMeta`).
-/

namespace Jank.ReadValue

open Jank.LexBytes

inductive Val where
  | nil
  | bool (b : Bool)
  /-- A long (jank `integer`/`small_integer`, Clojure `Long`). -/
  | long (v : Int)
  /-- A BigInt (jank `big_integer`, Clojure `BigInt`). -/
  | big (v : Int)
  | ratio (n : Int) (d : Nat)
  | dbl (d : Dec)
  | inf (neg : Bool)
  | nan
  | bigdec (d : Dec)
  | str (s : List Nat)
  /-- A jank string whose bytes are not valid UTF-8. -/
  | bytes (bs : List UInt8)
  | char (c : Nat)
  | sym (ns : List Nat) (name : List Nat)
  | kw (ns : List Nat) (name : List Nat)
  | list (xs : List Val)
  | vec (xs : List Val)
  | map (kvs : List (Val × Val))
  | set (xs : List Val)
  | regex (src : List Nat)
  | withMeta (m : Val) (v : Val)
  deriving Repr, BEq, Inhabited

/-- Clojure's `=` on read values (Util.equiv), as the readers' duplicate-key checks use it. -/
partial def Val.equiv : Val → Val → Bool
  | .long a, .long b | .long a, .big b | .big a, .long b | .big a, .big b => a == b
  | .dbl a, .dbl b => a.mant == b.mant && a.exp == b.exp  -- 0.0 = -0.0
  | .withMeta _ a, b => a.equiv b
  | a, .withMeta _ b => a.equiv b
  | .list xs, .list ys | .list xs, .vec ys | .vec xs, .list ys | .vec xs, .vec ys =>
    xs.length == ys.length && (xs.zip ys).all fun (x, y) => x.equiv y
  | .set xs, .set ys => xs.length == ys.length && xs.all fun x => ys.any (x.equiv ·)
  | .map a, .map b => a.length == b.length && a.all fun (k, v) => b.any fun (k', v') => k.equiv k' && v.equiv v'
  | a, b => a == b

def showName (ns name : List Nat) : String :=
  (if ns.isEmpty then "" else showCodes ns ++ "/") ++ showCodes name

partial def Val.show : Val → String
  | .nil => "nil"
  | .bool b => toString b
  | .long v => s!"{v}"
  | .big v => s!"{v}N"
  | .ratio n d => s!"{n}/{d}"
  | .dbl d => s!"{d.show} (double)"
  | .inf n => if n then "##-Inf" else "##Inf"
  | .nan => "##NaN"
  | .bigdec d => s!"{d.show}M"
  | .str s => "\"" ++ showCodes s ++ "\""
  | .bytes bs => "\"" ++ showBytes bs ++ "\" (invalid UTF-8)"
  | .char c => "\\" ++ showCodes [c]
  | .sym ns n => showName ns n
  | .kw ns n => ":" ++ showName ns n
  | .list xs => "(" ++ " ".intercalate (xs.map Val.show) ++ ")"
  | .vec xs => "[" ++ " ".intercalate (xs.map Val.show) ++ "]"
  | .map kvs => "{" ++ ", ".intercalate (kvs.map fun (k, v) => k.show ++ " " ++ v.show) ++ "}"
  | .set xs => "#{" ++ " ".intercalate (xs.map Val.show) ++ "}"
  | .regex s => "#\"" ++ showCodes s ++ "\""
  | .withMeta m v => "^" ++ m.show ++ " " ++ v.show

/-- Reading a whole input: its forms, or how reading stopped. -/
inductive Outcome where
  | ok (forms : List Val)
  | err (msg : String)
  /-- A loop that never ends (jank's lexer or parser). -/
  | hang (where_ : String)
  /-- Unbounded recursion: a stack overflow (SIGSEGV). -/
  | crash (where_ : String)
  deriving Repr, BEq, Inhabited

def Outcome.show : Outcome → String
  | .ok vs => " ".intercalate (vs.map Val.show)
  | .err m => s!"error ({m})"
  | .hang w => s!"HANG in {w}"
  | .crash w => s!"CRASH: {w}"

/-- How jank's outcome compares with Clojure's. -/
inductive Verdict where
  | agree
  /-- jank hangs or crashes. -/
  | notTotal
  /-- Both read, different values. -/
  | wrongValue
  /-- Clojure reads it, jank errors. -/
  | rejectsValid
  /-- Clojure errors, jank reads something. -/
  | acceptsInvalid
  deriving Repr, BEq, Inhabited

def verdict (jank clj : Outcome) : Verdict :=
  match jank, clj with
  | .hang _, _ | .crash _, _ => .notTotal
  | .ok a, .ok b => if a == b then .agree else .wrongValue
  | .err _, .err _ => .agree
  | .err _, _ => .rejectsValid
  | .ok _, _ => .acceptsInvalid

end Jank.ReadValue

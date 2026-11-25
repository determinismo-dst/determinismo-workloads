import Jank.Nrepl.Data

/-!
# bencode, replicated byte by byte (src/jank/jank/nrepl/server/bencode.jank at 7135b7708)

The decoder (lines 3–91) is the same code as at f3d82d654; `parse` moved from line 73 to 78. The
encoder changed: a map's keys go through `update-keys` (symbols and keywords to `named>string`,
line 73, anything else to `(str k)`), then `(into (sorted-map))`, then `reduce-kv` in key order
(lines 107–114).

The decoder walks the input with a `volatile!` position. Its helpers are macros:

    (defmacro nth-byte [data i]
      `(when (< ~i (count ~data))
         (int (cpp/aget (cpp/cast jtl.immutable_string ~data) (int ~i)))))
    (defmacro index-of [data start c]
      `(loop [i# (int ~start)]
         (when-let [b# (nth-byte ~data i#)]
           (if (== ~c b#) i# (recur (inc i#))))))
    (defmacro subs+ [data start end]
      `(when (and ~start ~end (<= ~start ~end (count ~data))) (subs ~data ~start ~end)))
    (defmacro peek-byte [position data] `(nth-byte ~data (deref ~position)))

`cpp/aget` on a `jtl::immutable_string` reads a `char`: signed on x86-64 and Apple arm64, so a
byte ≥ 0x80 reads as a negative int there (`Platform.signedChar`).

`parse` returns nil both for input that is incomplete and for input that can never parse (any
exception is caught by `(catch :default _ nil)`): the caller keeps waiting for more bytes.
`parse-recur` recurses once per nesting level: a C++ call each, on the connection thread's stack
(a stack overflow is not an exception: the process dies; `Platform.maxDepth` is the depth at which
that happens, an assumption).

The spec (`specDecode`, `specEncode`): bencode as the comments of bencode.jank describe it —
`i<base 10 integer>e`, `l<items>e`, `d<pairs>e`, `<length>:<contents>` — with a decoder that tells
a valid message, an incomplete one (a prefix of a valid message) and an invalid one apart.
-/

namespace Jank.NreplServer

/-- What the C++ platform decides for the decoder. -/
structure Platform where
  /-- `char` is signed (x86-64, Apple arm64) or unsigned (Linux AArch64). -/
  signedChar : Bool := true
  /-- Nesting depth at which `parse-recur` overflows the thread's stack (assumption). -/
  maxDepth : Nat := 4096
  deriving Repr, Inhabited

/-- A `char` read as an `int`: sign-extended where `char` is signed. -/
def charToInt (signedChar : Bool) (c : UInt8) : Int :=
  if signedChar && c ≥ 128 then (c.toNat : Int) - 256 else (c.toNat : Int)

/-- bencode.jank `nth-byte` (macro, line 3): the byte at `i` as an int, or nil past the end. -/
def nthByte (p : Platform) (data : Bytes) (i : Int) : Option Int :=
  if i < data.length then
    -- `i` is never negative here: positions start at 0 and only grow.
    some (charToInt p.signedChar (data.getD i.toNat 0))
  else none

/-- bencode.jank `index-of` (macro, line 7): the first index ≥ `start` holding `c`, or nil. -/
def indexOf (p : Platform) (data : Bytes) (start : Int) (c : Int) : Option Int :=
  go start (data.length + 1)
where
  go (i : Int) : Nat → Option Int
    | 0 => none
    | fuel + 1 => match nthByte p data i with
      | none => none
      | some b => if c == b then some i else go (i + 1) fuel

/-- bencode.jank `subs+` (macro, line 14). -/
def subsPlus (data : Bytes) (start end_ : Option Int) : Option Bytes :=
  match start, end_ with
  | some s, some e =>
    if s ≤ e && e ≤ data.length then some ((data.drop s.toNat).take (e - s).toNat) else none
  | _, _ => none

/-- jank's `+` on two longs (core/math.hpp `add`): two values that fit an i32 are added as C++
`int`s (round 1, D1), others as i64; both wrap. -/
def jankAdd (a b : Int) : Int :=
  let fits32 (x : Int) := -2147483648 ≤ x && x ≤ 2147483647
  if fits32 a && fits32 b then
    let s := a + b
    if s > 2147483647 then s - 4294967296 else if s < -2147483648 then s + 4294967296 else s
  else
    let s := a + b
    if s > i64max then s - 18446744073709551616 else if s < i64min then s + 18446744073709551616 else s

/-- How `parse-recur` can leave without a value. -/
inductive PErr where
  /-- A jank exception (caught by `parse`'s `(catch :default _ nil)`). -/
  | thrown (msg : String)
  /-- The connection thread's stack overflowed: the process dies. -/
  | stackOverflow
  /-- A loop ran past its fuel (never expected: each item consumes a byte). -/
  | hang
  deriving Repr, BEq, Inhabited

/-- The decoder's state: the `volatile!` position. -/
abbrev PM := StateT Int (Except PErr)

mutual
/-- bencode.jank `parse-recur` (line 21). `depth` is the stack left. -/
def parseRecur (p : Platform) (data : Bytes) : Nat → PM (Option JVal)
  | 0 => throw .stackOverflow
  | depth + 1 => do
    let pos ← get
    match nthByte p data pos with
    | some 105 =>
      -- \i: `(let [start (vswap! position inc) n (index-of data start 101)] ...)`
      let start := pos + 1
      set start
      let n := indexOf p data start 101
      match subsPlus data (some start) n with
      | none => pure none
      | some s =>
        let out := parseLong s
        set ((n.getD 0) + 1)
        pure (out.map JVal.int)
    | some 108 =>
      -- \l: `(vswap! position inc)` then the items until \e
      set (pos + 1)
      parseList p data depth [] (data.length + 1)
    | some 100 =>
      set (pos + 1)
      parseDict p data depth [] (data.length + 1)
    | some b =>
      if 48 ≤ b && b ≤ 57 then
        -- netstring `<length>:<contents>`
        let start := pos
        let end_ := indexOf p data start 58
        match subsPlus data (some start) end_ with
        | none => pure none
        | some n =>
          let len := parseLong n
          let start' := (end_.getD 0) + 1
          match len with
          | none => throw (.thrown "(+ start bytes): bytes is nil")
          | some l =>
            let stop := jankAdd start' l
            match subsPlus data (some start') (some stop) with
            | none => pure none
            | some out =>
              set stop
              pure (some (.str out))
      else pure none
    | none => pure none

/-- The list loop of `parse-recur` (line 35): `(loop [out (transient [])] ...)`. -/
def parseList (p : Platform) (data : Bytes) (depth : Nat) (out : List JVal) : Nat → PM (Option JVal)
  | 0 => throw .hang
  | fuel + 1 => do
    match nthByte p data (← get) with
    | none => pure none
    | some 101 =>
      modify (· + 1)
      pure (some (.vec out))
    | some _ =>
      match ← parseRecur p data depth with
      | some v => parseList p data depth (out ++ [v]) fuel
      | none => pure none

/-- The dict loop of `parse-recur` (line 47): both the key and the value are parsed before the
`(when (and k v) ...)` test. -/
def parseDict (p : Platform) (data : Bytes) (depth : Nat) (out : List (JVal × JVal)) :
    Nat → PM (Option JVal)
  | 0 => throw .hang
  | fuel + 1 => do
    match nthByte p data (← get) with
    | none => pure none
    | some 101 =>
      modify (· + 1)
      pure (some (.map out))
    | some _ =>
      let k ← parseRecur p data depth
      let v ← parseRecur p data depth
      match k, v with
      | some k, some v => parseDict p data depth (assocMap out k v) fuel
      | _, _ => pure none
end

/-- What `parse` gives. -/
inductive Parsed where
  /-- `[value remainder]`: the value and the unconsumed input (nil when none is left). -/
  | value (v : JVal) (rest : Option Bytes)
  /-- nil: incomplete, or never parsable (the caller cannot tell). -/
  | none
  /-- The thread's stack overflowed: the process dies. -/
  | crash
  deriving Repr, BEq, Inhabited

/-- bencode.jank `parse` (line 78): `(try (when s (let [position (volatile! 0) value (parse-recur
position s)] (when value [value (not-empty (subs s @position))]))) (catch :default _ nil))`. -/
def parse (p : Platform) (s : Option Bytes) : Parsed :=
  match s with
  | none => .none
  | some data =>
    match (parseRecur p data p.maxDepth).run 0 with
    | .ok (some v, pos) => .value v (notEmpty (data.drop pos.toNat))
    | .ok (none, _) => .none
    | .error (.thrown _) => .none
    | .error .hang => .none
    | .error .stackOverflow => .crash

/-- bencode.jank `named>string` (line 73): `ns/name` or `name`. -/
def namedString (ns : Option Bytes) (n : Bytes) : Bytes :=
  match ns with
  | some ns => ns ++ bytes "/" ++ n
  | none => n

/-- A map key as `update-keys` gives it in `write` (line 109): a symbol or keyword's
`named>string`, else `(str k)` (a string itself; a long its digits; nil ""). -/
def keyString : JVal → Bytes
  | .sym ns n => namedString ns n
  | .kw ns n => namedString ns n
  | .str b => b
  | .int i => intBytes i
  | .nil => []
  | v => bytes (JVal.render v)

/-- Unsigned byte order (`persistent_string::compare` → `immutable_string::compare`). -/
def bytesLt : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else bytesLt as bs

/-- Insert into a key-sorted list; an equal key replaces (assoc). -/
def insertSorted {α : Type} (k : Bytes) (v : α) : List (Bytes × α) → List (Bytes × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k == k' then (k, v) :: rest
    else if bytesLt k k' then (k, v) :: (k', v') :: rest
    else (k', v') :: insertSorted k v rest

/-- `(->> (update-keys x f) (into (sorted-map)))`: keys converted (a later entry with the same
converted key wins, `assoc!`), then sorted. -/
def sortedEntries {α : Type} (kvs : List (Bytes × α)) : List (Bytes × α) :=
  kvs.foldl (fun acc (k, v) => insertSorted k v acc) []

/-- `reduce-kv (fn [s k v] (str s (write k) (write v)))` over the sorted entries: the first
entry whose value cannot be written ends it (writing is pure, so each value's encoding can be
computed before the sort). -/
def joinSorted : List (Bytes × Except String Bytes) → Except String Bytes
  | [] => .ok []
  | (k, r) :: rest => do
    let b ← r
    let c ← joinSorted rest
    pure (natBytes k.length ++ bytes ":" ++ k ++ b ++ c)

/-- bencode.jank `write` (line 93). The `cond`: `number?` → `(str "i" x "e")`; `string?` →
`(str (count x) ":" x)` (count in bytes); symbol or keyword → `(write (named>string x))`;
`map?` → `d`, the converted, sorted entries, `e`; `coll?` → `l`, `(apply str (map write x))`,
`e`; nil → throws "cannot write nil as bencode"; anything else (a boolean, a character) → throws
"Unexpected data type for bencode". -/
def writeName (ns : Option Bytes) (n : Bytes) : Bytes :=
  let s := namedString ns n
  natBytes s.length ++ bytes ":" ++ s

mutual
def write : JVal → Except String Bytes
  | .int i => .ok (bytes "i" ++ intBytes i ++ bytes "e")
  | .real t => .ok (bytes "i" ++ bytes t ++ bytes "e")
  | .str b => .ok (natBytes b.length ++ bytes ":" ++ b)
  | .sym ns n => .ok (writeName ns n)
  | .kw ns n => .ok (writeName ns n)
  | .map kvs => do
    let body ← joinSorted (sortedEntries (writeValues kvs))
    pure (bytes "d" ++ body ++ bytes "e")
  | .vec xs => do pure (bytes "l" ++ (← writeItems xs) ++ bytes "e")
  | .list xs => do pure (bytes "l" ++ (← writeItems xs) ++ bytes "e")
  | .set xs => do pure (bytes "l" ++ (← writeItems xs) ++ bytes "e")
  | .nil => .error "cannot write nil as bencode"
  | .bool _ => .error "Unexpected data type for bencode"
  | .char _ => .error "Unexpected data type for bencode"
def writeItems : List JVal → Except String Bytes
  | [] => .ok []
  | x :: xs => do
    let a ← write x
    let b ← writeItems xs
    pure (a ++ b)
/-- Each entry's converted key and its value's encoding (`update-keys`, then `write v`). -/
def writeValues : List (JVal × JVal) → List (Bytes × Except String Bytes)
  | [] => []
  | (k, v) :: rest => (keyString k, write v) :: writeValues rest
end

/-! ## The spec: bencode -/

/-- How a spec decode of a buffer ends. -/
inductive Dec where
  | msg (v : JVal) (rest : Bytes)
  /-- The bytes are a proper prefix of a valid message. -/
  | incomplete
  /-- No continuation makes them a valid message. -/
  | invalid
  deriving Repr, BEq, Inhabited

def isDigit (c : UInt8) : Bool := c ≥ 48 && c ≤ 57

/-- Decimal digits to a number. -/
def digitsVal (ds : Bytes) : Nat := ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- The spec decoder: `.ok (v, rest)`, `.error true` (ran out of input: incomplete), `.error false`
(invalid). Integers: `i`, an optional `-`, one or more digits, `e`. Strings: digits, `:`, that many
bytes. Lists and dicts of values (dict keys are strings). -/
def specValue : Nat → Bytes → Except Bool (JVal × Bytes)
  | 0, _ => .error false
  | fuel + 1, b =>
    match b with
    | [] => .error true
    | 105 :: rest =>
      let (neg, r) := match rest with | 45 :: r => (true, r) | r => (false, r)
      let ds := r.takeWhile isDigit
      let after := r.drop ds.length
      match after with
      | [] => .error true
      | 101 :: tail =>
        if ds.isEmpty then .error false
        else
          let v : Int := if neg then -(digitsVal ds : Int) else (digitsVal ds : Int)
          .ok (.int v, tail)
      | _ => .error false
    | 108 :: rest => specList fuel rest []
    | 100 :: rest => specDict fuel rest []
    | c :: _ =>
      if isDigit c then
        let ds := b.takeWhile isDigit
        let after := b.drop ds.length
        match after with
        | [] => .error true
        | 58 :: tail =>
          let n := digitsVal ds
          if tail.length < n then .error true else .ok (.str (tail.take n), tail.drop n)
        | _ => .error false
      else .error false
where
  specList : Nat → Bytes → List JVal → Except Bool (JVal × Bytes)
    | 0, _, _ => .error false
    | _, [], _ => .error true
    | _, 101 :: tail, acc => .ok (.vec acc, tail)
    | f + 1, b, acc =>
      match specValue f b with
      | .ok (v, r) => specList f r (acc ++ [v])
      | .error e => .error e
  specDict : Nat → Bytes → List (JVal × JVal) → Except Bool (JVal × Bytes)
    | 0, _, _ => .error false
    | _, [], _ => .error true
    | _, 101 :: tail, acc => .ok (.map acc, tail)
    | f + 1, b, acc =>
      match specValue f b with
      | .ok (.str k, r) =>
        match specValue f r with
        | .ok (v, r') => specDict f r' (assocMap acc (.str k) v)
        | .error e => .error e
      | .ok _ => .error false
      | .error e => .error e

/-- The spec decoder on a buffer. -/
def specDecode (b : Bytes) : Dec :=
  match specValue (2 * b.length + 2) b with
  | .ok (v, rest) => .msg v rest
  | .error true => .incomplete
  | .error false => .invalid

/-- The spec encoder: the bencode of a value of the universe (longs, strings, lists, string-keyed
maps; keywords and symbols as their names); none for what bencode cannot hold. -/
partial def specEncode : JVal → Option Bytes
  | .int i => some (bytes "i" ++ intBytes i ++ bytes "e")
  | .str b => some (natBytes b.length ++ bytes ":" ++ b)
  | .kw ns n | .sym ns n => specEncode (.str ((ns.map (· ++ bytes "/")).getD [] ++ n))
  | .vec xs | .list xs | .set xs => do
    let parts ← xs.mapM specEncode
    pure (bytes "l" ++ parts.flatten ++ bytes "e")
  | .map kvs => do
    let parts ← kvs.mapM fun (k, v) => do
      let kb ← specEncode k
      let vb ← specEncode v
      pure (kb ++ vb)
    pure (bytes "d" ++ parts.flatten ++ bytes "e")
  | _ => none

/-! ## Facts about the replica -/

/-- `write` of a string is its byte count, a colon, its bytes. -/
theorem write_str (b : Bytes) : write (.str b) = .ok (natBytes b.length ++ bytes ":" ++ b) := by
  rw [write]

/-- `write` of nil throws. -/
theorem write_nil : write .nil = .error "cannot write nil as bencode" := by
  rw [write]

/-- `write` of a boolean throws. -/
theorem write_bool (b : Bool) : write (.bool b) = .error "Unexpected data type for bencode" := by
  rw [write]

/-- Sorted entries with a value that cannot be written: whatever the entries before it encode to,
the map cannot be written. -/
theorem join_sorted_error (pre post : List (Bytes × Except String Bytes)) (k : Bytes) (e : String)
    (hpre : ∃ b, joinSorted pre = .ok b) :
    ∃ e', joinSorted (pre ++ (k, .error e) :: post) = .error e' := by
  induction pre with
  | nil => exact ⟨e, by simp [joinSorted, bind, Except.bind]⟩
  | cons x xs ih =>
    obtain ⟨b, hb⟩ := hpre
    obtain ⟨k0, r0⟩ := x
    simp only [joinSorted, bind, Except.bind] at hb ⊢
    cases r0 <;> simp at hb ⊢
    cases h3 : joinSorted xs <;> simp [h3] at hb ⊢
    obtain ⟨e', he⟩ := ih ⟨_, h3⟩
    simp only [List.cons_append, joinSorted, bind, Except.bind, he]
    exact ⟨e', rfl⟩

end Jank.NreplServer

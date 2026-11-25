import Jank.R3.Search.Common
import Jank.R4.Core.Value
import Jank.R4.Core.Diff
import Jank.R4.Core.Exceptions
import Jank.R4.Core.Format
import Jank.R4.Core.Uuid
import Jank.R4.Core.Preds
import Jank.R4.Core.Walk
import Jank.R4.Core.Json
import Jank.R4.Core.Seqfns

/-!
# Round 4, core: the searches

Each world is walked completely with `censusUnder` (every timeline, every disagreement counted
under a class); the classes are the deviations reported, `unexplained` would be a new one.
-/

namespace Jank.R4.Core.Search

open Determinismo Jank.R4.Core

structure W where
  decisions : Decisions := {}

instance : Chaotic W where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

abbrev WM := EStateM Stop W

def runW (body : WM Unit) (source : Source) : Ended :=
  match body.run { decisions := { source, limit := 1000 } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

def pickFrom {α : Type} [Inhabited α] (name : String) (xs : List α) : WM α := do
  let i ← decide (σ := W) name xs.length
  return xs.getD i default

/-! ## clojure.data/diff -/

def k (n : String) : V := .kw "" n
def i (n : Int) : V := .int n

def diffUniverse : List V :=
  [ .nil, i 1, i 2, k "a", .str "s",
    .vec [], .vec [i 1], .vec [i 1, i 2], .vec [i 2, i 2], .list [i 1, i 3], .vec [.vec [i 1]],
    .map [], .map [(k "a", i 1)], .map [(k "a", i 2)], .map [(k "a", i 1), (k "b", i 2)],
    .map [(k "a", .vec [i 1])], .map [(k "a", .map [(k "b", i 1)])],
    .set [], .set [i 1], .set [i 1, i 2], .set [i 2] ]

def diffPair : WM Unit := do
  let a ← pickFrom "diff.a" diffUniverse
  let b ← pickFrom "diff.b" diffUniverse
  let j := Diff.jankDiff a b
  let c := Diff.cljDiff a b
  if !Diff.sameTriple j c then
    let cls := match Diff.partOf a, Diff.partOf b with
      | .map, .map => "G-diff: maps not subdiffed"
      | .sequential, .sequential => "G-diff: sequential not subdiffed"
      | .set, .set => "G-diff: sets not split"
      | _, _ => "unexplained"
    violate (σ := W) cls
      s!"(clojure.data/diff {a.src} {b.src}): Clojure {(Diff.triple c).code}, jank {(Diff.triple j).code}"

/-! ## format -/

def fmtAlphabet : List Char := ['%', 's', 'd', 'a', '{', '}']

def fmtArgs : List (List Format.Arg) :=
  [ [], [.long 1], [.str "x"], [.dbl "1.5" "0x1.8p0" "1.5"], [.long 1, .str "x"] ]

def fmtCase (maxLen : Nat) : WM Unit := do
  let len ← decide (σ := W) "format.length" (maxLen + 1)
  let mut cs : List Char := []
  for _ in [0:len] do
    cs := cs ++ [← pickFrom "format.char" fmtAlphabet]
  let args ← pickFrom "format.args" fmtArgs
  let f := String.ofList cs
  let j := Format.jankFormat f args
  let c := Format.javaFormat f args
  if !j.same c then
    let hasBrace := cs.any fun c => c == '{' || c == '}'
    let hasPct := cs.contains '%'
    let cls := if hasPct && !hasBrace then "G-format: Java conversions are text to jank"
      else if hasBrace && !hasPct then "G-format: braces are fields to jank, text to Java"
      else "G-format: both"
    violate (σ := W) cls
      s!"(format \"{f}\"{String.join (args.map (" " ++ ·.code))}): Clojure {c.show}, jank {j.show}"

/-! ## parse-uuid -/

def uuidTemplates : List String :=
  [ "00000000-0000-0000-0000-000000000000",
    "0123abcd-4567-89ef-ABCD-0123456789ab",
    "00000000000000000000000000000000",
    "{00000000-0000-0000-0000-000000000000}",
    "1-1-1-1-1" ]

def uuidAlphabet : List Char := ['0', 'f', 'F', '-', '{', '}', 'g', '+']

/-- Up to `maxMut` edits (insert, delete, replace) at chosen positions of a template. -/
def uuidCase (maxMut : Nat) : WM Unit := do
  let t ← pickFrom "uuid.template" uuidTemplates
  let n ← decide (σ := W) "uuid.edits" (maxMut + 1)
  let mut cs := t.toList
  for _ in [0:n] do
    let kind ← decide (σ := W) "uuid.kind" 3
    let pos ← decide (σ := W) "uuid.pos" (cs.length + 1)
    if kind == 0 then
      let ch ← pickFrom "uuid.char" uuidAlphabet
      cs := cs.take pos ++ [ch] ++ cs.drop pos
    else if kind == 1 then
      cs := cs.take pos ++ cs.drop (pos + 1)
    else
      let ch ← pickFrom "uuid.char" uuidAlphabet
      cs := cs.take pos ++ [ch] ++ cs.drop (pos + 1)
  let s := String.ofList cs
  let j := Uuid.stduuidFromString s
  let c := Uuid.jdkFromString s
  let doc := Uuid.canonical s
  if j != c then
    let cls := match j, c with
      | some _, none => if doc.isNone then "G-uuid: jank accepts outside the documented grammar (the JDK rejects)" else "unexplained"
      | none, some _ => if doc.isNone then "G-uuid: the JDK accepts outside the documented grammar (jank rejects)" else "unexplained"
      | some _, some _ => if doc.isNone then "G-uuid: both accept outside the grammar, different values" else "unexplained"
      | none, none => "unexplained"
    violate (σ := W) cls s!"(parse-uuid \"{s}\"): JDK {c.isSome}, jank {j.isSome}"
  else if j.isSome && doc.isNone then
    violate (σ := W) "G-uuid: both accept outside the documented grammar, same value" s!"(parse-uuid \"{s}\")"

/-! ## Exceptions -/

def exChains : List Exceptions.Chain :=
  [ [("a", .map [])], [("a", .map [(k "x", i 1)]), ("b", .map [(k "y", i 2)])],
    [("a", .map []), ("b", .map []), ("c", .map [])],
    [("a", .map []), ("b", .map []), ("c", .map []), ("d", .map [])] ]

def exThrown : List V := [ .str "boom", k "k", i 1, .nil, .map [(k "a", i 1)] ]

def exCase : WM Unit := do
  let which ← decide (σ := W) "ex.kind" 2
  if which == 0 then
    let v ← pickFrom "ex.obj" exThrown
    let t := Exceptions.Thrown.obj v
    let jThrows := match Exceptions.jankExMessage t with | .err _ => true | .ok _ => false
    let cNil := match Exceptions.cljExMessage t with | .ok none => true | _ => false
    if jThrows && cNil then
      violate (σ := W) "G-ex: ex-message/ex-data of a non-exception throws"
        s!"(ex-message {v.src}): Clojure nil, jank throws"
  else
    let c ← pickFrom "ex.chain" exChains
    let prop ← decide (σ := W) "ex.property" 3
    let jm := Exceptions.jankThrowableMap c
    let cm := Exceptions.cljThrowableMap c
    if prop == 0 && jm.cause != cm.cause then
      violate (σ := W) "G-ex: Throwable->map :cause is the outer message"
        s!"chain {c.map (·.1)}: Clojure :cause {cm.cause}, jank {jm.cause}"
    if prop == 1 && !V.eq jm.data cm.data then
      violate (σ := W) "G-ex: Throwable->map :data is the outer data"
        s!"chain {c.map (·.1)}: Clojure :data {cm.data.code}, jank {jm.data.code}"
    if prop == 2 && Exceptions.jankPrintedVia c != Exceptions.cljPrintedVia c then
      violate (σ := W) "G-ex: pr-str repeats the first cause"
        s!"chain {c.map (·.1)}: Clojure prints :via {Exceptions.cljPrintedVia c}, jank {Exceptions.jankPrintedVia c}"

/-! ## Type predicates -/

def predCase : WM Unit := do
  let t ← pickFrom "pred.type" Preds.table
  let prop ← decide (σ := W) "pred.property" 3
  if prop == 0 && t.jankCountable != t.cljCounted then
    violate (σ := W) "G-counted: counted? differs by type" s!"(counted? {t.src}): Clojure {t.cljCounted}, jank {t.jankCountable}"
  if prop == 1 then
    let n ← decide (σ := W) "pred.n" 5
    if Preds.jankBoundedCount t n != Preds.cljBoundedCount t n then
      violate (σ := W) "G-counted: bounded-count counts the whole collection"
        s!"(bounded-count {n} {t.src}): Clojure {Preds.cljBoundedCount t n}, jank {Preds.jankBoundedCount t n}"
  if prop == 2 && t.jankShuffle != t.cljShuffle then
    violate (σ := W) "G-shuffle: shuffle rejects seqs without a static empty() (R120's root)"
      s!"(shuffle {t.src}): Clojure {if t.cljShuffle then "a vector" else "throws"}, jank {if t.jankShuffle then "a vector" else "throws"}"

def entryUniverse : List V :=
  [ .vec [i 1, i 2], .entry (i 1) (i 2), .vec [i 1], .vec [], .vec [i 1, i 2, i 3], .list [i 1, i 2],
    .map [(i 1, i 2)], .nil, .str "ab", .seq [i 1, i 2] ]

def entryCase : WM Unit := do
  let v ← pickFrom "entry.v" entryUniverse
  if Preds.jankMapEntry v != Preds.cljMapEntry v then
    violate (σ := W) "G-map-entry: map-entry? holds for every 2-vector"
      s!"(map-entry? {v.src}): Clojure {Preds.cljMapEntry v}, jank {Preds.jankMapEntry v}"

/-! ## clojure.walk -/

def walkForms : List Walk.F :=
  let a := Walk.F.atom "1"
  [ a, .list none [a], .list (some "m") [a], .seq (some "m") [a], .vec (some "m") [a], .set (some "m") [a],
    .vec none [.list (some "m") [a]], .list (some "m") [.vec (some "n") [a]], .vec (some "m") [.seq (some "n") [a]] ]

partial def metas : Walk.F → List (Option String)
  | .atom _ => []
  | .list m xs | .seq m xs | .vec m xs | .set m xs => m :: xs.flatMap metas

def walkCase : WM Unit := do
  let f ← pickFrom "walk.form" walkForms
  let j := Walk.jankPostwalkId 8 f
  let c := Walk.cljPostwalkId 8 f
  if metas j != metas c then
    violate (σ := W) "G-walk: lists and seqs lose metadata (Clojure 1.12 keeps it)" s!"{repr f}"

/-! ## clojure.data.json -/

def jsonInts : List Int :=
  let bases : List Int := [0, 2 ^ 62, 2 ^ 63, 2 ^ 64, 2 ^ 65]
  let ds : List Int := [-2, -1, 0, 1, 2]
  let pos := bases.flatMap fun b => ds.map (b + ·)
  pos ++ pos.map (- ·)

def jsonIntCase : WM Unit := do
  let v ← pickFrom "json.int" jsonInts
  let j := Json.jankReadInteger v
  let c := Json.cljReadInteger v
  if !Json.sameNum j c then
    let cls := match j with
      | .long _ => "G-json: an integer in [2^63, 2^64) wraps to a negative long"
      | .dbl _ => "G-json: an integer past 64 bits becomes a double"
      | _ => "unexplained"
    violate (σ := W) cls s!"(json/read-str \"{v}\"): data.json {c.code}, jank {j.code}"

def jsonDecCase : WM Unit := do
  let m ← decide (σ := W) "json.dec.m" 201
  let kk ← decide (σ := W) "json.dec.k" 4
  if !Json.bigdecAgrees m kk then
    violate (σ := W) "G-json: :bigdec reads through a double (S9's path)" s!"m={m} k={kk}"

/-! ## Strings: bytes against chars -/

def strAlphabet : List Char := ['a', 'é', '\n', '\r', '😀']

def strCase (maxLen : Nat) : WM Unit := do
  let la ← decide (σ := W) "str.a.length" (maxLen + 1)
  let mut a : List Char := []
  for _ in [0:la] do a := a ++ [← pickFrom "str.a.char" strAlphabet]
  let lb ← decide (σ := W) "str.b.length" (maxLen + 1)
  let mut b : List Char := []
  for _ in [0:lb] do b := b ++ [← pickFrom "str.b.char" strAlphabet]
  let ua := Seqfns.utf8 a
  let ub := Seqfns.utf8 b
  if Seqfns.jankTrimNewline ub != Seqfns.utf8 (Seqfns.cljTrimNewline b) then
    violate (σ := W) "unexplained: trim-newline" s!"{b}"
  if Seqfns.isPrefixB ua ub != Seqfns.isPrefixC a b then
    violate (σ := W) "unexplained: starts-with?" s!"{a} {b}"
  if Seqfns.isSuffixB ua ub != Seqfns.isSuffixC a b then
    violate (σ := W) "unexplained: ends-with?" s!"{a} {b}"
  if Seqfns.isInfixB ua ub != Seqfns.isInfixC a b then
    violate (σ := W) "unexplained: includes?" s!"{a} {b}"

/-! ## cycle and nthrest, as a check of the theorems on the value model -/

def cycleCase : WM Unit := do
  let len ← decide (σ := W) "cycle.len" 4
  let n ← decide (σ := W) "cycle.n" 13
  let xs := (List.range (len + 1)).map (fun (j : Nat) => (j : Int))
  if Seqfns.jankCycleTake xs n != Seqfns.cljCycleTake xs n then
    violate (σ := W) "unexplained: cycle" s!"{xs} {n}"

end Jank.R4.Core.Search

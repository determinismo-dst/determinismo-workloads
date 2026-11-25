import Determinismo
import Jank.R3.Immer.Kit

/-!
# Sequence and collection objects (round 4): lists, vectors, vector seqs, `repeat`, `iterate`,
`cons`, sorted maps, transients, as jank's runtime objects and as Clojure's classes

Round 3 replicated immer's trees; the objects jank builds on them, and the lazy objects beside
them, were modeled only by their element order. This replica follows each object's methods that
`with-meta`, `meta`, `seq`, `pop`, `peek`, `conj`, `nth` (with and without a default),
`realized?` and `transient` reach, with object identity (a heap), so that an operation that
mutates an object another value holds is seen.

jank (7135b7708, paths under compiler+runtime/src/cpp/jank/runtime/):
- core/meta.cpp `meta` 13–35 (non-metadatable objects: nil), `with_meta` 37–58 (non-metadatable:
  throws an error whose text is `typed_o->to_code_string()`, which prints the whole sequence);
- obj/persistent_list.cpp: `with_meta` 156 (a new list), `seq`/`fresh_seq` 100–112 (a new list
  without meta), `conj` 119 (meta kept), `peek` 175, `pop` 180–189 (a new list, no meta; empty
  throws);
- obj/persistent_vector.cpp: `seq` 158 (`persistent_vector_sequence` from index 0), `conj` 177
  (meta kept), `with_meta` 194, `peek` 302, `pop` 312 (meta kept), `nth` 322–348 and `get` 218–235
  (`is_integral` index only: integer or BigInt, core/math.cpp 621);
- obj/persistent_vector_sequence.cpp: `seq` returns itself, `with_meta` a new seq;
- obj/repeat.cpp: `seq` returns itself; `fresh_seq` 53–60 returns *itself* for an infinite repeat;
  `with_meta` 124–130 sets the meta on what `fresh_seq` returns;
- obj/iterator.cpp (`iterate`, and `(range)` = `(iterate inc 0)`, core.jank 2832): no `with_meta`
  (not metadatable), not realizable;
- obj/cons.cpp: `seq` itself, `with_meta` a new cons;
- core/seq.cpp `nth` 648–696 and 698–735: `index = to_int(idx)` (a double truncates, math.hpp
  1411–1421); negative: throws (or the default); indexable objects get the *original* index
  (`persistent_vector::nth`/`get`, which reject a double); sequential seqs walk to `index`;
- core/seq.cpp `peek`/`pop` 737–785 (`stackable`: lists and vectors only), `transient` 161–179
  (`transientable`: vectors, maps, sets, sorted maps and sets: persistent_sorted_map.hpp 89);
- core.cpp `is_realized` 719–737 (`realizable` objects only: lazy seqs, delays, futures,
  promises).

Clojure 1.12 (clojure-ref/src/jvm/clojure/lang/): PersistentList (`withMeta` 125, `pop` 107: one
element gives `EMPTY.withMeta(_meta)`, more gives `_rest`, `cons` 115 keeps `meta()`), ASeq/RT.seq
(a list or seq is its own seq), PersistentVector (`pop` keeps meta), Repeat and Iterate
(`withMeta` returns a new object; Iterate is IPending, realized), Cons, RT.nth (`intCast` of the
index: a double truncates), PersistentTreeMap (not editable: `transient` throws).
-/

namespace Jank.R4.Immer.SeqObj

open Determinismo

/-- Metadata: `nil`, or the map `{:a n}`. -/
abbrev Meta := Option Nat

/-- An index argument: an integer, or a double with the integer it truncates to (`static_cast`
and Java's `(int)` both truncate toward zero). -/
inductive Idx where
  | int (i : Int)
  | dbl (text : String) (trunc : Int)
  deriving Repr, BEq

def Idx.trunc : Idx → Int
  | .int i => i
  | .dbl _ t => t

def Idx.code : Idx → String
  | .int i => toString i
  | .dbl s _ => s

/-- A list node with its own meta (Clojure keeps a meta per `PersistentList` node: `cons` copies
the head's, `pop` returns the rest with its own). jank keeps meta only on the list object. -/
structure LNode where
  x : Int
  md : Meta
  deriving Repr, BEq, DecidableEq

inductive Obj where
  /-- A list: its nodes (jank: only the first node's meta is the list's). Empty: the empty list
  with its meta. -/
  | list (nodes : List LNode) (emptyMeta : Meta)
  | vec (xs : List Int) (md : Meta)
  /-- A vector's seq from index `i`. -/
  | vseq (xs : List Int) (i : Nat) (md : Meta)
  /-- `repeat`: count (none: infinite) and value. -/
  | rep (count : Option Nat) (v : Int) (md : Meta)
  /-- `iterate inc`: the current value. -/
  | iter (cur : Int) (md : Meta)
  /-- `cons` onto a finite tail. -/
  | cons (h : Int) (tail : List Int) (md : Meta)
  | smap (md : Meta)
  | trans (kind : String)
  deriving Repr, BEq, DecidableEq

instance : Inhabited Obj := ⟨.smap none⟩

def Obj.md : Obj → Meta
  | .list (n :: _) _ => n.md
  | .list [] m => m
  | .vec _ m | .vseq _ _ m | .rep _ _ m | .iter _ m | .cons _ _ m | .smap m => m
  | .trans _ => none

/-- The first `k` elements (or fewer), and whether there are more. -/
def Obj.elems (k : Nat) : Obj → List Int × Bool
  | .list ns _ => (ns.map (·.x) |>.take k, ns.length > k)
  | .vec xs _ => (xs.take k, xs.length > k)
  | .vseq xs i _ => ((xs.drop i).take k, (xs.drop i).length > k)
  | .rep none v _ => (List.replicate k v, true)
  | .rep (some c) v _ => (List.replicate (min c k) v, c > k)
  | .iter c _ => ((List.range k).map fun j => c + Int.ofNat j, true)
  | .cons h t _ => ((h :: t).take k, (h :: t).length > k)
  | .smap _ => ([], false)
  | .trans _ => ([], false)

/-- The printed form, cut at 4 elements (the same text on both sides when the values agree). -/
def Obj.view (o : Obj) : String :=
  let (xs, more) := o.elems 4
  let body := " ".intercalate (xs.map toString) ++ (if more then " …" else "")
  match o with
  | .vec .. => s!"[{body}]"
  | .smap _ => "{}"
  | .trans k => s!"#transient-{k}"
  | _ => s!"({body})"

/-- The element at `n` of a sequential object (none past the end). -/
def Obj.at (o : Obj) (n : Nat) : Option Int :=
  match o with
  | .rep none v _ => some v
  | .iter c _ => some (c + Int.ofNat n)
  | .rep (some c) v _ => if n < c then some v else none
  | _ => (o.elems (n + 1)).1[n]?

inductive Op where
  | withMeta (m : Meta)
  | seq
  | pop
  | peek
  | conj (x : Int)
  | nth (i : Idx)
  | nthNf (i : Idx)
  | realized
  | transient
  deriving Repr, BEq

def Op.code : Op → String
  | .withMeta m => s!"with-meta {match m with | none => "nil" | some n => s!"\{:a {n}}"}"
  | .seq => "seq" | .pop => "pop" | .peek => "peek" | .conj x => s!"conj {x}"
  | .nth i => s!"nth {i.code}" | .nthNf i => s!"nth {i.code} :nf" | .realized => "realized?"
  | .transient => "transient"

/-- What an operation gives: a new or existing object (a heap index), a printed value, an error,
or no return. -/
inductive Res where
  | ref (r : Nat)
  | val (s : String)
  | err (why : String)
  | hang (why : String)
  deriving Repr, BEq, DecidableEq

abbrev Heap := Array Obj

def push (h : Heap) (o : Obj) : Heap × Res := (h.push o, .ref h.size)

/-! ## jank -/

/-- jank: one operation on object `r` (each arm cites the method it replicates). -/
def jank (h : Heap) (r : Nat) (op : Op) : Heap × Res :=
  let o := h[r]!
  match op with
  | .withMeta m =>
    match o with
    -- persistent_list::with_meta: a new list with the same nodes
    | .list ns em => push h (match ns with | n :: t => .list ({ n with md := m } :: t) em | [] => .list [] m)
    | .vec xs _ => push h (.vec xs m)
    | .vseq xs i _ => push h (.vseq xs i m)
    -- repeat::with_meta: `fresh_seq()` is `this` for an infinite repeat, then `ret->meta = meta`
    | .rep none v _ => (h.set! r (.rep none v m), .ref r)
    | .rep c v _ => push h (.rep c v m)
    -- iterator: not metadatable; meta.cpp with_meta formats `to_code_string()` of an infinite seq
    | .iter .. => (h, .hang "with_meta error text prints the infinite sequence (md.cpp 49-52)")
    | .cons x t _ => push h (.cons x t m)
    | .smap _ => push h (.smap m)
    | .trans _ => (h, .err "not metadatable")
  | .seq =>
    match o with
    | .list [] _ => (h, .val "nil")
    -- persistent_list::fresh_seq: a new list from the same data, no meta
    | .list ns _ => push h (.list (ns.map fun n => { n with md := none }) none)
    | .vec [] _ => (h, .val "nil")
    | .vec xs _ => push h (.vseq xs 0 none)
    | .smap _ => (h, .val "nil")
    | .trans _ => (h, .err "not seqable")
    | _ => (h, .ref r)
  | .pop =>
    match o with
    | .list [] _ => (h, .err "pop of an empty list")
    -- persistent_list::pop: `make_box<persistent_list>(data.rest())`: no meta
    | .list (_ :: t) _ => push h (.list (t.map fun n => { n with md := none }) none)
    | .vec [] _ => (h, .err "pop of an empty vector")
    | .vec xs m => push h (.vec xs.dropLast m)
    | _ => (h, .err "not stackable")
  | .peek =>
    match o with
    | .list [] _ => (h, .val "nil")
    | .list (n :: _) _ => (h, .val (toString n.x))
    | .vec [] _ => (h, .val "nil")
    | .vec xs _ => (h, .val (toString xs.getLast!))
    | _ => (h, .err "not stackable")
  | .conj x =>
    match o with
    -- persistent_list::conj keeps the list's meta (on the new head)
    | .list ns em => push h (.list ({ x, md := o.md } :: ns.map fun n => { n with md := none }) em)
    | .vec xs m => push h (.vec (xs ++ [x]) m)
    | .smap _ => (h, .err "conj of a non-entry onto a sorted map")
    | .trans _ => (h, .err "conj onto a transient")
    | _ => push h (.cons x ((o.elems 3).1) none)
  | .nth i =>
    let index := i.trunc
    if index < 0 then (h, .err "negative index") else
    match o with
    -- persistent_vector::nth: is_integral(index) or throw
    | .vec xs _ =>
      match i with
      | .int _ => if index.toNat < xs.length then (h, .val (toString xs[index.toNat]!)) else (h, .err "out of bounds")
      | .dbl .. => (h, .err "nth on a persistent_vector requires an integer index")
    | .smap _ | .trans _ => (h, .err "not indexable")
    | _ => match o.at index.toNat with
      | some v => (h, .val (toString v))
      | none => (h, .err "out of bounds")
  | .nthNf i =>
    let index := i.trunc
    if index < 0 then (h, .val ":nf") else
    match o with
    -- persistent_vector::nth(idx, fallback) = get(idx, fallback): is_integral or the fallback
    | .vec xs _ =>
      match i with
      | .int _ => if index.toNat < xs.length then (h, .val (toString xs[index.toNat]!)) else (h, .val ":nf")
      | .dbl .. => (h, .val ":nf")
    | .smap _ | .trans _ => (h, .err "not indexable")
    | _ => match o.at index.toNat with
      | some v => (h, .val (toString v))
      | none => (h, .val ":nf")
  | .realized => (h, .err "not realizable")
  | .transient =>
    match o with
    | .vec .. => push h (.trans "vector")
    | .smap _ => push h (.trans "sorted-map")
    | _ => (h, .err "not transientable")

/-! ## Clojure -/

/-- Clojure 1.12: the same operation on the corresponding class. -/
def clj (h : Heap) (r : Nat) (op : Op) : Heap × Res :=
  let o := h[r]!
  match op with
  | .withMeta m =>
    match o with
    | .list ns em => push h (match ns with | n :: t => .list ({ n with md := m } :: t) em | [] => .list [] m)
    | .vec xs _ => push h (.vec xs m)
    | .vseq xs i _ => push h (.vseq xs i m)
    | .rep c v _ => push h (.rep c v m)          -- Repeat.withMeta: a new Repeat
    | .iter c _ => push h (.iter c m)            -- Iterate.withMeta: a new Iterate
    | .cons x t _ => push h (.cons x t m)
    | .smap _ => push h (.smap m)
    | .trans _ => (h, .err "not IObj")
  | .seq =>
    match o with
    | .list [] _ => (h, .val "nil")
    | .list _ _ => (h, .ref r)                   -- RT.seq: an ASeq is its own seq
    | .vec [] _ => (h, .val "nil")
    | .vec xs _ => push h (.vseq xs 0 none)
    | .smap _ => (h, .val "nil")
    | .trans _ => (h, .err "not seqable")
    | _ => (h, .ref r)
  | .pop =>
    match o with
    | .list [] _ => (h, .err "Can't pop empty list")
    | .list [n] _ => push h (.list [] n.md)    -- EMPTY.withMeta(_meta)
    | .list (_ :: t) _ => push h (.list t none)  -- `_rest`, with its own nodes' meta
    | .vec [] _ => (h, .err "Can't pop empty vector")
    | .vec xs m => push h (.vec xs.dropLast m)
    | _ => (h, .err "not IPersistentStack")
  | .peek =>
    match o with
    | .list [] _ => (h, .val "nil")
    | .list (n :: _) _ => (h, .val (toString n.x))
    | .vec [] _ => (h, .val "nil")
    | .vec xs _ => (h, .val (toString xs.getLast!))
    | _ => (h, .err "not IPersistentStack")
  | .conj x =>
    match o with
    | .list ns em => push h (.list ({ x, md := o.md } :: ns) em)   -- PersistentList.cons: meta()
    | .vec xs m => push h (.vec (xs ++ [x]) m)
    | .smap _ => (h, .err "conj of a non-entry onto a sorted map")
    | .trans _ => (h, .err "conj onto a transient")
    | _ => push h (.cons x ((o.elems 3).1) none)
  | .nth i =>
    -- RT.nth(coll, intCast(index)): a double truncates
    let index := i.trunc
    match o with
    | .smap _ | .trans _ => (h, .err "nth not supported")
    | _ =>
      if index < 0 then (h, .err "IndexOutOfBounds") else
      match o.at index.toNat with
      | some v => (h, .val (toString v))
      | none => (h, .err "IndexOutOfBounds")
  | .nthNf i =>
    let index := i.trunc
    match o with
    | .smap _ | .trans _ => (h, .err "nth not supported")
    | _ =>
      if index < 0 then (h, .val ":nf") else
      match o.at index.toNat with
      | some v => (h, .val (toString v))
      | none => (h, .val ":nf")
  | .realized =>
    match o with
    | .iter .. => (h, .val "true")               -- Iterate is IPending: the seed is realized
    | _ => (h, .err "not IPending")
  | .transient =>
    match o with
    | .vec .. => push h (.trans "vector")
    | _ => (h, .err "not IEditableCollection")

/-! ## The deviations on the replica (kernel evaluation) -/

def isErr : Res → Bool
  | .err _ => true
  | _ => false

def isHang : Res → Bool
  | .hang _ => true
  | _ => false

/-- C1: `with-meta` on an infinite `repeat` writes the meta into the object itself (heap slot 0), and
returns it; Clojure leaves it alone and returns a new object. -/
theorem c1_repeat_meta_written :
    ((jank #[Obj.rep none 7 none] 0 (.withMeta (some 1))).1[0]!).md = some 1 ∧
    (jank #[Obj.rep none 7 none] 0 (.withMeta (some 1))).2 = .ref 0 ∧
    ((clj #[Obj.rep none 7 none] 0 (.withMeta (some 1))).1[0]!).md = none := by decide +kernel

/-- C2: `with-meta` on `(iterate inc 0)` never returns in jank. -/
theorem c2_iterate_with_meta :
    isHang (jank #[Obj.iter 0 none] 0 (.withMeta (some 1))).2 = true ∧
    isHang (clj #[Obj.iter 0 none] 0 (.withMeta (some 1))).2 = false := by decide +kernel

/-- C3: `(nth [1 2 3] 1.5)` throws in jank, is 2 in Clojure; `(nth '(1 2 3) 1.5)` is 2 in both. -/
theorem c3_nth_double :
    isErr (jank #[Obj.vec [1, 2, 3] none] 0 (.nth (.dbl "1.5" 1))).2 = true ∧
    (clj #[Obj.vec [1, 2, 3] none] 0 (.nth (.dbl "1.5" 1))).2 = .val "2" ∧
    (jank #[Obj.list [⟨1, none⟩, ⟨2, none⟩, ⟨3, none⟩] none] 0 (.nth (.dbl "1.5" 1))).2 = .val "2" := by decide +kernel

/-! ## The world -/

structure Start where
  code : String
  obj : Obj

def starts : List Start :=
  [ { code := "'(1 2)", obj := .list [⟨1, none⟩, ⟨2, none⟩] none },
    { code := "'(1)", obj := .list [⟨1, none⟩] none },
    { code := "[1 2 3]", obj := .vec [1, 2, 3] none },
    { code := "(seq [1 2 3])", obj := .vseq [1, 2, 3] 0 none },
    { code := "(repeat 7)", obj := .rep none 7 none },
    { code := "(repeat 2 7)", obj := .rep (some 2) 7 none },
    { code := "(iterate inc 0)", obj := .iter 0 none },
    { code := "(cons 0 '(1))", obj := .cons 0 [1] none },
    { code := "(sorted-map)", obj := .smap none } ]

def idxs : List Idx := [.int 1, .int 5, .int (-1), .dbl "1.0" 1, .dbl "1.5" 1, .dbl "-0.5" 0]

def ops : List Op :=
  [.withMeta (some 1), .withMeta none, .seq, .pop, .peek, .conj 9, .realized, .transient] ++
  idxs.map .nth ++ idxs.map .nthNf

structure W where
  decisions : Decisions := {}
  jh : Heap := #[]
  ch : Heap := #[]
  /-- Live values: (jank heap index, Clojure heap index). -/
  live : Array (Nat × Nat) := #[]
  story : Array String := #[]

instance : Chaotic W where
  decisions := W.decisions
  setDecisions w d := { w with decisions := d }

abbrev SW := EStateM Stop W

def metaCode : Meta → String
  | none => "nil" | some n => s!"\{:a {n}}"

def resCode (h : Heap) : Res → String
  | .ref r => h[r]!.view
  | .val s => s
  | .err _ => "throws"
  | .hang _ => "never returns"

/-- One timeline: a start, then `steps` operations, each on a live value; after each, the results
and the meta of every live value are compared. -/
def body (steps : Nat) (aside : List String) (sts : List Start := starts) (os : List Op := ops) : SW Unit := do
  let s := sts.getD (← decide "start" sts.length) ⟨"", .smap none⟩
  let w ← get
  set { w with jh := #[s.obj], ch := #[s.obj], live := #[(0, 0)], story := #[s!"start {s.code}"] }
  for _ in [0:steps] do
    let w ← get
    let t ← decide "target" w.live.size
    let op := os.getD (← decide "op" os.length) .seq
    let w ← get
    let (jr, cr) := w.live[t]!
    let (jh, jres) := jank w.jh jr op
    let (ch, cres) := clj w.ch cr op
    let line := s!"v{t} ← ({op.code} v{t})"
    let mut live := w.live
    match jres, cres with
    | .ref a, .ref b => live := live.push (a, b)
    | _, _ => pure ()
    let story := w.story.push line
    set { w with jh, ch, live, story }
    let jc := resCode jh jres
    let cc := resCode ch cres
    let cls := match jres, op with
      | .hang _, _ => "hang"
      | _, .nth _ | _, .nthNf _ => "nth-index"
      | _, .realized => "realized"
      | _, .transient => "transient"
      | _, .pop => "pop-meta"
      | _, .seq => "seq-meta"
      | _, _ => "result"
    if jc != cc && !aside.contains cls then
      violate cls s!"{"; ".intercalate story.toList}: jank {jc}, Clojure {cc}"
    -- metas of every live value (an in-place meta write shows on an earlier value)
    for i in [0:live.size] do
      let (a, b) := live[i]!
      let jm := jh[a]!.md
      let cm := ch[b]!.md
      if jm != cm then
        let c := match op with
          | .withMeta _ => "meta-mutated"
          | .pop => "pop-meta" | .seq => "seq-meta"
          | _ => "meta"
        if !aside.contains c then
          violate c s!"{"; ".intercalate story.toList}: (meta v{i}) jank {metaCode jm}, Clojure {metaCode cm}"

def run (steps : Nat) (aside : List String) (sts : List Start := starts) (os : List Op := ops)
    (source : Source) : Ended :=
  match (body steps aside sts os).run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

end Jank.R4.Immer.SeqObj

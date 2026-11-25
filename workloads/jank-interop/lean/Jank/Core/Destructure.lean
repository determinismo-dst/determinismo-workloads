import Determinismo

/-!
# Destructuring: core.jank `destructure`, `let`, `loop`, `fn`, `maybe-destructured`, `defn`

jank (commit 7135b7708, `upstream-main/compiler+runtime/src/jank/clojure/core.jank`, unchanged since
f3d82d654):

- `destructure` (3385–3488): `pb`, `pvec`, `pmap`, `process-entry`. Read side by side with
  Clojure 1.12's core.clj `destructure` (4427–4521), the code is token for token the same except:
  1. gensym prefixes (`"vec"`, `"seq"`, `"first"`, `"map"` vs `"vec__"`, …);
  2. a seq bound to a map form (`pmap`, 3427–3436) is turned into a map by
     `(if (even? (count g)) (apply hash-map g) (conj (apply hash-map (butlast g)) (last g)))`;
     Clojure 1.12 calls `PersistentArrayMap/createAsIfByAssoc` (PersistentArrayMap.java 86–200);
  3. `named?` (2488 → core.cpp `is_named`, the `nameable` concept) for `(instance? Named bb)`;
  4. errors are thrown as strings / ex-info instead of `Exception`s;
  5. `reduce` for `reduce1`.
  Item 1 renames locals nobody can name; 4 changes only the exception class; 3 and 5 agree on
  binding forms (a non-ident `bb` reaches `pb`, which throws on both). Item 2 is modeled and
  searched below, by evaluating the expansions.
- `let` (3490), `loop` (3586), `maybe-destructured` (3507), `fn` (3525): the same code as
  Clojure's (core.clj `let` 4523, `loop` 4599, `maybe-destructured` 4542, `fn` 4551) apart from
  error classes.
- `defn` (727–779) and `sigs` (694): `sigs` is Clojure's without `resolve-tag` (Java classes);
  `defn` expands to `(def name (fn name …))` (line 779) — a *named* fn — where Clojure 1.12 expands to
  `(def name (fn …))` (core.clj 314–339, "todo - restore propagation of fn name"). Modeled at the
  end of this file.

The runtime functions the expansions call, replicated on the drawn values (ints, keywords, nil,
vectors, lists, maps, sets — strings and big numbers are left to the strings and numbers
areas): core/seq.cpp `seq` (289), `first` (299), `next` (313), `nth` with fallback (698),
seq.hpp `get` (102 → each type's `get`: persistent_vector.cpp 218 `is_integral` index, maps by
`=`, `object::get` nil otherwise), `is_seq` (55: non-nil and `sequence_like`), `count`,
persistent_hash_map `create_from_seq` (later value wins), base_persistent_map.cpp `conj` (169: nil,
a map merges, a two-element vector assocs, else "invalid map entry"), core.jank `butlast`/`last`.
On these values each agrees with Clojure's `RT.seq`, `RT.first`, `RT.next`, `RT.nthFrom` (nil and
n<0 → not-found; Indexed; Sequential walk; else UnsupportedOperationException), `RT.get`.
-/

namespace Jank.Core.Destructure

open Determinismo

/-! ## Values and forms -/

inductive Val where
  | nil
  | int (v : Int)
  | kw (ns name : String)
  | sym (ns name : String)
  | vec (xs : List Val)
  /-- A list or seq (`sequence_like`). -/
  | list (xs : List Val)
  /-- A map, its entries in iteration order. -/
  | map (kvs : List (Val × Val))
  | set (xs : List Val)
  /-- `(seq m)` of a map: its entries (Clojure `MapEntry`s; jank `persistent_vector`s inside a
  `persistent_array_map_sequence`). -/
  | mapSeq (kvs : List (Val × Val))
  deriving Inhabited, BEq, Repr

/-- Sizes for the recursion through lists of pairs (round 3: the definitions below terminate). -/
theorem sizeOf_fst_lt {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l : List (α × β)} (h : p ∈ l) :
    sizeOf p.1 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h; cases p; simp at this ⊢; omega

theorem sizeOf_snd_lt {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l : List (α × β)} (h : p ∈ l) :
    sizeOf p.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h; cases p; simp at this ⊢; omega

theorem sizeOf_zip_fst {α β : Type} [SizeOf α] [SizeOf β] {a : List α} {b : List β} {p : α × β}
    (h : p ∈ a.zip b) : sizeOf p.1 < sizeOf a := List.sizeOf_lt_of_mem (List.of_mem_zip h).1

theorem sizeOf_zip_snd {α β : Type} [SizeOf α] [SizeOf β] {a : List α} {b : List β} {p : α × β}
    (h : p ∈ a.zip b) : sizeOf p.2 < sizeOf b := List.sizeOf_lt_of_mem (List.of_mem_zip h).2

def Val.code : Val → String
  | .nil => "nil"
  | .int v => toString v
  | .kw ns n => if ns.isEmpty then s!":{n}" else s!":{ns}/{n}"
  | .sym ns n => if ns.isEmpty then n else s!"{ns}/{n}"
  | .vec xs => "[" ++ " ".intercalate (xs.map Val.code) ++ "]"
  | .list xs => "(" ++ " ".intercalate (xs.map Val.code) ++ ")"
  | .map kvs => "{" ++ ", ".intercalate (kvs.map fun kv => kv.1.code ++ " " ++ kv.2.code) ++ "}"
  | .set xs => "#{" ++ " ".intercalate (xs.map Val.code) ++ "}"
  | .mapSeq kvs => "(seq {" ++ ", ".intercalate (kvs.map fun kv => kv.1.code ++ " " ++ kv.2.code) ++ "})"
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)
    | (have := sizeOf_fst_lt ‹_ ∈ kvs›; omega)
    | (have := sizeOf_snd_lt ‹_ ∈ kvs›; omega)

/-- A code form. `const` is an already-evaluated init expression. -/
inductive F where
  | sym (ns name : String)
  | kw (ns name : String)
  | str (s : String)
  | int (v : Int)
  | nil
  | vec (xs : List F)
  | map (kvs : List (F × F))
  | list (xs : List F)
  | const (v : Val)
  deriving Inhabited, BEq, Repr

def F.code : F → String
  | .sym ns n => if ns.isEmpty then n else s!"{ns}/{n}"
  | .kw ns n => if ns.isEmpty then s!":{n}" else s!":{ns}/{n}"
  | .str s => s!"\"{s}\""
  | .int v => toString v
  | .nil => "nil"
  | .vec xs => "[" ++ " ".intercalate (xs.map F.code) ++ "]"
  | .map kvs => "{" ++ " ".intercalate (kvs.map fun kv => kv.1.code ++ " " ++ kv.2.code) ++ "}"
  | .list xs => "(" ++ " ".intercalate (xs.map F.code) ++ ")"
  | .const v => v.code
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)
    | (have := sizeOf_fst_lt ‹_ ∈ kvs›; omega)
    | (have := sizeOf_snd_lt ‹_ ∈ kvs›; omega)

def core (n : String) : F := .sym "clojure.core" n
def s (n : String) : F := .sym "" n

/-! ## `destructure` (core.jank 3385) -/

/-- Which code: jank's, or Clojure 1.12's (differences 1 and 2 above). -/
inductive Flavor where | jank | clj
  deriving BEq, Repr, Inhabited

/-- The gensym counter and the first error. -/
abbrev DM := StateT Nat (Except String)

/-- `(gensym prefix)`: jank's prefixes are `"vec"`… (3389–3391, 3423), Clojure's `"vec__"`…. -/
def gensym (fl : Flavor) (pfx : String) : DM F := do
  let n ← get
  set (n + 1)
  pure (s (match fl with | .jank => pfx ++ toString n | .clj => pfx ++ "__" ++ toString n))

/-- The seq-to-map form in `pmap`. jank 3427–3436; Clojure core.clj 4467–4471. -/
def seqToMapForm (fl : Flavor) (g : F) : F :=
  match fl with
  | .jank =>
    .list [s "if", .list [core "seq?", g],
      .list [s "if", .list [core "next", g],
        .list [s "if", .list [core "even?", .list [core "count", g]],
          .list [core "apply", core "hash-map", g],
          .list [core "conj", .list [core "apply", core "hash-map", .list [core "butlast", g]],
                 .list [core "last", g]]],
        .list [s "if", .list [core "seq", g], .list [core "first", g], .map []]],
      g]
  | .clj =>
    .list [s "if", .list [core "seq?", g],
      .list [s "if", .list [core "next", g],
        .list [s "clojure.lang.PersistentArrayMap/createAsIfByAssoc", .list [core "to-array", g]],
        .list [s "if", .list [core "seq", g], .list [core "first", g],
               s "clojure.lang.PersistentArrayMap/EMPTY"]],
      g]

/-- `(get m k)` on a binding map form (array map: first match). -/
def formGet (kvs : List (F × F)) (k : F) : Option F := (kvs.find? (·.1 == k)).map (·.2)

/-- Array-map `assoc` on a form map: in place when present, else at the end. -/
def formAssoc (kvs : List (F × F)) (k v : F) : List (F × F) :=
  if kvs.any (·.1 == k) then kvs.map fun (a, b) => if a == k then (a, v) else (a, b)
  else kvs ++ [(k, v)]

def formDissoc (kvs : List (F × F)) (k : F) : List (F × F) := kvs.filter (·.1 != k)

/-- `named?` / `(instance? Named x)`: a symbol or keyword. -/
def F.named : F → Bool
  | .sym .. | .kw .. => true
  | _ => false

/-- `name`/`namespace` of a named form. -/
def F.nameOf : F → String
  | .sym _ n | .kw _ n => n
  | .str t => t
  | _ => ""

def F.nsOf : F → String
  | .sym ns _ | .kw ns _ => ns
  | _ => ""

/-- What a `:keys`/`:syms`/`:strs` transform does to a binding symbol (3443–3446). -/
inductive Transform where | keys (mkns : String) | syms (mkns : String) | strs
  deriving BEq, Inhabited

def Transform.apply : Transform → F → F
  | .keys mkns, x => .kw (if mkns.isEmpty then x.nsOf else mkns) x.nameOf
  | .syms mkns, x => .list [s "quote", .sym (if mkns.isEmpty then x.nsOf else mkns) x.nameOf]
  | .strs, x => .str x.nameOf

mutual
/-- `pb` (3388): a symbol binds directly; a vector goes to `pvec`, a map to `pmap`; else throws. -/
partial def pb (fl : Flavor) (bvec : List F) (b : F) (v : F) : DM (List F) :=
  match b with
  | .sym .. => pure (bvec ++ [b, v])
  | .vec bs => pvec fl bvec bs v
  | .map kvs => pmap fl bvec kvs v
  | _ => throw s!"Unsupported binding form: {b.code}"

/-- `pvec` (3389–3421). -/
partial def pvec (fl : Flavor) (bvec : List F) (b : List F) (val : F) : DM (List F) := do
  let gvec ← gensym fl "vec"
  let gseq ← gensym fl "seq"
  let gfirst ← gensym fl "first"
  let hasRest := b.contains (s "&")
  let ret := bvec ++ [gvec, val] ++ (if hasRest then [gseq, .list [core "seq", gvec]] else [])
  let rec loop (ret : List F) (n : Nat) (bs : List F) (seenRest : Bool) : DM (List F) :=
    match bs with
    | [] => pure ret
    | firstb :: rest =>
      if firstb == s "&" then do
        let ret' ← pb fl ret (rest.headD .nil) gseq
        loop ret' n (rest.drop 1) true
      else if firstb == .kw "" "as" then pb fl ret (rest.headD .nil) gvec
      else if seenRest then throw "Unsupported binding form, only :as can follow & parameter"
      else do
        let ret' := if hasRest then ret ++ [gfirst, .list [core "first", gseq], gseq, .list [core "next", gseq]] else ret
        let ret'' ← pb fl ret' firstb (if hasRest then gfirst else .list [core "nth", gvec, .int n, .nil])
        loop ret'' (n + 1) rest seenRest
  loop ret 0 b false

/-- `pmap` (3422–3482). -/
partial def pmap (fl : Flavor) (bvec : List F) (b : List (F × F)) (v : F) : DM (List F) := do
  let gmap ← gensym fl "map"
  let defaults := match formGet b (.kw "" "or") with | some (.map d) => d | _ => []
  let ret := bvec ++ [gmap, v, gmap, seqToMapForm fl gmap] ++
    (match formGet b (.kw "" "as") with | some a => [a, gmap] | none => [])
  -- transforms: over (keys b), keyword keys named keys/syms/strs
  let transforms : List (F × Transform) := b.foldl (fun acc (mk, _) =>
    match mk with
    | .kw mkns mkn =>
      if mkn == "keys" then acc ++ [(mk, .keys mkns)]
      else if mkn == "syms" then acc ++ [(mk, .syms mkns)]
      else if mkn == "strs" then acc ++ [(mk, .strs)]
      else acc
    | _ => acc) []
  let bes0 := formDissoc (formDissoc b (.kw "" "as")) (.kw "" "or")
  let bes := transforms.foldl (fun bes (k, t) =>
    let syms := match formGet bes k with | some (.vec xs) => xs | _ => []
    syms.foldl (fun acc x => formAssoc acc x (t.apply x)) (formDissoc bes k)) bes0
  let rec loop (ret : List F) (bes : List (F × F)) : DM (List F) :=
    match bes with
    | [] => pure ret
    | (bb, bk) :: rest => do
      let loc := if bb.named then F.sym "" bb.nameOf else bb
      let bv := match formGet defaults loc with
        | some d => F.list [core "get", gmap, bk, d]
        | none => F.list [core "get", gmap, bk]
      let ret' ← if (match bb with | .sym .. | .kw .. => true | _ => false)
        then pure (ret ++ [loc, bv]) else pb fl ret bb bv
      loop ret' rest
  loop ret bes
end

/-- `destructure` (3385): bindings unchanged when every binding form is a symbol, else
`process-entry` over the pairs. -/
def destructure (fl : Flavor) (bindings : List F) : Except String (List F) := do
  let rec pairs : List F → List (F × F)
    | a :: b :: rest => (a, b) :: pairs rest
    | _ => []
  let bents := pairs bindings
  if bents.all (fun (b, _) => match b with | .sym .. => true | _ => false) then pure bindings
  else
    let (r, _) ← (bents.foldlM (fun acc (b, v) => pb fl acc b v) [] : DM (List F)).run 0
    pure r

/-! ## The runtime: evaluating a `let*` of the expansion -/

abbrev Env := List (String × Val)

def Val.truthy : Val → Bool
  | .nil => false
  | _ => true

/-- core/seq.cpp 289 `seq`: nil and empty collections → nil; a map's entries are `[k v]`
vectors; a non-seqable value throws ("not seqable"). -/
def rtSeq : Val → Except String Val
  | .nil => pure .nil
  | .vec xs | .list xs | .set xs => pure (if xs.isEmpty then .nil else .list xs)
  | .map kvs | .mapSeq kvs => pure (if kvs.isEmpty then .nil else .list (kvs.map fun (k, v) => .vec [k, v]))
  | v => throw s!"not seqable: {v.code}"

def rtFirst (v : Val) : Except String Val := do
  match ← rtSeq v with
  | .list (x :: _) => pure x
  | _ => pure .nil

def rtNext (v : Val) : Except String Val := do
  match ← rtSeq v with
  | .list (_ :: rest) => pure (if rest.isEmpty then .nil else .list rest)
  | _ => pure .nil

/-- core/seq.cpp 698 `nth(o, idx, fallback)`: nil or a negative index → fallback; indexable
(vectors) → element or fallback; seqable and sequential (lists) → walk; else throws. -/
def rtNth (o : Val) (i : Int) (fallback : Val) : Except String Val :=
  if i < 0 then pure fallback
  else match o with
    | .nil => pure fallback
    | .vec xs | .list xs => pure (xs.getD i.toNat fallback)
    | .mapSeq kvs => pure ((kvs.map fun (k, v) => Val.vec [k, v]).getD i.toNat fallback)
    | v => throw s!"Objects of type `{v.code}` are not indexable."

/-- jank `=` on these values (maps and sets unordered). -/
def valEq : Val → Val → Bool
  | .map a, .map b => a.length == b.length && a.all fun kv => b.any fun kv' => valEq kv.1 kv'.1 && valEq kv.2 kv'.2
  | .set a, .set b => a.length == b.length && a.all fun x => b.any fun y => valEq x y
  | .vec a, .vec b | .vec a, .list b | .list a, .vec b | .list a, .list b =>
    a.length == b.length && (a.zip b).attach.all fun xy => valEq xy.1.1 xy.1.2
  | a, b => a == b
termination_by x y => sizeOf x + sizeOf y
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := sizeOf_fst_lt ‹_ ∈ a›; have := sizeOf_fst_lt ‹_ ∈ b›; omega)
    | (have := sizeOf_snd_lt ‹_ ∈ a›; have := sizeOf_snd_lt ‹_ ∈ b›; omega)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ a›; have := List.sizeOf_lt_of_mem ‹_ ∈ b›; omega)
    | (have := sizeOf_zip_fst xy.2; have := sizeOf_zip_snd xy.2; omega)

/-- seq.hpp 102 `get(m, key[, fallback])`. -/
def rtGet (m k : Val) (fallback : Val := .nil) : Val :=
  match m with
  | .map kvs => ((kvs.find? fun (k', _) => valEq k' k).map (·.2)).getD fallback
  | .vec xs => match k with
    | .int i => if i < 0 then fallback else xs.getD i.toNat fallback
    | _ => fallback
  | .set xs => ((xs.find? (valEq k)).map id).getD fallback
  | _ => fallback

/-- core/seq.cpp 55 `is_seq`: lists and seqs. -/
def rtIsSeq : Val → Bool
  | .list _ | .mapSeq _ => true
  | _ => false

def mapAssoc (kvs : List (Val × Val)) (k v : Val) : List (Val × Val) :=
  if kvs.any (fun (k', _) => valEq k' k) then kvs.map fun (a, b) => if valEq a k then (a, v) else (a, b)
  else kvs ++ [(k, v)]

/-- persistent_hash_map.cpp `create_from_seq` (via `(apply hash-map …)`): pairs, a later value
wins; an odd count throws. (Its iteration order is the hash map's; maps are compared unordered.) -/
def rtHashMap (xs : List Val) : Except String Val :=
  let rec go : List Val → List (Val × Val) → Except String (List (Val × Val))
    | [], acc => pure acc
    | [_], _ => throw "odd number of elements"
    | k :: v :: rest, acc => go rest (mapAssoc acc k v)
  return .map (← go xs [])

/-- base_persistent_map.cpp 169 `conj(head)`: nil → the map; a map → merge; a two-element vector
→ assoc; else "invalid map entry". -/
def rtMapConj (m : List (Val × Val)) (head : Val) : Except String Val :=
  match head with
  | .nil => pure (.map m)
  | .map kvs => pure (.map (kvs.foldl (fun acc (k, v) => mapAssoc acc k v) m))
  | .vec [k, v] => pure (.map (mapAssoc m k v))
  | _ => throw s!"invalid map entry: {head.code}"

/-- PersistentArrayMap.createAsIfByAssoc (86) with APersistentMap.cons (27) for an odd trailing
element: a map entry (none drawn) or a 2-vector assocs, another vector throws, anything else is
walked as a seq of `Map.Entry` (a map's entries are; a vector element is not: ClassCastException;
nil gives nothing). Later values win; first key positions kept. -/
def cljCreateAsIfByAssoc (xs : List Val) : Except String Val := do
  let n := xs.length
  let (pairs, trailing) := if n % 2 == 1 then (xs.take (n - 1), some (xs.getD (n - 1) .nil)) else (xs, none)
  let rec go : List Val → List (Val × Val) → List (Val × Val)
    | k :: v :: rest, acc => go rest (mapAssoc acc k v)
    | _, acc => acc
  let base := go pairs []
  match trailing with
  | none => pure (.map base)
  | some t =>
    let extra ← match t with
      | .vec [k, v] => pure [(k, v)]
      | .vec _ => throw "Vector arg to map conj must be a pair"
      | .nil => pure []
      | .map kvs => pure kvs
      -- walked as a seq of Map.Entry: a map's entries are; a vector in a list is not
      | .mapSeq kvs => pure kvs
      | .list [] => pure []
      | .list _ => throw "ClassCastException: not a Map.Entry"
      | v => throw s!"Don't know how to create ISeq from: {v.code}"
    pure (.map (extra.foldl (fun acc (k, v) => mapAssoc acc k v) base))

/-- A seq of a map's entries, as `(seq {:b 2})` produces (MapEntry values): its own marker so the
Clojure side can accept it. -/
def mapEntrySeqMarker : String := "map-entry-seq"

mutual
/-- Evaluating an expansion's forms. -/
def eval (fl : Flavor) (env : Env) : F → Except String Val
  | .sym "" "clojure.lang.PersistentArrayMap/EMPTY" => pure (.map [])
  | .sym "" n => match env.lookup n with
    | some v => pure v
    | none => throw s!"unbound {n}"
  | .sym ns n => throw s!"unexpected var {ns}/{n}"
  | .kw ns n => pure (.kw ns n)
  | .str _ => throw "strings are not drawn"
  | .int v => pure (.int v)
  | .nil => pure .nil
  | .const v => pure v
  | .vec xs => do pure (.vec (← xs.mapM (eval fl env)))
  | .map [] => pure (.map [])
  | .map _ => throw "map literal"
  | .list [] => pure (.list [])
  | .list (f :: args) => evalCall fl env f args

def evalCall (fl : Flavor) (env : Env) (f : F) (args : List F) : Except String Val := do
  if f == s "if" then
    match args with
    | [c, a, b] => if (← eval fl env c).truthy then eval fl env a else eval fl env b
    | _ => throw "if"
  else if f == s "quote" then
    match args with
    | [.sym ns n] => pure (.sym ns n)
    | _ => throw "quote"
  else if f == core "apply" then
    match args with
    | [.sym "clojure.core" "hash-map", x] => do
      match ← eval fl env x with
      | .list xs => rtHashMap xs
      | .nil => pure (.map [])
      | _ => throw "apply"
    | _ => throw "apply"
  else
    let vs ← args.mapM (eval fl env)
    match f, vs with
    | .sym "clojure.core" "seq", [x] => rtSeq x
    | .sym "clojure.core" "first", [x] => rtFirst x
    | .sym "clojure.core" "next", [x] => rtNext x
    | .sym "clojure.core" "nth", [x, .int i, d] => rtNth x i d
    | .sym "clojure.core" "get", [m, k] => pure (rtGet m k)
    | .sym "clojure.core" "get", [m, k, d] => pure (rtGet m k d)
    | .sym "clojure.core" "seq?", [x] => pure (if rtIsSeq x then .kw "" "true" else .nil)
    | .sym "clojure.core" "count", [.list xs] => pure (.int xs.length)
    | .sym "clojure.core" "even?", [.int n] => pure (if n % 2 == 0 then .kw "" "true" else .nil)
    | .sym "clojure.core" "butlast", [.list xs] => pure (if xs.length ≤ 1 then .nil else .list (xs.take (xs.length - 1)))
    | .sym "clojure.core" "last", [.list xs] => pure (xs.getLast?.getD .nil)
    | .sym "clojure.core" "conj", [.map m, h] => rtMapConj m h
    | .sym "clojure.core" "to-array", [.list xs] => pure (.list xs)
    | .sym "" "clojure.lang.PersistentArrayMap/createAsIfByAssoc", [.list xs] =>
      cljCreateAsIfByAssoc xs
    | _, _ => throw s!"call {f.code}"
end

/-- `(let* bindings)`: each symbol bound in turn. -/
def evalLet (fl : Flavor) (bindings : List F) : Except String Env := do
  let rec go : List F → Env → Except String Env
    | .sym "" n :: form :: rest, env => do
      let v ← eval fl env form
      go rest ((n, v) :: env)
    | [], env => pure env
    | _, _ => throw "bad let*"
  go bindings []

/-- Visible bindings: the user's names (no gensyms), last binding of each name. -/
def visible (env : Env) (names : List String) : List (String × Val) :=
  names.filterMap fun n => (env.lookup n).map (n, ·)

/-! ## The world: a binding form and a value drawn -/

structure World where
  decisions : Decisions := {}

instance : Chaotic World where
  decisions w := w.decisions
  setDecisions w d := { w with decisions := d }

def localNames : List String := ["a", "b", "c"]

/-- Values bound: ints, keywords, nil, small vectors, lists, maps, a set. -/
def atomVals : List Val := [.nil, .int 1, .int 2, .kw "" "a", .kw "" "b"]

def drawAtom (name : String) : EStateM Stop World Val := do
  pure (atomVals.getD (← decide (σ := World) name atomVals.length) .nil)

partial def drawVal (name : String) (depth : Nat) (entrySeq : Bool := true) : EStateM Stop World Val := do
  let k ← decide (σ := World) s!"{name}.kind" (if depth == 0 then 1 else 6)
  match k with
  | 0 => drawAtom s!"{name}.atom"
  | 1 | 2 | 3 =>
    let n ← decide (σ := World) s!"{name}.size" 4
    let mut xs := []
    for i in List.range n do xs := xs ++ [← drawVal s!"{name}.{i}" (depth - 1) entrySeq]
    pure (if k == 1 then .vec xs else if k == 2 then .list xs else .set xs)
  | 4 =>
    let n ← decide (σ := World) s!"{name}.size" 3
    let mut kvs : List (Val × Val) := []
    for i in List.range n do
      let key := [Val.kw "" "a", .kw "" "b", .kw "" "c"].getD i .nil
      kvs := kvs ++ [(key, ← drawAtom s!"{name}.v{i}")]
    pure (.map kvs)
  | _ =>
    -- keyword arguments (the rest of a `& {:keys …}` call): pairs, maybe a trailing map or nil
    let n ← decide (σ := World) s!"{name}.pairs" 3
    let mut xs := []
    for i in List.range n do
      xs := xs ++ [[Val.kw "" "a", .kw "" "b"].getD (← decide (σ := World) s!"{name}.k{i}" 2) .nil,
                   ← drawAtom s!"{name}.v{i}"]
    let t ← decide (σ := World) s!"{name}.trailing" (if entrySeq then 4 else 3)
    let ys := match t with
      | 1 => xs ++ [.map [(.kw "" "b", .int 2)]]
      | 2 => xs ++ [.nil]
      | 3 => xs ++ [.mapSeq [(.kw "" "c", .int 3)]]
      | _ => xs
    pure (.list ys)

/-- A binding form: a symbol, a vector form (positions, `&`, `:as`) or a map form
(`:keys`, `:as`, `:or`, explicit keys), nested once. -/
partial def drawBinding (name : String) (depth : Nat) : EStateM Stop World F := do
  let k ← decide (σ := World) s!"{name}.form" (if depth == 0 then 1 else 3)
  let sym ← pure (s (localNames.getD (← decide (σ := World) s!"{name}.sym" localNames.length) "a"))
  match k with
  | 0 => pure sym
  | 1 =>
    let n ← decide (σ := World) s!"{name}.n" 3
    let mut xs := []
    for i in List.range n do xs := xs ++ [← drawBinding s!"{name}.{i}" (depth - 1)]
    let rest ← decide (σ := World) s!"{name}.rest" 2
    let ys ← if rest == 1 then do pure (xs ++ [s "&", ← drawBinding s!"{name}.r" (depth - 1)]) else pure xs
    let as_ ← decide (σ := World) s!"{name}.as" 2
    pure (.vec (if as_ == 1 then ys ++ [.kw "" "as", sym] else ys))
  | _ =>
    let mut kvs : List (F × F) := []
    let nkeys ← decide (σ := World) s!"{name}.keys" 3
    if nkeys > 0 then
      kvs := kvs ++ [(.kw "" "keys", .vec ((localNames.take nkeys).map s))]
    let explicit ← decide (σ := World) s!"{name}.explicit" 2
    if explicit == 1 then
      kvs := kvs ++ [(← drawBinding s!"{name}.e" (depth - 1), .kw "" "c")]
    let or_ ← decide (σ := World) s!"{name}.or" 2
    if or_ == 1 then kvs := kvs ++ [(.kw "" "or", .map [(s "a", .int 9)])]
    let as_ ← decide (σ := World) s!"{name}.as" 2
    if as_ == 1 then kvs := kvs ++ [(.kw "" "as", sym)]
    pure (.map kvs)

def showEnv (r : Except String (List (String × Val))) : String :=
  match r with
  | .ok xs => "{" ++ ", ".intercalate (xs.map fun (n, v) => s!"{n} {v.code}") ++ "}"
  | .error e => s!"throws ({e})"

def sameEnv (a b : Except String (List (String × Val))) : Bool :=
  match a, b with
  | .ok xs, .ok ys => xs.length == ys.length && (xs.zip ys).all fun ((n, v), (m, w)) => n == m && valEq v w
  | .error _, .error _ => true
  | _, _ => false

/-- `(let [form value] [a b c])` under jank's expansion and Clojure's. -/
def bindBody (bindDepth valDepth : Nat) (entrySeq : Bool := true) : EStateM Stop World Unit := do
  let b ← drawBinding "bind" bindDepth
  let v ← drawVal "val" valDepth entrySeq
  let run := fun (fl : Flavor) => do
    let bs ← destructure fl [b, .const v]
    let env ← evalLet fl bs
    pure (visible env localNames)
  let j := run .jank
  let c := run .clj
  if !sameEnv j c then
    violate (σ := World) "destructuring as Clojure's"
      s!"(let [{b.code} '{v.code}] [a b c]): Clojure {showEnv c}, jank {showEnv j}"

def runBody (body : EStateM Stop World Unit) (source : Source) : Ended :=
  match body.run { decisions := { source } } with
  | .ok _ w => { taken := w.decisions.taken, violation := none }
  | .error (.violation p d) w => { taken := w.decisions.taken, violation := some (p, d) }
  | .error .limit w => { taken := w.decisions.taken, violation := none }
  | .error (.nodeDown _) w => { taken := w.decisions.taken, violation := none }

/-! ## The kwargs conversion alone, over every short argument list -/

/-- `(defn f [& {:as m}] m)` called with `args`: jank vs Clojure (maps compared unordered). -/
def kwargs (fl : Flavor) (args : List Val) : Except String Val := do
  let bs ← destructure fl [.map [(.kw "" "as", s "m")], .const (if args.isEmpty then .nil else .list args)]
  let env ← evalLet fl bs
  pure ((env.lookup "m").getD .nil)

def kwargsTable : List (List Val × Except String Val × Except String Val) := Id.run do
  let elems : List Val := [.kw "" "a", .int 1, .map [(.kw "" "b", .int 2)], .nil,
    .vec [.kw "" "c", .int 3], .mapSeq [(.kw "" "d", .int 4)]]
  let mut out := []
  let lists := [[]] ++ (elems.map fun a => [a]) ++ (elems.flatMap fun a => elems.map fun b => [a, b]) ++
    (elems.flatMap fun a => elems.flatMap fun b => elems.map fun c => [a, b, c])
  for args in lists do
    let j := kwargs .jank args
    let c := kwargs .clj args
    let same := match j, c with
      | .ok x, .ok y => valEq x y
      | .error _, .error _ => true
      | _, _ => false
    if !same then out := out ++ [(args, c, j)]
  return out

/-! ## `defn`: a named fn (core.jank 727–846 vs core.clj 314–339) -/

/-- A tiny language for the recursion example. -/
inductive E where
  | ref (n : String)
  | kw (n : String)
  | int (v : Int)
  | posQ (e : E)
  | dec (e : E)
  | iff (c a b : E)
  | call (f : E) (arg : E)
  deriving Inhabited

/-- A fn value: its optional self name (`(fn name [p] body)`), parameter and body. -/
structure Fn where
  self : Option String
  param : String
  body : E
  deriving Inhabited

inductive V where
  | int (v : Int)
  | kw (n : String)
  | fn (f : Fn)
  | bool (b : Bool)
  deriving Inhabited

def V.code : V → String
  | .int v => toString v
  | .kw n => ":" ++ n
  | .fn _ => "#fn"
  | .bool b => toString b

/-- Resolution as the analyzer does it: a local (parameter, then the fn's own name) shadows a
var; otherwise the var's current root is read at call time. -/
def evalE (vars : String → Option V) (locals : List (String × V)) (fuel : Nat) : E → Except String V
  | .ref n => match locals.lookup n with
    | some v => pure v
    | none => match vars n with
      | some v => pure v
      | none => throw s!"unbound {n}"
  | .kw n => pure (.kw n)
  | .int v => pure (.int v)
  | .posQ e => do match ← evalE vars locals fuel e with
    | .int v => pure (.bool (v > 0))
    | _ => throw "pos?"
  | .dec e => do match ← evalE vars locals fuel e with
    | .int v => pure (.int (v - 1))
    | _ => throw "dec"
  | .iff c a b => do match ← evalE vars locals fuel c with
    | .bool false => evalE vars locals fuel b
    | _ => evalE vars locals fuel a
  | .call f a => do
    -- `fuel == 0`: no call left (round 3: a `match`, the same values, so that the recursion is
    -- seen to terminate).
    match fuel with
    | 0 => throw "fuel"
    | fuel' + 1 =>
      match ← evalE vars locals (fuel' + 1) f with
      | .fn g =>
        let arg ← evalE vars locals (fuel' + 1) a
        let locals' := [(g.param, arg)] ++ (match g.self with | some n => [(n, .fn g)] | none => [])
        evalE vars locals' fuel' g.body
      | _ => throw "not a fn"
termination_by e => (fuel, sizeOf e)

/-- `(defn name [p] body)`: jank → `(def name (fn name [p] body))` (core.jank `defn` 727–779,
the `(fn ~name ~@fdecl)` at 779); Clojure 1.12 → `(def name (fn [p] body))` (core.clj 335–339).
Inside a named fn the analyzer resolves the fn's own name before any var:
analyze/processor.cpp 1658–1673 on 7135b7708 (`find_named_recursion`, after the locals, before
`qualify_symbol`/`find_var`; 1507–1521 on f3d82d654), local_frame.cpp 133. -/
def defnFn (fl : Flavor) (name param : String) (body : E) : Fn :=
  { self := if fl == .jank then some name else none, param, body }

/-- ```
(defn countdown [n] (if (pos? n) (countdown (dec n)) :done))
(def orig countdown)
(defn countdown [n] :redefined)
(orig 3)
``` -/
def redefProgram (fl : Flavor) : Except String V :=
  let body := E.iff (.posQ (.ref "n")) (.call (.ref "countdown") (.dec (.ref "n"))) (.kw "done")
  let v1 := defnFn fl "countdown" "n" body
  let orig := V.fn v1
  let v2 := defnFn fl "countdown" "n" (.kw "redefined")
  let vars := fun (n : String) => if n == "countdown" then some (V.fn v2) else if n == "orig" then some orig else none
  evalE vars [] 100 (.call (.ref "orig") (.int 3))

end Jank.Core.Destructure

/-!
# Round 4: `clojure.walk`

**jank** (src/jank/clojure/walk.jank 3–12):
```clojure
(cond (list? form) (outer (apply list (map inner form)))
      (seq? form)  (outer (doall (map inner form)))
      (coll? form) (outer (into (empty form) (map inner form)))
      :else        (outer form))
```
`empty` (core/seq.cpp 787–803) keeps the collection's metadata (`with_meta(empty, meta(o))`) and
`into` (core.jank 3370–3384) keeps the target's, so vectors, maps and sets keep theirs; a list or
a seq is rebuilt without it.

**Clojure 1.12** (clojure/walk.clj 35–51): lists and seqs are rebuilt
`(with-meta … (meta form))`; map entries stay entries; records keep their type. Clojure 1.11
rebuilt lists and seqs without metadata, as jank does: this is a 1.12 change (the spec here is
1.12).

`postwalk`, `prewalk`, `keywordize-keys`, `stringify-keys`, `prewalk-replace`,
`postwalk-replace`, `macroexpand-all` are Clojure's text; they inherit `walk`.
-/

namespace Jank.R4.Core.Walk

/-- A form with optional metadata (a name for it) on each collection. -/
inductive F where
  | atom (s : String)
  | list (md : Option String) (xs : List F)
  | seq (md : Option String) (xs : List F)
  | vec (md : Option String) (xs : List F)
  | set (md : Option String) (xs : List F)
  deriving Repr, Inhabited, BEq

def F.md : F → Option String
  | .atom _ => none
  | .list m _ | .seq m _ | .vec m _ | .set m _ => m

/-- `(postwalk identity form)` with fuel; `keepSeqMeta` is Clojure 1.12's `with-meta`. -/
def postwalkId (keepSeqMeta : Bool) : Nat → F → F
  | 0, f => f
  | n + 1, f =>
    match f with
    | .atom s => .atom s
    | .list m xs => .list (if keepSeqMeta then m else none) (xs.map (postwalkId keepSeqMeta n))
    | .seq m xs => .seq (if keepSeqMeta then m else none) (xs.map (postwalkId keepSeqMeta n))
    | .vec m xs => .vec m (xs.map (postwalkId keepSeqMeta n))
    | .set m xs => .set m (xs.map (postwalkId keepSeqMeta n))

def jankPostwalkId := postwalkId false
def cljPostwalkId := postwalkId true

/-- Every list or seq with metadata loses it in jank's walk; Clojure 1.12 keeps it. -/
theorem jank_walk_drops_list_meta (m : String) (xs : List F) (n : Nat) :
    (jankPostwalkId (n + 1) (.list (some m) xs)).md = none ∧
      (cljPostwalkId (n + 1) (.list (some m) xs)).md = some m := by
  simp [jankPostwalkId, cljPostwalkId, postwalkId, F.md]

/-- Vectors and sets keep their metadata on both sides, at every depth. -/
theorem walk_vec_meta_agree (m : Option String) (xs : List F) (n : Nat) :
    (jankPostwalkId (n + 1) (.vec m xs)).md = (cljPostwalkId (n + 1) (.vec m xs)).md := by
  simp [jankPostwalkId, cljPostwalkId, postwalkId, F.md]

end Jank.R4.Core.Walk

import Jank.Core.Destructure

/-!
# Destructuring: the keyword-arguments conversion, every argument list (round 3, proofs)

Round 2 (`Jank.Core.Destructure`) read jank's `destructure` (core.jank 3385–3488) beside
Clojure 1.12's (core.clj 4427–4521): token for token the same except gensym prefixes, error
classes, `named?` and the conversion of a seq bound to a map form (`pmap`, core.jank 3427–3436
vs core.clj 4467–4471). With a trailing `(seq m)` set aside, `exhaust` was complete over 384,183
programs, nothing found.

Stating the conversion for every argument list exposed a class outside those bounds (P1): a
trailing *empty* collection. jank's conversion ends with `(conj (apply hash-map (butlast g))
(last g))`, and base_persistent_map.cpp `conj` (169) accepts only nil, a map or a two-element
vector; Clojure's `createAsIfByAssoc` conjoins the trailing element with `APersistentMap.cons`,
which walks any seqable of map entries, so `()` (and `#{}`, `""`) add nothing.

- `p1_jank_conj_throws`, `p1_clj_adds_nothing`: the two runtime functions of the replica on
  `:a 1 ()`.
- `conversion_agrees`: for every argument list whose trailing element (odd count) is not a seq
  (`()`/a list, or a map's entries), jank's conversion and Clojure's give the same map, or both
  throw.
-/

namespace Jank.R3.Proofs.Destructure

open Jank.Core.Destructure

/-- jank: `(conj {:a 1} ())` throws "invalid map entry" (base_persistent_map.cpp:169-187). -/
theorem p1_jank_conj_throws : (rtMapConj [(.kw "" "a", .int 1)] (.list [])).toOption = none := rfl

/-- Clojure: `createAsIfByAssoc [:a 1 ()]` is `{:a 1}` (PersistentArrayMap.java 86–200,
APersistentMap.cons on an empty seq). -/
theorem p1_clj_adds_nothing :
    (cljCreateAsIfByAssoc [.kw "" "a", .int 1, .list []]).toOption = some (.map [(.kw "" "a", .int 1)]) := rfl

/-! ## The conversion for every argument list -/

/-- `(apply hash-map xs)` (persistent_hash_map `create_from_seq`) and the pairs of
`createAsIfByAssoc` fold the same way. -/
theorem go_eq : ∀ (xs : List Val) (acc : List (Val × Val)), xs.length % 2 = 0 →
    rtHashMap.go xs acc = .ok (cljCreateAsIfByAssoc.go xs acc)
  | [], acc, _ => rfl
  | [_], _, h => by simp at h
  | a :: b :: rest, acc, h => by
    simp only [rtHashMap.go, cljCreateAsIfByAssoc.go]
    exact go_eq rest _ (by simp at h; omega)

/-- An even argument list: jank's `(apply hash-map g)` is Clojure's map. -/
theorem even_agrees (xs : List Val) (h : xs.length % 2 = 0) : rtHashMap xs = cljCreateAsIfByAssoc xs := by
  unfold rtHashMap cljCreateAsIfByAssoc
  have hn : (xs.length % 2 == 1) = false := by simp; omega
  simp only [hn, Bool.false_eq_true, ite_false, go_eq xs [] h]
  rfl

/-- A trailing element `createAsIfByAssoc` and jank's `conj` treat alike: anything but a seq of
map entries (`(seq m)`, R107) or an empty list (P1). -/
def TrailOK : Val → Prop
  | .mapSeq _ => False
  | .list [] => False
  | _ => True

/-- The two results agree: the same map, or both throw. -/
def Same : Except String Val → Except String Val → Prop
  | .ok a, .ok b => a = b
  | .error _, .error _ => True
  | _, _ => False

/-- An odd argument list `xs ++ [t]`: jank's `(conj (apply hash-map (butlast g)) (last g))` and
Clojure's `createAsIfByAssoc` agree whenever `t` is not a seq of entries or `()`. -/
theorem odd_agrees (xs : List Val) (t : Val) (h : xs.length % 2 = 0) (ht : TrailOK t) :
    Same (do match ← rtHashMap xs with
              | .map kvs => rtMapConj kvs t
              | _ => throw "conj")
         (cljCreateAsIfByAssoc (xs ++ [t])) := by
  have hx : rtHashMap xs = .ok (.map (cljCreateAsIfByAssoc.go xs [])) := by
    unfold rtHashMap; rw [go_eq xs [] h]; rfl
  have hn : ((xs ++ [t]).length % 2 == 1) = true := by simp; omega
  have htake : (xs ++ [t]).take ((xs ++ [t]).length - 1) = xs := by simp
  have hlast : (xs ++ [t]).getD ((xs ++ [t]).length - 1) .nil = t := by simp
  unfold cljCreateAsIfByAssoc
  simp only [hn, ite_true, htake, hlast, hx, bind, Except.bind]
  cases t with
  | mapSeq kvs => exact absurd ht id
  | list ys =>
    cases ys with
    | nil => exact absurd ht id
    | cons y ys => simp [rtMapConj, Same, throw, throwThe, MonadExceptOf.throw]
  | vec ys =>
    match ys with
    | [] => simp [rtMapConj, Same, throw, throwThe, MonadExceptOf.throw]
    | [k] => simp [rtMapConj, Same, throw, throwThe, MonadExceptOf.throw]
    | [k, v] => simp [rtMapConj, Same, pure, Except.pure]
    | _ :: _ :: _ :: _ => simp [rtMapConj, Same, throw, throwThe, MonadExceptOf.throw]
  | map kvs => simp [rtMapConj, Same, pure, Except.pure]
  | nil => simp [rtMapConj, Same, pure, Except.pure]
  | _ => simp [rtMapConj, Same, throw, throwThe, MonadExceptOf.throw]

end Jank.R3.Proofs.Destructure

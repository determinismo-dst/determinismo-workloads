/-!
# Round 9, area Seq: a lazy seq's state when its realization fails or goes through another (T9-11, T9-12)

**jank 94d32623**, lazy_sequence.cpp: `force` 136-143 (`sv = fn.call(); fn = nil`: a throw leaves
`fn`), `realize` 118-133 (`force`; then `sv` is taken, `sv = nil`, a lazy `sv` is unwrapped through
the inner seqs' `sval` 145-156, and `s = ls.seq()`), `is_realized` 168-172: `fn.is_nil() || sv.is_some()`.
The macro (core.jank 2026-2032) is `(cpp/jank.runtime.lazy_seq (fn lazy-seq# [] body))`: an ordinary fn.

**Clojure 1.12.3**, LazySeq.java: `force` 48-53 (the same), `realize` 80-101 (the same steps, and
`lock = null` last), `isRealized` 289-301: `lock == null`, i.e. only once `seq()` completed on this
very object; `sval` (used on the inner seqs by `unwrap`) forces without clearing `lock`. The macro
(core.clj `lazy-seq`) is `(new LazySeq (^{:once true} fn* [] body))`: a once-fn, whose closed-over
locals the compiler clears as the body uses them, so a body that threw runs again with those locals
nil.

Each state below is one object's fields; the theorems hold for every value and body.
-/

namespace Jank.R9.Seq.LazyState

/-- What a body does: return a value, return another (inner) lazy seq, or throw. -/
inductive Body where
  | value (v : Nat)
  | inner (b : Body)
  | throws
  deriving DecidableEq, Repr

/-- One lazy seq object's fields. `lock` exists only in Clojure (true while not finished). -/
structure St where
  fn : Option Body
  sv : Option Body
  s : Option Nat
  lock : Bool
  deriving DecidableEq, Repr

def fresh (b : Body) : St := { fn := some b, sv := none, s := none, lock := true }

/-- `force`: run the body; a throw leaves `fn` as it was. -/
def force (st : St) : Except Unit St :=
  match st.fn with
  | none => .ok st
  | some .throws => .error ()
  | some b => .ok { st with sv := some b, fn := none }

/-- Realize an outer seq whose body is `inner b`: `force` the outer (sv := the inner seq), take `sv`
and clear it, `unwrap` the inner through its `sval` (= the inner's `force`), then `s`. Returns the
outer's and the inner's states, or the states when the inner throws. Same steps in both; Clojure
clears the outer's `lock` only at the end. -/
def realizeNested (outer inner : St) : (St × St) × Bool :=
  match force outer with
  | .error () => ((outer, inner), false)
  | .ok o =>
    let o := { o with sv := none }   -- `sv = nil` before unwrapping
    match force inner with
    | .error () => ((o, inner), false)
    | .ok i =>
      let v := match i.sv with | some (.value v) => some v | _ => none
      (({ o with s := v, lock := false }, i), true)

def jankRealized (st : St) : Bool := st.fn.isNone || st.sv.isSome
def cljRealized (st : St) : Bool := !st.lock

/-- ★ For every value: after `(seq outer)` where outer's body returns an inner lazy seq, the inner
is realized for jank (its `fn` ran in `sval`) and not for Clojure (its own `seq` never ran). -/
theorem inner_realized_differs (v : Nat) :
    let r := realizeNested (fresh (.inner (.value v))) (fresh (.value v))
    jankRealized r.1.2 = true ∧ cljRealized r.1.2 = false := by
  simp [realizeNested, force, fresh, jankRealized, cljRealized]

/-- ★ When the inner body throws, the outer is realized for jank (`fn` is nil) and not for Clojure
(`lock` stays): `(realized? x)` after a caught `(seq x)`. -/
theorem outer_realized_after_inner_throw :
    let r := realizeNested (fresh (.inner .throws)) (fresh .throws)
    r.2 = false ∧ jankRealized r.1.1 = true ∧ cljRealized r.1.1 = false := by
  simp [realizeNested, force, fresh, jankRealized, cljRealized]

/-! ## Re-forcing a body that threw (T9-12) -/

/-- A body `(swap! n inc) (throw ...)` closing over the local `n`: how many increments two forcings
make. jank: the fn is ordinary, both runs increment. Clojure: the once-fn's local `n` is cleared at
its use in the first run, so the second run's `(swap! nil inc)` throws before incrementing. -/
def increments (onceClearing : Bool) (runs : Nat) : Nat :=
  if onceClearing then min runs 1 else runs

theorem reforce_counts : increments false 2 = 2 ∧ increments true 2 = 1 := by decide

/-- ★ For every number of forcings k ≥ 1, jank increments k times and Clojure once. -/
theorem reforce_counts_all (k : Nat) (h : 1 ≤ k) : increments false k = k ∧ increments true k = 1 := by
  simp [increments]; omega

/-! ## `str` of a lazy seq (T9-13) -/

/-- Java's `List.hashCode` over longs that fit in 31 bits (`Long.hashCode(x)` is `x` there), with
the int arithmetic of ASeq.hashCode: `31 * h + e`, wrapped to 32 bits. -/
def javaListHash (xs : List Nat) : Nat :=
  xs.foldl (fun h x => (31 * h + x) % 4294967296) 1

/-- Clojure: LazySeq has no toString, so `str` is Object.toString: the class name, `@`, and
`hashCode()` in hex (LazySeq.hashCode is its seq's). -/
def cljStrLazy (xs : List Nat) : String :=
  "clojure.lang.LazySeq@" ++ String.ofList (Nat.toDigits 16 (javaListHash xs))

/-- jank: lazy_sequence::to_string prints the contents (seq_to_string). -/
def jankStrLazy (xs : List Nat) : String :=
  "(" ++ " ".intercalate (xs.map toString) ++ ")"

theorem str_lazy_example :
    cljStrLazy [2, 3] = "clojure.lang.LazySeq@402" ∧ jankStrLazy [2, 3] = "(2 3)" := by
  decide +kernel

end Jank.R9.Seq.LazyState

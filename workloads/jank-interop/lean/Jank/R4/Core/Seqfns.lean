/-!
# Round 4: functions jank implements differently from Clojure that agree

- **`cycle`** (core.jank 3150–3157): `(if-not (seq coll) '() (lazy-seq (concat coll (cycle coll))))`.
  Clojure 1.12: `(clojure.lang.Cycle/create (seq coll))`, element `i` is the `(i mod n)`-th of
  the seq. Proved: every prefix agrees, for every non-empty collection and length.
- **`nthrest`** (core.jank 2856–2865) against Clojure 1.12 (core.clj 3186–3200): jank walks
  `rest`; Clojure walks `rest` (or `IDrop.drop`, which returns the same elements) and turns an
  exhausted walk into `()`. Proved equal (both are `drop`) on every list and count.
- **`trim-newline`, `starts-with?`, `ends-with?`, `includes?`** (string.jank 195–271 →
  string_native.cpp 34–47, 356–383) work on UTF-8 bytes; Clojure on UTF-16 chars. Searched
  completely in `Search.lean`.
-/

namespace Jank.R4.Core.Seqfns

/-- jank's `cycle`, `take n` of it: `coll` then the cycle again (the lazy `concat`). -/
def jankCycleTake {α : Type} (xs : List α) : Nat → List α
  | 0 => []
  | n + 1 => (xs ++ jankCycleTake xs n).take (n + 1)

/-- Clojure's `Cycle`: element `i` is `xs[i mod n]`. -/
def cljCycleTake {α : Type} [Inhabited α] (xs : List α) (n : Nat) : List α :=
  (List.range n).map fun i => xs.getD (i % xs.length) default

/-- ★ `cycle`: every prefix of jank's lazy concatenation is Clojure's `Cycle`, for every
non-empty collection and every length. -/
theorem cycle_agrees {α : Type} [Inhabited α] (xs : List α) (hne : xs ≠ []) (n : Nat) :
    jankCycleTake xs n = cljCycleTake xs n := by
  have hlen : 0 < xs.length := by
    cases xs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  induction n with
  | zero => simp [jankCycleTake, cljCycleTake]
  | succ n ih =>
    rw [jankCycleTake, ih]
    apply List.ext_getElem
    · simp [cljCycleTake]; omega
    · intro i h1 h2
      simp only [List.getElem_take]
      simp only [cljCycleTake, List.length_map, List.length_range] at h2
      rw [List.getElem_append]
      split
      · next h =>
        simp [cljCycleTake, Nat.mod_eq_of_lt h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      · next h =>
        simp only [cljCycleTake, List.getElem_map, List.getElem_range]
        rw [Nat.mod_eq_sub_mod (a := i) (b := xs.length) (by omega)]

/-- jank's `nthrest` on a list (core.jank 2856–2865): `(seq coll)` of a non-empty list is the
list, an exhausted walk gives `(or (seq coll) ())`, i.e. `()`. -/
def jankNthrest {α : Type} : List α → Nat → List α
  | xs, 0 => xs
  | [], _ + 1 => []
  | _ :: t, n + 1 => jankNthrest t n

/-- Clojure 1.12's `nthrest` loop: `(if-let [xs (and (pos? n) (seq xs))] (recur (dec n) (rest xs))
(seq xs))`, then `(or … ())`. -/
def cljNthrest {α : Type} : List α → Nat → List α
  | xs, 0 => xs
  | [], _ + 1 => []
  | _ :: t, n + 1 => cljNthrest t n

theorem jankNthrest_drop {α : Type} (xs : List α) (n : Nat) : jankNthrest xs n = xs.drop n := by
  induction n generalizing xs with
  | zero => simp [jankNthrest]
  | succ n ih => cases xs <;> simp [jankNthrest, ih]

theorem cljNthrest_drop {α : Type} (xs : List α) (n : Nat) : cljNthrest xs n = xs.drop n := by
  induction n generalizing xs with
  | zero => simp [cljNthrest]
  | succ n ih => cases xs <;> simp [cljNthrest, ih]

/-- ★ `nthrest` agrees for every list and count. -/
theorem nthrest_agrees {α : Type} (xs : List α) (n : Nat) : jankNthrest xs n = cljNthrest xs n := by
  rw [jankNthrest_drop, cljNthrest_drop]

/-! ## Strings: bytes against chars -/

def utf8 (cs : List Char) : List UInt8 := (String.ofList cs).toUTF8.toList

/-- string_native.cpp `trim_newline` 356–383 on bytes. -/
def jankTrimNewline (bs : List UInt8) : List UInt8 :=
  (bs.reverse.dropWhile fun b => b == 10 || b == 13).reverse

/-- Clojure's `trim-newline` (string.clj): drop trailing `\n`/`\r` chars. -/
def cljTrimNewline (cs : List Char) : List Char :=
  (cs.reverse.dropWhile fun c => c == '\n' || c == '\r').reverse

def isPrefixB (a b : List UInt8) : Bool := b.take a.length == a
def isSuffixB (a b : List UInt8) : Bool := b.drop (b.length - a.length) == a
def isInfixB (a b : List UInt8) : Bool :=
  (List.range (b.length + 1)).any fun i => isPrefixB a (b.drop i)

def isPrefixC (a b : List Char) : Bool := b.take a.length == a
def isSuffixC (a b : List Char) : Bool := b.drop (b.length - a.length) == a
def isInfixC (a b : List Char) : Bool :=
  (List.range (b.length + 1)).any fun i => isPrefixC a (b.drop i)

end Jank.R4.Core.Seqfns

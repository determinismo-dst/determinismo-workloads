/-!
# Round 7, native values: `dotimes` and `loop` counters past 2^31 (R24's class)

jank (core.jank `dotimes` 2694-2709):

    `(let [n# (int ~n)] (loop [~i 0] (when (< ~i n#) ~@body (recur (unchecked-inc ~i)))))

- `(int n)` inlines to `to_int` (math.hpp 1409-1436): an `i64`, no range check (S40).
- The loop local `i` takes its init's C++ type, the literal `0`: `int` (cpp_util.cpp
  `literal_type` 628-648; `mutable_type` 1064-1090 keeps a builtin type; processor.cpp
  `analyze_let` 2370-2421).
- `(unchecked-inc i)` inlines to `unchecked_inc(object_ref)` (core.jank 1842-1848, math.cpp
  348-353): `i` is boxed and `make_box(data + 1ll)` returns an object.
- `recur` converts the argument into the local's type (processor.cpp `analyze_recur`):
  `convert<int>::from_object` = `static_cast<int>(o.to_integer())` (convert/builtin.hpp 236-245),
  modulo 2^32 (C++20 [conv.integral]).
- `(< i n#)` is `lt(int, i64)`: exact.

So after 2^31 - 1 the counter becomes -2^31, the test `(< i n#)` holds again, and for n ≥ 2^31
the loop never ends (the body sees negative counters). A `loop` with `(recur (inc i))` does the
same: `inc(int)` returns the exact `i64` (math.hpp 1184-1205) and the `recur` assignment into the
`int` local converts it modulo 2^32.

Clojure 1.12 (core.clj `dotimes`): `(let [n# (long ~n)] (loop [i 0] …))`, a primitive `long`
counter: `(dotimes [i n] …)` runs n times for every long n. Run on 1.12.3:
`(try (dotimes [i 2147483649] (when (neg? i) (throw (ex-info "w" {:i i})))) :done (catch Exception
e (:i (ex-data e))))` is :done in 0.6 s.
-/

namespace Jank.R7.Native.Loop

/-- `static_cast<int>` of an `i64` (modulo 2^32, two's complement). -/
def wrapI32 (v : Int) : Int :=
  if v % 4294967296 ≥ 2147483648 then v % 4294967296 - 4294967296 else v % 4294967296

/-- `f` applied k times. -/
def iter (f : Int → Int) : Nat → Int → Int
  | 0, x => x
  | k + 1, x => f (iter f k x)

theorem iter_succ (f : Int → Int) (k : Nat) (x : Int) : iter f (k + 1) x = f (iter f k x) := rfl

/-- One step of jank's counter: `recur (unchecked-inc i)` into the `int` local. -/
def jankStep (i : Int) : Int := wrapI32 (i + 1)

/-- One step of Clojure's counter: a primitive long (no wrap below 2^63 - 1). -/
def cljStep (i : Int) : Int := i + 1

theorem wrapI32_id (v : Int) (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) : wrapI32 v = v := by
  unfold wrapI32; split <;> omega

theorem wrapI32_lt (v : Int) : wrapI32 v < 2147483648 := by
  unfold wrapI32; split <;> omega

/-- ★ Below 2^31 the two counters agree: after k steps both are k. -/
theorem counter_agrees (k : Nat) (hk : k < 2147483648) : iter jankStep (k) 0 = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show jankStep (iter jankStep k 0) = _
    rw [ih (by omega)]
    unfold jankStep
    exact wrapI32_id _ (by omega) (by omega)

theorem clj_counter (k : Nat) : iter cljStep (k) 0 = k := by
  induction k with
  | zero => rfl
  | succ k ih => show cljStep (iter cljStep k 0) = _; rw [ih]; simp [cljStep]

/-- ★ After 2^31 steps jank's counter is -2^31 (Clojure's is 2^31). -/
theorem counter_wraps : iter jankStep (2147483648) 0 = -2147483648 := by
  rw [show (2147483648 : Nat) = 2147483647 + 1 from rfl, iter_succ,
    counter_agrees 2147483647 (by omega)]
  decide

/-- ★ For every n ≥ 2^31 (the `i64` from `(int n)`), the loop test `(< i n)` holds at every step:
jank's `dotimes` never ends, where Clojure's runs n times. -/
theorem never_ends (n : Int) (hn : 2147483648 ≤ n) (k : Nat) : iter jankStep (k) 0 < n := by
  cases k with
  | zero => show (0 : Int) < n; omega
  | succ k =>
    show wrapI32 (iter jankStep k 0 + 1) < n
    have := wrapI32_lt (iter jankStep k 0 + 1)
    omega

/-- ★ For every n < 2^31 jank's `dotimes` runs exactly n times, as Clojure's: the counter reaches
n after n steps and is below n before. -/
theorem agrees_below (n : Nat) (hn : n < 2147483648) :
    iter jankStep (n) 0 = n ∧ ∀ k < n, iter jankStep (k) 0 < n := by
  refine ⟨counter_agrees n hn, fun k hk => ?_⟩
  rw [counter_agrees k (by omega)]; omega

end Jank.R7.Native.Loop

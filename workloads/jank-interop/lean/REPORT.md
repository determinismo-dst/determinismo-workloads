# jank, modeled in Lean: where it departs from Clojure

This is a blind model of jank's C++ runtime at commit `f3d82d654`, written function by function. Beside it is a Lean model of Clojure 1.12's semantics for the same operation. Both are searched with `Determinismo` (decisions, `explore`, `exhaust`, `shrink`, `tape`, `Threads`, `History.linearizable`), and proved where the arithmetic allows (`bv_decide`, `decide`, `omega`).

**Sources read:**
- jank's tree at that commit (`upstream/`, plus its pinned `folly` and `immer` submodules), its book and its docs.
- The Clojure 1.12.0 sources (`clojure-ref/`) and docstrings.
- `sdk/lean`.

Nothing else was read.

**Every deviation is a hypothesis.** It is what the C++, read and modeled as written, predicts; jank was not built or run. Each one survived a second reading of the C++ path it cites. Paths below are under `upstream/compiler+runtime/`.

## Deviations at a glance

| # | Area | jank (predicted) | Clojure |
|---|---|---|---|
| D1 | `+ - *` | longs that fit i32 are combined as C++ `int`s and wrap at 2^31 | exact long |
| D2 | `/` | integer division truncates; i32 `MIN / -1` traps on x86-64 | ratio |
| D3 | `-'` | on overflow, boxes the wrapped i64 difference as a BigInt | exact BigInt |
| D4 | `quot` | goes through doubles; always returns a long | exact; a double for doubles |
| D5 | `==` | compares through doubles | longs exactly |
| D6 | `abs` | `(abs -0.0)` is -0.0 | +0.0 (docstring) |
| D7 | `bigdec` | a long goes through a double | exact |
| D8 | BigDecimal `=` | equal within 2^-52; not transitive | exact |
| D9 | NaN boxing | on x86-64 the hardware default NaN is read as a pointer to address 0 | NaN |
| D10 | `parse-long`, `parse-double` | `strtoll`/`strtod` grammar | `Long/valueOf` / `Double/valueOf` |
| D11 | `=` | a vector or list equals nil, sets, maps and strings; not symmetric | false |
| D12 | `hash` vs `=` | `1`/`1N`, `0.0`/`-0.0`, `()`/`(lazy-seq nil)`, `(seq m)`/entry vector are equal but hash differently | consistent |
| D13 | `hash-unordered-coll` | never the hash of the set of the same elements | equal |
| D14 | array-map transients | share the source map's array: `assoc!`, `dissoc!`, `into` mutate the original | original unaffected |
| D15 | transient vector | `nth` works after `persistent!` | throws |
| D16 | atom watches | a watch that adds or removes watches deadlocks; a nested `swap!` beside an `add-watch` can deadlock | no lock held |
| D17 | `compare-and-set!` | a single weak CAS that can fail spuriously (LL/SC builds) | strong |
| D18 | `alter-meta!` | read, apply, write: updates can be lost | synchronized |
| D19 | `delay` | a nil-returning body runs again; `realized?` false after nil or a throw | runs once |
| D20 | `deliver` | returns the promise on every call | the promise once, then nil |
| D21 | `deref` with timeout | returns nil at once | value or timeout-val |
| D22 | `future` bindings | frames outlive the thread under its OS id; a later thread reusing the id sees them | creator's frame only |
| D23 | `set!` in a future | allowed on a conveyed binding | throws |
| D24 | `try` | catch throws and finally throws: `std::terminate` | finally's exception propagates |
| D25 | `locking` | `monitor-enter` is not defined | works |

## Deviations in full

### D1. `+ - *` wrap at 32 bits for longs that fit i32

**C++ path:**
- `core/math.hpp: add(object_ref, object_ref)` (line 71) computes `make_box(typed_l->data + typed_r->data)` (line 86).
- A tagged small integer is visited as `small_integer_ref`, whose `data` is `i32` (`oref.hpp`: `i32 data{}` at line 2250; `operator->` returns `this` at line 1942).
- So `i32 + i32` is a C++ `int` addition, and it wraps before `make_box` sees the result.
- `sub` (line 200), `mul` (line 426) and unary `-` (which is `(- 0 x)`) do the same.

```clojure
(defn add [a b] (+ a b)) (defn mul [a b] (* a b)) (defn neg [a] (- a))
(add 2147483647 1)        ; Clojure 2147483648   jank -2147483648
(mul 65536 65536)         ; Clojure 4294967296   jank 0
(neg -2147483648)         ; Clojure 2147483648   jank -2147483648
(reduce + (range 100000)) ; Clojure 4999950000   jank 704982704
```

**Why this is not jank's documented overflow:**
- jank documents "signed integer overflow is well defined", but these sums are far inside the i64 range Clojure uses (theorem `small_add_fits_i64`).
- The wrong results are exactly the 32-bit-overflowing sums (`small_add_exact_iff`).
- `+'` is correct (`promoting_add_small_exact`).

**Search:** found by `exhaust` after 30 timelines; 143 of 1200 `+ - *` questions deviate.

### D2. `/` on integers is C++ integer division

**C++ path:** `core/math.hpp: div` (line 299) computes `make_box(typed_l->data / typed_r->data)` (line 314). There is no ratio for two integers.

```clojure
(defn div [a b] (/ a b))
(div 1 2)             ; Clojure 1/2         jank 0
(div -2147483648 -1)  ; Clojure 2147483648  jank SIGFPE on x86-64 (i32 idiv), -2147483648 on AArch64
```

**Search:** found by `explore` at seed 0; 271 of 400 `/` questions deviate. The book documents division by 0 as undefined, but not that `/` truncates.

### D3. `-'` overflow is wrapped

**C++ path:** `core/math.cpp: promoting_sub` (line 108) builds `native_big_integer l{l_val}`, then boxes `make_box<obj::big_integer>(l_val - typed_r->data)` (line 126), the i64 difference. Theorem `promoting_sub_overflow_wrong`: every overflowing case returns the wrong value.

```clojure
(-' -9223372036854775808 1)  ; Clojure -9223372036854775809N  jank 9223372036854775807N
```

### D4. `quot` through doubles

**C++ path:** `core/math.cpp: quot` (line 321) computes `make_box(static_cast<i64>(to_real(l) / to_real(r)))` (line 338).

```clojure
(quot 9007199254740993 1)       ; Clojure 9007199254740993     jank 9007199254740992
(quot 7.5 2)                    ; Clojure 3.0                  jank 3
(quot -9223372036854775808 -1)  ; Clojure -9223372036854775808 jank 9223372036854775807 on AArch64 (UB cast)
```

**Search:** 38 of the 400 long pairs deviate on x86-64.

### D5. `==` through doubles

**C++ path:** `core/math.cpp: is_equiv` (line 469) converts both operands to doubles and compares them (line 482).

```clojure
(== 9007199254740993 9007199254740992)  ; Clojure false  jank true
```

### D6. `(abs -0.0)` is -0.0

**C++ path:** `core/math.hpp: abs`, object_ref branch (line 1016), tests `data < 0ll`, which is false for -0.0, so the value is returned unchanged.

```clojure
(defn f [x] (abs x)) (str (f -0.0))  ; Clojure "0.0"  jank "-0.0"
```

### D7. `bigdec` of a long goes through a double

**C++ path:** `core/math.cpp: to_big_decimal` (line 803) builds `make_box<obj::big_decimal>(typed_o->to_real())`.

```clojure
(bigdec 9007199254740993)  ; Clojure 9007199254740993M  jank 9007199254740992M
```

### D8. BigDecimal `=` uses an epsilon

**C++ path:** `obj/big_decimal.cpp: equal` (line 154) returns `abs(a - b) < numeric_limits<f64>::epsilon()`. Theorems: `bigdec_eq_epsilon`, `bigdec_eq_not_transitive`.

```clojure
(= 1M 1.0000000000000000001M)  ; Clojure false  jank true
(= 0M 0.00000000000000015M)    ; Clojure false  jank true; also 0.00000000000000015M = 0.0000000000000003M in jank, but 0M ≠ 0.0000000000000003M
```

### D9. On x86-64, the default NaN crashes jank

**C++ path:**
- `oref.hpp`: a double is stored as its raw bits (`tag(f64)`, line 194, a `bit_cast` with no canonicalization).
- A word counts as a real only if `bits < 0xFFF8000000000000` (`max_real` at line 94, check at line 113).
- x86-64 SSE's default NaN is exactly `0xFFF8000000000000`. It comes from `∞-∞`, `0/0` and `0·∞`.
- That word is neither a real nor a tagged integer nor a tagged pointer, so `get_type()` and `to_string()` read `ptr()`, which `as_pointer` (line 142) masks to address 0.

Theorems: `real_decoded_iff`, `misdecoded_are_negative_nans`, `x86_default_nan_is_null_object`, `arm_default_nan_is_real`.

```clojure
(defn sub [a b] (- a b)) (defn div [a b] (/ a b))
(sub ##Inf ##Inf)  ; Clojure ##NaN   jank x86-64: segfault (null object); AArch64: ##NaN
(div 0.0 0.0)      ; same, although the book says "Division by floating point 0.0 is well defined"
```

### D10. `parse-long` and `parse-double` follow `strtoll`/`strtod`

**C++ path:** `core/math.cpp: parse_long` (678, `std::stoll` at 689) and `parse_double` (712, `std::stod` at 723).

```clojure
(parse-long " 5")       ; Clojure nil    jank 5
(parse-double "inf")    ; Clojure nil    jank ##Inf
(parse-double "1.5 ")   ; Clojure 1.5    jank nil
(parse-double "1.5d")   ; Clojure 1.5    jank nil
(parse-double "1e400")  ; Clojure ##Inf  jank nil
(parse-double "1e-400") ; Clojure 0.0    jank nil
```

**Search:** over all 1111 strings of length ≤ 3, 5 `parse-long` and 25 `parse-double` results deviate.

### D11. `=` matches non-sequential seqables; it is not symmetric

**C++ path:**
- `persistent_vector::equal` (persistent_vector.cpp 91) falls back to `seq.cpp: sequence_equal` (872).
- `sequence_equal` only requires both sides to be seqable (879), and nil, strings, sets and maps are seqable.
- `persistent_list::equal` goes through `seq_ext.hpp: equal` (16), which excludes only nil.

```clojure
(= [] nil)   ; Clojure false  jank true   (and (= nil []) is false)
(= [] #{})   ; Clojure false  jank true
(= '() {})   ; Clojure false  jank true
(= [1] #{1}) ; Clojure false  jank true   (and (= #{1} [1]) is false)
(= [\a] "a") ; Clojure false  jank true
```

**Search:**
- `exhaust` found `(= [] nil)` after 6761 timelines and the asymmetry after 11.
- Over 645² value pairs, 1034 disagree with Clojure and 1772 are asymmetric.

### D12. Equal values with different hashes

| Pair | jank hashes | Cause |
|---|---|---|
| `1` / `1N` | 1392991556 / 2654435770 | `big_integer::to_hash` (155) is boost's `hash_combine` of the limbs, not Murmur3 `hashLong` |
| `0.0` / `-0.0` | 0 / 2147483648 | `hash::real` (hash.cpp 116) hashes the bits; Clojure 1.12 hashes -0.0 as 0 |
| `(lazy-seq nil)` / `()` | 1 / 2277397642 | `lazy_sequence.cpp` line 103 returns 1 for an empty seq |
| `(seq {:a 1})` / `[[:a 1]]` | 2767208205 / 1242899341 | `base_persistent_map_sequence::to_hash` uses `hash::unordered` (line 86) |

```clojure
(count (hash-set 1 1N))              ; Clojure 1     jank 2
(get (hash-map 1N :a) 1)             ; Clojure :a    jank nil
(contains? #{0.0} -0.0)              ; Clojure true  jank false
(count (hash-set [] (lazy-seq nil))) ; Clojure 1     jank 2
```

**Search:** `exhaust` found `1`/`1N` after 1356 timelines; 1858 equal pairs have different hashes. Theorems: `negzero_hashes`, `mapseq1_ne_vector1`.

### D13. `hash-unordered-coll` is never the set's hash

**C++ path:**
- `core.jank` (6574) calls `core.cpp: hash_unordered` (1369), which calls `hash.cpp: unordered(object_ref)` (181).
- That function starts the sum at 1 (line 186); sets start at 0.
- For a non-`sequence_like` argument such as a vector, it returns that object's own ordered hash.

```clojure
(= (hash-unordered-coll '(1 2)) (hash #{1 2}))  ; Clojure true  jank false
(= (hash-unordered-coll [1 2]) (hash #{1 2}))   ; Clojure true  jank false
```

Theorem `unorderedSeq_ne_unorderedRange`: for every list of element hashes, the two never agree, because `mix_collection_hash` is injective (`mix_injective`).

### D14. A transient array map writes into its persistent source

**C++ path:**
- `persistent_array_map::to_transient` (108–110) calls the `transient_array_map(native_array_map const&)` constructor, which does `data{d}` (24–26).
- The copy constructor is defaulted (native_array_map.hpp 33), so the transient shares the source map's array.
- `insert_or_assign` writes `data[i+1] = val` in place (147/159).
- `erase` shifts entries in place (178/196).

```clojure
(let [m {:a 0 :b 1} t (transient m)] (assoc! t :a 2) m) ; Clojure {:a 0, :b 1}  jank {:a 2, :b 1}
(let [m {:a 0 :b 1} t (transient m)] (dissoc! t :a) m)  ; Clojure {:a 0, :b 1}  jank {:b 1, :b 1}
(let [m {:a 1}] (into m {:a 2}) m)                      ; Clojure {:a 1}        jank {:a 2}
```

**Search:**
- `explore` found it after 118 timelines and `exhaust` after 1145. Story: `m1 = {:a 0, :b 1}; t0 = (transient m1); (assoc! t0 :a 2)` leaves `m1` as `{:a 2, :b 1}`.
- With `to_transient` cloning instead, `exhaust` is complete over 33,849 timelines with no violation.
- Theorems: `assoc_bang_changes_source`, `dissoc_bang_changes_source`.

### D15. Transient vector `nth` after `persistent!`

**C++ path:** `transient_vector.cpp: nth` (line 53) has no `assert_active()`. Clojure's `nth` calls `ensureEditable`.

```clojure
(let [t (transient [7])] (persistent! t) (nth t 0))  ; Clojure throws  jank 7
```

### D16. Watches run under the watches lock

**C++ path:**
- `atom.cpp: notify_watches` (43) holds `watches.rlock()` (45) while it calls each watch.
- `add_watch` and `remove_watch` (249, 255) take `wlock()`.
- folly's `SharedMutex` is non-reentrant and gives writers priority (SharedMutex.h 1421).

```clojure
(def a (atom 0))
(add-watch a :once (fn [k r _ _] (remove-watch r k)))
(reset! a 1)   ; Clojure 1   jank hangs (single thread, 0 decisions)

(def b (atom 0))
(add-watch b :w (fn [_ r _ n] (when (< n 2) (swap! r inc))))
(future (add-watch b :j (fn [& _])))
(swap! b inc)  ; Clojure 2   jank can hang
```

**Search:** `exhaust` found the second case after 232 timelines; the Clojure mode is complete over 53,815 with nothing found. The shrunk tape is 15 × `thread.next=0`, then `1`, then `0`. Story:
1. Thread 0's `swap!` sets 0→1 and takes the shared watches lock.
2. Its watch `swap!`s 1→2.
3. Thread 1 announces a writer (`add-watch`).
4. Thread 0's nested shared lock blocks behind that writer.
5. Thread 1's exclusive lock blocks behind thread 0's shared lock. Deadlock.

### D17. `compare-and-set!` is one weak CAS

**C++ path:** `atom.cpp: compare_and_set` (215, `compare_exchange_weak` at 220).

```clojure
(compare-and-set! (atom 0) 0 1)  ; Clojure true   jank: rarely false on AArch64 LL/SC builds
```

**Search:** the tape `{"name":"cpu.cas_spurious","options":2,"value":1}` gives a non-linearizable history. Two racing CASes from 0 can both fail (`exhaust` after 421). On x86-64 the search is complete with nothing found.

### D18. `alter-meta!` is not atomic

**C++ path:** `core.jank` 1235–1243 does `; TODO: Atomics. (reset-meta! o (apply f (meta o) args))`.

```clojure
(def a (atom 0))
(run! deref (doall (for [_ (range 8)] (future (dotimes [_ 1000] (alter-meta! a update :n (fnil inc 0)))))))
(:n (meta a))  ; Clojure 8000  jank possibly less
```

**Search:** with two threads, the tape `thread.next` = 1, 0, 0 gives `:n` = 1.

### D19. `delay` treats nil as not realized

**C++ path:**
- `delay.cpp: deref` (19) checks `if(val.is_some())` (22) before running `val = fn.call()` (34).
- `val` starts as nil, so a nil result is never cached.
- `is_realized` is `val.is_some()` (52).

```clojure
(def d (delay (println "running") nil))
@d @d          ; Clojure prints once   jank prints twice
(realized? d)  ; Clojure true          jank false (also false after a body that threw)
```

### D20. `deliver` returns the promise every time

**C++ path:** `promise.cpp: call` (24–33) returns `this` whether or not it delivered.

```clojure
(let [p (promise)] (deliver p 1) (deliver p 2))  ; Clojure nil  jank #<promise>
```

### D21. `deref` with a timeout returns nil

**C++ path:** `core.jank` 1095–1096: the 3-arity body is commented out (`; TODO: Blocking.`), so it returns nil.

```clojure
(deref (promise) 10 :timeout)  ; Clojure :timeout  jank nil
```

### D22. A dead future's bindings leak to a thread that reuses its id

**C++ path:**
- `core.cpp: future` (1091) pushes bindings on the new thread (1126) and never pops them.
- `context.cpp: push_thread_bindings` (706) keys frames by `std::thread::id` (711) and starts each new frame from the existing front frame (714).

```clojure
(def ^:dynamic *x* :root)
(binding [*x* :one] @(future nil))
@(future *x*)   ; Clojure :root   jank :one when the second thread gets the first's id
```

**Search:** the tape includes `{"name":"os.thread_id","options":2,"value":1}`. Thread-id reuse is allowed by POSIX and common with glibc. The Clojure mode is complete over 576 timelines.

### D23. `set!` of a conveyed binding works in a future

**C++ path:** a conveyed binding is re-boxed with the future's own thread id (context.cpp 738), so the thread check in `var.cpp` (123) passes. Theorem `set_in_future`.

```clojure
(def ^:dynamic *x* 1)
(binding [*x* 2] @(future (set! *x* 3) *x*))  ; Clojure throws  jank 3
```

### D24. try: a catch that throws and a finally that throws

**C++ path:**
- The generated code (`cpp_processor.cpp` 1054–1138) puts `finally` in a `scope_exit` guard (1137).
- When a matching `catch` handler throws, the guard's destructor runs `finally` during unwinding.
- `~scope_exit` (scope_exit.cpp 19–28) is implicitly `noexcept`, so a throw from `finally` there calls `std::terminate`.

```clojure
(try (try (throw (ex-info "a" {}))
          (catch cpp/jank.runtime.object_ref e (throw (ex-info "b" {})))
          (finally (throw (ex-info "c" {}))))
     (catch cpp/jank.runtime.object_ref e (ex-message e)))
; Clojure "c"   jank std::terminate
```

Theorem `only_handler_and_finally_throwing`: across every body/catch/handler/finally shape, this is the only disagreement. `exhaust` found it after 18 timelines.

### D25. `locking` cannot compile

**C++ path:** `core.jank: locking` (5088) expands to `monitor-enter` and `monitor-exit` (5095), which are defined nowhere in jank. Found by reading; there is no model.

```clojure
(locking :lock 1)  ; Clojure 1   jank: unable to resolve monitor-enter
```

## What was modeled

Each row gives the C++ code, the Lean definitions for jank, and the Lean definitions for the Clojure spec. Files are under `Jank/`.

| Area | jank C++ → Lean | Clojure spec in Lean |
|---|---|---|
| **Numbers** (`Numbers.lean`) | `make_box` → `makeBoxI64`; the `small_integer` oref → `JNum.small (BitVec 32)`; `math.hpp` add/sub/mul → `jankIntOp`; `promoting_*` → `jankPromotingOp`; `div` → `jankIntDiv`; `quot` → `jankQuot`/`castF64ToI64`; `is_equiv` → `jankEquiv`; `abs` → `jankAbsReal`; `to_big_decimal` → `jankBigdecOfLong`; `big_decimal::equal` → `jankDecEq`; `rem` → `jankRemI64`; oref tagging (`max_real`, `is_tagged_*`, `as_pointer`, `tag`) → `decode` and helpers; `parse_long`/`parse_double` → `jankParseLong`/`jankParseDouble` | `Clj.intOp`, `Clj.promotingOp`, `Clj.intDiv`, `cljQuot`, `cljEquiv`, `cljAbsReal`, `cljBigdecOfLong`, `cljDecEq`, `cljParseLong`, `cljParseDouble`; `isNaN64` for IEEE |
| **Hashing** (`Hash.lean`) | hash.cpp `rotate_left`, `fmix`, `mix_k1`, `mix_h1`, `mix_collection_hash`, `combine`, `integer`, `real`, `string`, `ordered`/`unordered` in both forms; `immutable_string::to_hash`; symbol, keyword and `big_integer::to_hash` | Murmur3.java (`hashLong`, `mixCollHash`, `hashOrdered`, `hashUnordered`), `Numbers.hasheq` for Double and BigInt |
| **Equality** (`Equality.lean`) | `jankEq` (each type's `equal`, `sequence_equal`, `seq_ext::equal`, immer lookup `containsH`, array-map `find` as `lookupA`); `jankHash` (each `to_hash`); `obj_behaviors` → `seqable`/`elements` | `cljEq` (`Util.equiv`, `Numbers.equal`, `APersistentVector.doEquiv`, `ASeq.equiv`, `LazySeq.equals`, set and map `equiv`) |
| **Vector** (`Vector.lean`) | `get`, `nth`, `contains`, `assoc`, `pop`, `subvec`; transient `nth` → `tNth` | documented laws (as theorems); `cTNth` |
| **Array map** (`ArrayMap.lean`) | `make_next_array`, `insert_unique`, `insert_or_assign`, `erase`, `clone`, the shallow copy constructor; persistent and transient `assoc`, `dissoc`, `to_transient`, `to_persistent` | association lists |
| **Atom** (`Atom.lean`, `Sync.lean`) | swap/reset/compare_and_set/notify_watches/add_watch/remove_watch/validate as `Instr` steps; folly `SharedMutex`; `alter-meta!` → `metaStep` | Clojure mode: strong CAS, snapshot watches with no lock, synchronized `alterMeta` |
| **delay, promise** (`Delay.lean`) | `delay::deref`/`is_realized`, `promise::call`/`deref`, the 3-arity `deref` | `Delay.realize`/`isRealized`, core.clj `promise` |
| **Bindings** (`Bindings.lean`) | `push_thread_bindings`, `pop_thread_bindings`, `get_thread_bindings`, `var::deref`/`set`, `future` | `binding-conveyor-fn`, `resetThreadBindingFrame`, `Var.set` |
| **try** (`Try.lean`) | the generated try/catch/`catch(...)` plus `scope_exit` | JVM try/catch/finally |

## Assumptions and simplifications

- **A1. Signed overflow wraps.** Modeled as two's complement (`BitVec`), as the book documents. Where C++ is undefined, the model flags it: integer division by 0, `INT_MIN / -1`, an out-of-range double→i64 cast, shifts ≥ 64.
- **A2. Documented differences are not deviations.** A long overflow, where Clojure throws, and integer division by 0 may give any jank answer without being flagged.
- **A3. immer is abstracted.** Its vector, map and set internals are not modeled: vectors are `List`s, and sets keep insertion order (order-sensitive examples use only singletons). Hash lookup is modeled as "same hash, then `equal`".
- **A4. Standard-library and boost layout.** `std::hash<u64>` is the identity on libc++ and libstdc++; boost limbs are 64 bits; `size_t` is 64 bits.
- **A5. Hardware.**
  - The x86-64 default NaN is `0xFFF8…`; the AArch64 default NaN is `0x7FF8…`.
  - An out-of-range double→i64 cast gives `0x8000…` on x86-64 and saturates on AArch64.
  - Spurious weak-CAS failures happen only on LL/SC builds (AArch64 without LSE).
- **A6. Programs pass values through function parameters.** This forces the `object_ref` overloads that the model covers; the analyzer may type literal arguments differently.
- **A7. Threads granularity.** One step is one lock acquire or release, one atomic operation, or one user-function call taken as its effect only. `wlock()` is two steps: announce (which blocks new readers, write priority), then acquire. Condition-variable waits are modeled as blocked threads.
- **A8. Thread ids.** A new thread's id is a world decision: fresh, or the id of a joined thread.
- **A9. Equality universe.** The atoms are nil, 0, 1, 1N, 0.0, -0.0, "", "a", \a, :a; collections hold 0–2 atoms each. Keywords compare by name.
- **A10. Clojure quirks are not the spec.** For example, `get` truncating a long key with `intValue` is ignored.
- **A11. parse-double results.** Only the result class is modeled (nil, finite, ##Inf or ##NaN), not the value. `ERANGE` on overflow or underflow makes jank return nil.
- **A12. try.** One `catch` clause, matched by exception name.
- **A13. BigDecimal.** Decimals are exact rationals n/10^s, and epsilon is exactly 2^-52.

## Properties checked

- **Arithmetic:** jank's result equals Clojure's whenever Clojure returns without an overflow or divide-by-zero exception.
- **Equality:** jank's `=` matches Clojure's; `=` is symmetric; `=` implies equal hashes.
- **Persistence:** a persistent map never changes after it is created.
- **Atoms:** no deadlock; histories are linearizable against a register.
- **`alter-meta!`:** loses no update.
- **delay:** the body runs at most once, and the delay is realized after a deref.
- **promise:** exactly one `deliver` returns the promise; a timed `deref` returns the value or timeout-val.
- **futures:** a future sees exactly its creator's bindings.
- **try:** the outcome is the JVM's.

## Search runs

`explore n` uses seeds 0..n-1. "Complete" means every timeline within the bounds was run.

| World | explore | exhaust | Clojure mode, fix or table |
|---|---|---|---|
| Arithmetic | 3000 seeds: found at seed 0 | found after 30 | 479 of 2800 questions deviate (`+'` and `*'`: 0) |
| `==` and `quot` over 20² longs | — | — | 4 and 38 pairs deviate |
| Parse strings ≤ 3 chars (1111) | — | — | 5 and 25 deviate |
| Equality: agrees with Clojure | 3000: found after 16 | found after 6761 | 1034 of 416,025 pairs disagree |
| Equality: symmetric | found after 16 | found after 11 | 1772 asymmetric pairs |
| Equality: hash-consistent | found after 16 | found after 1356 | 1858 pairs equal with different hashes |
| Array map, 3 operations | 3000: found after 118 | found after 1145 | with cloning: complete, 33,849 timelines, nothing |
| Self-removing watch | found (0 decisions) | found after 1 | complete, nothing |
| Watch that `swap!`s plus `add-watch` | 2000: nothing | found after 232 | complete, 53,815, nothing |
| `compare-and-set!` on a fresh atom (LL/SC) | found after 2 | found after 2 | x86-64 and Clojure: complete |
| Two `compare-and-set!` from 0 (LL/SC) | found after 97 | found after 421 | x86-64: complete, 4228; Clojure: complete, 2116 |
| Two `swap! inc` | nothing | x86-64: complete, 217,500; LL/SC: stopped at 500,000 | Clojure: complete, 48,610 |
| Two `swap! inc` plus `deref` | nothing | stopped at 500,000, nothing | — |
| `alter-meta!`, 2 threads | found after 2 | found after 2 | complete |
| delay, nil body / throwing body | found | found after 1 | complete, 168 |
| delay, value body | nothing | complete | — |
| promise, two `deliver`s / timed `deref` | found after 1 | found after 1 | complete, 40 / 10 |
| futures and thread ids | 200: found after 2 | found after 49 | complete, 576 |
| try | 500: found after 2 | found after 18 | theorem |

## Theorems proven (48 including helper lemmas; no `sorry` or `native_decide`)

- **Numbers:** `small_add_exact_iff`, `small_add_fits_i64`, `promoting_add_small_exact`, `promoting_sub_overflow_wrong`, `jank_rem_eq_java` (jank's `rem` is Java's `%` for all i64 pairs), `shift_in_range_java`, `real_decoded_iff`, `misdecoded_are_negative_nans`, `x86_default_nan_is_null_object`, `arm_default_nan_is_real`, `small_int_roundtrip`, `bigdec_eq_epsilon`, `bigdec_eq_not_transitive`.
- **Hash:**
  - `mixK1_eq`, `mixH1_eq`, `fmix_eq`, `integer_eq_hashLong`: jank's integer hash is Clojure's for all inputs.
  - `inverses`, the 11 `step*_inj` lemmas, `mixCollectionHash_steps`, `mix_injective`.
  - `unorderedSeq_ne_unorderedRange`, `mapseq1_ne_vector1`, `negzero_hashes`.
- **Vector:** `get_in_range`, `get_out_of_range`, `contains_iff`, `nth_some_iff_contains`, `assoc_count`, `assoc_get`, `pop_conj`, `subvec_length`, `transient_nth_after_persistent`.
- **Array map:** `assoc_bang_changes_source`, `dissoc_bang_changes_source`.
- **Try:** `only_handler_and_finally_throwing`.
- **Bindings:** `set_in_future`.

## Checked and agreeing

- `+'` and `*'` on longs; `inc`/`dec`; `rem` (theorem); `mod`.
- Long and ASCII-string hashes equal Clojure's.
- `swap!` is linearizable (complete over 217,500 timelines on x86-64).
- `reset!` has the same load-then-store race as Clojure's `Atom.reset`.
- Lazy-seq locking matches Clojure's; hash map and hash set transients are safe (immer `transient()`).
- Vector bounds checks satisfy Clojure's documented laws (theorems).

## Library gaps filled in the project

- **No locks:** `Threads` has none, so `Jank/Sync.lean` adds folly's write-priority `SharedMutex` and `std::mutex`.
- **`.done` doesn't unblock waiters:** in `interleave`, a step that returns `.done` does not clear the blocked set, so a thread's lock-releasing last step must return `.ran`; otherwise a false deadlock is reported.
- **Spawning threads:** futures are spawned by pushing onto `Process.threads` from inside a step.
- **No Threads story:** `Threads` doesn't write `Process.log`; the atom model logs each step and `storyOf` replays a tape into a story.
- **Linearizability:** `OpRec` histories are built from step stamps so `History.linearizable` can be used.
- **First counterexample only:** `exhaust` stops at the first and doesn't shrink it; full tables use plain enumeration, and `report` shrinks exhaust results.
- **`Float` is opaque to `decide`/`bv_decide`:** proofs about doubles are done on their bit patterns.

## Notes: latent issues not reported as deviations

- **Self-deadlock in the no-argument `push_thread_bindings()`** (context.cpp 678–692): it holds `rlock()`, then folly's non-const `operator->` takes the exclusive lock. Its only caller is never used.
- **Platform-dependent symbol and keyword hashes:** `hash::string` widens `char`, so non-ASCII symbol and keyword hashes differ between platforms.
- **Agents and refs/STM are unported** ("TODO: port"), so they could not be checked.

# REPORT-6: jank 94d32623 compared with Clojure 1.12, round 6

**Version.** jank main is still `94d32623e3e6f0f40c412d41802fe02693aec094` (checked by the coordinator today), the tree of round 5's `upstream-r5/`. Its `compiler+runtime/` is byte-identical to 7135b7708, the commit the real jank was tested at. Every jank path below is under `upstream-r5/compiler+runtime/`.

**Libraries.** Rounds 1–5's pinned sources, plus libstdc++ 15.3.0's `locale_conv.h` and `codecvt.cc` (the UTF-8 decoder behind jank's `upper-case`/`lower-case`), fetched from GCC's releases/gcc-15.3.0 into `deps/libstdcxx-15.3.0-codecvt/` and added to `fetch-sources.sh`.

**Status.** Every item is a hypothesis from Lean replicas, re-read against the source. jank was not built or run. Every Clojure result was run on Clojure 1.12.0.

**Who did what.**
- Five area agents worked in parallel:
  - numbers on boxed and literal values, overflow (N);
  - native values reaching Clojure operations (P);
  - strings and characters (W);
  - CHAMP's remaining laws (H);
  - the nREPL's T7, T3 and T9 (Q).
- Three fix agents wrote the local fixes of rounds 1–2 (F1), 3–4 (F2) and 5 (F3); N, P and W wrote those of their own areas and LG1–LG3. A merge agent built one combined patch.
- I wrote the brief check (`jank6-coord`: the brief's seven observations put to the replica), kernel-only proofs of area P's eight `bv_decide` theorems, the test merge, the Clojure check, the fixes' conflict map, and this report.
- Area reports: `results/r6-<area>-report.txt` (num, native, str, champ, nrepl, fix1, fix2, fix3); `fixes/combined/README.txt`.

**Build.**
- `lake build` of the six round-6 targets (`jank6-num`, `-native`, `-str`, `-champ`, `-nrepl`, `-coord`) succeeds: 266 jobs. Round 6 adds 30 Lean files (7,898 lines) under `Jank/R6/` and `Run/R6/`.
- No `sorry`, no `native_decide`, no new axiom in a proof this report relies on. Area P proved eight theorems with `bv_decide`, whose proofs add a per-proof axiom (its LRAT certificate checked by compiled code); `Jank/R6/Coord/NativeKernel.lean` proves the same eight statements (checked to have exactly P's types) by `omega`, so every main theorem rests on `propext`, `Classical.choice` and `Quot.sound` only (`results/r6-*-axioms.txt`).
- The directory grew by about 0.4 GB this round (1.1 GB to 1.5 GB), mostly `.lake` build products.

## 1. The lesson of LG1–LG3

The generated differential tests (random clojure.core forms against Clojure 1.12) found three deviations on the real jank that no round reported. For each, why the replica missed it, read from the earlier rounds' own files:

**LG1 (`count`'s `usize` in `<`, `min`, `max`).**
- `count` inlines to `cpp/jank.runtime.sequence_length` (core.jank 186–192), which returns `usize` (core/seq.hpp 132, seq.cpp 837).
- Round 2's analyzer replica had no unsigned type: its C++ type universe is `objectRef`, `typed`, `bool`, `int`, `long`, `double`, `cstr`, `void` and an opaque `other` (`Jank/Analyzer/Types.lean` 18–34). A `usize` was `other`, so no search could draw an unsigned comparison.
- Round 3's native-values world (`Jank/R3/Codegen/Native.lean`) modeled the inline arithmetic, but only `+ - * / <` over int, long and double literals and `^cpp/int|long|double` parameters. It drew neither `count` nor `min`/`max`.
- So the class was outside every model's universe, not outside its reach in the code.

**LG2 (long overflow).**
- Round 1's assumption A2 ("Documented differences are not deviations. A long overflow, where Clojure throws, … may give any jank answer without being flagged") rested on jank's book, differences-from-clojure.md 56: "Signed integer overflow is well defined and will wrap".
- Round 3 repeated it for emitted code: "64-bit wrap is the documented behavior" (`results/r3-codegen-report.txt` 100).
- Only overflow inside the i64 range (round 1's D1, round 2's R25: the 32-bit wraps) was reported.
- The real jank does not even do what the book says: `inc` throws, `dec` of a BigInt literal gives a BigInt, `*` wraps. An assumption that silenced a disagreement with Clojure is what hid it. This round drops A2: Clojure's behavior is the property, and the book's sentence is a note on the deviation.

**LG3 (`subs` indexes bytes).**
- Round 2 predicted it: R52 names `subs` with `(subs "é" 0 1)` (Clojure "é", jank "\xC3"), path core.cpp `subs` 398/411.
- Its test b01 asserted `(subs "é" 0 1)` as its fifth assertion. The runner's evidence records only b01's first failure (`(count "é")` is 2), so subs's own result was never recorded.
- b03 (`(seq (subs "aé" 0 2))`) failed with "Invalid UTF-8 string", which is what byte-indexed `subs` predicts.
- So LG3 is R52's `subs` part, found again. The lesson here is about tests: one assertion per prediction, so a run records each.

**What this round changed because of it.**
- Rule: an assumption that hides a disagreement with Clojure is not allowed. Clojure 1.12's behavior is the property; a jank document that says otherwise is a note on the deviation (round 1's A2 and A6 and round 2's "documented" string notes are replaced, section 7).
- Every value is followed to where a program sees it. Area P's type universe has every C++ arithmetic type (`bool`, the `char`s, `short`, `int`, `long`, `long long` and their unsigned forms, `float`, `double`), with ranks, promotions, the usual arithmetic conversions and `std::common_type` (`Jank/R6/Native/Types.lean`), and every producer of a native number a plain program can write: `count`, `alength`, `hash`, `int`, `float`, bit operations, typed-array elements, inlined predicates.
- Every test says which path it runs (inlined with literals, `let`-bound, or through a fn value), and tests each path that deviates. Round 1's d03 shows why: it wrote the literal `-9223372036854775808`, which jank reads as a BigInt, so it never reached the bug it predicted (V54).

**The brief's observations, put to this round's replica** (`lake exe jank6-coord`, `results/r6-coord-brief.txt`). Each row is the real jank's value, then the replica's prediction:
- `(< -1 (count [1]))`: false, false.
- `(max (count [1]) -1)`: -1, -1.
- `(min (count [1 2 3]) -1)`: 3, 3.
- `(< -1 (long (count [1])))`: true, true.
- `(* -3 9223372036854775807)`: -9223372036854775805, -9223372036854775805.
- `(dec -9223372036854775808)`: -9223372036854775809N, -9223372036854775809N.
- `(subs "é-è" 2)`: "-è", "-è" (also the kernel-checked `lg3_model`).
All seven agree. Clojure gives true, 1, -1, true, an ArithmeticException, an ArithmeticException and "è".

## 2. Deviations at a glance

Clojure's result comes first, then jank's. LG1–LG3 keep the brief's names and are extended; V49 onwards continue round 5's numbering. D, R, S, U and V below 49 refer to earlier rounds. Each item has a test in `tests/jank_lean/deviations_r6_test.jank` (section 13).

**Long overflow and the long minimum (area N):**
- **LG2** (extended to every path) `(* -3 9223372036854775807)`, and `+`, `-`, `*` with let-bound literals, fn parameters, a literal and a parameter, and `(- Long/MIN_VALUE)`: ArithmeticException vs a wrapped value. `(dec -9223372036854775808)`: ArithmeticException vs -9223372036854775809N, since the literal reads as a BigInt (R5). lg2, lg2b–lg2f.
- **V53** (extends R25, D1) two `let`-bound `int`s: `(* a a)` with a = 65536 is 4294967296 vs 0. v53.
- **V54** (D3, re-tested; round 1's test could not reach it) `(-' (dec' -9223372036854775807) 1)`: -9223372036854775809N vs 9223372036854775807N. v54.
- **V55** (low; Clojure's own path difference) `((fn [a b] (- a b)) -1 Long/MIN_VALUE)`: throws vs 9223372036854775807. v55.

**Native values in comparisons and arithmetic (area P, with N):**
- **LG1** (extended) `< <= > >=` of an unsigned native (`count`, `alength`, `hash`) with any negative number, inlined, from a literal, a `let`, a parameter, `int` or a bit operation: true vs false. `(max (count [1]) -1)`: 1 vs -1; `(min (count [1 2 3]) -1)`: -1 vs 3. lg1, lg1b–lg1d; controls lg1e, lg1f.
- **V49** `(< (- (count [1]) 2) 0)`: true vs false; `(inc (- (count []) 1))`: 0 vs "Overflow on increment.". v49.
- **V50** `(/ (count [1 2 3]) -1)`: -3 vs 0; `(/ -6 (count [1 2]))`: -3 vs 9223372036854775805. v50.
- **V51** `(hash 2)`: -971005196 vs 3323962100 (`hash` is a `u32`); `(- (hash 0) 1)`: -1 vs 4294967295. v51, v51b.
- **V52** (extends R23, R26) `((fn [c] (if c (hash 1) -1)) false)`: -1 vs 4294967295. v52.
- **V56** `min`/`max` with ##NaN: ##NaN vs the other operand. v56, v56b.
- **V57** `max` on a tie: `((fn [a b] (max a b)) 1 1.0)` is 1.0 vs 1. v57, v57b.
- **V58** `min`/`max` of natives of two types: `(min 1 2.5)` is 1 vs 1.0; `(min 0.0 -0.0)` is -0.0 vs 0.0. v58, v58b.
- **V59** (extends S20) `(pr-str (+ 1/2 1/2))`: "1N" vs "1". v59.
- **V60** (extends S40, S12) `(long 1e20)`: throws vs an undefined cast. v60.
- **V61** (low) `(pr-str (numerator 1/2))`: "1" vs "1N". v61.
- **V62** `(== (float 0.1) 0.1)`: false vs true; `(float 1e40)`: throws vs 1.0E40. v62.
- **V63** `(+ (aget (float-array [0.1]) 0) 1)`: 1.1000000014901161 vs 1.100000023841858. v63.
- **V64** (extends R33) `(+ (nil? nil) 1)`, `(+ (aget (char-array "a") 0) 1)`: ClassCastException vs 2, 98. v64.

**Strings and characters (area W):**
- **LG3** (R52's `subs`, re-found) `(subs "é-è" 2)`: "è" vs "-è". lg3.
- **V65** (extends R52) `(nth "é" 0)`: \é vs the byte 0xC3. v65.
- **V66** (extends R52) `(get "éa" 1)`: \a vs the byte 0xA9; `(contains? "é" 1)`: false vs true. v66.
- **V67** `(upper-case (subs "é" 0 1))`: "É" vs ""; of `(subs "é" 1)`: "" vs `std::range_error`. v67.
- **V68** `(reverse (subs "é" 1))`: "" vs "Invalid UTF-8 string.". v68.
- **V69** (R54's first test) the seq of a cut string walks past its end and throws. v69.
- **V70** `(hash \a)`: 97 vs 1455541201. v70.
- **V71** `(hash "é")`: -1107437598 vs 958611385. v71.
- **V72** (extends R57) `(compare "é" "")`: 1 vs 2; `(compare "é" "e")`: 132 vs 94. v72.
- **V73** (extends R57) `(compare (first "é") \e)`: 132 vs 94. v73.
- **V74** (R58's starts) `(index-of "a" "a" -1)`: 0 vs nil. v74.
- **V75** (extends R78, R62) `(split "aéb" #"")`: ["a" "é" "b"] vs four pieces. v75.
- **V76** `(int (first "\ud83d"))`: 55357 vs 63 ("?"). v76.
- **V77** (extends R53) `(int (first "😀"))`: 55357 vs 128512. v77.
- **V78** (R64's first test) `(int (char 55296))`: 55296 vs "Unfinished character". v78.
- **V79** (R66 and R64) `(char -4294967231)`, `(char 128512)`: throws vs \A and the emoji. v79.
- **V80** (R65's first test) `(namespace (keyword "a/b" "c"))`: "a/b" vs "a". v80.
- **V81** (R67's first test) `(namespace (symbol nil "b/c"))`: nil vs "b". v81.
- **V82** `char-name-string`, `char-escape-string`: defined vs missing. v82.
- **V83** `(hash :c)`: -1763192079 vs 1458033393; qualified keywords and symbols always differ. v83.

**CHAMP (area H):**
- **V84** (extends D12; corrects its third example) an unrelated `conj` of 2.0 hides -0.0 from a set holding 0.0: [true true true] vs [true false true]. v84, v84b.
- **V85** (extends V48; another cause) the same ##NaN object in a set: [true 1 1 1 true] vs [false 2 nil 2 false]. v85.

**nREPL (area Q):** no new deviation (section 5).

## 3. Deviations in full

Each item gives the program (Clojure's result, then jank's), the property and its source, the path at 94d32623, the test (in `tests/jank_lean/deviations_r6_test.jank`), and whether it is new. Every Clojure result was run on Clojure 1.12.0.

### How a number reaches core/math.hpp (what sections 3.1 and 3.2 rest on)

Read from the source by areas N and P, and checked against each other:
- **Inlining.** A call of a var with `:inline` metadata is replaced by the inline form before analysis (analyze/processor.cpp `analyze_call` 3536–3567). Two-argument `+ - * /` (core.jank 1371–1435), `< <= > >=` (1552–1615, `>` swaps its operands), `min`/`max` (1616–1645), `inc`/`dec` (1646–1662), `abs`, `zero?`, `count` (186–192), `hash` (2476–2486), `int`, `float`, `alength`, the typed-array constructors and `aget` all inline to `cpp/jank.runtime.*`. `long`, `double`, `char`, `compare`, `mod`, `num`, `-'`, `+'`, `*'`, `inc'`, `dec'` and `=` never do.
- **Literals.** An integer literal is a C++ `int` when it fits 32 bits, else a `long` (analyze/cpp_util.cpp `literal_type` 602–648). A double literal is a `double`; `true`/`false` a `bool`. BigInt, ratio and BigDecimal literals are objects. The literal `-9223372036854775808` reads as a BigInt (round 2's R5, read/lex.cpp 1143–1157).
- **Locals.** A `let` local keeps its init's C++ type (processor.cpp `analyze_let` 2370–2421); a `loop` local too (cpp_util.cpp `mutable_type` 1064–1090).
- **Natives returned by inlines.** `count` → `sequence_length`: `usize` (core/seq.hpp 132, seq.cpp 837); `alength` → `usize` (array.hpp 88–100); `hash` → `to_hash`: `uhash`, a `u32` (core.hpp 87, core.cpp 623–626); `int` → `to_int`: `i64` (math.hpp 1409–1436); `float` → `to_real`: `f64` (1438–1464); every inlined predicate → `bool`; a typed array's `aget` → `T&` (array.hpp 32–36).
- **Codegen.** A literal is emitted as `auto tN(<text>);` and a call as `auto &&t(jank::runtime::lt(a, b));` (codegen/cpp_processor.cpp 1278–1285, 1352–1440), so Clang resolves math.hpp's templates again on the temporaries' C++ types.
- **math.hpp.** Each binary operation has four templates, chosen by `detail::primitive_number<T>` (`std::is_integral_v || std::is_floating_point_v`, 28–29, so `bool` and `char` count). Both primitive: C++'s operator under the usual arithmetic conversions (`add` 172–178, `lt` 622–628, `div` 400–406); `min`/`max` convert both to `std::common_type` and call `std::min`/`std::max` (856–863, 983–990). A primitive meeting an object computes with the object's `data`: `i32` for a `small_integer`, `i64` for an `integer`, `f64` for a `real`.
- **Objects.** A fn parameter, or a value passed through a fn value (`apply`), is an object: a `small_integer` (i32) when it fits, else an `integer` (core/make_box.hpp 89–101; visit.hpp `visit_number_like` 463–498). Through a fn value, no native operand reaches math.hpp.
- **Clojure.** Two primitive longs call `Numbers.add/minus/multiply(long, long)`, which throw "long overflow"; Object operands call the Object overloads (Numbers.java 154–178), where `minus(x, y)` is `add(x, negate(y))`.

### 3.1 Long overflow and the long minimum (LG2's class; area N)

**LG2 (extended). Long overflow wraps silently on every path with a long operand.**
- Programs, each compiled inside a deftest (Clojure throws ArithmeticException "long overflow" for each):
  - literals, `mul(int, long)`: `(* -3 9223372036854775807)`, jank -9223372036854775805 (the brief's form);
  - `(+ 9223372036854775807 1)` → -9223372036854775808; `(- -9223372036854775807 2)` → 9223372036854775807;
  - `let`-bound literals: `(let [a 9223372036854775807 b 2] (* a b))` → -2;
  - fn parameters (objects): `((fn [a b] (* a b)) 3037000500 3037000500)` → -9223372036709301616;
  - a literal and a parameter: `((fn [a] (+ a 9223372036854775807)) 1)` → -9223372036854775808;
  - `(- x)` of Long/MIN_VALUE (it is `(- 0 x)`): -9223372036854775808.
- Exactly which pairs: those whose true result leaves the i64 range, for `+ - *` and every mix of native `long` and `integer` object operands, always "a value where Clojure throws" (★ `i64_pair_verdict`).
- `inc` and `dec` are checked (`__builtin_add/sub_overflow`, math.hpp 1194–1199, 1272–1277) and agree for every fixed integer (★ `incdec_fixed_agree`). So jank is inconsistent with its own book ("Signed integer overflow is well defined and will wrap", differences-from-clojure.md 56) as well as with Clojure.
- Property: Numbers.java `add/minus/multiply(long, long)` and the Object overloads; the docstrings of `+`, `-`, `*` ("Does not auto-promote longs, will throw on overflow").
- Path: math.hpp `add` 68–178, `sub` 182–292, `mul` 408–518: `make_box(typed_l->data OP typed_r->data)` (object/object), `make_box(l OP typed_r->data)` (native/object), `return l OP r` (native/native), with `-fwrapv`.
- Tests: lg2-long-overflow-throws-with-literals [literals], lg2b-long-overflow-throws-with-let-bound-literals [let], lg2c-long-overflow-throws-through-fn-parameters [fn], lg2d-long-overflow-throws-with-a-literal-and-a-parameter, lg2e-negating-long-min-throws.

**LG2 (the brief's second form). Arithmetic on the literal -9223372036854775808 gives BigInts.**
- `(dec -9223372036854775808)`: Clojure throws; jank -9223372036854775809N (the brief's form).
- `(let [x -9223372036854775808] (* x 2) (- x 2))`: Clojure throws; jank -18446744073709551616N, -9223372036854775810N.
- `(pr-str (inc -9223372036854775808))`: Clojure "-9223372036854775807", jank "-9223372036854775807N"; `(pr-str (* -9223372036854775808 0))`: "0" vs "0N".
- Cause: the reader, not `dec`: round 2's R5 (read/lex.cpp 1143–1157: `strtoll` of the digits after `-` overflows, so a `big_integer` is built). The literal then takes math.hpp's exact `cpp_int` branches.
- Test: lg2f-arithmetic-on-the-long-minimum-literal.

**V49. A negative count difference stays unsigned.** New; LG1's cause through arithmetic.
- `(< (- (count [1]) 2) 0)`: Clojure true, jank false. `(inc (- (count []) 1))`: Clojure 0, jank throws the string "Overflow on increment.".
- Path: `sub(usize, int)` wraps to 2^64−1 (math.hpp 286–292); the next inlined template reads it unsigned (lt 622–628), or `inc`'s `__builtin_add_overflow` into i64 overflows (1188–1205). Boxed alone, the value reads back as −1.
- Test: v49-a-negative-count-difference-stays-negative [inlined].

**V53. Two `let`-bound `int`s are combined as C++ `int`s.** Extends R25 (literals) and D1 (objects) to `let`.
- `(let [a 65536 b 2147483647] [(* a a) (+ b 1)])`: Clojure [4294967296 2147483648]; jank [0 -2147483648].
- Exactly when the true result leaves i32, and Clojure never throws there (★ `i32_pair_verdict`, ★ `i32_exact_fits_i64`).
- Test: v53-let-bound-int-arithmetic-is-long [let].

**V54 (D3, re-tested). `-'` overflow is wrapped.** Corrects round 1's "refuted".
- `(-' (dec' -9223372036854775807) 1)`: Clojure -9223372036854775809N; jank 9223372036854775807N.
- Round 1's test d03 wrote `(-' -9223372036854775808 1)`. That literal is a BigInt in jank (R5), so `promoting_sub`'s BigInt branch answered exactly and the test passed. With a long operand the i64 branch runs.
- Path: core/math.cpp `promoting_sub` 102–134; line 126 boxes `l_val - typed_r->data`, an i64 difference.
- ★ `promoting_sub_wrong_iff`: wrong exactly when the true difference leaves i64. Test: v54-promoting-subtraction-overflow-of-a-long [fn].

**V55 (low). Subtracting Long/MIN_VALUE through a fn.** New; Clojure's own path difference.
- `((fn [a b] (- a b)) -1 Long/MIN_VALUE)`: Clojure throws "long overflow" (its Object `minus` negates the second operand first: Numbers.java 162–172, `LongOps.negate` 651–654); jank 9223372036854775807. With `-'`: Clojure 9223372036854775807N, jank 9223372036854775807.
- With literals, Clojure gives 9223372036854775807. Reported because Clojure 1.12's behavior is the property; even the fixed jank differs exactly here (★ `fixed_vs_object_sub`).
- Test: v55-subtracting-long-min-through-a-fn [fn].

### 3.2 Native values in comparisons and arithmetic (LG1's class; area P)

**LG1 (extended). `< <= > >=` compare an unsigned native with a negative number as unsigned.**
- Programs, inlined (Clojure true, jank false for each):
  - `(< -1 (count [1]))`, `(> (count [1]) -1)`, `(<= -1 (count [1]))`, `(>= (count [1]) -1)` (the brief's form first);
  - an object left operand: `((fn [x] (< x (count [1]))) -1)`; its i32/i64 `data` meets the `usize`;
  - every signed native: `(< (int -1) (count [1]))`, `(< (bit-and -1 -1) (count [1]))`, `(let [a -1] (< a (count [1])))`;
  - other unsigned producers: `(< -1 (alength (long-array 2)))`, `(< -2 (hash 0))`.
- Through a fn value it agrees: `(apply < [-1 (count [1])])` is true (control). `(< -1 (long (count [1])))` is true, since `long` is not inlined and returns an object (the brief's control; `jank6-coord` reproduces it).
- Exact set: for a count below 2^63, the two differ exactly when the other operand is negative, in both orders and for `int` and `i64` operands (★ `lt_i64_usize_differs_iff`, ★ `lt_usize_i64_differs_iff`, ★ `le_differs_iff`, ★ `lt_int_usize_differs_iff`).
- Property: Numbers.java `lt`/`lte` compare numbers; `count` is RT.count, an int used as a long.
- Path: core.jank 1552–1615 → math.hpp `lt` both-primitive 622–628 (`l < r`: `int` converts to `unsigned long long`, [expr.arith.conv]), primitive-right 594–620 (`typed_l->data < r` at 608–610), `lte` 630–736 likewise.
- Tests: lg1-lt-of-a-negative-literal-and-a-count, lg1b-lt-of-a-negative-parameter-and-a-count, lg1c-lt-of-signed-natives-and-a-length [inlined]; control lg1e-control-lt-through-a-fn-value [fn value, predicted to pass].

**LG1 (min and max).**
- `(max (count [1]) -1)`: Clojure 1, jank -1. `(min (count [1 2 3]) -1)`: Clojure -1, jank 3. `((fn [x] (max (count [1]) x)) -1)`: Clojure 1, jank -1.
- Path: math.hpp `min` 856–863, `max` 983–990: `std::common_type_t<usize, int>` is `usize`, so -1 becomes 2^64−1, `std::max` returns it, and boxing reads it as -1. The object form is 917–948.
- Exact set: differ exactly when the other operand is negative (★ `min_differs_iff`, ★ `max_differs_iff`).
- Tests: lg1d-min-and-max-of-a-count-and-a-negative [inlined]; control lg1f-control-min-and-max-through-a-fn-value.

**V50. `/` of a count and a negative number divides unsigned.** New.
- `(/ (count [1 2 3]) -1)`: Clojure -3, jank 0. `(/ -6 (count [1 2]))`: Clojure -3, jank 9223372036854775805.
- Not D2: D2's truncating division gives -3 for both.
- Path: core.jank 1421–1435 → math.hpp `div` 400–406 (`l / r` in `unsigned long long`), 342–369 (object left).
- Exact sets (★ `div_usize_by_i64_differs_iff`, ★ `div_i64_by_usize_differs_iff`): `(/ a b)` differs from truncating division iff b < 0 and |b| ≤ a; `(/ b a)` iff b < 0 and a ≥ 2.
- Test: v50-divide-a-count-by-a-negative [inlined].

**V51. `hash` is never negative: `to_hash` returns a `u32`.** New; a separate cause (the hash's type).
- `(hash 2)`: Clojure -971005196, jank 3323962100. `(neg? (hash 3))`: Clojure true, jank false. Both paths.
- Through inlined arithmetic it wraps at 32 bits: `(- (hash 0) 1)`: Clojure -1, jank 4294967295.
- jank's `hash::integer` (hash.cpp 71–114) is Murmur3's `hashLong` bit for bit, so jank's value is Clojure's read as unsigned: they differ exactly when the top bit is set (★ `hash_boxed_eq_iff`).
- Path: core.jank 2476–2486 → core.cpp 623–626 (`uhash`); arithmetic: math.hpp `sub` 286–292.
- Tests: v51-hash-of-a-long-is-a-signed-int [both paths], v51b-arithmetic-on-a-hash-is-signed [inlined].

**V52. An `if` or `case` whose branches are a hash and a negative `int` converts the `int` to unsigned.** Extends R23 and R26 to `u32`.
- `((fn [c] (if c (hash 1) -1)) false)` and `((fn [k] (case k 0 -1 1 -1 (hash 1))) 0)`: Clojure -1, jank 4294967295.
- Path: cpp_util.cpp `find_branch_common_type` 1907–1995 (the common type of `u32` and `int` is `u32`, 1970–1974).
- Test: v52-if-of-a-hash-and-a-negative [compiled inside a fn].

**V56. `min` and `max` with ##NaN drop the NaN.** New.
- Through fns: `((fn [a b] (min a b)) ##NaN 1)` → jank 1; `((fn [a b] (max a b)) 1 ##NaN)` → 1; `(apply max [1.0 ##NaN])` → 1.0. Literals: `(min 1.0 ##NaN)`, `(max 1 ##NaN)` → 1.0. Clojure: ##NaN each.
- Property: Numbers.java `min`/`max` 4044–4228 check NaN first; Math.min/max propagate it.
- Path: math.hpp `min` 738–865 (`l < r ? l : r`), `max` 865–992 (`l < r ? r : l`): NaN loses whenever it is min's first or max's second operand; native `std::min/max` likewise.
- Tests: v56-min-and-max-with-nan-through-fns [fn], v56b-min-and-max-with-nan-literals [literals].

**V57. On a tie, jank's `max` returns its first operand, Clojure's its second.** New (areas N and P found it independently).
- `((fn [a b] (max a b)) 1 1.0)`: Clojure 1.0, jank 1. `(max 1 1N)` through a fn: 1N vs 1. `(max 0.0 -0.0)` through a fn: -0.0 vs 0.0. `(str (apply max [1 1.0]))`: "1.0" vs "1".
- Property: Numbers.java `max(Object, Object)` is `gt(x, y) ? x : y` (4124–4136). `min` agrees on both sides.
- Path: math.hpp `max` 877–907 (`typed_l->data < typed_r->data ? typed_r : typed_l`).
- Tests: v57-max-of-a-tie-is-the-second-operand [fn], v57b-max-of-equal-numbers-keeps-the-second [fn value].

**V58. `min`/`max` of natives of different types return their common C++ type.** New; V58 shares LG1's lines.
- `(min 1 2.5)`: Clojure 1, jank 1.0. `(str (max 1 0.5))`: "1" vs "1.0". `(max 9007199254740993 1.0)`: Clojure 9007199254740993, jank 9.007199254740992E15. `(min 0.0 -0.0)`: Clojure -0.0 (Math.min), jank 0.0 (`std::min(a, b)` is `b < a ? b : a`).
- Property: Numbers.java `max(long, double)` and the other mixed overloads return the chosen operand (4072–4081).
- Path: math.hpp 855–863, 982–990.
- Tests: v58-min-and-max-of-literals-return-an-operand, v58b-min-and-max-keep-the-chosen-operand [inlined].

**V59. A ratio operation with a whole-number result is a long.** Extends S20 (which had a BigInt operand) to every operand.
- `(pr-str (+ 1/2 1/2))`, `(pr-str (* 1/2 2))`, `(pr-str (apply - [3/2 1/2]))`: Clojure "1N" each, jank "1".
- Property: RatioOps → `Numbers.divide(BigInteger, BigInteger)` gives a BigInt (Numbers.java 387–401).
- Path: obj/ratio.cpp `operator+` 172–176, `-` 198–203, `*` 235–238, `/` 270–273 → `ratio::create` 88–101, which narrows to a long.
- Test: v59-ratio-arithmetic-with-an-integral-result-is-a-bigint.

**V60. `long` of a double outside the long range.** Extends S40 (int) and S12 (BigDecimal).
- `((fn [x] (long x)) 1e20)`, `(long ##Inf)`: Clojure throws "Value out of range for long" (RT.longCast); jank `static_cast<i64>` of an out-of-range double, undefined (x86-64 gives -9223372036854775808).
- Path: core.jank `long` 5773–5776 → math.hpp `to_int` 1411–1431 → obj/number.cpp `real::to_integer` 358–366.
- Test: v60-long-of-an-out-of-range-double-throws [fn].

**V61 (low). `numerator` prints with N.**
- `(pr-str (numerator 1/2))`: Clojure "1" (a BigInteger), jank "1N".
- Path: math.cpp `numerator` 594–597 returns a `native_big_integer`, boxed as a `big_integer`.
- Test: v61-numerator-prints-as-a-biginteger.

**V62. `float` is a double.** New.
- `(== (float 0.1) 0.1)`: Clojure false, jank true. `(+ (float 0.1) 0.2)`: Clojure 0.30000000149011613, jank 0.30000000000000004. `(float 1e40)`: Clojure throws "Value out of range for float", jank 1.0E40. Both paths.
- Property: RT.floatCast rounds to single precision and checks the range.
- Path: core.jank 211–217 → math.hpp `to_real` 1438–1464 (`static_cast<f64>`).
- Test: v62-float-rounds-to-single-precision.

**V63. A float array's element computes in single precision.** New; LG1's cause (no widening to Clojure's double).
- `(+ (aget (float-array [0.1]) 0) 1)`: Clojure 1.1000000014901161 (the Float widened to double), jank 1.100000023841858 (`float + int` is a `float`).
- Path: array.hpp `aget` 32–36 (`float&`) → math.hpp `add` 172–178. Inlined only.
- Test: v63-float-array-arithmetic-is-double [inlined].

**V64. A predicate's `bool` and a char array's `char` are numbers to the inlined arithmetic.** Extends R33 to every inlined predicate; the char part is new.
- `(+ (nil? nil) 1)`: Clojure ClassCastException, jank 2. `(inc (empty? []))`: CCE vs 2. `(+ (aget (char-array "a") 0) 1)`: CCE vs 98.
- Path: math.hpp `primitive_number` 28–29 (`std::is_integral<bool>`, `<char>`). Through a fn value jank throws a `std::runtime_error` "not a number" (visit.hpp 507), which `thrown?` misses (V7's class).
- Test: v64-boolean-and-char-natives-are-not-numbers [inlined].

**One design choice, or separate?**
- One choice, math.hpp computing natives under C++'s usual arithmetic conversions instead of Clojure's long and double: LG1, V49, V50, V63, and through `+ - *` the overflow part of LG2 and V53 (with R25 and D1).
- `std::common_type` in `min`/`max`: LG1's min/max and V58.
- Separate: the reader (LG2's second form, R5), V51 (the hash's type), V52 (R23's branch typing), V54 (`promoting_sub`), V55 (Clojure's own path difference), V56 and V57 (min/max's operand choice), V59 (`ratio::create`), V60 (an unchecked cast), V61, V62 (`float`), V64 (`primitive_number` takes `bool` and `char`).

### 3.3 Strings and characters (area W)

**The answer in one paragraph.** jank's strings are UTF-8 bytes (`jtl::immutable_string`), and every function that takes or returns an index counts bytes: `count`, `nth`, `get`, `contains?`, `subs`, `clojure.string/index-of` and `last-index-of` (persistent_string.cpp, string_native.cpp). This is design choice A. jank's characters are code points: `seq`, `first`, `rest`, `vec`, `reverse` walk code points (persistent_string_sequence.cpp). This is design choice B. Clojure counts and walks UTF-16 code units. LG3 is A. A and B together give round 2's R53: jank's `(count (seq s))` equals its own `(count s)` exactly when s is ASCII, and Clojure's exactly when s has no supplementary character (★ `seqCount_eq_count_iff`, ★ `seqCount_eq_clojure_iff`). Everything else is a separate defect inside jank's own model.

**The property of every item below** is Clojure 1.12's result, which is java.lang.String's and Character's as core.clj and string.clj call them (the JDK javadoc: indices, lengths and `compareTo` values in UTF-16 units; `hashCode`; RT.charCast's range), and Util.hasheq, Keyword.hasheq and Symbol.hasheq for the hashes. Each value was run on Clojure 1.12.0 (`results/r6-str-clojure.txt`).

Every test writes non-ASCII text with `\u` escapes or `(char n)` and passes it through `identity`; functions that inline (`nth`, `get`, `contains?`, `hash`, `count`, `first`) are also called through `apply`. Both reach the same C++ here.

**LG3 (R52's `subs`). `subs` counts bytes.**
- `(subs "é-è" 2)`: Clojure "è", jank "-è" (the brief's form). `(subs "é-è" 0 2)`: Clojure "é-", jank "é".
- Exact shape (★ `subs1_agrees_iff`): `(subs s i)` agrees exactly when i < 0, or i is within s's longest ASCII prefix, or i is past jank's byte count (both throw). The three-argument form agrees by the analogous rule, with 9,392 coincidences in 37,606,285 cases (e.g. `(subs "éaa" 2 3)` is "a" on both sides), so it is searched, not stated as an iff.
- Property: `subs` is String.substring (core.clj `subs`; the JDK javadoc: indices are UTF-16 units).
- Path: core.jank `subs` 1979–1985 → core.cpp `subs` 398–422 → persistent_string.cpp `substring` 133–155 (`data.substr(start, end - start)`).
- Test: lg3-subs-indexes-characters (direct and through `apply`). Status: R52 (section 1).

**V65 (extends R52). `nth` of a string returns one byte.**
- `(nth "é" 0)`: Clojure \é, jank a character holding the byte 0xC3. `(nth "éa" 2 :nf)`: Clojure :nf, jank \a.
- Path: seq.cpp `nth` 648–696 → persistent_string.cpp `nth` 107–126 (`make_box<character>(data[i])`). Design A.
- Test: v65-nth-of-a-string-is-a-character.

**V66 (extends R52). `get` and `contains?` index bytes.**
- `(get "éa" 1)`: Clojure \a, jank the byte 0xA9. `(contains? "é" 1)`: Clojure false, jank true.
- Path: persistent_string.cpp `get` 78–93, `contains` 95–105. Design A.
- Test: v66-get-and-contains-index-characters.

**V67. The case functions on a cut string.** New; a separate defect.
- `(clojure.string/upper-case (subs "é" 0 1))`: Clojure "É", jank "" (the cut byte 0xC3 is dropped). `(upper-case (subs "é" 1))`: Clojure "", jank a `std::range_error`.
- Path: util/string.cpp `to_uppercase` 26–36 → `wstring_convert<codecvt_utf8<wchar_t>>::from_bytes`. In libstdc++ 15.3.0 an incomplete last character is `partial` and a stray continuation byte `invalid` (codecvt.cc `read_utf8_code_point` 252–330), and `from_bytes` throws only on an error (locale_conv.h 55–100, 336–347). Same for lower-case and capitalize.
- Corrects round 2's case-function model, which threw for both. Test: v67-upper-case-of-a-cut-string.

**V68. `reverse` of a cut string throws.** New; a separate defect.
- `(clojure.string/reverse (subs "é" 1))`: Clojure "", jank throws "Invalid UTF-8 string.".
- Path: string_native.cpp `reverse` 24–32 → utf8.cpp `utf8_iterator` 79–84 (`next_char_size` 13–36 throws on a continuation byte).
- Test: v68-reverse-of-a-cut-string.

**V69 (R54, first test of its own). The seq of a string whose last character is cut walks past its end.**
- `(let [s (str "a" (nth "é" 0))] (= (count (seq s)) (count (vec (seq s)))))`: Clojure true; jank throws a `std::runtime_error`.
- Path: persistent_string_sequence.cpp `next` 128–138 (at n = 1 + 2 = 3 ≠ 2 the walk goes on), `first` 122–126 reads past the end, then `substr` throws "position outside of string" (immutable_string.hpp 162–169), unless `next_char_size` throws "Invalid UTF-8 string." first on that byte.
- So round 2's b03 ("Invalid UTF-8 string.") was R54's predicted path, not "unclear" (section 11).
- Test: v69-a-cut-string-seq-has-its-count. The cut comes from `nth`, so `subs` plays no part.

**V70. A character hashes as a Murmur3-mixed string.** New; separate.
- `(hash \a)`: Clojure 97 (Character.hashCode), jank 1455541201. `(hash (first "é"))`: Clojure 233, jank 958611385.
- Path: core.jank `hash` 2476–2486 → character.cpp `to_hash` 89–92 → immutable_string.hpp `to_hash` 648–660.
- Test: v70-a-character-hashes-as-its-code (inline and `apply`).

**V71. `hash` of a non-ASCII string.** New; design A.
- `(hash "é")`: Clojure -1107437598 (Murmur3 of String.hashCode over units), jank 958611385 (over the bytes C3 A9). ASCII strings agree (round 1).
- Path: immutable_string.hpp `to_hash` 648–660. Test: v71-hash-of-a-non-ascii-string.

**V72 (extends R57: the value, not only the sign). `compare` of strings.**
- `(compare "é" "")`: Clojure 1 (units), jank 2 (bytes). `(compare "é" "e")`: Clojure 132 (0xE9 − 0x65), jank 94 (memcmp's 0xC3 − 0x65 on glibc; assumption StrA6-1).
- Property: String.compareTo documents its value, and Clojure's `compare` returns it. Round 2 kept only the sign, which this round's rule rejects.
- Path: core.jank `compare` 5064–5071 → core/equal.cpp `compare` 24–32 → persistent_string.cpp `compare` 63–71 → immutable_string.hpp `compare` 576–584.
- Test: v72-compare-of-strings-counts-units (its first assertion holds whatever memcmp returns).

**V73 (extends R57). `compare` of characters.**
- `(compare (first "é") \e)`: Clojure 132, jank 94. Path: character.cpp `compare` 94–102. Test: v73-compare-of-characters-subtracts-units.

**V74 (R58's starts, first test of their own; b07 stopped at its first assertion). `index-of` and `last-index-of` with a negative or past-the-end start.**
- `(index-of "a" "a" -1)`: Clojure 0, jank nil. `(last-index-of "aa" "a" -1)`: Clojure nil, jank 1. `(index-of "a" "" 5)`: Clojure 1, jank nil.
- Path: string.jank `index-of` 227–238, `last-index-of` 240–251 → string_native.cpp `index_of` 257–262 (the i64 start becomes a `size_t`, -1 is 2^64−1), `last_index_of` 264–269 (`rfind` clamps).
- Test: v74-index-of-starts-clamp-as-java.

**V75 (extends R78 and R62). `split` on an empty pattern cuts characters.**
- `(clojure.string/split "aéb" #"")`: Clojure ["a" "é" "b"], jank ["a" "\xC3" "\xA9" "b"].
- Path: string_native.cpp `split` 392–449 (`cregex_iterator` over bytes); libstdc++'s `regex_iterator` steps an empty match by one byte (regex.tcc 556–584).
- Test: v75-split-on-an-empty-pattern-keeps-characters.

**V76. A lone surrogate escape becomes "?".** New; design B.
- `(int (first "\ud83d"))`: Clojure 55357, jank 63.
- Path: read/parse.cpp `parse_escaped_string` 2007–2020 → util/escape.cpp `unescape` 46–68: a high surrogate not followed by `\u` becomes "?"; a lone low one goes through `to_char(cp, "?")`.
- Test: v76-a-lone-surrogate-escape-is-kept.

**V77 (extends R53). The first character of an emoji.** Design B.
- `(int (first "😀"))`: Clojure 55357, jank 128512. `(count (vec "😀"))`: 2 vs 1.
- Path: persistent_string_sequence.cpp `first` 122–126, character.cpp `to_integer` 104–110.
- Test: v77-int-of-the-first-of-an-emoji.

**V78 (R64, first test). `char` of a surrogate.**
- `(int (char 55296))`: Clojure 55296, jank throws "Unfinished character: 55296".
- Path: core.jank `char` 5795–5798 → core.cpp `to_char` 1311–1319 → character.cpp 57–61 → utf8.cpp `to_char` 170–194 (`wcrtomb` of a surrogate fails). Design B.
- Test: v78-char-of-a-surrogate.

**V79 (R66 and R64's range, first test). `char` past its range.**
- `(char -4294967231)`: Clojure throws, jank \A. `(char 128512)`: Clojure throws "Value out of range for char", jank the emoji.
- Path: utf8.cpp `to_char` 172 checks only `ch > 0x10FFFF`; `static_cast<wchar_t>` keeps the low 32 bits.
- Test: v79-char-past-its-range-throws. The wrap is separate; 128512 is design B.

**V80 (R65, first test).** `(namespace (keyword "a/b" "c"))`: Clojure "a/b", jank "a". Path: core.cpp `keyword` 521– → context.cpp `intern_keyword` 561–583 (joins with "/") → symbol.cpp `separate` 8–20 (splits at the first "/"). Test: v80-keyword-keeps-a-slashed-namespace.

**V81 (R67, first test).** `(namespace (symbol nil "b/c"))`: Clojure nil, jank "b". Path: core.jank `symbol` 520–530 → core.cpp `to_unqualified_symbol` 84–98 → symbol.cpp `separate`. Test: v81-symbol-with-a-nil-namespace.

**V82 (U74's class). `char-name-string` and `char-escape-string` are not defined.**
- `(char-name-string (char 32))`: Clojure "space"; jank an unresolved-symbol analysis error (an `error_ref`, V7). Test: v82-char-name-and-escape-strings (through `ev`).

**V83. Keyword and symbol hashes differ, even for ASCII.** New.
- `(hash :c)`: Clojure -1763192079, jank 1458033393. `(hash :b/c)`: -1763191981 vs 45199738. `(hash 'b/c)`: -122660454 vs 1685731265. 13 of the 26 keywords :a–:z differ.
- Path: hash.cpp `combine` 67–70 shifts a `u32` (`seed >> 2`, logical) where Util.hashCombine shifts an int (arithmetic): they differ whenever the name's Murmur3 hash is negative as an int. symbol.cpp `to_hash` 152–155 also hashes the namespace with Murmur3, where Symbol.hasheq uses String.hashCode.
- Test: v83-keyword-and-symbol-hashes.

**Also checked and agreeing:** clojure.string/reverse on valid text (both keep surrogate pairs or code points together), trim-newline, starts-with?, ends-with?, includes?, join, split-lines, replace-first and char/char replace, printing non-ASCII strings and characters, `char?`/`string?`, `(name :é)`, sort of BMP characters, and first/last/rest/vec/into/`apply str` on BMP text.

**One design choice, or separate?**
- **A, byte indices:** LG3, V65, V66, V71, the values in V72 and V73, and R52's and R58's byte results. Under code-point indexing every disagreement of count/nth/get/contains?/subs/index-of/last-index-of on text without a supplementary character disappears (★ `cp_design_agrees_bmp`; search A's residual is 0 for every operation on BMP-only text).
- **B, code-point characters:** V76, V77, V78, V79's 128512, R53's difference on emoji, R57's sign, R64's surrogates. These remain under any fix short of UTF-16 strings (`cp_design_supplementary`).
- **Separate defects:** the cut (V67, V68, V69/R54), R55/V48, R56, R57's values, R58/V74, R59, R60, R61, R62/V75, R63, R65/V80, R66's wrap, R67/V81, V70, V82, V83. Section 4 gives local fixes for eleven of them.

### 3.4 CHAMP (area H)

Round 5 left out `get` of another key after add or remove, and iteration. Both are now proved for every input under a lawful equality (section 9). Dropping the premises one at a time gave two deviations. Values pass through `(defn- id [x] x)`, so they are objects, and `hash-set`/`hash-map` build CHAMPs at every size.

**V84 (extends D12; corrects D12's third example). Whether an equal key with another hash is found depends on unrelated elements.**
- `(let [s1 (hash-set (id 0.0)) s2 (conj s1 (id 2.0))] [(contains? s1 -0.0) (contains? s2 -0.0) (contains? (disj s2 2.0) -0.0)])`: Clojure [true true true]; jank [true false true].
- Same cause: `(count (conj s2 -0.0))` is 3 vs 2; `(get (hash-map 0.0 :a 2.0 :b) -0.0)` nil vs :a; `(= (hash-set 0.0 2.0) (hash-set -0.0 2.0))` false vs true; the same through a transient.
- Why: `hash::real` (hash.cpp 116–127) hashes 0.0 as 0 and -0.0 as 2^31. Their low 30 bits agree (CHAMP levels 0–5), so -0.0 finds 0.0 while 0.0 sits in a data slot there. Adding 2.0 (hash 2^30) pushes 0.0 down to level 6, where -0.0 asks for another slot. So law 1 (get of another key after add/remove is unchanged) breaks.
- Correction: round 1's D12 said `(contains? #{0.0} -0.0)` is false. The CHAMP replica says true. That assertion never ran: the d12 test failed on its first assertion.
- Property: `contains?`, `get`, `conj`, `disj` docstrings; PersistentHashSet and BitmapIndexedNode find with Util.equiv.
- Tests: v84-an-unrelated-element-hides-an-equal-key, v84b-a-transient-hides-an-equal-key-too.

**V85 (extends V48; another cause). The same ##NaN object is never found in a set or map.**
- `(let [x (id ##NaN)] [(contains? (hash-set x) x) (count (hash-set x x)) (get (hash-map x 1) x) (count (disj (hash-set x 3) x)) (= (hash-set x) (hash-set x))])`: Clojure [true 1 1 1 true]; jank [false 2 nil 2 false].
- Why: immer compares with `runtime::equal`, which has no identity check (core/equal.cpp 19–22; a NaN uses C++ `==`). Clojure's Util.equiv tests `k1 == k2` first. `(= ##NaN ##NaN)` agrees on both sides, so a fix for R55 does not fix V85.
- Test: v85-a-set-finds-its-own-nan.

### 3.5 nREPL (area Q)

No new deviation. Every search found only the known classes it was built to set aside (R125, R126, R139, R1, S76); section 5 gives what was decided. No test is added for the nREPL.

## 4. Fixes

**What was written.** 181 diffs in `fixes/<id>.diff`, for 159 deviation ids (others are covered by one of them: e.g. S19 by D2, S9 by U2, U9–U11, U13 and U13b by U8, V39, V40 and V45 by V38, V42 by V41, V48 by R55a, V20 on the dynamic runtime by V19). By round: LG 3 diffs, D 19, R 63, S 24, U 51, V 21.
- Each is the smallest local change: one function or one file, a header and its source for one function counting as one. A deviation with several causes has one diff per cause (`D12a`–`D12d`, `R59a`/`R59b`, …), each naming the test or assertion it makes pass.
- Each applies alone to 94d32623: `git -C upstream-r5 apply --check ../fixes/<id>.diff` passes for all 181, and `upstream-r5` is clean.
- Each names the test that should pass with it (rounds 1–6's `tests/jank_lean/*.jank`), what was checked by reading, and what a build must confirm.
- Fixes were written for confirmed deviations only (assumption FixA6-1), except V22 and V23 (c_api.h's missing `<stdbool.h>`, a debug print), which are certain from reading and marked "not confirmed by a run".
- No fix was compiled inside jank. Standalone checks are named in each section.

**LG1–LG3:**
- **LG1:** `LG1.diff` widens native operands to `i64`/`f64` in math.hpp's `lt`, `lte`, `min`, `max`, `div`, `inc`, `dec`, and makes mixed-type `min`/`max` return the chosen operand boxed. It covers LG1, V49, V50 and V58's mixed-type part (v58b). Two operands of one type still go through `std::min`/`std::max`, so v58's `(min 0.0 -0.0)` and V56's NaN cases stay as they are; V51 (the hash's type), V62 (`float`) and V63 (float arithmetic) are not covered.
- **LG2:** needs four diffs together: `LG2a` (checked 64-bit `+ - *` at all 33 sites in math.hpp; covers V53, D1, R25), `R5a` (the reader reads -9223372036854775808 as a long), `R5b` (codegen emits Long/MIN_VALUE as `(-9223372036854775807L - 1)`), `LG2c` (`promoting_sub`, V54).
- **LG3: no coherent local fix.** A code-point `subs` beside the byte `count` would make `(subs "é" (count "é"))` throw and break `(subs s (index-of s x))`. The smallest design change is code-point indexing across persistent_string.cpp (`count`, `nth`, `get`, `contains`, `substring`) and string_native.cpp (`index_of`, `last_index_of`), with R62a and R63a. It would still differ from Clojure on supplementary characters (design B). A `subs` that refuses a cut inside a character was written, checked and withdrawn: jank's own nREPL `abbreviate` cuts strings by byte count and would start throwing.

**Overlaps, and the combined patch.** Each diff applies alone, but some touch the same lines. For one build with all of them, `fixes/combined/all.diff` (80 files, accepted by `git apply --check`) applies every fix at once; `fixes/combined/README.txt` gives the order and each resolution:
- **math.hpp** (D2, D6, LG1, LG2a, R33a, R33b): hand-merged (`math-hpp.diff`). Each native operand of `/` is widened (LG1), then divided exactly (D2's `checked_div`). A native bool can no longer reach LG2a's helpers; it throws R33b's error.
- **delay** (D19, V10, V11, S64): F3's merged D19+V10+V11, with S64 folded in as an atomic `realized` flag (`delay.diff`).
- **multi_function** (U19, R100): R100 kept; it fixes u19 as well. U19 is superseded.
- **S17:** its `#include <limits>` hunk dropped (R5a adds it). **R59a, S12, S14, S15, S37, U2:** adjacent hunks, applied with fuzz, and each re-checked to land in its intended function (diff3 of each file's single-fix results; 30 of 32 multi-fix files byte-identical, the other two read).
- **Corrected after the merge's compile check:** U2 (a missing `template` keyword) and D19 (`fn = {}` picked a deleted operator) did not compile even alone; both diffs are corrected. R33a now also adds two `else`s math.hpp lacks, so a native bool reaching `*` or `pow` throws instead of failing to compile at JIT time.
- Syntax-only compile with Apple clang 16: 45 of the 58 changed `.cpp` files compile in the combined tree, the same set that compiles at 94d32623 on this Mac. The other 13 need LLVM, CppInterOp or cpptrace headers (core.cpp, analyze/processor.cpp, read/parse.cpp, c_api.cpp, …).

**Pairings a build should know:**
- D12a (−0.0 hashes as 0.0) needs R42: otherwise jank's constant pools merge a `-0.0` literal into `0.0`.
- D18a and D18b only work together; R59a and R59b; V17a and V17b; R122a alone passes r122.
- r25's loop assertion needs LG2a and R24 (the loop local's type); lg2f needs R5a, R5b and LG2a.
- Tests that a fix can't make pass: r34 (jank's arity error is a C++ exception `thrown?` misses), u49 (also needs `ns-aliases`, not local), u59 (needs U59a, a CLI choice), b07's first assertion (a byte index), v03 (`thrown?` again: use fix-v03).
- Round 1's d09 and d09b assert behaviors Clojure 1.12 does not have (section 12); judge D9 with `(NaN? (- ##Inf ##Inf))`.

**What a build must check first** (fixes/combined/README.txt):
1. math.hpp's templates on libstdc++ and jank's clang: every instantiation core.jank's inlines make. Return types changed and the analyzer reads them: integer `/` is an `object_ref` (D2), `min`/`max` of a long and a double an `object_ref` (LG1), `+ - *` of two `int`s an `i64` (LG2a).
2. The 13 files not compiled here, first analyze/processor.cpp (R26, R27, R29, R34, S37, S38 together), core.cpp (15 diffs), read/parse.cpp (6) and c_api.cpp (5).
3. delay.hpp gained members (`exception_ptr`, `option<error_ref>`, `atomic<bool>`): rebuild everything that includes it.
4. Then each named test, and jank's own suites (test/cpp, test/jank, test/bash).

### The fixes, one by one

Sorted by id. "Test that should pass" names a test of rounds 1–6 under `tests/jank_lean/`.

### LG1 — include/cpp/jank/runtime/core/math.hpp
- Fixes: LG1 (every producer, and its min/max form), V49, V50 and V58's mixed-type part. Today `(< -1 (count [1]))` is false, `(max (count [1]) -1)` is -1, `(/ (count [1 2 3]) -1)` is 0 and `(max 1 0.5)` is 1.0; after, true, 1, -3 and 1, as in Clojure.
- Change: a new `detail::widen` turns every primitive operand into `i64` (integers) or `f64` (floating point) before the operation, in `lt`, `lte`, `min`, `max`, `div`, `inc` and `dec`.
- Change: new `detail::primitive_min`/`primitive_max` compare the widened values. Two operands of the same widened type still use `std::min`/`std::max`. A long and a double give the chosen operand, boxed in its own type, and a NaN operand wins.
- Why it is safe: only branches with a primitive operand change. The object-object branches, `add`, `sub` and `mul` are untouched. A usize that wrapped below zero now reads as the negative long it stands for, which is what boxing it already gives (`convert<T>::into_object`). Ratio, bigint and bigdecimal data now meet an `i64`/`f64`; the operators for those exist (ratio.hpp's integral and floating templates, boost mixed operations). A bool still widens to 0 or 1, so R33 is left to R33a/R33b.
- Test that should pass: tests/jank_lean/deviations_r6_test.jank `lg1-lt-of-a-negative-literal-and-a-count`, `lg1b-lt-of-a-negative-parameter-and-a-count`, `lg1c-lt-of-signed-natives-and-a-length`, `v49-a-negative-count-difference-stays-negative`, `lg1d-min-and-max-of-a-count-and-a-negative`, `v50-divide-a-count-by-a-negative`, `v58b-min-and-max-keep-the-chosen-operand`. The controls `lg1e` and `lg1f` still pass. Each needs only this diff.
- Checked by reading: every primitive branch of the seven templates; the `typed_object` branches (integer_ref and real_ref data are primitive); the analyzer takes the return type of the instantiated template (`get_function_return_type`). `min`/`max` now return `i64`/`f64` or `object_ref` depending on the instantiation (`if constexpr`).
- Checked by reading: the `+ - *` lines are agent N's LG2a.diff. Its checked operations make V51 (`(- (hash 0) 1)`) exact, but leave V63 (float arithmetic) as it is.
- Standalone check: results/r6-native-cxx-check.txt, built from .r6-scratch/native/cxx/check.cpp with Apple clang, C++20, -O2. It gives jank's current values and the fixed ones.
- A build must check: every instantiation core.jank makes compiles.
- A build must check: the JIT handles an `auto` template that returns `object_ref` for mixed types.
- A build must check: `(/ int int)` now divides in `i64`, so `(/ -2147483648 -1)` is 2147483648 instead of SIGFPE.
- A build must check: no jank test expects `(min 1 2.0)` to be 1.0.
- A build must check: the hand merge with LG2a.diff, D2.diff and D6.diff, which also edit math.hpp.

### LG2a — include/cpp/jank/runtime/core/math.hpp
- Fixes: LG2 (with R5a, R5b, LG2c), V53, D1, R25. Today `(* -3 9223372036854775807)` is -9223372036854775805 and `((fn [a b] (+ a b)) 2147483647 1)` is -2147483648; after, the first throws "integer overflow" and the second is 2147483648.
- Change: three helpers, `detail::checked_add/sub/mul`, compute every pair of fixed-width integers in i64 with `__builtin_*_overflow` and throw the string "integer overflow" on overflow.
- All 33 `l OP r` sites of `add`, `sub` and `mul` (object/object, native/object, typed, native/native) call them.
- Why it is safe: bool (R33) and non-integers (double, cpp_int, ratio, decimal) keep their own operator.
- The operands are taken by reference, so a boost expression template refers to the same objects as the inline expression did.
- inc and dec already throw the same way; div, lt, min and max are untouched.
- Test that should pass: tests/jank_lean/deviations_test.jank `d01-arithmetic-past-32-bits`.
- Also tests/jank_lean/deviations_main_test.jank `r25-literal-arithmetic-is-long`, first assertion only (its loop assertion also needs area P's loop-local typing).
- Also tests/jank_lean/deviations_r6_test.jank `lg2-long-overflow-throws-with-literals`, `lg2b-…`, `lg2c-…`, `lg2d-…`, `lg2e-…` and `v53-let-bound-int-arithmetic-is-long`.
- Checked by reading: every overload of add/sub/mul and the inline expansions in core.jank 1371-1434. Theorem `fixed_eq_static` proves the fixed arithmetic is Clojure's for every pair.
- Standalone check: .r6-scratch/num/cppcheck/lg2a.cpp → results/r6-num-cppcheck-lg2a.txt.
- A build must check: the template instantiations; that `int + int` now inferred as i64 changes no caller that needs an `int`; that a loop local typed `int` still truncates (R24/R86, a separate analyzer matter).

### LG2c — src/cpp/jank/runtime/core/math.cpp
- Fixes: D3 (re-tested as V54; part of LG2). Today `(-' (dec' -9223372036854775807) 1)` is 9223372036854775807N; after, -9223372036854775809N.
- Change: `promoting_sub` boxes `l - typed_r->data`, using the native_big_integer `l` it already builds, instead of the i64 difference.
- Why it is safe: one line in the overflow branch only; the non-overflow path and the other promoting ops are unchanged.
- Test that should pass: tests/jank_lean/deviations_r6_test.jank `v54-promoting-subtraction-overflow-of-a-long`.
- Round 1's d03 used R5's BigInt literal and never reached this branch.
- Checked by reading: promoting_sub 102-134 and its BigInt branch. Theorem `promoting_sub_wrong_iff`. Standalone check: none.
- A build must check: nothing beyond compiling.

### D2 — include/cpp/jank/runtime/core/math.hpp
- Fixes: D2, D2b, S19. Today `((fn [a b] (/ a b)) 1 2)` is 0 and `(/ 7N 2)` is 3N; after, 1/2 and 7/2.
- Change: `detail::checked_div` at the 11 `/` sites of `div`. Two integers (fixed or BigInt) divide exactly: a ratio unless it divides.
- When it divides: a long from two longs (Long/MIN_VALUE goes to BigInt, as LongOps.divide does), a BigInt when a BigInt takes part; dividing by zero throws "Divide by zero".
- Why it is safe: doubles, ratios and decimals keep their `/`. `-2147483648 / -1` no longer reaches C++ int division (it used to trap with SIGFPE).
- Test that should pass: tests/jank_lean/deviations_test.jank `d02-integer-division-is-a-ratio` and `d02b-int32-minimum-divided-by-minus-one`; tests/jank_lean/deviations_r3_test.jank `s19-bigint-division-is-a-ratio`.
- Checked by reading: every div overload, ratio_data's constructor (gcd, sign), make_box of a ratio. Standalone check: none.
- A build must check: the mixed return types per instantiation; that it composes with LG2a in one math.hpp (fixes/combined may merge them).

### D4 — src/cpp/jank/runtime/core/math.cpp
- Fixes: D4, D4b. Today `(quot 9007199254740993 1)` is 9007199254740992 and `(quot 7.5 2)` is 3; after, 9007199254740993 and 3.0.
- Change: `quot` follows Numbers.quotient for each kind:
  - doubles give a double (Java's in-range cast, else trunc; NaN or Inf throws);
  - two longs use Java `/`, with MIN / -1 = MIN;
  - a BigInt or a ratio gives a BigInt;
  - decimals give the truncated decimal quotient;
  - dividing by zero throws.
- Why it is safe: only quot changes; a ratio with a decimal keeps the old double path.
- Test that should pass: tests/jank_lean/deviations_test.jank `d04-quot-exact-on-longs` and `d04b-quot-of-doubles-is-a-double`.
- Checked by reading: visit_number_like's data types; Numbers.quotient 197-210, LongOps/BigIntOps/RatioOps/BigDecimalOps quotient. Standalone check: none.
- A build must check: boost `trunc` on the et_off decimal; the int64 cast bounds.

### D5 — src/cpp/jank/runtime/core/math.cpp
- Fixes: D5. Today `(== 9007199254740993 9007199254740992)` is true; after, false.
- Change: `is_equiv` compares through doubles only when a double takes part; otherwise it uses the exact `!(a < b) && !(b < a)` with the same operators math.hpp's `lt` uses.
- Why it is safe: `==` with a double is unchanged; the exact operators already compile for every pair in `lt`.
- Test that should pass: tests/jank_lean/deviations_test.jank `d05-numeric-equivalence-of-longs`.
- Checked by reading: is_equiv 469-489, lt's pairs. Standalone check: none.
- A build must check: overload lookup of `<` from math.cpp for every pair.

### D6 — include/cpp/jank/runtime/core/math.hpp
- Fixes: D6. Today `((fn [x] (abs x)) -0.0)` prints -0.0; after, 0.0.
- Change: `abs`'s object branch uses `std::fabs` for real and small_real.
- Why it is safe: integers, BigInts, ratios and decimals keep `data < 0 ? -1 * data : data`; the native branches already used std::abs.
- Test that should pass: tests/jank_lean/deviations_test.jank `d06-abs-of-negative-zero`.
- Checked by reading: abs 994-1040. Standalone check: none.
- A build must check: compiling only.

### D7 — src/cpp/jank/runtime/core/math.cpp
- Fixes: D7. Today `(bigdec 9007199254740993)` is 9007199254740992M; after, 9007199254740993M.
- Change: `to_big_decimal` builds an integer's decimal from its i64 directly instead of through `to_real()`.
- Why it is safe: one branch; cpp_dec_float from long long is exact.
- Test that should pass: tests/jank_lean/deviations_test.jank `d07-bigdec-of-a-long-is-exact`.
- Checked by reading: to_big_decimal 790-839. Standalone check: none.
- A build must check: compiling only.

### D8 — src/cpp/jank/runtime/obj/big_decimal.cpp
- Fixes: D8 and S10's instance. Today `(= 1M 1.0000000000000000001M)` is true and the two hash apart; after, false.
- Change: `big_decimal::equal` compares with `==` instead of `abs(a - b) < f64 epsilon`.
- Why it is safe: equal is only called for two big_decimals; compare is unchanged.
- Test that should pass: tests/jank_lean/deviations_test.jank `d08-bigdecimal-equality-is-exact`; tests/jank_lean/deviations_r3_test.jank `s10-equal-bigdecimals-hash-alike`.
- Checked by reading: equal 146-155, to_hash. Standalone check: none.
- A build must check: that cpp_dec_float has no second representation (such as a negative zero) of an equal value that hashes apart.

### D9 — include/cpp/jank/runtime/oref.hpp
- Fixes: D9. Today `(- ##Inf ##Inf)` and `(/ 0.0 0.0)` through fn params segfault on x86-64; after, they give ##NaN.
- Change: `detail::tag(f64)` stores any double whose bits are at or above `max_real` (a negative quiet NaN, such as x86-64's default NaN 0xFFF8...) as the canonical quiet NaN 0x7FF8....
- Why it is safe: those bit patterns are the integer and pointer tag space, so no real value is lost; only a NaN's sign and payload change, which nothing observes. `tag(f64)` is the only path from a small_real to an object_ref (the oref<object> constructor, 280-289, and `erase`, 2303); `make_box(f64)` returns oref<small_real>.
- Test that should pass: tests/jank_lean/deviations_test.jank `d09-nan-from-infinities`, `d09b-nan-from-zero-over-zero` (no more crash). Both tests are wrong against Clojure 1.12: Clojure gives false for d09's `(let [x (sub ##Inf ##Inf)] (not= x x))` (Util.equiv's identity check on the one boxed Double), and throws ArithmeticException "Divide by zero" for d09b's `(div 0.0 0.0)`. With D9, jank gives true and ##NaN, so both pass on jank while asserting what Clojure does not. A sound test: `(is (NaN? (sub ##Inf ##Inf)))`. jank's `(/ 0.0 0.0)` = ##NaN is D2's area.
- Checked by reading: every oref construction from a double (grep for bit_cast to object pointers), math.hpp sub/div boxing, cpp_processor 195 (reads tagged reals back). Standalone check: none.
- A build must check: jank's tests; `(- ##Inf ##Inf)` prints ##NaN on x86-64.

### D10 — src/cpp/jank/runtime/core/math.cpp
- Fixes: D10, D10b. Today `(parse-long " 5")` is 5, `(parse-double "inf")` is ##Inf and `(parse-double "1.5 ")` is nil; after, nil, nil and 1.5.
- Change: `parse_long` first checks Long/valueOf's grammar `[+-]?[0-9]+`.
- `parse_double` checks Double/valueOf's grammar: trimmed, a sign, NaN/Infinity, a decimal or hex float, an f/F/d/D suffix.
- It then reads with `strtod`, so an overflow is ##Inf and an underflow 0, as in Java.
- Why it is safe: only the two functions; the non-string error is unchanged.
- Test that should pass: tests/jank_lean/deviations_test.jank `d10-parse-long-grammar` and `d10b-parse-double-grammar`.
- Checked by reading: both functions, java.lang.Double#valueOf's grammar. Standalone check: none.
- A build must check: compiling only.

### D12a — src/cpp/jank/hash.cpp
- Fixes: D12 (0.0/-0.0). Today `(contains? #{0.0} -0.0)` is false; after, true.
- Change: `real()` (116) returns 0 for 0.0 and -0.0, as Clojure 1.12's Numbers.hasheq.
- Why it is safe: Java's hash of 0.0 is 0 already, so only -0.0 changes. Callers: real::to_hash and small_real::to_hash (number.cpp 337, 455).
- Test that should pass: tests/jank_lean/deviations_test.jank `d12-equal-means-same-hash`, third assertion; the whole test needs D12a, D12b, D12c and D12d.
- Checked by reading: the callers above; small_real/real equality (number.cpp 267-282, 385-400). Standalone check: none.
- A build must check: apply together with R42. Without it the constant pools (cpp_processor global_constants, ir/processor.hpp 86/91, hoist_literals.cpp 17) merge a -0.0 literal with 0.0, since they now hash alike and are `=`.

### D12b — src/cpp/jank/runtime/obj/big_integer.cpp
- Fixes: D12 (1/1N). Today `(count (hash-set 1 1N))` is 2 and `(get (hash-map 1N :a) 1)` is nil; after, 1 and :a.
- Change: `to_hash(native_big_integer)` (155) hashes a value in the i64 range with `hash::integer(i64)`, as long and small_integer do (Clojure's BigInt.hasheq uses hashLong). Out of range: unchanged.
- Why it is safe: `equal` already makes 1 and 1N equal (big_integer.cpp 116-131, number.cpp 184-204). The other user, ratio::to_hash (ratio.cpp 135), only needs consistency among ratios.
- Test that should pass: tests/jank_lean/deviations_test.jank `d12-equal-means-same-hash`, first two assertions (whole test needs D12a-d).
- Checked by reading: jank's test/cpp/jank/runtime/obj/big_integer.cpp "Hashing" stays true (0 and -1 hash differently; big values keep the limb hash). Standalone check: none.
- A build must check: test/cpp big_integer and ratio tests; d12.

### D12c — src/cpp/jank/runtime/obj/lazy_sequence.cpp
- Fixes: D12 (empty lazy seq). Today `(count (hash-set [] (lazy-seq nil)))` is 2; after, 1.
- Change: `to_hash` (98-106) returns `mix_collection_hash(1, 0)` for an empty lazy seq, what hash::ordered gives for () and [].
- Why it is safe: only the empty case changes; non-empty lazy seqs keep hash::ordered.
- Test that should pass: tests/jank_lean/deviations_test.jank `d12-equal-means-same-hash`, fourth assertion (whole test needs D12a-d).
- Checked by reading: persistent_list and persistent_vector to_hash (hash::ordered over their elements). Standalone check: none.
- A build must check: d12.

### D12d — src/cpp/jank/runtime/obj/detail/base_persistent_map_sequence.cpp
- Fixes: D12 (map seq). Today `(hash (seq {:a 1}))` differs from `(hash [[:a 1]])`; after, equal.
- Change: `to_hash` (84-87) uses hash::ordered instead of hash::unordered: the seq is sequential and `=` to the vector or list of its entries.
- Why it is safe: entries hash as [k v] vectors either way; only the combination changes.
- Test that should pass: tests/jank_lean/deviations_test.jank `d12-equal-means-same-hash`, fifth assertion (whole test needs D12a-d).
- Checked by reading: hash::ordered(object_ref) (hash.cpp 161-179). Standalone check: none.
- A build must check: d12.

### D13 — src/cpp/jank/hash.cpp
- Fixes: D13. Today `(hash-unordered-coll [1 2])` and `(hash-unordered-coll '(1 2))` never equal `(hash #{1 2})`; after, they do.
- Change: `unordered(object_ref)` (181-199) starts its sum at 0, as sets' hash::unordered(begin, end) and Clojure's hashUnordered, and iterates any seqable (a vector, set or map), not only sequence_like.
- Why it is safe: its callers are core.cpp hash_unordered (1369) and base_persistent_map_sequence::to_hash (which D12d moves to ordered).
- Test that should pass: tests/jank_lean/deviations_test.jank `d13-hash-unordered-coll-is-a-set-hash`.
- Checked by reading: make_sequence_range(object_ref) seqs any seqable (sequence_range.cpp). Standalone check: none. Not covered: Clojure 1.12 also has `(= (hash-unordered-coll {:a 1}) (hash {:a 1}))` true; jank's map hash adds 31*h(k)+h(v), not the entry vector's hash.
- A build must check: d13.

### D16 — src/cpp/jank/runtime/obj/atom.cpp
- Fixes: D16. Today a watch that removes itself (or a watch that swap!s beside an add-watch) deadlocks; after, it runs.
- Change: `notify_watches` (43-54) copies the watches map under the read lock, releases it, then calls the watches, as Clojure calls them with no lock held.
- Why it is safe: the map is persistent, so the copy is a snapshot; add_watch and remove_watch (249-259) still swap it under the write lock.
- Test that should pass: tests/jank_lean/deviations_test.jank `d16-watch-removing-itself`.
- Checked by reading: every use of `watches` (only atom.cpp). Standalone check: none.
- A build must check: d16; jank's atom tests.

### D18a — include/cpp/jank/runtime/core/meta.hpp, src/cpp/jank/runtime/core/meta.cpp
- Fixes: D18 (with D18b). Today concurrent alter-meta! loses updates; after, none are lost.
- Change: a new `alter_meta(o, f, args)` = reset_meta(o, apply_to(f, cons(meta(o), args))) under a static recursive mutex; reset_meta (84) takes the same lock (Clojure's alterMeta and resetMeta are synchronized).
- Why it is safe: one lock for every object is stronger than Clojure's per-reference monitor, never weaker; recursive, so alter_meta calls reset_meta and f may alter other metadata.
- Test that should pass: tests/jank_lean/deviations_test.jank `d18-alter-meta-loses-no-update`, only with D18b. D18a alone changes nothing a program sees.
- Checked by reading: meta.hpp is in the JIT prelude (prelude.hpp 11), as reset_meta is; apply_to (call.hpp 20) and cons (seq.hpp 87). Standalone check: none.
- A build must check: d18; no deadlock in jank's tests.

### D18b — src/jank/clojure/core.jank
- Fixes: D18 (with D18a).
- Change: `alter-meta!` (1235-1243) calls `cpp/jank.runtime.alter_meta`.
- Why it is safe: callers of alter-meta! in core.jank (6591, 7066) only gain the lock. Alone it does not resolve (alter_meta exists only with D18a).
- Test that should pass: tests/jank_lean/deviations_test.jank `d18-alter-meta-loses-no-update`, only with D18a.
- Checked by reading: core.jank's reset-meta! and alter-meta! users. Standalone check: none.
- A build must check: d18 with D18a. Two units: D18 may be counted as not local.

### D19 — include/cpp/jank/runtime/obj/delay.hpp, src/cpp/jank/runtime/obj/delay.cpp
- Corrected after the merge's compile check: the first version wrote `fn = {};`, which picks oref's deleted `operator=(nullptr_t)`; the diff now writes `fn = jank_nil;` (three places) and compiles alone.
- Fixes: D19. Today a delay whose body returns nil runs its body at every deref, and `realized?` is false after nil or a throw; after, it runs once and is realized.
- Change: a `realized` flag set once the body has run (returned anything, or threw a std::exception or an object); deref then returns the value or rethrows the stored error; `is_realized` returns the flag; `fn` is cleared after running, as Clojure's Delay.
- Why it is safe: all under the existing mutex. A body throwing anything else (an error_ref, V11) still runs again at the next deref, as today.
- Test that should pass: tests/jank_lean/deviations_test.jank `d19-delay-runs-once-even-for-nil`.
- Checked by reading: delay's only uses (core.cpp is_realized, deref). Standalone check: none.
- A build must check: d19; the struct gained a member (rebuild everything including delay.hpp); combine with another agent's V10/V11 diffs, which touch the same files.

### D22 — src/cpp/jank/runtime/core.cpp
- Fixes: D22. Today a finished future's binding frame stays under its thread id, and a later thread with the same id sees it; after, it is gone.
- Change: in `future` (1091-1160), a scope_exit pops the conveyed frame when the thread's body ends (returns, throws or is cancelled).
- Why it is safe: pop_thread_bindings (context.cpp 752-763) only pops; the guard runs before the GC-unregister guard.
- Test that should pass: tests/jank_lean/deviations_test.jank `d22-future-sees-its-creators-bindings-only`.
- Checked by reading: push_thread_bindings (context.cpp 706-750) starts a new frame from the front one. Standalone check: none.
- A build must check: d22.

### D24 — src/cpp/jank/codegen/cpp_processor.cpp
- Fixes: D24. Today a catch that throws plus a finally that throws calls std::terminate; after, the finally's exception propagates, as on the JVM.
- Change: in `gen(try)` (1054-1100), with a finally, an outer try encloses the body's try and its catch handlers; a handler's exception reaches the outer catch(...), which runs the finally outside any destructor. With no catch, the inner try is not emitted (the old output). Without a finally, unchanged.
- Why it is safe: before, a throwing handler unwound through the guard's destructor, which ran the finally; the guard stays for other exits.
- Test that should pass: tests/jank_lean/deviations_test.jank `d24-finally-throwing-after-a-throwing-catch`.
- Checked by reading: evaluate.cpp eval(try) wraps the form in a fn (623-626), so every try goes through this codegen; test/jank/form/try/*.jank keep their meaning; util::format substitutes only "{}". Standalone check: none.
- A build must check: test/jank/form/try/* and cpp/try/*; d24.

### R1 — src/cpp/jank/read/lex.cpp
- Fixes: R1. Today a NUL in a string, symbol or comment hangs read-string, and `#` before a NUL overflows the stack; after, a NUL is read as a character.
- Change: `convert_to_codepoint` (452-468) returns length 1 for a NUL (mbrtowc returns 0 for it).
- Why it is safe: every lexer loop advances by the codepoint length; only NUL's length changes. NUL becomes a symbol constituent, as in Clojure's reader.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a01-a-nul-in-a-string-reads`.
- Checked by reading: the string, symbol, keyword, character, comment, `#` and `~` loops. Standalone check: none.
- A build must check: a01; jank's lexer tests.

### R2 — src/cpp/jank/read/lex.cpp
- Fixes: R2. Today `[1"a"]` and `(str"a")` are read errors; after, they read as in Clojure.
- Change: in `next()`, `"`, `^`, the backquote, `~` and `@` no longer demand whitespace before them (terminating macro characters in Clojure), and a string no longer demands whitespace after it. Numbers, symbols and keywords still do before a number, symbol, keyword or `#` (one invalid token in Clojure).
- Why it is safe: the 12 lexer tests asserting lex_expecting_whitespace (test/cpp/jank/read/lex.cpp 690-1398) are all a number followed by a letter or digit, unchanged. Clojure 1.12: `"\"a\"b"` reads "a", `":a\"b\""` reads :a.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a02-adjacent-atoms-need-no-space` (and, with R14, `a14-at-sign-ends-a-symbol`).
- Checked by reading: lexer and parser test inputs for adjacent macro characters. Standalone check: none.
- A build must check: jank's lexer tests; the book's lex/expecting-whitespace page no longer covers these cases.

### R3 — src/cpp/jank/read/lex.cpp
- Fixes: R3. Today `[-0]` and `-0` at a line end are read errors; after, 0.
- Change: the single-0 escape (1027-1035) also handles `-0`, whose branch (691-707) has already stepped past the `-`.
- Why it is safe: traced -07 (octal kept), -0.5, -0x10, -0N; Clojure 1.12 reads `[-0 -07 -0.5]` as `[0 -7 -0.5]`.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a03-minus-zero-before-a-delimiter`.
- Checked by reading: the number state machine paths above. Standalone check: none.
- A build must check: jank's lexer tests; a03.

### R5a — src/cpp/jank/read/lex.cpp
- Fixes: R5 (the int64 minimum), and LG2's second example together with R5b. Today `-9223372036854775808` reads as a BigInt and `(dec -9223372036854775808)` is -9223372036854775809N; after, it reads as a long and `dec` throws.
- Change: the lexer reads the integer's magnitude with `strtoull`.
- It counts as out of range only above 2^63 for a negative literal, or above 2^63-1 for a positive one.
- The value is the magnitude's two's complement negation when negative.
- Why it is safe: every other integer reads as before, BigInt literals (`N`, out of range) still go to big_integer, and radix forms use the same magnitude.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a05-int64-minimum-reads-as-a-long` (alone).
- Also tests/jank_lean/deviations_r6_test.jank `lg2f-arithmetic-on-the-long-minimum-literal` (needs R5b, and LG2a for its overflow assertions).
- Checked by reading: lex.cpp 1143-1157 and the token's i64 constructor. Standalone check: .r6-scratch/num/cppcheck/r5.cpp → results/r6-num-cppcheck-r5.txt.
- A build must check: `<limits>` include; radix literals of exactly 2^63.

### R5b — src/cpp/jank/codegen/cpp_processor.cpp
- Fixes: R5 in compiled code (with R5a). Without it, a compiled `-9223372036854775808` literal would be emitted as text no signed C++ type holds; after, it is `(-9223372036854775807L - 1)`.
- Change: `lift_constant` (eval, unboxed) and `gen_constant` (boxed and unboxed) emit Long/MIN_VALUE as `(-9223372036854775807L - 1)`, the way the code already special-cases i32's minimum.
- Why it is safe: only the one value is affected; every other integer is emitted as before.
- Test that should pass: tests/jank_lean/deviations_r6_test.jank `lg2f-arithmetic-on-the-long-minimum-literal` (with R5a).
- Checked by reading: cpp_processor.cpp lift_constant 131-149, gen_constant's integer branch 233-246. Standalone check: none.
- A build must check: the emitted text in JIT and AOT (the `L` suffix on Windows, where long is 32-bit, still yields long long).

### R8 — src/cpp/jank/util/escape.cpp
- Fixes: R8. Today `"\101"` and `"\0"` are read errors; after, "A" and NUL.
- Change: `unescape` (35-145) reads octal escapes as Clojure's reader: up to three digits 0-7, ended early by the end, whitespace, a comma or a macro character; any other character is "Invalid digit: c"; at most \377.
- Why it is safe: only parse.cpp's parse_escaped_string calls unescape. jank's extra `\a`, `\v`, `\?` stay accepted (its lexer tests use them).
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a08-octal-string-escapes`.
- Checked by reading: Clojure's StringReader/readUnicodeChar rules (checked on Clojure 1.12: "\08" and "\400" error). Standalone check: .r6-scratch/fix1/cpp/check.cpp (101 -> 65, 08 -> Invalid digit, 400 -> range error, "1 x" ends at the space).
- A build must check: a08; jank's parser tests.

### R9 — src/cpp/jank/read/lex.cpp
- Fixes: R9. Today `(read-string ";x\r42")` hits EOF; after, 42.
- Change: `;` comments (643) and `#!` comments (1419) end at `\r` too, as Clojure's comment reader; the `\r` is then skipped as whitespace.
- Why it is safe: the lexer's comment tests have no `\r`.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a09-a-comment-ends-at-a-carriage-return`.
- Checked by reading: test/cpp/jank/read/lex.cpp comment cases. Standalone check: none.
- A build must check: jank's lexer tests.

### R10 — src/cpp/jank/read/parse.cpp, test/cpp/jank/read/parse.cpp
- Fixes: R10. Today `@x` reads as `(deref x)`, which a local named `deref` captures; after, `(clojure.core/deref x)`.
- Change: `parse_deref` (1786-1807) builds the qualified symbol; jank's parse test "Deref" (1180-1201) is updated to expect it.
- Why it is safe: core.jank uses no `@` before deref's definition (1081); nothing special-cases the bare `deref` symbol; syntax quote qualified it anyway.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a10-deref-is-qualified`.
- Checked by reading: analyzer uses of "deref"; jank's .jank tests (none read `@` as a form). Standalone check: none.
- A build must check: the updated parse test.

### R12 — src/cpp/jank/read/parse.cpp
- Fixes: R12. Today `#(+ %10 %1)` is "invalid shorthand function parameter"; after, a 10-parameter fn.
- Change: in parse_symbol's `%n` branch (1853-1880), only a leading 0 is rejected; a number over 255 is an error instead of wrapping the u8.
- Why it is safe: jank's tests fail-%0 (leading 0) and fail-too-many-args `#(do %20)` (the analyzer rejects more than max_params = 10, processor.cpp 1866) still fail; pass-fixed-args unchanged.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a12-percent-ten-in-an-anonymous-fn`.
- Checked by reading: test/jank/reader-macro/function/*. Standalone check: none.
- A build must check: test/jank/reader-macro/function/*; a12.

### R14 — src/cpp/jank/read/lex.cpp
- Fixes: R14 (the `@` part). Today `a@b` is one symbol; after, `a` then `(clojure.core/deref b)`.
- Change: `is_special_char` (493-497) includes `@`, so symbol, keyword and character tokens end there.
- Why it is safe: no jank source or test has `@` inside a symbol; `~@` and `#?@` are lexed by their own cases.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a14-at-sign-ends-a-symbol`, only with R2 (after `a`, the `@` must not demand whitespace).
- Checked by reading: is_special_char's users (is_symbol_char, keyword checks 1230/1248). Standalone check: none.
- A build must check: a14 with R2; jank's lexer tests.

### R16 — src/cpp/jank/read/parse.cpp
- Fixes: R16. Today `(name :/)` is ""; after, "/".
- Change: `parse_keyword` (1903-1938) treats a slash as a separator only when the text is longer than "/", as parse_symbol does (1832-1837).
- Why it is safe: the lexer already gives the token "/" for `:/` (lexer test "Single slash"); `://`, `:/foo`, `::/` stay lexer errors.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a16-keyword-slash`.
- Checked by reading: symbol `separate` and intern_keyword. Standalone check: none.
- A build must check: a16.

### R19 — src/cpp/jank/read/parse.cpp
- Fixes: R19 (dotted names). Today `` `clojure.set `` is `user/clojure.set`; after, `clojure.set`.
- Change: in `syntax_quote` (1457-1510), an unqualified symbol with a `.` after its first character is left unqualified (Clojure's resolveSymbol).
- Why it is safe: names starting with `.` were already left alone; test/jank/syntax-quote/* have no other dotted names. Clojure 1.12: `` `foo. `` is `foo.`.
- Test that should pass: tests/jank_lean/deviations_reader_test.jank `a19-syntax-quote-leaves-dotted-names`.
- Checked by reading: the symbol branches of syntax_quote. Standalone check: none. Not covered: R19's `~@#{a b}` part.
- A build must check: test/jank/syntax-quote/*.

### R23 — src/cpp/jank/analyze/cpp_util.cpp
- Fixes: R23, U7 (S57) and V52, plus the first assertion of R26's test. Today `(if true 1 2.5)` is 1.0, `((fn [c] (if c 1 cpp/gd)) false)` is 2 and `((fn [c] (if c (hash 1) -1)) false)` is 4294967295. After, each branch keeps its value: 1, 2.5 and -1.
- Change: in `find_branch_common_type`, two branches of different built-in, non-void types are both boxed (`object_ref`) instead of converted to their common C++ type. The types are compared without references and cv.
- Why it is safe: a branch that recurs, a missing else, an object branch and two branches of the same type all keep today's path. `analyze_if` and `analyze_case` already box a branch whose `*_needs_conversion` is set. Boxing strips references and cv (cpp_processor.cpp 1316-1326), so a `cpp/` global boxes.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r23-if-keeps-each-branch-value`; deviations_r4_test.jank `u07-cpp-if-in-a-fn-keeps-a-reference-branchs-value`; tests/jank_lean/deviations_r6_test.jank `v52-if-of-a-hash-and-a-negative`. Each needs only this diff.
- Checked by reading: both callers; the into_object codegen; the `and`/`or` expansions that R23's examples go through.
- Standalone check: none. The Lean typing walk (results/r6-native-typing.txt) gives 0 differences with this switch and the value switches V51, R122 and V62.
- A build must check: no jank test relies on an `if` of two native types keeping a native type. The cost of boxing those ifs.

### R24 — src/cpp/jank/analyze/cpp_util.cpp
- Fixes: R24. Today `(loop [x 0 n 0] (if (= n 1) x (recur 1.5 1)))` is 1; after, 1.5.
- Fixes: with LG2a.diff, also R25's loop example. That loop sums 0..99,999 and gives 704982704 today, 4999950000 after.
- Change: `mutable_type` makes a loop local of a built-in type (number or bool) an `object_ref`, so `recur` boxes into it rather than converting.
- Why it is safe: `analyze_let` already converts a loop's initial value into an object when the type changes (processor.cpp 2396-2411). `analyze_recur` converts each argument to the same type.
- Why it is safe: its `(cpp/= local arg)` check takes the object-on-the-left, native-on-the-right branch (processor.cpp 436-458), which boxes the argument. Clang accepts `=` on two `object_ref`s as a built-in assignment (SemaExpr.cpp 10186-10232 treats a C++ class like a C struct), so R36's caveat does not hold.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r24-loop-local-takes-any-value` (alone). Its `r25-literal-arithmetic-is-long` loop assertion needs LG2a.diff too.
- Checked by reading: `analyze_let`, `analyze_recur`, `build_cpp_call`'s operator branches, CppInterOp `GetBuiltinOperatorType`, Clang's `CheckSingleAssignmentConstraints`.
- Standalone check: none.
- A build must check: `(recur <native>)` into an object local analyzes and runs. The cost of boxed loop counters in core.jank's loops (`dotimes`, `amap`, chunked `doseq`).

### R26 — src/cpp/jank/analyze/processor.cpp
- Fixes: R26. Today `(case 1 1 1.5 2 7 0)` is 1, and `(case 1 1 "one" 2 :two :other)` throws a native error; after, 1.5 and "one".
- Change: in `analyze_case`, after the branches are analyzed, if any branch's type differs from the default's (canonical types), the whole case is boxed: `object_ref`, with every branch and the default converted.
- Why it is safe: a case whose branches all have the default's type keeps today's path. The existing conversion loop boxes natives and erases typed objects. A recur branch was already converted when `needs_conversion` held.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r26-case-branches-keep-their-values` (alone, both assertions).
- Checked by reading: `analyze_case` 1386-1581; how the `case` expression's type reaches codegen.
- Standalone check: none. The Lean case walk (results/r6-native-typing.txt) gives 0 differences with this switch and the value switches.
- A build must check: the macro-generated `case` forms in core.jank still compile, including keyword and string branches.

### R27 — src/cpp/jank/analyze/processor.cpp
- Fixes: R27 (fn inside a loop). Today `recur` in a fn written inside a loop targets the loop; after, the fn.
- Change: `analyze_fn` (1941-) saves, clears and restores `loop_details` around the fn.
- Why it is safe: analyze_recur (2120-2241) targets the loop exactly when loop_details is set; loops inside the fn set it again.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r27-recur-in-a-fn-inside-a-loop-targets-the-fn`.
- Checked by reading: every loop_details use (analyze_recur, analyze_let 2338, analyze_loop 2611). Standalone check: none. Not covered: recur inside the loop's own bindings.
- A build must check: jank's recur/loop tests.

### R29 — src/cpp/jank/analyze/processor.cpp
- Fixes: R29. Today `((fn when [n] (if (= n 0) :done (when 0))) 1)` is nil; after, :done.
- Change: `analyze_call` (3498-3535) skips macroexpansion when the operator is the fn's own name (recursion_reference), as for a local.
- Why it is safe: no defmacro in jank's sources calls its own name as code (core.jank, test.jank, template.jank scanned: only docstrings, comments, syntax quotes). Note R108: jank's defn names its fn, so a defn body calling its own name as a macro would now call the fn; none found.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r29-a-named-fn-shadows-a-macro`.
- Checked by reading: analyze_symbol's named-recursion branch (1660-1675). Standalone check: none.
- A build must check: jank's full suite.

### R30 — src/cpp/jank/runtime/context.cpp
- Fixes: R30 (`&form`). Today a macro gets `&form` = `((args))` and `&env` = its own symbol; after, `&form` is the call form and `&env` nil.
- Change: `macroexpand1` (604-635) passes (form, nil, args...) to the macro fn; the TODO for `&env` stays.
- Why it is safe: jank's macros reading `&form` (`fn`, core.jank 652 and 3584) do `(meta &form)` and now get the call's metadata, as Clojure's do; no macro reads `&env`.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r30-macro-form`.
- Checked by reading: core.jank `&form`/`&env` uses; the analyzer's macroexpand call (processor.cpp 3510). Standalone check: none.
- A build must check: jank's full suite (fn* forms now carry the call's metadata; error positions).

### R33a — include/cpp/jank/runtime/core/math.hpp
- Corrected after the merge's review: R33a now also adds the `else` missing before `if constexpr(jtl::is_same<L, object_ref>)` in math.hpp's `mul` and `pow` primitive-right overloads (94d32623 lines 495 and 1155). Without it, a native bool reaching `*` or `pow` would be a JIT compile error instead of R33b's thrown error.
- Fixes: R33 (with R33b), and the bool part of V64. Today `(+ true 1)` and `(+ (nil? nil) 1)` are 2; after, they throw.
- Change: `detail::primitive_number` excludes `bool`. A `bool` operand then takes a template's "not a number" branch, which throws.
- Why it is safe: no other header uses the concept. `is_zero` already excluded bool. `to_int`, `to_real`, `abs`, `inc` and `dec` of a bool now throw, as Clojure's casts do. `char` stays a number, so `(int \a)` is still 97.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r33-boolean-arithmetic-throws`; tests/jank_lean/deviations_r6_test.jank `v64-boolean-and-char-natives-are-not-numbers`, bool assertions only. Both need R33b.diff too: alone, the throw is a `std::runtime_error`, which `thrown?` misses (V7's class).
- Checked by reading: every template's branches for a `bool` L or R; `detail::type_name` for bool.
- Standalone check: none.
- A build must check: no core.jank code passes a native bool to `+ - * / < min max inc dec abs int float`.

### R33b — include/cpp/jank/runtime/core/math.hpp
- Fixes: with R33a, R33. Today math.hpp's type errors ("Can't add a bool to int.") are `std::runtime_error`s, which `thrown?` and Clojure-level catches cannot see. After, they are string objects, like `inc`'s "Overflow on increment.".
- Change: the file's 35 `throw std::runtime_error{ util::format(...) };` become `throw make_box<obj::persistent_string>(util::format(...)).erase();`.
- Why it is safe: the messages are unchanged. Only the thrown type changes, to the one jank's own `inc` already uses. visit.hpp's "not a number" error is not in this file and stays native.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r33-boolean-arithmetic-throws` (needs R33a.diff too).
- Checked by reading: each replaced throw sits in a template's error branch; persistent_string has a constructor from `jtl::immutable_string`.
- Standalone check: none.
- A build must check: no C++ caller catches `std::runtime_error` from these templates, including the nREPL's handlers and the test runner.

### R34 — src/cpp/jank/analyze/processor.cpp
- Fixes: R34. Today `(:k)` is nil; after, an arity error (Clojure: ArityException, checked on 1.12).
- Change: in `analyze_call` (3569-3579) a keyword call becomes an inlined get only with 1 or 2 arguments; otherwise it is an ordinary call, which throws invalid_arity (object.cpp 80-88).
- Why it is safe: one- and two-argument keyword calls are unchanged.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r34-keyword-call-without-a-map` still FAILS: invalid_arity is a C++ exception and thrown? sees only objects (V7's family); its failure becomes "uncaught C++ exception".
- Checked by reading: keyword::call overloads. Standalone check: none.
- A build must check: r34's new failure text.

### R37 — src/cpp/jank/ir/processor.cpp
- Fixes: R37. Today compiled calls evaluate the arguments before the operator; after, the operator first.
- Change: `gen(call)` (110-121) generates the operator before the arguments.
- Why it is safe: jank's interpreted top level already does this (evaluate.cpp 376); only instruction order changes.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r37-operator-evaluated-first`.
- Checked by reading: dynamic_call's use of the identifiers. Standalone check: none.
- A build must check: the IR optimization passes and -O levels.

### R39 — src/cpp/jank/ir/processor.cpp
- Fixes: R39. Today a nested loop that rebinds a name breaks the outer `recur` (C++ "undeclared identifier"); after, it compiles and runs.
- Change: `gen(let)` for loop_with_recur (510-585) saves and restores `local_to_loop_shadow` around the loop.
- Why it is safe: the outer recur (422, 439) then finds the outer shadow; locals were already restored the same way.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r39-nested-loop-rebinding`.
- Checked by reading: every local_to_loop_shadow use (270, 287, 305, 422, 439, 541, 560). Standalone check: none.
- A build must check: jank's loop tests.

### R41 — src/cpp/jank/codegen/cpp_processor.cpp
- Fixes: R41. Today two letfns in one fn emit invalid C++; after, valid.
- Change: `gen(letfn)` (886-906) clears `deferred_bindings` after filling them in.
- Why it is safe: defer() is called only from gen(closure) (762), and each fn has its own builder.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r41-two-letfns-in-one-fn`.
- Checked by reading: builder::defer and its one caller. Standalone check: none.
- A build must check: jank's letfn tests.

### R42 — src/cpp/jank/runtime/object.cpp
- Fixes: R42 (and keeps D12a safe). Today literal constants that are `=` and hash alike share one object (`['()]` becomes `[[]]`); after, they stay distinct.
- Change: `very_equal_to` and `very_equal_to_with_meta` (336-353) also require the same `to_code_string`.
- Why it is safe: used only by the constant pools (cpp_processor 126, ir/processor.hpp 86/91, hoist_literals.cpp 17); the string is built only when type, hash and `=` already match.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r42-equal-constants-stay-distinct`.
- Checked by reading: the pools' users. Standalone check: none.
- A build must check: compile time is unchanged in practice; jank's tests.

### R54a — src/cpp/jank/runtime/obj/persistent_string_sequence.cpp
- Fixes: R54. Today the seq of a string whose last character is cut short (for example "a" plus the
  first byte of "é") walks past the end and then throws. After the fix it ends at the last byte.
- Change: `next` and `next_in_place` end the walk when the next index is at or past the size
  (`>=`), not only when it equals the size.
- Why it is safe: `count` (78-88) already stops with `<`. `first` is never called past the end
  after the change. Valid UTF-8 text walks exactly as before.
- Test that should pass: tests/jank_lean/deviations_r6_test.jank `v69-a-cut-string-seq-has-its-count` (alone).
- Checked by reading: `next` 128-138, `next_in_place` 140-150, `first` 122-126, `count` 78-88, and
  `substr`'s position check (immutable_string.hpp 162-169). Lean: `jSeqFixed_no_ub` proves the
  fixed walk never goes past the end of any byte string. Standalone check: none.
- A build must check: jank's own sequence tests, and `(vec (seq s))` on a cut string.

### R55a — src/cpp/jank/runtime/obj/persistent_string_sequence.cpp
- Fixes: R55 and V48. Today `(let [x (seq "é")] (= x x))` is false, and such a seq is never found
  in a hash set. After the fix it is true and found.
- Change: `equal` calls `runtime::sequence_equal(this, o)`. That compares the characters the seq
  yields with the other side's elements, instead of the string's bytes.
- Why it is safe: `sequence_equal` (core/seq.cpp 881-) checks identity first, then requires both
  sides sequential, then compares elements with `runtime::equal`. It never calls back into this
  `equal`. `untagged(this)` and `untagged(&o)` convert to object_ref as `seq()` and seq_ext.hpp
  already do. ASCII text compares as before.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b04-string-seq-equals-itself`
  (both assertions); tests/jank_lean/deviations_r5_test.jank `v48-a-set-finds-its-own-string-seq`.
  Both need only this diff.
- Checked by reading: seq_ext.hpp `equal` 12-35, core/equal.cpp `equal(char, object)` 8-17,
  `sequence_equal` 881-, oref.hpp `untagged` 169-185. Standalone check: none.
- A build must check: compiles, since `sequence_equal` is declared in core/seq.hpp 130; and `=`
  between a string seq and lists, vectors and nil.

### R56a — src/cpp/jank/runtime/obj/persistent_string_sequence.cpp
- Fixes: R56. Today `(seq "a")` and `[\a]` are equal but hash differently, so
  `(contains? (hash-set (seq "a")) [\a])` is false. After the fix both hash alike.
- Change: `to_hash` returns `hash::ordered(this)`. That hashes each character the seq yields, the
  way a vector of those characters hashes, instead of hashing raw bytes.
- Why it is safe: `hash::ordered(oref)` (hash.cpp 156-172) walks the sequence and calls each
  character's `to_hash`, the same path a vector takes. It never calls this `to_hash` again.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank
  `b05-string-seq-hashes-as-the-equal-vector` (alone; R55a only matters for non-ASCII text).
- Checked by reading: hash.cpp `ordered` 156-172 and `visit` 151-159, character.cpp `to_hash`
  89-92, persistent_vector's hash. Standalone check: none.
- A build must check: compiles (the one-argument `ordered` is declared in hash.hpp 44); the hash
  of a string seq equals the hash of `(vec s)`.

### R57a — src/cpp/jank/runtime/obj/persistent_string.cpp
- Fixes: R57 and V72. Today `(compare "Ａ" "😀")` is negative, `(compare "é" "")` is 2 and
  `(compare "é" "e")` is 94. After the fix they are Clojure's 9956, 1 and 132.
- Change: `compare(persistent_string)` walks both strings as UTF-16 code units, like Java's
  `compareTo`. It returns the first differing units' difference, else the difference in unit
  counts. A byte that does not start a complete character counts as 0xDC00 plus the byte, so
  only equal bytes compare as 0.
- Why it is safe: only `runtime::compare` reaches it (sort, sorted collections, `compare`).
  `immutable_string::compare` and `operator<`, which jank's internal maps use, are unchanged.
  The order changes only between characters above U+FFFF and U+E000..U+FFFF.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank
  `b06-string-compare-in-utf16-order`; tests/jank_lean/deviations_r6_test.jank
  `v72-compare-of-strings-counts-units` (alone).
- Checked by reading: core/equal.cpp `compare` 24-32 and oref.hpp `compare` 829-881 (no
  normalization), persistent_string.cpp `compare` 63-71. Standalone check:
  .r6-scratch/str/cpp/harness.cpp (results/r6-str-fixes-check.txt).
- A build must check: compiles; sorting strings that hold emoji; sorted sets of strings.

### R57b — src/cpp/jank/runtime/obj/character.cpp
- Fixes: R57 for characters, and V73. Today `(compare \é \e)` is 94; after the fix it is
  Clojure's 132.
- Change: `compare(character)` returns the difference of the two code points, decoded from the
  bytes (no locale). A stray byte counts as 0xDC00 plus the byte.
- Why it is safe: only `runtime::compare` reaches it. ASCII characters give the same values as
  today (memcmp's byte difference).
- Test that should pass: tests/jank_lean/deviations_r6_test.jank `v73-compare-of-characters-subtracts-units`
  (alone).
- Checked by reading: character.cpp `compare` 94-102, `to_integer` 104-110 (left unchanged).
  Standalone check: .r6-scratch/str/cpp/harness.cpp.
- A build must check: compiles; `(sort [\é \e \€ \a])`.

### R58a — src/cpp/clojure/string_native.cpp
- Fixes: R58's start handling and V74. Today `(index-of "a" "a" -1)` is nil,
  `(last-index-of "aa" "a" -1)` is 1 and `(index-of "a" "" 5)` is nil. After the fix they are
  0, nil and 1, as in Clojure.
- Change: `index_of` and `last_index_of` apply java.lang.String's rules for the start, after
  Clojure's `unchecked-int`. For `index_of`, a negative start is 0, and at or past the end only
  an empty value is found (at the end). For `last_index_of`, the start is at most size minus the
  value's size, and a negative start finds nothing.
- Why it is safe: the callers are string.jank `index-of` 227-238 and `last-index-of` 240-251.
  Indices stay bytes, so `(index-of "éa" "a")` is still 2. jank's nREPL bencode defines its own
  `index-of` macro and is not affected.
- Test that should pass: tests/jank_lean/deviations_r6_test.jank `v74-index-of-starts-clamp-as-java` (alone).
  In tests/jank_lean/deviations_r2_test.jank `b07-index-of-in-characters-and-negative-starts`,
  the later two assertions pass; its first (a byte index) does not.
- Checked by reading: immutable_string.hpp `find` 281-320 and `rfind` 340-381; Clojure string.clj
  331-338 and 352-359. Standalone check: .r6-scratch/str/cpp/harness.cpp.
- A build must check: compiles; `index-of` and `last-index-of` with chars and strings.

### R59a — src/cpp/clojure/string_native.cpp
- Fixes: R59 for trim. Today trim of an em space (U+2003) followed by "a" keeps the em space, and
  U+001F is not trimmed. After the fix Java's `Character.isWhitespace` decides, as in Clojure.
- Change: `triml_index` and `trimr_index` step over whitespace characters, ASCII or 3-byte
  (U+1680, U+2000-U+2006, U+2008-U+200A, U+2028, U+2029, U+205F, U+3000), instead of calling
  `isspace` on bytes.
- Why it is safe: the callers are `trim`, `triml` and `trimr` (string.jank 180-193). A stray or
  cut byte is not whitespace, so nothing is cut inside a character.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank
  `b08-trim-and-blank-on-unicode-whitespace`. It needs R59b too (its second assertion is blank?).
- Checked by reading: `trim` 337-354, `triml` 287-302, `trimr` 320-335. Standalone check:
  .r6-scratch/str/cpp/harness.cpp, which caught a bug in the first draft (now fixed).
- A build must check: compiles; trim of text ending in a non-ASCII letter keeps that letter.

### R59b — include/cpp/jtl/immutable_string.hpp
- Fixes: R59 for blank?. Today `(blank? "\u001f")` is false; after the fix it is Clojure's true.
  Text made only of Unicode spaces such as U+2003 is blank too.
- Change: `is_blank` tests each character with Java's `Character.isWhitespace` (ASCII, or a 3-byte
  space character) instead of `std::isspace` on bytes.
- Why it is safe: its only caller is `blank?` (string.jank 205). Through `blank?`, jank's nREPL
  also drops :out or :err that holds only Unicode spaces (handler/eval.jank 41-58).
- Test that should pass: tests/jank_lean/deviations_r2_test.jank
  `b08-trim-and-blank-on-unicode-whitespace` (needs R59a too).
- Checked by reading: immutable_string.hpp `is_blank` 635-645; grep found no other caller.
  Standalone check: .r6-scratch/str/cpp/harness.cpp.
- A build must check: the header still compiles as constexpr/noexcept everywhere it is included.

### R61a — src/cpp/jank/util/string.cpp
- Fixes: R61. Today `(capitalize "Éa")` is "éa"; after the fix it is Clojure's "Éa".
- Change: `capitalize` upper-cases the first character (its UTF-8 bytes, through `to_uppercase`),
  not its first byte through `std::toupper`.
- Why it is safe: its only caller is string.jank `capitalize` 156-164, which lower-cases the text
  first. ASCII text gives the same result. ß as the first letter still stays ß (R60).
- Test that should pass: tests/jank_lean/deviations_r2_test.jank
  `b10-capitalize-of-a-non-ascii-first-letter` (alone).
- Checked by reading: util/string.cpp `to_lowercase`/`to_uppercase` 14-36, `capitalize` 53-71.
  Standalone check: .r6-scratch/str/cpp/harness.cpp (with a stand-in `to_uppercase`).
- A build must check: capitalize under a UTF-8 locale.

### R62a — src/cpp/clojure/string_native.cpp
- Fixes: R62. Today `(replace "é" "" "-")` is "-", byte 0xC3, "-", byte 0xA9, "-" (invalid UTF-8).
  After the fix it is Clojure's "-é-".
- Change: with an empty match, the replacement goes around every character, not every byte.
- Why it is safe: only the empty-match branch of the string/string `replace` changes. Non-empty
  matches and the regex and char overloads are untouched. Characters above U+FFFF stay whole,
  where Java splits the surrogate pair.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b11-replace-of-an-empty-match`
  (alone).
- Checked by reading: string_native.cpp `replace` 164-209 and its callers in string.jank 43-70.
  Standalone check: .r6-scratch/str/cpp/harness.cpp.
- A build must check: compiles; `(replace "ab" "" "-")` is still "-a-b-".

### R63a — src/jank/clojure/string.jank
- Fixes: R63. Today `(escape "é" {\é "X"})` is "é", because each byte is looked up and never
  matches. After the fix it is Clojure's "X".
- Change: `escape` walks `(seq s)`, whose elements are characters, instead of `(count s)` bytes
  with `(nth s index)`.
- Why it is safe: map lookups now see the same characters `seq` and the reader produce. Text with
  no matching key comes out byte for byte as before. A cut string goes through the seq (R54a).
- Test that should pass: tests/jank_lean/deviations_r2_test.jank
  `b12-escape-of-a-non-ascii-character` (alone).
- Checked by reading: string.jank `escape` 207-225, persistent_string_sequence `first`/`next`.
  Standalone check: none (jank code).
- A build must check: clojure.string loads; escape with a map and with a fn.

### R70 — src/cpp/jank/util/escape.cpp
- Fixes: R70. Today `pr-str` writes BEL and VT as `\a`, `\v`, which Clojure's reader rejects; after, raw.
- Change: `escape` (147-201) no longer escapes BEL and VT (Clojure's string printer escapes only \n \t \r \" \\ \f \b).
- Why it is safe: escape() is used by persistent_string::to_code_string (55) and for C++ string literals in cpp_processor (331-456), where other control bytes already go raw.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b17-pr-str-of-bel`.
- Checked by reading: escape()'s callers. Standalone check: none.
- A build must check: string constants with BEL/VT compile.

### R71 — src/cpp/jank/runtime/obj/re_pattern.cpp
- Fixes: R71. Today `(pr-str (re-pattern "\""))` is `#"""`; after, `#"\""`.
- Change: `to_code_string` (23-30) follows Clojure's print-method for a Pattern: `"` becomes `\"`, or `\E\"\Q` inside `\Q...\E`; escapes are copied.
- Why it is safe: only the printed form changes; `to_string` (str) is unchanged.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b18-pr-str-of-a-regex-with-a-quote`.
- Checked by reading: Clojure's core_print.clj Pattern method. Standalone check: .r6-scratch/fix1/cpp/check.cpp (equals Clojure 1.12 for `"` and for `a\Qb"c\E`).
- A build must check: b18.

### R73 — src/jank/clojure/core.jank
- Fixes: R73. Today `(pr-str 1 2)` is an arity error; after, "1 2".
- Change: a full `pr-str` defined after with-out-str (before prn-str, 6315): no args "", one arg to_code_string, more `(with-out-str (apply pr x more))`. The early one-argument def (628-631) stays for core's own use.
- Why it is safe: one-argument calls are unchanged; Clojure 1.12: `(pr-str)` "", `(pr-str nil 1)` "nil 1".
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b20-pr-str-of-several-values`.
- Checked by reading: pr (C++ pr, core.cpp 192), with-out-str (6275). Paren balance checked by script. Standalone check: none.
- A build must check: b20.

### R80 — src/cpp/jank/runtime/core.cpp
- Fixes: R80. Today `(re-find #"(a)?b" "b")` is `["b" ""]`; after, `["b" nil]`.
- Change: `smatch_to_vector` (945-970) puts nil for a group that took no part in the match.
- Why it is safe: users are re-find/re-groups and string_native's replace with a fn (108), where Clojure also gives nil.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b26-an-unmatched-group-is-nil`.
- Checked by reading: smatch_to_vector's callers. Standalone check: none.
- A build must check: b26.

### R82 — src/cpp/jank/runtime/core.cpp
- Fixes: R82 (and R83 for re-matches). Today `(re-matches #"a|ab" "ab")` is nil; after, "ab".
- Change: `re_matches` (1002-1018) uses std::regex_match on the whole input (Java's Matcher.matches), built from data()/size(), so not cut at a NUL.
- Why it is safe: only re-matches calls it.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b28-re-matches-finds-a-full-match`.
- Checked by reading: libstdc++'s DFS executor tries the right alternative in exact mode. Standalone check: .r6-scratch/fix1/cpp/check.cpp (libc++: "ab").
- A build must check: b28 on libstdc++.

### R83 — src/cpp/jank/runtime/obj/re_matcher.cpp
- Fixes: R83 (re-find, re-seq, re-groups). Today `(re-find #"b" "a\u0000b")` is nil; after, "b".
- Change: the constructor (8-13) builds match_input from data()/size(), not c_str().
- Why it is safe: same string up to the first NUL. clojure.string's replace/split (string_native.cpp 82-87, 95, 222-231) still cut at NUL.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b29-regex-input-past-a-nul`.
- Checked by reading: re_matcher's users in core.cpp. Standalone check: none.
- A build must check: b29.

### R84 — src/cpp/clojure/string_native.cpp
- Fixes: R84. Today `(replace "5" #"(\d)" "\\$$1")` is `"\$1"` and a replacement fn gets the match string; after, "$5" and the groups vector.
- Change: `replace(s, regex, string)` (220-226) expands the replacement by Java's appendReplacement rules (a new static helper); `replace(s, regex, fn)` (228-252) calls the fn with re-groups' result (smatch_to_vector).
- Why it is safe: matches are still iterated with std::sregex_iterator (R85 untouched); replace-first with a string keeps ECMAScript format rules.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `b31-replacement-templates-and-functions` (both assertions).
- Checked by reading: Java's appendExpandedReplacement. Standalone check: .r6-scratch/fix1/cpp/check.cpp ("$5"; "$12" with one group "a2"; "$2", "$x", "$", trailing "\" give Clojure 1.12's errors; an unmatched group "").
- A build must check: b31; clojure-test-suite's replace tests.

### R96 — src/cpp/jank/runtime/obj/number.cpp
- Fixes: R96. Today `(compare true false)` throws and `(compare true 1)` is 0; after, 1 and a throw.
- Change: `boolean::compare(object)` compares with another boolean and throws for anything else.
- Why it is safe: `compare(boolean)` already existed; sort goes through compare.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `c01-booleans-compare`.
- Checked by reading: number.cpp 56-71, core/equal.cpp compare. Standalone check: none.
- A build must check: compiling only.

### R97 — src/cpp/jank/runtime/obj/keyword.cpp
- Fixes: R97. Today `(compare :a 1)` is undefined behavior (an unchecked cast); after, it throws an error a program's catch sees, as Clojure's ClassCastException.
- Change: `compare(object const &)` (50-53) checks the type and throws an object (make_box(...).erase(), as inst.cpp, uuid.cpp, math.hpp do).
- Why it is safe: keyword-keyword comparison is unchanged; string and character compare (std::runtime_error) are not changed.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `c02-keyword-against-a-number-throws`.
- Checked by reading: runtime::compare (equal.cpp 24). Standalone check: none.
- A build must check: c02.

### R98 — src/cpp/jank/runtime/core/equal.cpp
- Fixes: R98. Today `(let [x '(1)] (compare x x))` throws; after, 0.
- Change: `compare` (24-32) returns 0 first when both are the same object, as Clojure's Util.compare.
- Why it is safe: identity on the raw oref, as is_identical; Clojure 1.12: `(compare '() '())` 0, distinct lists still throw.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `c03-compare-of-identical-empty-lists`, only if both `'()` are one object in jank.
- Checked by reading: compare's callers. Standalone check: none.
- A build must check: c03 (that `'()` literals share one object).

### R99a — src/cpp/jank/runtime/obj/big_decimal.cpp
- Fixes: R99. Today `(compare 0.1M 0.1)` is -1; after, 0.
- Change: `big_decimal::compare` against a real or small_real compares the decimal's double with the double, as DoubleOps does.
- Why it is safe: every other pair is unchanged.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `c04-bigdecimal-against-a-double`.
- S6 alone also makes it pass.
- Checked by reading: compare 182-190. Standalone check: none.
- A build must check: compiling only.

### R99b — src/cpp/jank/runtime/obj/number.cpp
- Fixes: R99, the other operand order. Today `(compare 0.1 0.1M)` is 1; after, 0.
- Change: `real::compare` and `small_real::compare` against a big_decimal compare doubles.
- Why it is safe: every other pair is unchanged.
- Test that should pass: none existing; the reverse of c04 (`(compare 0.1 0.1M)`).
- Checked by reading: number.cpp 342-356, 460-474. Standalone check: none.
- A build must check: compiling only.

### R100 — src/cpp/jank/runtime/obj/multi_function.cpp
- Fixes: R100. Today a prefer-method declared on an ancestor is ignored ("neither is preferred"); after, honored.
- Change: `reset_cache` (137-143) caches the hierarchy's value, not the var; `is_a` (219-225) takes that value as is; is_preferred then gets a map, so `parents` finds ancestors (Clojure's MultiFn).
- Why it is safe: prefer_method already passed the value (167); get_method's cache check (249) now compares like with like, so the method cache works between hierarchy changes.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `c05b-prefer-method-on-an-ancestor`.
- Checked by reading: every cached_hierarchy/is_a/is_dominant use. Standalone check: none.
- A build must check: c05, c05b; jank's multimethod tests.

### R101 — src/cpp/jank/runtime/core.cpp
- Fixes: R101. Today `get-method` throws when nothing applies; after, nil.
- Change: `get_method` (613-616) calls multi_function::get_method (nil, or the default method) instead of get_fn.
- Why it is safe: dispatch (get_fn) is unchanged; Clojure 1.12 checked.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `c06-get-method-without-one-is-nil`.
- Checked by reading: multi_function::get_method (247-260). Standalone check: none.
- A build must check: c06.

### R103 — src/cpp/jank/runtime/core.cpp
- Fixes: R103. Today `(remove-ns 'clojure.core)` succeeds; after, it throws "Cannot remove clojure namespace".
- Change: `remove_ns` (840-843) refuses clojure.core, throwing an object so thrown? sees it.
- Why it is safe: other namespaces unchanged.
- Test that should pass: tests/jank_lean/deviations_r2_test.jank `c08-clojure-core-cannot-be-removed`.
- Checked by reading: context::remove_ns (420). Standalone check: none.
- A build must check: c08.

### R104 — src/cpp/jank/runtime/obj/persistent_sorted_set.cpp
- Fixes: R104 (sorted sets). Today `(= (sorted-set 0) (sorted-set "a"))` throws; after, false.
- Change: `equal` (56-82) answers false when a lookup throws (keys that cannot be compared), as PersistentTreeSet.equiv catches ClassCastException; catches std::runtime_error and objects.
- Why it is safe: the default comparator runs no user code; broader than Clojure's catch, but only lookups are inside.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r104-sorted-sets-with-incomparable-keys-are-unequal`.
- Checked by reading: contains on sorted sets. Standalone check: none. Not covered: sorted maps (base_persistent_map::equal is shared) and a hash set compared with a sorted one from the hash set's side.
- A build must check: r104.

### R105 — src/cpp/jank/runtime/obj/persistent_sorted_map.cpp
- Fixes: R105. Today `(find (sorted-map 1 :x) 1.0)` is `[1.0 :x]`; after, `[1 :x]`.
- Change: `find` (80-88) builds the entry from the stored key.
- Why it is safe: get and contains unchanged.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r105-sorted-find-returns-the-stored-key`.
- Checked by reading: the map's data iterator (pair of key and value). Standalone check: none.
- A build must check: r105.

### R105b — src/cpp/jank/runtime/obj/transient_sorted_map.cpp
- Fixes: R105 (transient side). Same change in `find` (59-68).
- Change: the entry carries the stored key.
- Why it is safe: as R105.
- Test that should pass: none of the existing tests reaches it; r105 needs R105 only.
- Checked by reading: as R105. Standalone check: none.
- A build must check: compiles.

### R110 — src/cpp/jank/runtime/core.cpp
- Fixes: R110. Today `(find-var 'map)` returns #'clojure.core/map; after, it throws "Symbol must be namespace-qualified".
- Change: `find_var` (835-838) follows Clojure's Var.find: unqualified throws, an unknown namespace throws "No such namespace: x" (both objects), only a var interned in that namespace is found (a referred one gives nil).
- Why it is safe: context::find_var (used everywhere else) is untouched; the one jank caller with a symbol, clojure.test (test.jank 736), passes a qualified one. Clojure 1.12 checked all three cases.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r110-find-var-wants-a-qualified-symbol`.
- Checked by reading: ns::find_var (ns.cpp 117-133). Standalone check: none.
- A build must check: clojure.test runs (test-ns-hook lookup).

### R112 — src/cpp/jank/runtime/core.cpp
- Fixes: R112. Today `in-ns` returns nil; after, the namespace.
- Change: `in_ns` (819-823) returns the namespace it sets.
- Why it is safe: callers (core.jank in-ns, the ns macro) ignore the result.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r112-in-ns-returns-the-namespace`.
- Checked by reading: in-ns's users. Standalone check: none.
- A build must check: r112.

### R114 — src/cpp/jank/runtime/obj/integer_range.cpp
- Fixes: R114. Today `(take 2 (range 9223372036854775807))` throws "integer_range overflow"; after, (0 1).
- Change: `next` and `next_in_place` (113-130) decide whether there is a next element by one overflow-checked step against the bound, not by count().
- Why it is safe: the same answer as `count() > 1` wherever count() works; a step past the i64 range ends the range (Clojure 1.12 agrees on three edge ranges).
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r114-take-from-a-long-range`.
- Checked by reading: both bounds checks. Standalone check: .r6-scratch/fix1/cpp/check.cpp. Not covered: count() itself (R115).
- A build must check: test/cpp integer_range tests; r114.

### R117 — include/cpp/jank/runtime/obj/cons.hpp, src/cpp/jank/runtime/obj/cons.cpp
- Fixes: R117 (through cons). Today `(let [w (cons 0 [1 2 3])] (doseq [x w]) (count w))` never returns; after, 4.
- Change: cons overrides `next_in_place` to return `tail.fresh_seq()`, a seq its caller owns, instead of the tail every copy of the cons shares.
- Why it is safe: object.hpp's next_in_place contract (565-604) says the result is owned and may be mutated; doseq (core.jank 2742/2750) relies on it.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r117-doseq-leaves-held-seqs-alone`.
- Checked by reading: cons::fresh_seq (25-28), cons::next. Standalone check: none. Not covered: other seqs whose next() returns shared state.
- A build must check: r117.

### R118 — src/jank/clojure/core.jank
- Fixes: R118. Today the partition-by transducer sends a partition twice after `reduced`; after, once.
- Change: in partition-by (3291-3321) the buffer is cleared before the partition is sent, refilled only when rf did not return reduced; the completion step clears it too (Clojure's "clear first!").
- Why it is safe: the collection arity is unchanged.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r118-partition-by-after-reduced`.
- Checked by reading: Clojure's partition-by. Paren balance checked by script. Standalone check: none.
- A build must check: r118.

### R120 — include/cpp/jank/runtime/obj/cons.hpp, src/cpp/jank/runtime/obj/cons.cpp
- Fixes: R120 (cons). Today `(coll? (cons 0 [1]))` is false; after, true, and `empty` gives `()`.
- Change: cons gets `static empty()` (persistent_list::empty()), which makes it collection_like.
- Why it is safe: the same change upstream's 2a4777bd made for lazy and string seqs.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r120-cons-is-a-collection`.
- Checked by reading: is_collection (seq.cpp 77), empty (seq.cpp 787). Standalone check: none. Not covered: repeat, sort results, array seqs.
- A build must check: r120.

### R121 — src/cpp/jank/runtime/core/seq.cpp
- Fixes: R121. Today `(get-in 5 [])` is nil; after, 5.
- Change: `get_in` (473-511) drops the outer `get` behavior check; get of a value without lookup is nil or the fallback (object.cpp 190-198).
- Why it is safe: Clojure 1.12: `(get-in 5 [])` 5, `(get-in 5 [:a] :nf)` :nf; inner steps already worked this way.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r121-get-in-with-no-keys`.
- Checked by reading: core.jank get-in (2354) inlines both arities. Standalone check: none.
- A build must check: r121.

### R122a — include/cpp/jank/runtime/core/array.hpp, src/cpp/jank/runtime/core/array.cpp
- Fixes: R122. Today `(aget (byte-array [-1]) 0)` is 255 and `(aget (byte-array [200]) 0)` is 200; after, -1 and -56, as Clojure's signed bytes.
- Change: `byte_array` (all three overloads) and `bytes` create and return `i8` arrays instead of `u8` arrays.
- Why it is safe: `i8` arrays already exist everywhere: the `array<i8>` instantiation, visit.hpp, object.hpp and cpp_util `literal_type`. Nothing else in the runtime makes `u8` arrays.
- Test that should pass: tests/jank_lean/deviations_main_test.jank `r122-bytes-are-signed` (alone).
- Checked by reading: all uses of `u8_array`, `array<u8>` and `element_type::u8`; both `aget` paths (the inlined typed template and `array::nth`).
- Standalone check: none.
- A build must check: any C++ or jank code that reads a byte array as `u8` (none found by grep). `bytes?` needs R122b.diff.

### R122b — src/jank/clojure/core.jank
- Fixes: with R122a, keeps `(bytes? (byte-array 1))` true; with R122a alone it would be false.
- Change: `bytes?` tests for element type `i8` instead of `u8`.
- Why it is safe: one comparison in one function.
- Test that should pass: none of its own; goes with R122a.diff.
- Checked by reading: `bytes?` (core.jank 6775-6781).
- Standalone check: none.
- A build must check: nothing beyond R122a's checks.

### S1 — src/cpp/jank/read/parse.cpp
- Fixes: S1. `(read-string "#'1")` is a read error today; after, it is `(var 1)`.
- Change: parse_reader_macro_var_quote no longer requires a symbol after `#'`. The "must be
  present" error stays.
- Why it is safe: analyze_var_call (processor.cpp 2808-2830) still rejects a non-symbol, which is
  where Clojure fails too. jank's fail-not-a-symbol.jank (`#'"str"`) still fails, now at analysis.
- Test that should pass: deviations_r3_test.jank `s01-var-quote-of-a-non-symbol`.
- Checked by reading: jank's var-quote tests; the jit test runner's fail- rule. Standalone check:
  none.
- A build must check: the in_place list built from a symbol and an object_ref.

### S6 — include/cpp/jank/runtime/obj/big_decimal.hpp, src/cpp/jank/runtime/obj/big_decimal.cpp
- Fixes: S6, and through `<` and `compare` also R99. Today `(+ 1M 0.5)` is 1.5M; after, 1.5.
- Change: non-template `f64` operators `+ - * / < <=` for (decimal, double) and (double, decimal) in `jank::runtime`.
- They convert the decimal to a double. As non-templates they beat boost's mixed templates in math.hpp's lookup.
- Why it is safe: they apply only to exactly those type pairs; decimal/decimal, decimal/long and decimal/BigInt keep their operators.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s06-bigdecimal-and-double-give-a-double`.
- Checked by reading: math.hpp's lambdas, big_decimal.hpp's existing jank::runtime operators and their `using` in obj. Standalone check: none.
- A build must check: the overload choice against boost's templates; no other jank::runtime code expected a decimal from decimal OP double.

### S8 — src/cpp/jank/runtime/core/math.cpp
- Fixes: S8. Today `(rem 1.75M 1/2)` is 0N and `(rem 1/2 0.1M)` throws; after, 0.25M and 0.0M.
- Change: `rem` takes the BigDecimal branch before the ratio branch and turns a ratio operand into a decimal (numerator / denominator).
- Why it is safe: double, ratio-only, BigInt and long branches are unchanged; the decimal fmod is the one jank already used.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s08-rem-of-a-bigdecimal-and-a-ratio`.
- Checked by reading: rem 226-304. Standalone check: none.
- A build must check: native_big_decimal from cpp_int (already used by big_decimal(ratio)).

### S11 — src/cpp/jank/runtime/obj/big_decimal.cpp
- Fixes: S11. Today `(double 1E-310M)` is 0.0; after, 1.0E-310.
- Change: `big_decimal::to_real` reads the decimal's full scientific text with `strtod`: one rounding, subnormals kept. Non-finite values keep convert_to.
- Why it is safe: only to_real; every user of a decimal's double gets the nearest double.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s11-double-of-a-tiny-bigdecimal`.
- Checked by reading: to_real 197-200, cpp_dec_float `str(0, scientific)`. Standalone check: none.
- A build must check: compiling only.

### S12 — src/cpp/jank/runtime/obj/big_decimal.cpp
- Fixes: S12. Today `(long 1E130M)` is 9223372036854775807; after, it throws "Value out of range for long".
- Change: `big_decimal::to_integer` follows RT.longCast: through the double, throwing (as an object) outside the long range, Java's truncation inside it.
- Why it is safe: only to_integer. Within range it now matches Clojure's precision loss too.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s12-long-of-a-huge-bigdecimal-throws`.
- Checked by reading: to_integer 192-195, RT.longCast. Standalone check: none.
- A build must check: make_box include in big_decimal.cpp.

### S14 — src/cpp/jank/runtime/core/math.cpp
- Fixes: S14. Today `(bigdec "inf")` is inf; after, it throws.
- Change: `to_big_decimal` checks BigDecimal(String)'s grammar for strings before building the decimal: `[+-]? (digits [. digits?] | . digits) ([eE] [+-]? digits)?`.
- Why it is safe: only the string branch; BigInt, ratio and small_real keep theirs.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s14-bigdec-of-text-follows-javas-grammar`.
- Checked by reading: to_big_decimal, big_decimal(immutable_string). Standalone check: none.
- A build must check: compiling only.

### S15 — src/cpp/jank/runtime/core/math.cpp
- Fixes: S15. Today `(bigint "010")` is 8N and `(bigint "+5")` throws; after, 10N and 5N.
- Change: `to_big_integer` checks BigInteger(String)'s grammar for strings (a sign, then decimal digits), drops leading zeros and a `+`, then builds the cpp_int.
- Why it is safe: only the string branch; integers keep theirs.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s15-bigint-of-text-is-decimal`.
- Checked by reading: to_big_integer, big_integer::init. Standalone check: none.
- A build must check: compiling only.

### S16 — src/cpp/jank/read/lex.cpp
- Fixes: S16. `0010/3` reads as 8/3 today; after, it reads as 10/3.
- Change: the ratio branch reads the numerator and a big denominator as decimal: a sign and the
  leading zeros are dropped before boost's assign, which read a leading 0 as octal.
- Why it is safe: only the text given to boost changes, and one zero is kept for "0".
- Test that should pass: deviations_r3_test.jank `s16-ratio-parts-are-decimal`.
- Checked by reading: both denominator kinds (integer, big_integer). Standalone check:
  cpp/check.cpp.
- A build must check: native_big_integer::assign(std::string).

### S17 — src/cpp/jank/read/lex.cpp
- Fixes: S17. `1e4294967296M` reads as 1.0M today; after, it is the read error "Exponent
  overflow.".
- Change: a BigDecimal literal whose exponent doesn't fit in an int is a lex error. boost read
  the exponent with atoll and wrapped it.
- Why it is safe: only literals ending in M with such an exponent change.
- Test that should pass: deviations_r3_test.jank `s17-bigdecimal-exponent-overflow-throws`.
  It needs V7 too (read errors as objects); alone, it fails as "uncaught jank error".
- Checked by reading: lex.cpp 1105-1132. Standalone check: cpp/check.cpp.
- A build must check: the <limits> include.

### S18 — src/cpp/jank/runtime/core/math.cpp
- Fixes: S18. Today `(bigint 100000000000000000000/3)` throws; after, 33333333333333333333N.
- Change: `to_big_integer` of a ratio divides numerator by denominator in cpp_int instead of going through i64.
- Why it is safe: one branch; truncation is Ratio.bigIntegerValue's.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s18-bigint-of-a-big-ratio`.
- Checked by reading: to_big_integer, ratio_data. Standalone check: none.
- A build must check: compiling only.

### S20 — src/cpp/jank/runtime/obj/ratio.cpp
- Fixes: S20 and V59. Today `(* 0N 1/2)` and `(+ 1/2 1/2)` print 0 and 1; after, 0N and 1N.
- Change: the four ratio/ratio operators (`+ - * /`) return through a helper that gives a BigInt for an integral result.
- `ratio::create`, which the reader uses (4/2 reads as 2), is unchanged.
- Why it is safe: every integer-with-ratio operator reaches these four or cannot yield an integer.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s20-ratio-arithmetic-with-a-bigint-stays-big`; tests/jank_lean/deviations_r6_test.jank `v59-ratio-arithmetic-with-an-integral-result-is-a-bigint`.
- Checked by reading: ratio.cpp 172-273, ratio.hpp templates, parse.cpp 1975. Standalone check: none.
- A build must check: compiling only.

### S21 — src/cpp/jank/runtime/obj/ratio.cpp
- Fixes: S21. Today `(double -7/3)` is -2.3333333333333335; after, -2.333333333333333.
- Change: `ratio_data::to_real` rounds the quotient half-even to 16 significant digits in cpp_int (MathContext.DECIMAL64), then `strtod`.
- Why it is safe: only to_real; zero is handled first.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s21-double-of-a-ratio`.
- Checked by reading: to_real 108-111, Ratio.doubleValue. Standalone check: .r6-scratch/num/cppcheck/s21.cpp → results/r6-num-cppcheck-s21.txt (bit-identical to Clojure 1.12.0 on 10 ratios).
- A build must check: compiling only.

### S37 — src/cpp/jank/analyze/processor.cpp
- Fixes: S37. `(case 1 1 (def h 1) (h))` fails with "unresolved h" today; after, it gives #'h.
- Change: analyze_case analyzes the clauses before the default, as Clojure's CaseExpr.Parser does.
  The common-type pass runs after, over the clauses in the same order.
- Why it is safe: types and conversions are computed exactly as before. Errors from
  find_branch_common_type are wrapped by analyze_invalid_case, as before.
- Test that should pass: deviations_r3_test.jank `s37-case-analyzes-its-clauses-first`.
- Checked by reading: analyze_case 1386-1580. Standalone check: none.
- A build must check: compile; jank's case tests.

### S38 — src/cpp/jank/analyze/processor.cpp
- Fixes: S38. `(let [comment (fn [x] (str "// " x))] (-> "hi" comment))` gives nil today; after,
  it gives "// hi".
- Change: analyze_call expands one step (macroexpand1) and analyzes the result, so a head that
  names a local is called, not expanded. It adds the :jank/macro-expansion meta that
  context::macroexpand adds per step.
- Why it is safe: this is the analyzer's only macroexpand call, and clojure.core/macroexpand is
  unchanged.
- Test that should pass: deviations_r3_test.jank `s38-macro-expansion-headed-by-a-local`.
- Checked by reading: push_macro_expansions and latest_expansion read the same key. Standalone
  check: none.
- A build must check: compile; error-reporting outputs that show macro expansions.

### S40 — src/jank/clojure/core.jank
- Fixes: S40 (b, c). Today `(int 2147483648)` is 2147483648 and `(int 1e20)` is undefined behavior; after, both throw an ex-info "Value out of range for int", as RT.intCast throws.
- Change: `int` loses its `:inline`. Its body gives a character's code. Otherwise it converts the value to a double, throws when that is outside [-2147483648, 2147483647], else returns `to_int`.
- Why it is safe: `long` keeps calling `to_int`. The callers in core.jank (`dotimes`, `rand-int`, chunked `doseq`/`for`) pass small values. NaN passes and gives 0, as in RT.intCast. `subvec` calls `to_int` directly.
- Test that should pass: tests/jank_lean/deviations_r3_test.jank `s40-int-of-a-long-past-int32-throws` (alone).
- Checked by reading: every use of `int` and `to_int` in core.jank.
- Checked by reading: the new body uses only special forms, `ex-info` (core.jank 113) and runtime functions: `is_char`, `to_real`, `lt`, `to_int`.
- Standalone check: none.
- A build must check: the new body analyzes at its position in core.jank. `(int x)` now returns an object rather than an `i64`, so check the inlined uses in `dotimes`.

### S41a — src/cpp/jank/codegen/api.cpp
- Fixes: S41 (compiled code). `(let [a 1 b 1] {a :x b :y})` is {1 :y} today; after, it throws
  "Duplicate key: 1".
- Change: the six _jank_hset, _jank_amap and _jank_hmap builders throw when a key is already
  there. Key and value are now read in sequence (two va_args in one call had unspecified order).
- Why it is safe: literal duplicates are already read errors, so constant maps never throw.
- Test that should pass: deviations_r3_test.jank `s41-runtime-duplicate-map-keys-throw` (a
  compiled deftest body).
- Checked by reading: the builders' callers in cpp_processor.cpp 413-451 and 655-693. Standalone
  check: none.
- A build must check: compile.

### S41b — src/cpp/jank/evaluate.cpp
- Fixes: S41 (top-level, interpreted). `{(identity 1) :x (identity 1) :y}` is a 2-entry map
  today; after, it throws.
- Change: eval(map) and eval(set) evaluate every key and value, then throw on a duplicate key, as
  RT.map does.
- Why it is safe: in_place_unique keeps its assumption, which now holds.
- Test that should pass: none of the named tests runs this path. s41's assertion is in compiled
  code (S41a).
- Checked by reading: eval(map) 447-491, eval(set) 493-509. Standalone check: none.
- A build must check: immer transient count().

### S60 — src/cpp/jank/runtime/obj/transient_array_map.cpp
- Fixes: S60. `(get t :a :nf)` after `(persistent! t)` returns 1 today; after, it throws.
- Change: get(key, fallback), find and contains call assert_active, and assert_active throws an
  object.
- Why it is safe: the other transients already assert in these methods.
- Test that should pass: deviations_r3_test.jank `s60-array-map-transient-after-persistent`.
- Checked by reading: transient_hash_map, sorted map, sets, vector; no jank test on the text.
  Standalone check: none.
- A build must check: compile.

### S61 — src/cpp/jank/runtime/obj/detail/base_persistent_map.cpp
- Fixes: S61. `(conj {} ())` throws today; after, it gives {}.
- Change: a map's conj of a seq that is neither a vector nor a map assocs each element. Each
  element must be a 2-vector (jank's map entry).
- Why it is safe: vectors and maps take the old paths. Strings fail on their first element, as
  Clojure fails.
- Test that should pass: deviations_r3_test.jank `s61-conj-of-an-empty-list-onto-a-map`.
- Checked by reading: shared by array, hash and sorted maps; test/cpp persistent_array_map.cpp's
  conj test. Standalone check: none.
- A build must check: compile.

### S62 — src/cpp/jank/runtime/obj/atom.cpp
- Fixes: S62. A validator that calls set-validator! on its own atom hangs today; after, it
  returns.
- Change: validate copies the validator under the lock and calls it after releasing it.
- Why it is safe: set_validator validates before it takes the lock, as before.
- Test that should pass: deviations_r3_hangs_test.jank `s62-a-validator-calling-set-validator`.
- Checked by reading: atom.cpp 228-265. Standalone check: none.
- A build must check: compile.

### S63 — include/cpp/jank/runtime/var.hpp, src/cpp/jank/runtime/var.cpp
- Fixes: S63, and U13's same-thread case. An alter-var-root that re-enters its var hangs today;
  after, it gives 10.
- Change: the var's write_mutex is a std::recursive_mutex. Clojure's synchronized alter-var-root is
  re-entrant.
- Why it is safe: write_mutex is used only by bind_root and alter_root.
- Test that should pass: deviations_r3_hangs_test.jank `s63-alter-var-root-re-entering-its-var`.
- Checked by reading: every write_mutex use. Standalone check: none.
- A build must check: compile.

### S64 — include/cpp/jank/runtime/obj/delay.hpp, src/cpp/jank/runtime/obj/delay.cpp
- Fixes: S64. A delay whose body asks `(realized? d)` hangs today; after, it gives false.
- Change: is_realized reads an atomic set where val is set, with the same condition, without
  the mutex.
- Why it is safe: what realized? answers is unchanged, only the lock goes. A failed or nil delay
  is left to D19/V10/V11.
- Test that should pass: deviations_r3_hangs_test.jank `s64-a-delay-asking-whether-it-is-realized`.
- Checked by reading: delay.cpp; core.cpp's delay users. Standalone check: none.
- A build must check: compile. It meets V10/V11's hunks in delay.cpp.

### S71 — src/cpp/jank/runtime/context_dynamic.cpp
- Fixes: S71. `(eval '(do (defmacro m [] 2) (m)))` fails today; after, it gives 2.
- Change: a top-level `(do …)` is evaluated form by form, recursively, as in Clojure's
  Compiler.eval. eval_string and context::eval both use the new helper.
- Why it is safe: other forms are analyzed and evaluated as before. Module compilation still
  records the original form. The static runtime is unchanged.
- Test that should pass: deviations_r3_test.jank `s71-a-top-level-do-sees-its-own-macros`.
- Checked by reading: eval_string 50-125; eval 220-226. Standalone check: none.
- A build must check: compile; module loading and the nREPL.

### S73 — src/cpp/jank/runtime/ns.cpp
- Fixes: S73. `(pr-str *ns*)` is "user" today; after, it is `#object[ns 0x… "user"]`.
- Change: ns::to_code_string writes an #object form; to_string (str) stays the name.
- Why it is safe: codegen emits constants by type, not through an ns's to_code_string.
- Test that should pass: deviations_r3_test.jank `s73-pr-str-of-a-namespace`.
- Checked by reading: cpp_processor.cpp constant paths. Standalone check: none.
- A build must check: compile.

### U2 — src/cpp/jank/runtime/core/math.cpp
- Corrected after the merge's compile check: the first version wrote `d.convert_to<native_big_integer>()`, which needs the `template` keyword (d's type depends on the lambda's argument); the diff now has `d.template convert_to<…>()` and compiles alone (syntax-only, Apple clang).
- Fixes: U2 and S9. Today `(bigdec 0.1)` is the binary value 0.1000000000000000055…M; after, 0.1M. `(bigint 1.0E23)` likewise.
- Change: a helper builds the decimal from the double's shortest text (`std::to_chars`), as BigDecimal.valueOf does through Double.toString.
- Both `to_big_decimal` and `to_big_integer` use it for doubles.
- Why it is safe: only the double branches; NaN and Inf still throw first in to_big_decimal; decimals keep their path in to_big_integer.
- Test that should pass: tests/jank_lean/deviations_r4_test.jank `u02-bigdec-of-a-double-uses-its-shortest-text`.
- Checked by reading: both functions, cpp_dec_float's string constructor (rd_string accepts to_chars' forms). Standalone check: none.
- A build must check: `<charconv>` double support in the toolchain's libstdc++/libc++.

### U3 — src/cpp/jank/analyze/pass/strip_source_meta.cpp
- Fixes: U3 (S44 re-tested). `(eval (list 'quote v))` sets v's `{}` metadata to nil today;
  after, v keeps it.
- Change: a quoted value's :jank/source is stripped on a copy, and only when present. Vars,
  namespaces and atoms keep the old in-place reset.
- Why it is safe: optimize.cpp is the only caller. IR lifting runs after the pass and sees the
  copy.
- Test that should pass: deviations_r4_test.jank `u03-eval-of-a-quoted-object-keeps-its-meta`.
- Checked by reading: ir/builder.cpp 104; eval(primitive_literal). Standalone check: none.
- A build must check: compile.

### U8 — include/cpp/jank/runtime/obj/deferred_cpp_function.hpp, src/cpp/jank/runtime/obj/deferred_cpp_function.cpp
- Fixes: U8, U9, U10, U11, U13, U13b (one cause), and u14's test.
  - Today a lazily compiled fn's first call rebinds its var to the compiled fn: wrappers and
    stubs are lost, identity changes, and alter-var-root hangs.
  - After, the var is left alone.
- Change: realize no longer calls var->bind_root. The deferred object stays the fn's value and
  proxies to the compiled fn. An atomic flag skips the mutex after the first call.
- Why it is safe: the class already proxied for captured values. Only evaluate.cpp 538 creates
  it, and is_fn knows the type.
- Tests that should pass:
  - deviations_r4_test.jank `u08-a-wrapped-fn-stays-wrapped-after-its-first-call`,
    `u09-with-redefs-keeps-its-stub-after-the-original-runs`,
    `u10-calling-an-old-fn-value-keeps-the-redefinition`,
    `u11-a-fn-keeps-its-identity-after-its-first-call`,
    `u14-a-defn-d-fn-has-no-metadata-after-its-first-call`;
  - deviations_r4_hangs_test.jank `u13-alter-var-root-whose-fn-calls-the-vars-fn`,
    `u13b-alter-var-root-whose-fn-waits-on-a-first-call`.
- Checked by reading: deferred_cpp_function.cpp; evaluate.cpp 525-553. Standalone check: none.
- A build must check: the per-call cost of the proxy; eagerly compiled fns still carry {:name}
  meta (U14's other cause, not changed).

### U15 — src/cpp/jank/runtime/core.cpp
- Fixes: U15. `(get (get-thread-bindings) #'*x*)` is a binding box today; after, it is the value.
- Change: the runtime get_thread_bindings returns a copy that maps each var to its value.
- Why it is safe: context::get_thread_bindings, which futures and var lookups use with boxes, is
  unchanged. bound-fn* pushes plain values, which push accepts.
- Test that should pass: deviations_r4_test.jank `u15-get-thread-bindings-holds-values`.
- Checked by reading: context.cpp 693-775; var.cpp 145-165; core.jank bound-fn*. Standalone
  check: none.
- A build must check: compile.

### U16 — src/cpp/jank/runtime/var.cpp
- Fixes: U16. `(str @#'x)` of an unbound var is "unbound@0x… for var #'x" today; after, it is
  "Unbound: #'x".
- Change: var_unbound_root::to_string writes Clojure's text.
- Why it is safe: it is printing only.
- Tests that should pass: deviations_r4_test.jank `u16-an-unbound-root-prints-as-clojure-prints-it`;
  also deviations_r3_test.jank `s70-an-unbound-root-survives-its-var`, unless the GC frees the
  var (S70's unconfirmed half).
- Checked by reading: var.cpp 346-354. Standalone check: none.
- A build must check: compile.

### U17 — src/cpp/jank/runtime/context.cpp
- Fixes: U17. `(push-thread-bindings (array-map #'*x* 1))` throws today; after, it binds.
- Change: push_thread_bindings(object_ref) copies any map's entries into a hash map.
- Why it is safe: hash maps take the old path.
- Test that should pass: deviations_r4_test.jank `u17-push-thread-bindings-takes-an-array-map`.
- Checked by reading: context.cpp 693-747. Standalone check: none.
- A build must check: compile.

### U19 — include/cpp/jank/runtime/obj/multi_function.hpp, src/cpp/jank/runtime/obj/multi_function.cpp
- Superseded in the combined patch by R100.diff, which caches the hierarchy's value as Clojure does; that alone makes `get_method`'s cache check match, which is all u19 needs. U19 and R100 edit the same lines of `reset_cache`, so apply one of them.
- Fixes: U19. A defmethod whose lazy dispatch value is realized by a thread calling the
  multimethod hangs today; after, the call hits the cache without the lock.
- Change: reset_cache also records the hierarchy's value, and get_method compares the current
  value with it. Before, it compared the reference with the value, so it never matched and every
  call took the mutex.
- Why it is safe: cached_hierarchy keeps the reference, which is_a and is_dominant deref. Method
  and prefer changes still reset the cache, and so does a derive (a new value).
- Same cache as fix1's R100.diff, which makes cached_hierarchy itself the value (and is_a take a
  value):
  - R100 alone also fixes u19: get_method's comparison then matches;
  - U19 alone fixes u19;
  - the two conflict in reset_cache. Take R100 and drop U19; R100 is Clojure's shape and also
    passes values to is_preferred.
- Test that should pass: deviations_r4_hangs_test.jank
  `u19-defmethod-with-a-lazy-dispatch-value-realized-by-a-caller-thread`.
- Checked by reading: multi_function.cpp 129-300 (is_a, is_dominant, is_preferred callers).
  Standalone check: none.
- A build must check: compile.

### U27 — src/cpp/jank/runtime/obj/repeat.cpp
- Fixes: U27. `(with-meta (repeat 7) m)` writes m into the original today; after, it makes a copy.
- Change: with_meta always makes a new repeat. For an infinite repeat, fresh_seq returned this
  one.
- Why it is safe: fresh_seq and in-place iteration are unchanged.
- Test that should pass: deviations_r4_test.jank `u27-with-meta-leaves-an-infinite-repeat-alone`.
- Checked by reading: repeat.cpp. Standalone check: none.
- A build must check: compile.

### U28 — include/cpp/jank/runtime/obj/iterator.hpp, src/cpp/jank/runtime/obj/iterator.cpp
- Fixes: U28. `(with-meta (iterate inc 0) m)` and `(range)` never return today; after, they carry
  m.
- Change: iterator is metadatable. with_meta copies fn and current and shares the cached next,
  as Iterate.withMeta does.
- Why it is safe: the other metadatable visitors (sort, the meta hint, the strip pass) only gain
  the type.
- Tests that should pass: deviations_r4_hangs_test.jank `u28-with-meta-on-an-iterate`,
  `u28b-with-meta-on-an-infinite-range`.
- Checked by reading: meta.cpp 40-60 (the hang printed the infinite seq); core.jank range
  (`(iterate inc 0)`). Standalone check: none.
- A build must check: compile. It applies with U30.

### U29 — src/cpp/jank/runtime/core/seq.cpp
- Fixes: U29. `(nth [1 2 3] 1.5)` throws today; after, it gives 2.
- Change: nth/2 and nth/3 pass the truncated index to an indexable's nth, as RT.nth(Object, int)
  receives it.
- Why it is safe: the inline and the fn call the same function. A vector called as a fn still
  needs an integer, as Clojure's does.
- Test that should pass: deviations_r4_test.jank `u29-nth-of-a-vector-truncates-a-double-index`.
- Checked by reading: seq.cpp 648-735; persistent_vector::nth; transient_vector::nth. Standalone
  check: none.
- A build must check: compile.

### U30 — include/cpp/jank/runtime/obj/iterator.hpp, src/cpp/jank/runtime/obj/iterator.cpp
- Fixes: U30. `(realized? (iterate inc 0))` throws today; after, it gives true.
- Change: iterator::is_realized returns true (jank computes each value when the iterator is
  made).
- Why it is safe: it only adds the realizable behavior.
- Test that should pass: deviations_r4_test.jank `u30-an-iterate-is-realized`.
- Checked by reading: core.cpp is_realized 719-737. Standalone check: none.
- A build must check: compile. `(realized? (next it))` stays true (Clojure: false).

### U31 — src/cpp/jank/runtime/obj/persistent_list.cpp
- Fixes: U31. `(pop (with-meta '(1) m))` loses m today; after, it keeps it.
- Change: pop of a one-element list keeps the metadata (EMPTY.withMeta).
- Why it is safe: longer lists pop as before.
- Test that should pass: deviations_r4_test.jank `u31-pop-of-a-one-element-list-keeps-its-meta`.
- Checked by reading: persistent_list.cpp 180-190. Standalone check: none.
- A build must check: compile.

### U32 — src/cpp/jank/runtime/obj/persistent_list.cpp
- Fixes: U32. `(seq (with-meta '(1 2) m))` loses m today; after, it is the list itself.
- Change: seq of a non-empty list returns the list. It returned a copy without metadata.
- Why it is safe: every in-place iteration takes fresh_seq:
  - the next_in_place callers read: seq.cpp, context.cpp, multi_function.cpp, processor.cpp,
    to_string.hpp, sequence_range.hpp;
  - core.jank's doseq uses fresh-seq;
  - repeat::seq already returns this.
- Test that should pass: deviations_r4_test.jank `u32-seq-of-a-list-is-the-list`.
- Checked by reading: the callers above. Standalone check: none.
- A build must check: no caller needs a fresh object from seq().

### U34 — include/cpp/jank/runtime/obj/persistent_array_map.hpp, src/cpp/jank/runtime/obj/persistent_array_map.cpp
- Fixes: U34. `(array-map 0 0 … 8 8)` has 8 entries today; after, it has 9.
- Change: create_from_seq keeps the transient that assoc_in_place returns (a hash map past 8
  entries), and returns object_ref.
- Why it is safe: core.jank's array-map is the only caller, through interop.
- Test that should pass: deviations_r4_test.jank `u34-array-map-keeps-every-pair`.
- Checked by reading: transient_array_map.cpp 67-89; every create_from_seq declaration.
  Standalone check: none.
- A build must check: compile. Past 8 pairs the map is a hash map (Clojure keeps an array map).

### U36 — src/cpp/jank/runtime/obj/re_matcher.cpp
- Fixes: U36 and U37.
  - `(nth m 0)` for a pattern without groups is a byte of the match today; after, it is the match.
  - Without a match it is nil today; after, it throws.
- Change: re_matcher::nth follows Matcher.group(n): "No match found" without a match, and group 0
  only when re-find kept a string.
- Why it is safe: patterns with groups index the groups vector as before.
- Tests that should pass: deviations_r4_test.jank `u36-nth-of-a-matcher-is-the-match`,
  `u37-nth-of-a-matcher-without-a-match-throws`.
- Checked by reading: core.cpp smatch_to_vector and re_find 945-988. Standalone check: none.
- A build must check: compile.

### U38 — src/cpp/jank/runtime/obj/re_pattern.cpp
- Fixes: U38. `(re-pattern (str "x" (char 0) "y"))` matches "x" today; after, the NUL is part of
  the pattern.
- Change: std::regex is built from data() and size(), not c_str().
- Why it is safe: libstdc++ 15.3.0 reads a NUL as an ordinary character in ECMAScript
  (regex_scanner.tcc 168-174).
- Test that should pass: deviations_r4_test.jank `u38-a-pattern-keeps-its-nul`.
- Checked by reading: regex_scanner.tcc 94-200. Standalone check: none.
- A build must check: compile.

### U39 — src/cpp/jank/runtime/core.cpp
- Fixes: U39. `(print-str #"a")` is "a" today; after, it is `#"a"`.
- Change: print, print1 and println write a pattern with to_code_string; str keeps the bare text.
- Why it is safe: only patterns at the top of a print change.
- Test that should pass: deviations_r4_test.jank `u39-print-of-a-pattern`.
- Checked by reading: core.jank print (593-603), core.cpp print, print1, println. Standalone check:
  none.
- A build must check: compile. A pattern inside a printed collection is unchanged.

### U41 — src/jank/jank/nrepl/server/handler/completions.jank
- Fixes: U41. `mapv`'s completion says :ns "user" today; after, it says "clojure.core".
- Change: a var candidate's :ns is its own namespace.
- Why it is safe: candidates that aren't vars keep the searched namespace.
- Test that should pass: deviations_r4_test.jank `u41-completions-name-each-vars-own-namespace`.
- Checked by reading: nrepl-proof's completion snippet checks only the value. Standalone check:
  the file reads whole with Clojure's reader.
- A build must check: the nREPL suite.

### U44 — src/cpp/jank/runtime/obj/exception_info.cpp
- Fixes: U44. `(ex-message *e)` after a compile error is "" today; after, it is the error's
  message.
- Change: exception_info(error_ref) takes the error's message, or its kind's text when empty.
- Why it is safe: to_string still pretty-prints the error.
- Test that should pass: deviations_r4_test.jank `u44-ex-message-of-a-compile-error-in-star-e`.
- Checked by reading: evaluate.cpp safe_eval 733-775; error.hpp base. Standalone check: none.
- A build must check: compile.

### U45 — src/cpp/main.cpp
- Fixes: U45. -main under run-main sees *ns* = clojure.core today; after, it sees user.
- Change: run_main does (in-ns 'user) and (refer 'clojure.core) before loading the target, as
  `jank run` and clojure.main -m do.
- Why it is safe: load_module restores *ns* after loading.
- Test that should pass: deviations_r4_test.jank `u45-main-runs-in-user`.
- Checked by reading: main.cpp run 46-63 and run_main 83-115; the test/bash run-main scripts.
  Standalone check: none.
- A build must check: the cli and clojure.test bash suites.

### U48 — src/jank/clojure/core.jank
- Fixes: U48. `(load "/clojure/walk")` fails today; after, it loads clojure.walk.
- Change: load reads a string as Clojure's resource path; a path without a slash is relative to
  the current namespace. Symbols from load-one pass through.
- Why it is safe: jank's own callers pass lib symbols.
- Test that should pass: deviations_r4_test.jank `u48-load-takes-a-resource-path`.
- Checked by reading: load, load-one, load-lib. Standalone check: portcheck.clj (the mapping
  inverts Clojure's root-resource for libs without `_`).
- A build must check: the module bash suite.

### U49a — src/jank/clojure/core.jank
- Fixes: U49 (load-string). It throws "TODO: port" today; after, it evaluates each form and
  returns the last value.
- Change: load-string calls context::eval_string through __rt_ctx, as load calls load_module.
- Why it is safe: it is a new body for a stub.
- Test that should pass: deviations_r4_test.jank `u49-loading-functions-exist`. It needs U49b-d
  and ns-aliases too, and ns-aliases is not fixed.
- Checked by reading: context_dynamic.cpp eval_string. Standalone check: none.
- A build must check: `(.eval_string ctx (.to_string s))` and `(.unwrap_or … nil)`.

### U49b — src/jank/clojure/core.jank
- Fixes: U49 (load-file). It doesn't exist today; after, it evaluates a file.
- Change: a new load-file that calls context::eval_file.
- Why it is safe: it is a new name.
- Test that should pass: as U49a.
- Checked by reading: context_dynamic.cpp eval_file. Standalone check: none.
- A build must check: as U49a.

### U49c — src/jank/clojure/core.jank
- Fixes: U49 (ns-refers). It throws today; after, it returns the map.
- Change: ns-refers is ported as ns-publics is, with not= on var_ns.
- Why it is safe: it is a new body for a stub.
- Test that should pass: as U49a.
- Checked by reading: ns-publics, ns-interns, filter-key. Standalone check: none.
- A build must check: compile.

### U49d — src/jank/clojure/core.jank
- Fixes: U49 (requiring-resolve). It throws today; after, it resolves, requiring the namespace
  if needed.
- Change: ported with require (serialized-require is unported).
- Why it is safe: it is a new body for a stub.
- Test that should pass: as U49a.
- Checked by reading: resolve, require. Standalone check: none.
- A build must check: compile.

### U50 — src/jank/clojure/core.jank
- Fixes: U50. `(refer 'clojure.string :only #{'join})` is accepted today; after, it throws.
- Change: refer throws when a given :only or :refer is not sequential (Clojure's check).
- Why it is safe: `(keys …)` defaults aren't checked, and :all passes.
- Test that should pass: deviations_r4_test.jank `u50-refer-only-must-be-sequential`.
- Checked by reading: refer 4717-4755. Standalone check: portcheck.clj (the condition).
- A build must check: compile.

### U51 — src/jank/clojure/core.jank
- Fixes: U51. `:verbose` prints nothing today; after, it prints `(clojure.core/load "/lib")`.
- Change: *loading-verbosely* moves before load. load-lib binds it from :verbose, and load-one
  prints.
- Why it is safe: nothing prints unless :verbose is given.
- Test that should pass: deviations_r4_test.jank `u51-require-verbose-prints-the-load`.
- Checked by reading: load-lib, load-one. Standalone check: portcheck.clj (the line is the one
  Clojure prints).
- A build must check: compile. Clojure's alias and refer lines aren't printed.

### U55 — src/jank/clojure/core.jank
- Fixes: U55. `(meta (find-ns 'x))` after `(ns x)` is {:jank/source …} today; after, it is nil.
- Change: the ns macro drops :jank/source from the name's metadata before reset-meta!.
- Why it is safe: a docstring or attr-map still becomes the namespace's metadata.
- Test that should pass: deviations_r4_test.jank `u55-ns-form-leaves-no-namespace-meta`.
- Checked by reading: the ns macro 5604-5645. Standalone check: none.
- A build must check: compile.

### U59b — src/cpp/jank/runtime/core.cpp
- Fixes: U59, in part. `(compile lib)` returns nil today; after, it returns lib.
- Change: compile returns its argument.
- Why it is safe: callers ignored the nil.
- Test that should pass: deviations_r4_test.jank `u59-compile-at-run-time` needs U59a too, and
  U59a is not fixed.
- Checked by reading: core.cpp 1358-1362. Standalone check: none.
- A build must check: compile.

### U61 — src/jank/clojure/data.jank
- Fixes: U61. `(diff {:a 1 :b 2} {:a 1 :b 3})` is `[{:a 1 :b 2} {:a 1 :b 3} nil]` today; after, it
  is `[{:b 2} {:b 3} {:a 1}]`.
- Change: equality-partition and diff-similar dispatch as Clojure's protocols do (set, map,
  sequential, atom), with diff-set.
- Why it is safe: atoms diff as before.
- Test that should pass: deviations_r4_test.jank `u61-diff-subdiffs-maps-and-vectors`.
- Checked by reading: Clojure's data.clj. Standalone check: portcheck.clj (equal to Clojure's
  diff on 20,000 random pairs).
- A build must check: compile.

### U62 — include/cpp/jank/runtime/core.hpp, src/cpp/jank/runtime/core.cpp
- Fixes: U62. `(ex-message "boom")` throws today; after, it is nil, and so are ex-data and
  ex-cause.
- Change: the three give nil for anything but exception_info; ex_message returns object_ref.
- Why it is safe: no C++ caller besides core.jank's three defs.
- Test that should pass: deviations_r4_test.jank `u62-ex-message-of-a-non-exception-is-nil`.
- Checked by reading: every caller (grep). Standalone check: none.
- A build must check: compile.

### U63 — src/cpp/jank/runtime/obj/exception_info.cpp
- Fixes: U63. Throwable->map's :cause and :data come from the outer exception today; after, from
  the root.
- Change: to_map walks to the last cause for :cause and :data.
- Why it is safe: :via and :trace are unchanged.
- Test that should pass: deviations_r4_test.jank `u63-throwable-map-cause-is-the-root-cause`.
- Checked by reading: exception_info.cpp 116-150. Standalone check: none.
- A build must check: compile.

### U66 — src/cpp/jank/runtime/core/seq.cpp
- Fixes: U66. `(counted? "abc")` is true today; after, it is false, as are arrays and hash/sorted
  map and set seqs.
- Change: is_counted returns false for those types first.
- Why it is safe: other types keep the countable rule. Clojure 1.12 was run on 26 values to pick
  the list.
- Test that should pass: deviations_r4_test.jank `u66-strings-are-not-counted`.
- Checked by reading: every countable type. Standalone check: clj/probe1.clj.
- A build must check: compile. jank's clojure-test-suite keeps counted-qmark commented out for
  this.

### U68 — src/cpp/jank/runtime/core/seq.cpp
- Fixes: U68. `(shuffle (repeat 3 :x))` throws today; after, it shuffles.
- Change: shuffle takes any seq; maps, strings and arrays still throw.
- Why it is safe: collections shuffle as before.
- Test that should pass: deviations_r4_test.jank `u68-shuffle-of-any-seq`.
- Checked by reading: visit_seqable's cases. Standalone check: none.
- A build must check: compile.

### U69 — src/jank/clojure/walk.jank
- Fixes: U69. postwalk and prewalk drop list and seq metadata today; after, they keep it (Clojure
  1.12).
- Change: walk's list and seq branches use with-meta of the form's meta.
- Why it is safe: other branches are unchanged.
- Test that should pass: deviations_r4_test.jank `u69-postwalk-keeps-list-metadata`.
- Checked by reading: Clojure 1.12's walk.clj. Standalone check: portcheck.clj (equal to
  clojure.walk on 20,000 forms).
- A build must check: compile.

### U70 — src/cpp/jank/runtime/obj/tagged_literal.cpp
- Fixes: U70. `(pr-str (tagged-literal 'foo "bar"))` is `#foo bar` today; after, it is
  `#foo "bar"`.
- Change: to_code_string writes the form with to_code_string.
- Why it is safe: print and str keep to_string.
- Test that should pass: deviations_r4_test.jank `u70-tagged-literal-prints-its-form-readably`.
- Checked by reading: pr-str is .to_code_string (core.jank 630). Standalone check: none.
- A build must check: compile.

### U71 — src/cpp/jank/runtime/core.cpp
- Fixes: U71. parse-uuid of 32 bare hex digits or a {braced} form gives a uuid today; after, nil.
- Change: parse_uuid needs exactly four dashes and no leading brace before calling stduuid.
- Why it is safe: the #uuid reader is unchanged, and jank's reader tests expect it strict.
- Test that should pass: deviations_r4_test.jank `u71-parse-uuid-needs-the-dashed-form`.
- Checked by reading: stduuid from_string (uuid.h 503-547). Standalone check: none.
- A build must check: compile. Java's short forms ("0-0-0-0-0") stay nil.

### U72 — src/jank/clojure/core.jank
- Fixes: U72. areduce throws "TODO: port unchecked-inc-int" today; after, it reduces.
- Change: unchecked-inc-int is unchecked_inc; jank's int is its long.
- Why it is safe: it is a new body for a stub.
- Test that should pass: deviations_r4_test.jank `u72-areduce-over-an-array`.
- Checked by reading: the areduce macro. Standalone check: none.
- A build must check: compile.

### U73a — src/jank/clojure/core.jank
- Fixes: U73 (newline). It throws today; after, it writes "\n".
- Change: newline prints system-newline.
- Why it is safe: it is a new body for a stub.
- Test that should pass: deviations_r4_test.jank `u73-newline-and-flush` needs U73b too.
- Checked by reading: print. Standalone check: none.
- A build must check: compile.

### U73b — src/jank/clojure/core.jank
- Fixes: U73 (flush). It throws today; after, it flushes *out* and returns nil.
- Change: `(cpp/fflush (cpp/unbox (:* FILE) *out*))`, the unbox form nrepl/server/capture.jank
  uses.
- Why it is safe: it is a new body for a stub.
- Test that should pass: as U73a.
- Checked by reading: *out* is `(cpp/box cpp/stdout)` and with-out-str binds a boxed FILE*.
  Standalone check: none.
- A build must check: the unbox type in core.jank.

### U74b-a — src/jank/clojure/core.jank
- Fixes: U74b (reversible?). It throws today; after, it is true for vectors and sorted
  collections.
- Change: `(or (vector? coll) (sorted? coll))`.
- Why it is safe: it is a new body for a stub.
- Test that should pass: deviations_r4_test.jank `u74b-collection-predicates` needs U74b-a..d.
- Checked by reading: Clojure's Reversible types. Standalone check: none.
- A build must check: compile.

### U74b-b — src/jank/clojure/core.jank
- Fixes: U74b (indexed?). It throws today; after, it is true for vectors.
- Change: `(vector? coll)`.
- Why it is safe: it is a new body for a stub.
- Test that should pass: as U74b-a.
- Checked by reading: Clojure's Indexed types. Standalone check: none.
- A build must check: compile. Transient vectors give false (Clojure: true).

### U74b-c — src/jank/clojure/core.jank
- Fixes: U74b (special-symbol?). It throws today; after, it checks jank's special forms.
- Change: a private set copied from processor.cpp specials() plus catch and finally.
- Why it is safe: it is a new body for a stub.
- Test that should pass: as U74b-a.
- Checked by reading: processor.cpp 1190-1215 and is_special. Standalone check: portcheck.clj
  (the set reads).
- A build must check: compile.

### U74b-d — src/jank/clojure/core.jank
- Fixes: U74b (into-array/1). It throws today; after, it makes an object array.
- Change: into-array/1 is to-array.
- Why it is safe: it is a new body for a stub; into-array/2 stays unported.
- Test that should pass: as U74b-a.
- Checked by reading: to-array (core.jank 5020). Standalone check: none.
- A build must check: compile.

### U75 — src/cpp/jank/runtime/core/math.cpp
- Fixes: U75. Today `(bit-not 5N)` is -6; after, it throws.
- Change: the bit operations read their operands through a `bit_operand` that rejects a big_integer (Numbers.bitOpsCast), then calls `to_i64`.
- Why it is safe: `to_i64` itself is unchanged, since vector and string indexes use it with BigInts.
- Test that should pass: tests/jank_lean/deviations_r4_test.jank `u75-bit-operations-reject-bigints`.
- Checked by reading: every to_i64 caller. Standalone check: none.
- A build must check: compiling only.

### U76 — src/jank/clojure/core.jank
- Fixes: U76. `(spit f 42)` throws today; after, it writes "42".
- Change: spit writes `(str content)`.
- Why it is safe: strings write as before.
- Test that should pass: deviations_r4_test.jank `u76-spit-writes-any-value-as-str`.
- Checked by reading: spit. Standalone check: none.
- A build must check: compile.

### U77 — src/jank/clojure/core.jank
- Fixes: U77. `(slurp f :encoding "UTF-8")` is an arity error today; after, it reads the file.
- Change: slurp takes `[f & opts]`; the options are ignored (jank reads bytes).
- Why it is safe: one-argument calls are unchanged.
- Test that should pass: deviations_r4_test.jank `u77-slurp-takes-options`.
- Checked by reading: slurp. Standalone check: none.
- A build must check: compile.

### U78 — src/jank/clojure/core.jank
- Fixes: U78. spit to a path it can't open returns nil today; after, it throws.
- Change: spit throws `(str f " (No such file or directory)")`, slurp's own form, when the file
  doesn't open.
- Why it is safe: files that open write as before.
- Test that should pass: deviations_r4_test.jank `u78-spit-into-a-missing-directory-throws`.
- Checked by reading: spit and slurp. Standalone check: none.
- A build must check: compile.

### U83 — src/cpp/clojure/data/json_native.cpp
- Fixes: U83. `(json/read-str "18446744073709551615")` is -1 today; after, it is the BigInt.
- Change: an unsigned JSON integer past i64 is boxed as a big_integer.
- Why it is safe: smaller integers are unchanged.
- Test that should pass: deviations_r4_test.jank `u83-json-reads-big-integers-exactly`.
- Checked by reading: json_native.cpp read. Standalone check: cpp/check.cpp (the boundary).
- A build must check: compile. Integers past u64 still arrive as doubles.

### U86 — src/cpp/clojure/data/json_native.cpp
- Fixes: U86. `(json/write-str ##NaN)` is "null" today; after, it throws.
- Change: writing NaN or an infinity throws data.json's messages.
- Why it is safe: finite doubles write as before.
- Test that should pass: deviations_r4_test.jank `u86-json-does-not-write-nan`.
- Checked by reading: json_native.cpp write. Standalone check: none.
- A build must check: compile.

### U87 — src/cpp/clojure/data/json_native.cpp
- Fixes: U87. `(json/read-str "" :eof-error? false :eof-value :none)` throws a native error
  today; after, it gives :none.
- Change: empty or whitespace-only text is EOF: the eof-value, or "JSON error (end-of-file)" when
  eof-error? is set.
- Why it is safe: other text goes to nlohmann as before.
- Test that should pass: deviations_r4_test.jank `u87-json-eof-value`.
- Checked by reading: json.jank read-str's options. Standalone check: none.
- A build must check: compile.

### V3 — src/cpp/jank/jit/processor_dynamic.cpp
- Fixes: V3. Today a library file dlopen refuses goes to `llvm::cantFail`: undefined behavior in a release build, an abort in a debug one. After: a `std::runtime_error` naming the library and giving LLVM's message.
- Change: in `load_dynamic_library_impl`, the `llvm::Error` from `LoadDynamicLibrary` is checked instead of passed to `cantFail`. On failure it throws "Unable to load the dynamic library `<path>`: <message>".
- Why it is safe: nothing changes when dlopen succeeds. The same file already checks an `llvm::Error` this way (662-669). The function's other two failures are also `std::runtime_error`. The only callers are `load_libs` (startup `-l`) and the function's own recursion.
- Test that should pass: tests/jank_lean/deviations_r6_test.jank `fix-v03-loading-a-file-that-is-not-a-library-throws`. Round 5's v03 asserts `thrown?`, which sees only objects (V7), so v03 itself still fails: the error is native.
- Checked by reading: the callers (432-435, 873-895, 936); the test's path through `parse_ld_script` to the changed lines; `llvm::toString` and `jtl::move` are used in jank already. Standalone check: none.
- A build must check: it compiles; the round 6 test gives `:native`; a failing `-l` at startup prints the error.

### V8 — src/jank/clojure/core.jank
- Fixes: V8. Today a require whose module fails leaves the namespace it created. After: the namespace is removed, as in Clojure.
- Change: `load-lib` gets a second handler, `(catch cpp/jank.error_ref e …)`. Like the object handler beside it, it removes the namespace if it was new, then rethrows.
- Why it is safe: `load_module` turns every failure into an `error_ref` (context.cpp 340-353), which the existing object handler never saw. The same value is rethrown, so callers see what they saw before. Bundled jank code already catches `jank.error_ref` (nrepl/server/core.jank 101, 139).
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v08-a-failed-require-removes-the-namespace-it-created`.
- Checked by reading: `load` and `.expect_ok` (core.jank 4801-4812); `remove-ns` (4610); `throw` of a native value (analyze_throw 2865-2910; codegen 1024-1051); round 5's `vb-outcome` used the same catch and ran on jank. The hunk also applies after U51.diff. Standalone check: none.
- A build must check: clojure.core compiles with the handler; v08 passes.

### V10 — include/cpp/jank/runtime/obj/delay.hpp, src/cpp/jank/runtime/obj/delay.cpp
- Fixes: V10. Today a failed delay throws the native error at the first deref and a string object at the second. After: the same exception at every deref.
- Change: the `std::exception` handler keeps `std::current_exception()` in a new member, `std::exception_ptr native_error`. Later derefs rethrow it with `std::rethrow_exception`.
- Why it is safe: jank's native errors are `std::runtime_error`s that hold no GC pointers, and the `exception_ptr` keeps them alive. `delay` is used only by core.cpp's `delay`, `force` and `deref`. `is_realized` is unchanged.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v10-a-failed-delay-throws-the-same-kind-each-deref`.
- Checked by reading: delay.cpp 19-47; core.cpp 1253-1264; `nth`'s error is a `std::runtime_error` (persistent_vector.cpp 329). Standalone check: none.
- A build must check: it compiles; v10 passes. Conflicts with D19.diff (the same lines). The merged version is .r6-scratch/fix3/merged/D19+V10+V11.diff.

### V11 — include/cpp/jank/runtime/obj/delay.hpp, src/cpp/jank/runtime/obj/delay.cpp
- Fixes: V11. Today a delay whose body raises a read, analysis or load error runs the body again at every deref. After: the body runs once, and the error is rethrown.
- Change: a `catch(error_ref const e)` keeps the error in a new member, `jtl::option<error_ref> jank_error`. Later derefs throw it. delay.hpp now includes jank/error.hpp.
- Why it is safe: the error is kept as an `error_ref`, so the GC sees what it points to. jank's GC doesn't scan exception memory. exception_info.hpp 55 keeps an `error_ref` the same way. The other handlers are unchanged.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v11-a-delay-whose-body-fails-to-read-runs-once`.
- Checked by reading: `error_ref` (error.hpp 293); `make_ref` allocates with the GC (ref.hpp 147); `jtl::option` accepts an assignment (option.hpp 133). V10 and V11 apply together in either order. Standalone check: none.
- A build must check: it compiles with the new include; v11 passes. Conflicts with D19.diff, as V10 does.

### V12 — src/cpp/jank/runtime/core.cpp
- Fixes: V12. Today a future whose body raises a read, analysis or load error ends the process: `catch(...)` rethrows out of the thread, which calls `std::terminate`. After: deref throws an exception object.
- Change: the future's thread function gets a `catch(error_ref const e)`, placed after the object handler. It stores `make_box<obj::exception_info>(e)` as the future's error.
- Why it is safe: this is the constructor evaluate.cpp 750 uses for `*e`. The new handler takes the same lock and sets the same fields as its neighbors. `catch(...)` and the forced-unwind handler are unchanged.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v12-a-future-whose-body-fails-to-read-can-be-dereferenced`.
- Checked by reading: future 1091-1171; future.cpp deref 26-29; exception_info.hpp is already reachable from core.cpp. V12 and V13 apply together in either order. Standalone check: none.
- A build must check: v12 passes and the process doesn't abort.

### V13 — src/cpp/jank/runtime/core.cpp
- Fixes: V13. Today a failed future's deref throws a string. After: it throws an exception object with the native error's message and nil data, like Clojure's ExecutionException.
- Change: the future's `std::exception` handler stores `make_box<obj::exception_info>(e.what(), jank_nil)` instead of `make_box(e.what())`.
- Why it is safe: only the type of what a failed future throws changes. Its message is the same text. No jank test expects a string (the parallelism tests' futures never fail).
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v13-a-failed-futures-deref-throws-an-exception-not-a-string`.
- Checked by reading: the constructor `exception_info(message, data)` (exception_info.cpp 16); `jank_nil` (nil.hpp 70); test/bash/parallelism. Standalone check: none.
- A build must check: v13 passes.

### V14 — src/cpp/jank/evaluate.cpp
- Fixes: V14. Today a top-level `def` whose value throws still sets the def's metadata on the var. After: the metadata is set only once the value is bound.
- Change: in `eval(def)`, `var->set_meta(meta)` moves after `bind_root`, and before the return in the no-value branch. The metadata is still evaluated, and `set_dynamic` still runs, before the value.
- Why it is safe: this is the order of Clojure's DefExpr.eval, and of jank's own generated code for `def` (ir/processor.cpp 82-95, cpp_processor.cpp 528-556). Evaluating the value never reads the var's metadata.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v14-a-def-whose-value-throws-sets-no-metadata`.
- Checked by reading: eval(def) 333-362; eval(function) 522-554; deferred_cpp_function.cpp 17-70; jank's form/def tests. Standalone check: none.
- A build must check: v14 passes, and so do test/jank/form/def.

### V16 — src/cpp/jank/runtime/core.cpp
- Fixes: V16. Today `(ex-data (ex-info "m" nil))` is nil. After: `{}`, as in Clojure 1.12.
- Change: in `ex_info`, nil data is replaced by `persistent_array_map::empty()`.
- Why it is safe: `ex_info` is the only place that builds an exception_info from a message and data. Non-nil data is unchanged.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v16-ex-info-with-nil-data-has-empty-data`.
- Checked by reading: ex_info 1321-1336; the other construction is evaluate.cpp 750; `empty()` (persistent_array_map.hpp 48-52). Standalone check: none.
- A build must check: v16 passes.

### V17a — src/cpp/jank/runtime/context.cpp
- Fixes: V17 (part 1 of 2). Today `read-string` of a text with no form returns nil. After: it throws "EOF was reached while reading", unless the options give an `:eof` value (nil included), as in Clojure.
- Change: `read_string(code, reader_opts)` adds `:eof :eofthrow` when the options are a map without `:eof`.
- Why it is safe: this overload is called only by clojure.core's `read-string` and by the one-argument overload, which already passes `:eofthrow`. Whole-file reading uses a different overload and is unchanged. A text that holds a form still returns it.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v17-read-string-of-an-empty-text-throws`, `v17b-read-string-of-a-comment-throws` and `v17c-read-string-with-options-but-no-eof-throws`. They need V17b too.
- Checked by reading: context.cpp 166-313; core.cpp read_string 1285-1296; core.jank read-string 5974-5985 and read's docstring 5919-5920; Clojure's LispReader.read. Standalone check: none.
- A build must check: the three tests pass; `(read-string "(")` still raises the same error (v07).

### V17b — src/cpp/jank/runtime/context.cpp
- Fixes: V17 (part 2 of 2). Today the end-of-text error is a native `std::runtime_error`, which an object catch and `thrown?` don't see. After: an object with the same message.
- Change: the end-of-text throw becomes `throw make_box("…").erase()`, the way inst.cpp throws its read errors.
- Why it is safe: nothing in jank catches this error (no other user of the message or of `:eofthrow`). Only its kind changes.
- Test that should pass: the three V17 tests above, with V17a.
- Checked by reading: the `throw_on_eof && eof_found` branch (291-295); grep for its catchers. Standalone check: none.
- A build must check: the three tests pass.

### V19 — src/cpp/jank/c_api.cpp
- Fixes: V19, and V20 under the dynamic runtime. Today `jank_call2` catches what the fn throws, prints it and returns nil. After: the exception reaches the caller, as with `jank_call1` and `jank_call3`-`11`.
- Change: the `cpptrace::try_catch` in `jank_call2` is removed. Its body is `return f_obj.call(a1_obj, a2_obj).erase().raw();`, as before commit cf163ef8.
- Why it is safe: the only jank caller is the generated AOT main. There the exception now reaches `jank_init_dynamic`'s handlers, which print it once and return 1. A C caller now gets the exception, as from every other `jank_callN`.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v19-c-api-call2-lets-the-fns-exception-reach-the-caller`. The control `v19b-…` still passes.
- Checked by reading: jank_call2 168-181; aot/processor.cpp 119-127; c_api_dynamic.cpp 103-129; the AOT bash tests' expectations. Standalone check: none.
- A build must check: v19 and v19b pass; an AOT program whose `-main` throws exits 1 under the dynamic runtime.

### V20 — src/cpp/jank/c_api.cpp
- Fixes: V20 under the static runtime (also round 4's U47). Not confirmed by a run. Today the program exits 0 when `-main` throws. After: 1 (with V19.diff).
- Change: `jank_init_static` returns `ret` instead of `0`.
- Why it is safe: `ret` holds `fn`'s result, or 1 from each handler. Commit 9cd54e5b set it and left `return 0;` behind. `jank_init_dynamic` returns `ret`.
- Test that should pass: none. Use REPORT-5's V20 shell steps with a static-runtime build and V19.diff; expected status 1.
- Checked by reading: jank_init_static 1133-1169 and its history (84c91211, 78bdf47d, 9cd54e5b). Standalone check: none.
- A build must check: a throwing `-main` exits 1 and a normal program exits 0, on both runtimes.

### V21a — src/cpp/jank/c_api.cpp
- Fixes: V21 (symbols). Today `jank_symbol_create(nil, "a")` gives `nil/a`. After: `a`, as `Symbol/intern(null, "a")` does.
- Change: in `jank_symbol_create`, a nil namespace builds the symbol with an empty namespace and the name as given.
- Why it is safe: only the nil-namespace case changes. No codegen emits this call. An empty namespace is how jank represents an unqualified symbol (`namespace` returns nil, core.cpp 494).
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v21-c-api-symbol-with-a-nil-namespace-is-unqualified`.
- Checked by reading: c_api.cpp 433-438; symbol.cpp 60-65; ns_dynamic.cpp 35 makes symbols the same way. Standalone check: none.
- A build must check: v21 passes.

### V21b — src/cpp/jank/c_api.cpp
- Fixes: V21 (keywords). Today `jank_keyword_intern(nil, "a")` gives `:nil/a`. After: `:a`.
- Change: in `jank_keyword_intern`, a nil namespace interns the name alone, as jank's own `keyword` does.
- Why it is safe: only the nil-namespace case changes. It mirrors core.cpp `keyword` (521-542).
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v21b-c-api-keyword-with-a-nil-namespace-is-unqualified`.
- Checked by reading: c_api.cpp 139-147; context.cpp intern_keyword 561-600. Standalone check: none.
- A build must check: v21b passes.

### V22 — include/cpp/jank/c_api.h
- Fixes: V22. Not confirmed by a run. Today a C file that includes c_api.h fails at the uses of `bool` (358, 367). After: it compiles.
- Change: `#include <stdbool.h>` when compiled as C, before the `extern "C"` block.
- Why it is safe: C++ doesn't see the include. C gets the standard `bool`.
- Test that should pass: none.
- Checked by reading: the header's two uses of `bool`. Standalone check: .r6-scratch/fix3/check-v22/result.txt. The fixed header compiles with the Mac's clang as C11, C17, gnu17 and C++20; the original fails as C.
- A build must check: nothing beyond the normal build.

### V23 — src/cpp/jank/c_api.cpp
- Fixes: V23. Not confirmed by a run. Today `jank_eval_file_c` prints "jank_eval_file_c <path>" on stdout. After: it doesn't.
- Change: the debug `println` is removed.
- Why it is safe: the line only prints.
- Test that should pass: none.
- Checked by reading: jank_eval_file_c 65-75. Standalone check: none.
- A build must check: nothing beyond the normal build.

### V24 — src/jank/jank/math.jank
- Fixes: V24. Today `(require 'jank.math)` fails: "The symbol `native/raw` could not be resolved." After: it loads, and `(jank.math/sqrt 4.0)` is 2.0.
- Change:
  - The four bodies call jank's runtime math (`cpp/jank.runtime.tan`, `sqrt`, `abs`, `pow`).
  - The unused `:arities` metadata goes.
  - The ns form excludes clojure.core's `abs`.
- Why it is safe: clojure.core already calls these templates this way with object arguments (`abs`, and `add`, which has the same four overloads as `pow`). For objects they compute what the old raw code did.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v24-jank-math-loads`.
- Checked by reading: math.hpp 994-1176; core.jank 1827 and 1373-1383; ns.cpp 89-97 (the warning when a name replaces a referred one); grep finds no reader of the `:arities` keys. Standalone check: none.
- A build must check: v24 passes; `tan`, `abs` and `pow` give the old values.

### V38 — src/cpp/jank/runtime/obj/inst.cpp
- Fixes: V38, V39, V40 and V45. One cause: `#inst` was read with `std::chrono::parse` and four fixed formats.
  - Today a `Z` offset, a leap second, an offset after a date or an hour alone is a read error.
  - Today a fraction of more than 9 digits is a read error or moves the instant.
  - After: each reads as in Clojure.
- Change: `inst_from_string` reads Clojure's grammar directly, with Clojure's checks (instant.clj parse-timestamp and validated):
  - `yyyy[-MM[-dd[Thh[:mm[:ss[.fraction]]]]]][Z|(+|-)hh:mm]`;
  - fraction digits past the 9th are dropped;
  - a leap second rolls into the next minute.
  An instant outside the years 1678-2261, which jank's nanosecond time point can't hold, is now a read error.
- Why it is safe: the only caller is `inst::inst(string)`. jank's own reader tests read the same values as before, and `#inst ""` is still an error. The libc++ branch is unchanged. The read no longer needs the en_US.UTF-8 locale.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v38-inst-reads-a-z-offset`, `v39-inst-reads-a-leap-second`, `v40-inst-fraction-of-more-than-nine-digits` and `v45-inst-reads-an-offset-after-a-date`.
- Checked by reading: inst.cpp 31-64; the creators (parse.cpp 963, c_api.cpp 461); test/jank/reader-macro/instant. Standalone check: .r6-scratch/fix3/inst-parse/ (the parser verbatim, compiled with the Mac's clang).
  - It matched Clojure 1.12.0 on 64 chosen inputs: every test literal, the range limits, and 30 errors.
  - On 30,000 generated inputs, 29,821 matched. The 179 that differ all have years outside 1678-2261.
- A build must check: the four tests and test/jank/reader-macro/instant pass on Linux (libstdc++).

### V41 — src/cpp/jank/runtime/obj/inst.cpp
- Fixes: V41 and V42. One cause: an inst kept sub-millisecond precision, which a Clojure Date doesn't.
  - Today, before 1970 `inst-ms` and printing are 1 ms off.
  - Today `=` compares nanoseconds, so an inst isn't `=` to the read of its printed form.
  - After: both are to the millisecond, as in Clojure.
- Change: `inst::inst(string)` floors the read instant to milliseconds.
- Why it is safe: Clojure's reader floors the instant to milliseconds the same way (instant.clj 247). `inst-ms`, printing, `=` and the hash all keep working on the stored value; it is now whole milliseconds.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v41-inst-before-1970-keeps-its-millisecond` and `v42-inst-equality-is-to-the-millisecond`.
- Checked by reading: core.cpp inst_ms 1056-1066; inst.cpp equal 66-75, printing 77-81, to_hash 104-107. Standalone check: .r6-scratch/fix3/inst-floor/floor.cpp (results: -1; -31536000000; equal).
- A build must check: both tests pass.

### V43 — include/cpp/jank/runtime/obj/inst.hpp, src/cpp/jank/runtime/obj/inst.cpp
- Fixes: V43. Today `compare` and `sort` of insts throw. After: insts compare as java.util.Date does, to the millisecond (-1, 0 or 1).
- Change: inst gets the compare behavior: `compare(object const &)` overrides the throwing default, and `compare(inst const &)`, modeled on character's.
- Why it is safe: `compare` and `sort` reach the override (equal.cpp 24-32, seq.cpp 1098-1131). Comparing an inst with another type still throws, as in Clojure.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v43-insts-compare`.
- Checked by reading: object.cpp 228-233; character.cpp 94-102; oref compare. Standalone check: .r6-scratch/fix3/inst-floor/floor.cpp (results: -1, 1, 0).
- A build must check: v43 passes.

### V44 — src/cpp/jank/read/parse.cpp
- Fixes: V44. Today, with `*default-data-reader-fn*` bound, `#inst` and `#uuid` become tagged literals. After: they are read as an inst and a uuid, and the default fn gets only tags nothing else reads.
- Change: in `parse_reader_macro_tagged`, the built-in tags (`uuid`, `inst`, `cpp`) are tried before `*default-data-reader-fn*`. The unsupported-tag error stays last.
- Why it is safe: this is Clojure's order (LispReader.readTagged 1435-1451) and jank's own docstring (core.jank 7699-7703). `*data-readers*` is still first. No jank test binds the default fn.
- Test that should pass: tests/jank_lean/deviations_r5_test.jank `v44-default-data-reader-fn-leaves-inst-and-uuid`.
- Checked by reading: parse.cpp 1008-1124; grep of test/ and src/jank. Standalone check: none.
- A build must check: v44 and test/cpp/jank/read/parse.cpp pass.

V48 has no diff of its own: its fix is the same code line as R55a.diff (string seq equality by characters). `v48-a-set-finds-its-own-string-seq` should pass with R55a.diff.

### Not fixed, by area

One line per confirmed id that has no diff, and why.

#### Numbers (area N)

- S2 (and U1, its re-test): BigDecimal is cpp_dec_float<100> without a scale; exact division needs a new representation or a rational bridge in every decimal operator.
- S3: the non-terminating check needs the same exact decimal arithmetic as S2.
- S4: 128 significant digits are the representation's limit.
- S5: Java's toString needs the scale the representation lacks (R72).
- S7: an exact remainder of decimals beyond 128 digits needs exact arithmetic.
- R5's ratio half (`9223372036854775808/2` read as a long): parse.cpp needs to know the token was big; not local to the lexer fix.
- Note on overlaps: each diff applies alone. Several edit the same file:
  - math.hpp: LG2a, D2, D6;
  - math.cpp: LG2c, D4, D5, D7, D10, S8, S14, S15, S18, U2, U75;
  - big_decimal.cpp: D8, R99a, S6, S11, S12;
  - number.cpp: R96, R99b;
  - ratio.cpp: S20, S21.
- fixes/combined/README.txt (another agent) may resolve those overlaps.

#### Native values (area P)

- R25: its literal arithmetic, `(+ 2147483647 1)`, is fixed by agent N's LG2a.diff (exact `i64` checked operations on `+ - *`); its loop example needs R24.diff as well. No separate diff, so as not to rewrite the same math.hpp lines a third time.
- U7: covered by R23.diff (same cause: a reference branch meets a native branch in `find_branch_common_type`).

#### Strings (area W)

- LG3 / R52 (byte indices in count, nth, get, contains?, subs, index-of): no coherent local fix.
  A code-point `subs` beside the byte `count` breaks `(subs s (count s))` and
  `(subs s (index-of s x))`, and jank's nREPL relies on byte offsets.
  Smallest design change: code-point indexing in persistent_string.cpp (`count`, `get`, `nth`,
  `contains`, `substring`) and string_native.cpp (`index_of`, `last_index_of`), with R62a and R63a.
  It matches Clojure on all text without emoji and still differs on emoji (UTF-16 is excluded).
- R52's cut (subs splitting a character): the candidate R52a refused such a cut and was withdrawn.
  jank's nREPL `abbreviate` (nrepl/server/util.jank 4-11) cuts by byte count and would throw, and
  no Clojure test can pass with it.
- R53 (count is bytes, seq is code points): either fix alone breaks the other half of the design.
- R60 (ß to "SS", final sigma): a local fix needs Unicode's SpecialCasing data for the JDK's
  Unicode version; a partial table would not be a fix.

#### Rounds 1-2 (D and R ids)

Design change:
- D15 (failed another way): fixed upstream (607de3f9); what remains is a C++ exception thrown? cannot see (V7's family).
- D25: object monitors; monitor-enter and monitor-exit exist nowhere and jank objects carry no lock.
- R11: jank quotes a symbol tag so evaluated def/fn metadata does not resolve it; unquoting needs analyzer support.
- R18: std::regex ECMAScript has no (?i), lookbehind, named or atomic groups.
- R21: every read form carries :jank/source metadata, used for error reporting.
- R38: locals are named by their munged names; a-b and a_b munge alike.
- R69, R76: one to_string serves both str (readable for collections in Clojure) and print; R76 alone would make `(str (seq "ab"))` "(a b)" where Clojure gives "(\\a \\b)".
- R72: boost's cpp_dec_float keeps no BigDecimal scale.
- R78, R79: regexes run over bytes, with ECMAScript `$`.
- R108: defn emits a named fn, so recursion skips the var.

Needs a new feature:
- D21: timed blocking deref (promise has an untimed wait; future joins its thread, no condition variable).
- D23 (failed another way): jank has no set! for vars.
- R17: namespaced map literals and `#^`.
- R74: *print-length* and the other printer vars.

More than one unit (neither half works alone):
- R28: the fn's own name is consulted after every enclosing local; needs local_frame's lookup and analyze_symbol.
- R44: case keys outside i32 (c_api.cpp hashing and cpp_processor case codegen).
- R81: re-find needs new matcher state (re_matcher.hpp) and a new re_find (core.cpp).
- R119: chunk_cons seqs the rest eagerly (seq.cpp), and chunked_cons assumes a realized rest.

Cause outside this scope:
- R13: shares D12a/D12b (the literal duplicate check hashes); with them jank rejects #{1 1N} and #{0.0 -0.0}, but a13 still fails: the read error is an error_ref, which thrown? cannot see (V7).
- R20: a20 fails for another cause: jank lexes "1-2" as 1 then an erroring "-2" (Clojure: one invalid token), and the read error would be an error_ref anyway; R20's own predictions were never run (its NUL part is fixed by R1).
- R89 (failed another way): its test ran a cpp/raw and its use as one form (S71).
- R116: range.cpp's add wraps at i32, D1's cause (another agent's).

Local but not written (time or confidence):
- R4: `+5` needs the number state machine's `-` path (octal, radix, ratio) for `+`.
- R6: radix letter digits, e/r past expecting_more_digits, the i8 radix cast.
- R7: leading zeros through M, and boost reading a ratio numerator's leading 0 as octal.
- R15: Java's isWhitespace set in the whitespace skip (decoding UTF-8), is_symbol_char and keyword checks.
- R40: the out_of_range in hoist_scoped_values was not traced to one cause.
- R47: the closure context read from the argument was not traced.
- R68: Java's Double.toString format from to_chars' shortest digits.
- R102: intern of a referred name is shared with def; not traced far enough.

Notes:
- d09 and d09b are wrong against Clojure 1.12 (see D9): Clojure gives false for d09's assertion and throws for d09b's division; judge D9 by `(NaN? (sub ##Inf ##Inf))`.
- D12a must be applied with R42, or the constant pools merge -0.0 literals with 0.0.
- D18a and D18b only work together; D19 shares delay.cpp/delay.hpp with another agent's V10/V11.

#### Rounds 3-4 (S and U ids)

Owned by other agents (the brief):
- S2-S12, S14, S15, S18-S21, S40, U1, U2, U7, U75.
- U84: shares S9's cause (big_decimal from a double).

Regex engine (libstdc++'s std::regex in place of java.util.regex; a translator or another engine):
- S22, S23, S24: the regex reads bytes, not characters.
- S25-S33: grammar and lookahead differences.
- S34: matching recurses per character.
- S35: NFA state limit.
- U35: libstdc++ starts each position with clean captures.

Analyzer and callable design:
- S36: literal locals are natively typed (R23/R24's root).
- S42: the 10-parameter limit is built into the callable interface.

Library behavior:
- S59, U81: immer's set/update store the given key, and no public API returns the stored one.
- U85: nlohmann's DOM has no arbitrary-precision number.

Lock protocols:
- S65: future deref and cancel take two locks in opposite orders (future.cpp, core.cpp).
- S67: lazy_meta evaluates under its write lock and needs a re-entry design; R43 is the same site.

C++ interop through CppInterOp:
- U6, U24: no built-in operator candidates.
- U22, U23: GetOperator's lookup.
- U25: no class template argument deduction.
- U4, U5, U20, U21: possibly local, but each depends on CppInterOp answers I couldn't check
  without a build.

Runtime design:
- U12: what a lazily compiled fn's metadata is (tied to U14's {:name}).
- U18: no base-frame notion; a throwing pop would reach binding_scope's destructor.
- U26: cpp/delete can't tell GC memory from C++'s new.
- U33: jank offers transient sorted collections on purpose.
- U67: jank's map entries are 2-vectors.

Several files or a subsystem:
- U40, U40b, U40c: line/column meta spans the reader, def analysis and var meta.
- U49's ns-aliases: needs a new runtime accessor (core.hpp/core.cpp) plus core.jank.
- U59a: the run-time output target is unset outside `jank compile` (a CLI decision).
- U65: format is std::format; Java's Formatter is a subsystem.
- U91, U92: pprint is prn, and cl-format is a subsystem.

Not confirmed:
- No result: U64, U79, U80, U82.
  - U64 is one token, exception_info.cpp 83: cause -> cause_it.
- U74: its evidence was another test's.
- U88, U89, U90: failed with an error none predicted.
- S49, S57, S70: failed another way.
  - S49 was re-tested as U4 and S57 as U7.
  - S70's text is U16's; its pointer_free half is unseen.
- Never run: S13, S39, S43, S45-S48, S51, S52, S54-S56, S58, S66, S68, S72, S74-S76, U42, U43,
  U46, U47, U52-U54, U56-U58, U60.
- Refuted: S69. S44 was re-tested as U3, which is fixed.

#### Round 5 (V ids)

Not run, and not certain from reading alone:
- V1: one ld script naming several files would need the parser to return a list and the loader to load each. That is two functions in two files.
- V2: ld's quoting and comment rules in the script lexer; local, but not certain without ld to compare against.
- V4: ld's directory-by-directory search against the JIT's search; which side to change is a choice.
- V5: the AOT link could pass a path given to `-l` as a file. Plausible, but untested.

Design, not local:
- V6: a module loaded from its `.o` doesn't run its C++ global initializers. jank's own comment says this waits for the ORC runtime.
- V7: read, analysis and load errors are `error_ref`s, not objects. Changing that is the error design itself.
- V9: the loader and the macro expander both turn a thrown ex-info into an `error_ref` holding its text. Keeping the object would need errors to carry a cause object.
- V18: an `*e` built from an `error_ref` has no data and no cause. jank's analysis errors have no cause object to give.

Representation, not local:
- V15: an exception's message can't be nil. For `ex-message` to return nil, exception_info's message has to become optional, across exception_info and core.cpp.

U39's root (one `to_string` serves both `str` and `print`):
- V46: changing inst's `to_string` would change `str`. A print-only hook would miss insts inside collections.

A port, not a fix:
- V47: `clojure.instant` is a whole namespace. V38's parser is its parse-timestamp in C++.

C++ interop:
- V25, V26, V27, V28, V29, V30: jank doesn't track which C++ arguments are lvalues and which are rvalues. Fixing it needs one model, shared by the analyzer and the codegen.
- V31, V32: the fix is in CppInterOp's GetOperator, outside jank's repo.
- V33, V34: need overload candidates that neither jank nor CppInterOp adds.

Regex (libstdc++, not jank's source):
- V35, V36: `std::regex` over UTF-8 bytes. Fixing them means another regex engine.

nREPL:
- V37: an `interrupt` op needs per-session tracking of running evals and a way to stop them.

Fixed through another id's diff:
- V20 under the dynamic runtime: V19's diff.
- V39, V40, V45: V38's diff.
- V42: V41's diff.
- V48: R55a.diff.

## 5. What REPORT-5 left out: CHAMP and the nREPL

### CHAMP: `get` of another key, and iteration (area H)

**Proved for every hash and every equality**, over round 3's replica of immer's champ.hpp (`Jank/R6/Champ/`):
- ★ `getLoop_walk`: `get k` returns the first value equal to k on the list its hash's walk reaches.
- ★ `iter_slots`, ★ `iter_split`: a node's iteration is, up to order, its 32 slots' values.
- ★ `edit_*` (eight lemmas): each node constructor of node.hpp gives a well-formed node that changes exactly one slot.
- ★ `add_step`, ★ `sub_step`: `do_add` and `do_sub` keep well-formedness and the hash-path invariant `HP` (every value sits at the path its hash's 5-bit chunks name; collision nodes only at the last level, so their values share the 65 bits `get` reads). The iteration gains v, has one equal value replaced by v, or loses one value equal to the key. Every collapse case of `do_sub` is covered.
- ★ `addMut_step`, ★ `subMut_step`: the same for the transient versions on every branch (in-place writes, `ensure_mutable_values`, the order-keeping collision write, moves, copies, owners).
- ★ `HP_makeMerged`, ★ `wf_makeMerged`, ★ `iter_makeMerged`.
- ★ `count_eq_seq_add`, ★ `count_eq_seq_sub`: `count` equals the iteration's length whatever the equality, so `count` and `(count (seq s))` never disagree through `conj`/`disj`.
- ★ `walk_complete`, ★ `get_sound`, ★ `get_complete`.

**For every equality that is an equivalence compatible with the hash (`Lawful`):**
- ★ `inv_add`, ★ `inv_sub`: well formed, `HP`, no two stored values equal, and size equals the iteration's length.
- ★ `get_iff`: `get k` is the stored value equal to k. This discharges round 5's premise on `get_sub`.
- ★ `get_add_other`, ★ `get_sub_other`: law 1, `get` of another key after add or remove is unchanged.
- ★ `keys_add`, ★ `keys_sub`, ★ `build_keys`, ★ `build_from_empty`: law 2, every add/sub sequence from empty yields each key once, and exactly the keys Clojure's model holds.

**Not closed:**
- `get_add_other` and `get_sub_other` assume the invariant (HP and uniqueness), which every champ built by these operations has; a direct proof for any well-formed champ was not written.
- The sequence theorem covers persistent add/sub only: transient steps also need "`do_sub_mut` of a key `get` finds never returns nothing", which round 5 proved for `do_sub` only.
- Transients were compared by contents, not node by node (collision order differs).

**Dropping the premises** (jank's real equality and hash) gave V84 (0.0/-0.0: law 1 breaks) and V85 (##NaN: no identity test). The walk over every sequence of at most 4 `conj`/`disj` over 11 values found nothing else: its other disagreements are D12's static cases and V48's class, and `count` vs `(count (seq s))` never differs, as proved.

### The nREPL: T7 at ≤4, T3 and T9 (area Q)

**Method.** Instead of reducing the worlds further, area Q built an exact state-graph search over round 3's World T code, unchanged. It merges states only when they are exactly equal and counts preemption-bounded timelines exactly by dynamic programming on the graph. It reproduces every complete walk count of rounds 3–5 (17 timeline counts and 4 violation counts, e.g. T1's 16,224 + 4,800, T8's 3,145, T10's 864).

**T7 (one client, partial reads, every op), with no reduction:**
- Under every schedule: 1,239 states, one final state, no violation, no deadlock. So T7 is decided at every bound.
- ≤4: complete, about 2.0·10⁸⁷ timelines, nothing. ≤0 to ≤6, ≤8 and ≤10 are also complete. ≤0 alone is 2²⁵⁵·64 (every way of splitting the 261 request bytes into reads).
- The whole-read world at ≤4: 119,937,952; with the unused eintr draw held at 0: 1,805,188 (round 5's walk had stopped at 688,909 of these).

**T9 (two connections, the capture locked):**
- Under every schedule: decided, 433,374 states, 42 final states, nothing.
- Complete counts, nothing at any bound: ≤1 53,312; ≤2 21,112,352; ≤3 5,398,067,072; ≤4 1,013,473,635,216; ≤5 to ≤8 and ≤10 in `results/r6-nrepl-t9.txt` (≤10: about 9.6·10⁴⁴).

**T3:**
- Complete counts, nothing: ≤1 1,358,848; ≤2 884,608,512; ≤3 377,378,112,512; ≤4 118,916,805,223,424; ≤5 29,577,136,869,748,736; ≤6 6,057,877,513,946,363,904. ≤7 was not run (≤6 took about 3.6 GB).
- Under every schedule: searched, not decided. The exact graph is past the memory bound, so states were kept as 64+64-bit hashes: 3,174,744 states, 245 final states, nothing. Three runs agree exactly, two hashing different serializations; the collision bound is below 2.7·10⁻⁷ for a uniform hash.

**The capture lock, re-checked (this round's rule).** T3's and T9's "nothing" rested on round 3's capture lock, which sets R125 aside. Rerun with jank's real, unlocked capture, setting aside only R125's two properties: T9 ≤0 to ≤3 complete, nothing (every schedule stopped at the 1,700 s limit after 14.3 million states, nothing); T3 ≤0 to ≤2 complete, nothing (≤3 stopped at its 1.2-million-state bound). With the full judge, T9 ≤2 shows R125 in 252,672 of 18,727,456 timelines. So the lock hid R125 and nothing else.

**Reductions, proved, checked or argued:**
- Proved: ★ `eintr_draw_unused` (with EINTR off, the step blocks and leaves memory and threads unchanged whatever the draw gives; round 5's nREPLA5-4 is now a theorem); ★ `byCid_bucket`, ★ `byCid_append` and the filter/find?/any variants (ordering the six process-wide logs by client changes no client's view); ★ `tRepliesOf_orderMem`, ★ `evalsFind_orderMem`, ★ `handlerErrorsFind_orderMem`, ★ `hungAny_orderMem` (round 3's own readers give the same answer in either order, for every state).
- Checked at every reachable state: round 5's reduction steps 1–5, as a stuttering simulation of T7 against the whole-read world (16,080 steps, 0 unmatched; T7 no longer needs it); per-client log ordering (8,708,758 step runs and final states, 0 differences); the eintr draw (34 sites in T7 and T7w, 0 differ).
- Argued: a step depends only on memory, threads and its own drawn values (nREPLA6-1); the logs are written only by appending (also checked); the counter equals the sdk's walk (it reproduces 21 results; not proved).

## 6. What was replicated, and what is not exact

**Replicated this round:**
- **Numbers** (`Jank/R6/Num/`):
  - `Int.lean`: the C++ operand types a number takes (`literal_type`, `analyze_let`, `make_box`, R5's reader); math.hpp `add`/`sub`/`mul` (68–518, every overload), unary `-` (core.jank 1393–1394), `inc`/`dec` (1186–1340), `abs` (994–1040); math.cpp `promoting_add/sub/mul` (50–175), `promoting_inc/dec` (352–403), `rem` (226–304). Beside them Numbers.java's static and Object paths (add/minus/multiply, negate, inc/dec, addP/minusP/multiplyP, incP/decP, abs, remainder, quotient), and the fixed jank (LG2a + R5a).
  - `MinMax.lean`: math.hpp `lt`/`lte` (522–736) for every kind pair, `min`/`max` (738–992, object and native branches with `std::min/max` on the common type), `compare`, `is_equiv`; Clojure's `min`/`max` overloads (Numbers.java 4044–4228) with Math.min/max's NaN and -0.0 rules.
  - `Search.lean`: the walks.
- **Native values** (`Jank/R6/Native/`):
  - `Types.lean`: every C++ arithmetic type with ranks, integral promotion, the usual arithmetic conversions, `std::common_type` and conversions ([conv], [expr.arith.conv]).
  - `Math.lean`: math.hpp's four templates per operation over native and boxed operands (`lt`, `lte`, `min`, `max`, `add`, `sub`, `mul`, `div`), `convert<T>::into_object`, and the 15 native producers (`count`, `alength`, `hash`, `int`, `bit-and`, typed-array `aget` of byte/short/int/float/char arrays, `float`, inlined predicates); Clojure's Numbers beside them, with RT.intCast, RT.floatCast and Murmur3.hashLong.
  - `Typing.lean`: `find_branch_common_type` for `if` and `case` (cpp_util.cpp 1907–1995).
  - `Theorems.lean`; `Jank/R6/Coord/NativeKernel.lean` re-proves its eight `bv_decide` theorems by `omega`.
- **Strings** (`Jank/R6/Str/`): round 2's byte and UTF-16 models extended:
  - `Proofs.lean`: `subs`, `count`, `nth` on both sides, UTF-16 recombination, the code-point design;
  - `SeqCount.lean`: the string seq's walk (persistent_string_sequence.cpp);
  - `Cut.lean`: libstdc++ 15.3.0's `wstring_convert<codecvt_utf8<wchar_t>>::from_bytes` (codecvt.cc 252–330, 468–475; locale_conv.h 55–100, 336–347), replacing round 2's case-function decoder;
  - `Fixes.lean`: jank's and Java's `compare` values, `index-of` starts, whitespace, `capitalize`, `escape`, `replace ""`, each with its fix;
  - `Search.lean`: the walks.
- **CHAMP** (`Jank/R6/Champ/`): over round 3's replica of immer's champ.hpp:
  - `Slots.lean`: packed-bitmap positions and the node constructors of node.hpp;
  - `Ops.lean`: `do_add`, `do_sub` and `make_merged` with the hash-path invariant;
  - `Mut.lean`: the transient paths;
  - `Laws.lean`: the laws;
  - `Breaks.lean`: kernel-checked single inputs with jank's real equality and hash.
- **nREPL** (`Jank/R6/Nrepl/`): state equality and hashing for round 3's World T, its reachable-state graph with path counting, a lazy walk, the stuttering-simulation check, and the theorems (section 5).
- **Coordinator** (`Run/R6/Coord.lean`, `Jank/R6/Coord/NativeKernel.lean`): the brief check and the kernel-only proofs.

**Not exact:**
- Exceptions are compared by "throws", not by class or message (jank throws strings, `std::runtime_error`s or objects).
- The literal -2147483648 is left out of the integer walk: the analyzer types it `int` but the emitted text is a C++ `long` (round 3's CG8).
- Floats are Lean's binary64 and Float32, printed with 17 significant digits, not Clojure's shortest form. Ratio and BigInt operands are walked in comparisons and min/max only.
- `char` signedness is x86-64's; on AArch64 Linux a char-array element above 127 differs.
- memcmp's value is glibc x86-64's (StrA6-1); C promises only its sign. Only V72's second assertion and V73 depend on it.
- Case mapping uses round 2's small towupper/towlower table.
- V69's exception text depends on the byte after a small string's terminator (both texts are named).
- CHAMP: Clojure's side is a set model with Util.equiv's identity test; Clojure's hasheq is not modeled.
- The nREPL's T3 walk keeps states as hashes, so it searches every schedule but does not decide them (section 5).
- The combined patch (`fixes/combined/`) was merged by reading; nothing was compiled against jank's headers.

## 7. Assumptions

**Rounds 1–5's assumptions stand**, except those replaced below.

**Replaced:**
- Round 1's A2 ("documented differences are not deviations": long overflow and division by zero unflagged) and round 3's "64-bit wrap is the documented behavior": dropped. Clojure's behavior is the property (LG2, V53, V54).
- Round 1's A6 ("programs pass values through function parameters"): the inlined path with literals, `let`-bound locals and natives is the one plain programs take, and it is modeled and tested separately (LG1, V49–V64).
- Round 2's analyzer type universe (bool, int, long, double) and round 3's native-values world (no unsigned type; no `count`, `hash`, `alength`, `min`, `max`): replaced by area P's full C++ arithmetic types.
- Round 2's "strings are UTF-8 bytes in jank (documented)" as a reason to judge R53 and R57 only against jank's own `count`: Clojure's behavior is the property (LG3, V65, V66, V72).
- Round 2's R57 model ("only the sign is kept"): Java documents compareTo's value (V72, V73).
- Round 2's case-function decoder ("invalid UTF-8 throws"): libstdc++ 15.3.0 drops an incomplete last character and throws only on a stray byte (V67).
- Round 2's R54 ("UB read"): an over-read followed by an exception in every case (V69).
- Round 1's hash agreement claim: it never covered characters, keywords or symbols (V70, V83).
- Round 1's `containsH` abstraction of immer ("same full hash and ="): replaced by round 3's CHAMP walk, which changes D12's third example (V84).
- Round 5's nREPLA5-3 (the reduction's steps 3–5, argued): no longer needed for T7, and checked at every reachable state; nREPLA5-4 (eintr unused): now ★ `eintr_draw_unused`; nREPLA5-5 (step bound): checked (T7's longest run is 597 progress steps).

**New:**
- **Numbers:** NA6-1, a deftest body is compiled, so its forms inline. NA6-2, `std::min(a, b)` is `b < a ? b : a` and `std::max(a, b)` is `a < b ? b : a` (libstdc++ and libc++). NA6-3, `##NaN` as a native literal is a positive quiet NaN.
- **Native values:** PA6-1, x86-64 Linux LP64 (`long` and `long long` 64 bits, `char` signed). PA6-2, `-fwrapv` in emitted code (round 3's Flags). PA6-3, Clang picks the both-primitive template when both operands are primitive and re-resolves the call on the temporaries' C++ types. PA6-4, a collection has fewer than 2^63 elements. PA6-5, boost `cpp_int` compares exactly with `unsigned long long` and `long long`.
- **Strings:** StrA6-1, glibc x86-64's `memcmp` returns the first differing bytes' difference for a 1-byte common length (C promises only the sign). StrA6-2, the tested jank links libstdc++ 15.3.0 and runs under a glibc UTF-8 locale. StrA6-3, the bytes after a temporary small string's terminator are arbitrary (why V69 names two texts).
- **CHAMP:** champA6-1, `##NaN` is `jank_nan`, a positive quiet NaN and a tagged `small_real` (round 1's D9 concerns only the negative default NaN). champA6-2, `-0.0` read from source is IEEE negative zero.
- **nREPL:** nREPLA6-1, a World T step's result is a function of memory, threads, the thread index and its drawn values (confirmed by 21 exact reproductions). nREPLA6-2, derived structural equality on World T's types is equality. nREPLA6-3, the six process-wide logs are written only by appending and read only per client, except the judge's choice of which violation to report first (checked at every step taken). nREPLA6-4, the hash-compaction searches had no collision (probabilistic).
- **Fixes:** FixA6-1, "confirmed" is a test that failed on the real jank as predicted (validation/*.txt, every round-5 prediction run, LG1–LG3). FixA6-2, a fix is local when it changes one function or one file, a header and its source for one function counting as one; a deviation with several causes gets one diff per cause.
- **Coordinator:** CoordA6-1, the brief's observations are of main 7135b7708, whose compiler+runtime is 94d32623's.

## 8. Properties, with their sources

1. `+`, `-`, `*`, `inc`, `dec`, unary `-` on longs throw on overflow (Numbers.java `add`/`minus`/`multiply`/`inc`/`dec`/`negate`, long and Object overloads; the docstrings "will throw on overflow").
2. `+'`, `-'`, `*'`, `inc'`, `dec'` give the exact result, promoting to BigInt (Numbers.java `addP`, `minusP`, `multiplyP`, `incP`, `decP`).
3. `abs`, `quot`, `rem` on integers equal Clojure's (Numbers.java; `abs`'s docstring).
4. `<`, `<=`, `>`, `>=`, `==`, `compare` compare numbers across long, double, ratio, BigInt and BigDecimal as Numbers' combined ops do.
5. `min` and `max` return the operand Clojure returns, of its own kind; a NaN operand wins; `max` keeps the second on a tie (Numbers.java 4044–4228; Math.min/max).
6. A ratio result with a whole-number value is a BigInt (RatioOps, `Numbers.divide(BigInteger, BigInteger)`).
7. `long` of an out-of-range double throws (RT.longCast); `float` rounds to single precision and checks its range (RT.floatCast); `int` checks its range (RT.intCast).
8. `numerator` and `denominator` are BigIntegers.
9. `count`, `alength` and `hash` results are Clojure numbers: an int used as a long (RT.count, Array.getLength), and Murmur3's signed int (Murmur3.hashLong, Util.hasheq).
10. Booleans and characters are not numbers (ClassCastException in Numbers).
11. A byte array holds signed bytes (Java's byte).
12. `if` and `case` give the value of the branch taken (Compiler.java IfExpr, CaseExpr).
13. `subs`, `count`, `nth`, `get`, `contains?` on strings index UTF-16 units (String.substring, length, charAt; core.clj).
14. `clojure.string/index-of` and `last-index-of` follow String.indexOf/lastIndexOf with Java's start rules (string.clj 319–359).
15. `compare` of strings and characters returns String.compareTo's and Character.compareTo's value.
16. `seq`, `first`, `int` of a character walk and give UTF-16 units; a lone surrogate is a character (Character; RT.charCast's range 0–0xFFFF).
17. The case functions, `reverse` and `split` give Java's String results (toUpperCase, StringBuilder.reverse, Pattern.split).
18. `hash` of a character is Character.hashCode; of a string, Murmur3 of String.hashCode; of a keyword or symbol, Keyword.hasheq and Symbol.hasheq (Util.hashCombine).
19. `keyword` and `symbol` keep the namespace and name they were given (Keyword.intern, Symbol.intern).
20. `char-name-string` and `char-escape-string` exist (core.clj).
21. A hash set or map finds a key exactly when it holds an `=` element (identity first); `get` of another key is unchanged by `conj`/`disj`; `count` equals `(count (seq s))`; `seq` yields each element once; `disj` removes exactly the `=` element (PersistentHashSet, BitmapIndexedNode, Util.equiv).
22. nREPL: every request gets replies with its id and session ending in exactly one `done`; no hang or deadlock; the process stays up (nREPL 1.8.0's transport and middleware).
23. nREPL: each eval's `:out` is what it printed, and fd 1 is the terminal again after every eval (session.clj's per-session `*out*`).
24. nREPL: each client's values, `:ns` and eval-errors are those of its script run alone (Clojure 1.12's Compiler.load).
25. Each fix: its deviation's property, and jank's own tests under compiler+runtime/test/ still hold.

## 9. Search runs

"Complete n" means every case within the bounds was run.
- **Numbers:**
  - Integer walk: complete 33,152 questions (14 operators × 23 values × 3 sources per operand: literal, literal through a fn, computed through a fn). Disagreements: `*` 1,465; `+` 835; `-` 858; `-'` 507; `quot` 1,029 (D4); `rem` 222; `abs`, `dec`, `inc`, `inc'` 2 each; `*'` 24; `+'` 132 (the last eight all R5's literal).
  - The same walk against the fixed jank (LG2a + R5a): `+ * +' *' inc dec inc' dec' abs rem` all agree; `-` 85 left (V55); `-'` 619 (V54, V55); `quot` 1,029 (D4's fix is not in that model).
  - Mixed kinds: complete, 29 values (long, double with ±0.0, NaN, ±Inf, BigInt, ratio, BigDecimal) × 2 paths per operand, 3,364 questions per operation: `min` 230, `max` 406, `<` 68, `<=` 68, `compare` 72, `==` 80.
  - Clojure probe: 121 forms run on 1.12.0.
- **Native values:**
  - Walk: complete 38,880 cases (45 sources × 45 × 10 operations × 2 paths). 10,907 differ; 10,067 once D2's truncating `/`, long overflow and division by zero are set aside (inlined 6,827, fn value 3,240). By single cause: LG1 723 (all inlined), V58 336, R33's class 1,760, V64's char 850, V51 2,424, R122 2,309, V62 652, V63 119, V57 42, R25/D1's class 213, several together 639. With every fix switch: 0. Fn-value cases that need LG1's fix: 0.
  - All 38,880 forms run on Clojure 1.12.0 against the model's Clojure predictions: 0 disagree.
  - Typing: `if` complete 2,592 (934 differ, 156 with an unsigned common type, V52); `case` complete 1,029 (336 differ). With R23's and R26's fixes: 0.
- **Strings:**
  - Index functions: every text of at most 6 code points over a, -, é, €, Ａ, 😀, U+0301 (complete 137,257 texts; 37,606,285 three-argument `subs` cases; 5,490,280 `index-of` cases). At 6: `count` differs 137,130 times, `nth` 1,766,480, `subs`/2 1,775,244, `subs`/3 14,439,366, `index-of` 2,133,936, `last-index-of` 1,802,502. The code-point design's residual on BMP-only text: 0 for every operation.
  - Cut strings: complete 11,111 byte strings; 862 walk past the end today, 0 with R54a.
  - Whitespace: complete 18,724 cases; jank differs 9,920 times, R59a/R59b 0.
  - `capitalize`: complete 400 texts; jank differs 299 times, R61a 99 (each holds ß or Σ, R60).
  - `compare`: complete 3,249 pairs; sign differs 142 times, value 3,010; R57a 0. Characters: 36 pairs, 28 differ, R57b 0.
- **CHAMP:** every sequence of at most 4 `conj`/`disj` over 11 values from `#{}`: complete 245,411 states (≤3: 11,155). Disagreements: NaN 43,842 (V85, V48), D12 as stated 184,450, path-dependent 8,628 (V84), count 28,095, count vs `(count (seq s))` 0.
- **nREPL** (section 5): T7 every schedule (1,239 states) and ≤0–≤6, ≤8, ≤10 complete; T9 every schedule (433,374 states) and ≤0–≤8, ≤10 complete; T3 ≤0–≤6 complete and every schedule searched by hash compaction (3,174,744 states); unlocked T9 ≤0–≤3 and T3 ≤0–≤2 complete; the stuttering check 16,080 steps; the log-order check 8,708,758 step runs. Nothing found anywhere.
- **Fixes' standalone checks:** LG2a's helpers, R5a's literal read, S21's ratio-to-double (bit-identical to Clojure on 10 ratios), the merged math.hpp's values, LG1's widening (Apple clang, C++20); 46 checks of the string fixes' extracted functions under ASan/UBSan; the round-1–2 fixes' R84, R71, R8, R114, R82 logic; S16, S17, U83's logic; the ported U61 and U69 against Clojure on 20,000 random inputs each.

## 10. Theorems

No sorry, no native_decide, no new axiom in what this report relies on. ★ marks a new for-every-input proof.

- **Numbers** (`Jank/R6/Num/Int.lean`): ★ `cpp_int_op`, ★ `cpp_long_op`, ★ `cpp_int_long_op` (C++ `int`/`long` arithmetic with `-fwrapv` is the exact result wrapped), ★ `wrap32_eq_iff`, ★ `wrap64_eq_iff`, ★ `i32_exact_fits_i64`, ★ `i32_pair_verdict` (V53/D1/R25), ★ `i64_pair_verdict` (LG2), ★ `fixed_eq_static` (LG2a is Clojure's static path), ★ `fixed_vs_object_sub` (V55), ★ `incdec_fixed_agree`, ★ `abs_fixed_agree`, ★ `promoting_add_mul_agree`, ★ `promoting_sub_wrong_iff` (V54); lemmas `bmod32_eq_iff`, `bmod64_eq_iff`, `inI32_iff`, `inI64_iff`, `jRepFixed_val`, `jRepFixed_not_big`, `jArithFixed_fixed`, `jArithP_fixed`.
- **Native values** (`Jank/R6/Native/Theorems.lean`, re-proved kernel-only in `Jank/R6/Coord/NativeKernel.lean` as `same_*`): ★ `lt_i64_usize_differs_iff`, ★ `lt_usize_i64_differs_iff`, ★ `le_differs_iff`, ★ `lt_int_usize_differs_iff`, ★ `min_differs_iff`, ★ `max_differs_iff` (LG1), ★ `div_usize_by_i64_differs_iff`, ★ `div_i64_by_usize_differs_iff` (V50), ★ `add_usize_exact`, ★ `hash_boxed_eq_iff` (V51), `hash_sub_one_wraps`, ★ `uac_unsigned_wins`, `uac_signed_survives`, `uac_ullong_int`, `uac_ullong_long`, `uac_ullong_llong`, `uac_uint_int`, `uac_uint_llong`, `uac_uchar_int`, `uac_bool_int`, `commonType_ullong_int`, `commonType_int_double`; coordinator lemmas `msb_iff`, `toInt_eq`, `toNat_signExtend_32`, `msb32_iff`.
- **Strings** (`Jank/R6/Str/`): ★ `unitsToCps_cstr`, ★ `unitsToBytes_cstr`, ★ `unitsToBytes_drop_le`, ★ `subs1_agrees_iff` (LG3's exact set), ★ `cp_design_agrees_bmp`, ★ `nextCharSize_utf8`, ★ `seqCount_jstr`, ★ `seqCount_eq_count_iff`, ★ `seqCount_eq_clojure_iff` (R53), ★ `jSeqFixed_no_ub` (R54a), `byte_subs_count_coherent`; single inputs `lg3_model`, `cp_design_supplementary`, `mixed_design_incoherent`, `jSeq_cut_ub`, `jSeqFixed_cut`, `w4_values`, `w4_round2_model`, `w9_values`, `w11_values`.
- **CHAMP** (`Jank/R6/Champ/`): ★ `getLoop_walk`, ★ `getLoop_slot`, ★ `iter_slots`, ★ `iter_split`, ★ `walk_sub`, ★ `edit_replace`, ★ `edit_replaceValue`, ★ `edit_insertValue`, ★ `edit_replaceMerged`, ★ `edit_replaceInline`, ★ `edit_removeValue`, ★ `edit_rootCollapse`, ★ `edit_empty`, ★ `add_step`, ★ `sub_step`, ★ `HP_makeMerged`, ★ `wf_makeMerged`, ★ `iter_makeMerged`, ★ `HP_edit`, ★ `iter_edit`, ★ `addMut_step`, ★ `subMut_step`, ★ `edit_setChild`, ★ `edit_writeValue`, ★ `walk_complete`, ★ `get_sound`, ★ `get_complete`, ★ `get_iff`, ★ `get_none_iff`, ★ `count_eq_seq_add`, ★ `count_eq_seq_sub`, ★ `inv_add`, ★ `inv_sub`, ★ `get_add_other`, ★ `get_sub_other`, ★ `keys_add`, ★ `keys_sub`, ★ `build_keys`, ★ `build_from_empty`, `inv_empty`; single inputs (`decide +kernel`) `negzero_compat_fails`, `negzero_found_alone`, `negzero_lost_after_add`, `negzero_found_after_sub`, `negzero_found_with_one`, `negzero_disj`, `nan_stored_twice`, `nan_never_found`.
- **nREPL** (`Jank/R6/Nrepl/Theorems.lean`, `Graph.lean`): ★ `eintr_draw_unused`, `next_error_limit`, ★ `byCid_bucket`, ★ `byCid_append`, ★ `byCid_filter_sub`, ★ `byCid_find?_sub`, ★ `byCid_any_sub`, ★ `tRepliesOf_orderMem`, ★ `evalsFind_orderMem`, ★ `handlerErrorsFind_orderMem`, ★ `hungAny_orderMem`; lemmas `bucket_unique`, `bucket_of_key`, `filter_flatMap_bucket`, `cidsOf_spec`, `flatMap_congr'`.

## 11. Library gaps (built in the project; sdk/lean untouched)

- A model of C++'s arithmetic types: ranks, promotions, the usual arithmetic conversions, `std::common_type`, conversions, and an exact IEEE-bits printer.
- An Int-level bridge for C++ wrapping (`bmod` lemmas for `omega`): `bv_decide` timed out on 64-bit signed multiplication overflow, and its proofs carry a per-proof axiom.
- UTF-16 recombination lemmas, a lossless UTF-8 decoder and libstdc++'s `from_bytes` decoder.
- Packed-bitmap positions (popcount as `List.countP`) and `List.Perm` helpers at an index, for CHAMP.
- For World T: state equality and hashing, a state graph under every schedule with each step's decisions enumerated, exact counting of preemption-bounded timelines by dynamic programming (the sdk can only enumerate them), stuttering-simulation checking, hash-compaction reachability, and state merging with a run-time check of its premise.
- Plain complete enumerations with per-operation tallies where a census needs counts, which the sdk's `exhaust` (stop at the first counterexample) does not give.

## 12. Model errors of earlier rounds corrected

- **Round 1's D3 "refutation":** its test used the literal -9223372036854775808, a BigInt in jank (R5), so `promoting_sub`'s i64 branch never ran. D3 holds (V54, ★ `promoting_sub_wrong_iff`).
- **Round 1's d09 and d09b** assert behaviors Clojure 1.12 does not have: `(not= x x)` of one NaN object is false in Clojure (`=` tests identity first), and `(div 0.0 0.0)` through Object operands throws "Divide by zero". D9 itself stands; `(NaN? (- ##Inf ##Inf))` observes it soundly (F1's report).
- **Round 1's D12, third example** (`(contains? #{0.0} -0.0)` false): true by the CHAMP replica; the miss needs another element sharing 0.0's first six hash chunks (V84). It never ran, since d12 failed on its first assertion.
- **Round 1's jankIntOp** saw only objects; the native literal and `let` paths are now modeled (Int.lean `jArith`/`jRep`).
- **Round 2's R122 path:** `(aget (byte-array [-1]) 0)` is inlined twice (`byte_array` returns a `u8_array_ref`, `aget`'s template returns `u8&`, array.hpp 32–36), not array.cpp 275. Same 255.
- **Round 2's R54 "unclear":** b03's "Invalid UTF-8 string." was R54's predicted path (V69).
- **Round 2's R52:** its model was right about `subs` (`lg3_model`); only its test never reported the `subs` assertion.
- **Round 2's case functions** threw on any invalid UTF-8; libstdc++ 15.3.0 drops an incomplete last character (V67).
- **Round 2's R57** kept only the sign (V72, V73).
- **Rounds 4–5's World T size estimates:** low by up to 70 orders of magnitude (T7 at ≤1: estimated 3.2·10¹¹, exact 1.25·10⁸¹), because the estimator drew partial reads by weight (1 in 7) instead of uniformly. Where earlier walks stopped, as fractions: round 5's T7w ≤3 97%, its eintr-0 ≤4 38%; round 4's T3 ≤1 89%; round 3's T9 ≤2 4%.
- **Round 5's "World T's states have no decidable equality":** they are plain data with structural equality.
- **Round 5's abstraction α** needed "nonempty remainder"; the check found 2 states and 4 steps where it was wrong, with no verdict changed.
- **Round 5's CHAMP verdict** "every break found is in an existing class": the path dependence (V84) was not named.

## 13. Tests

- **The test file.** `tests/jank_lean/deviations_r6_test.jank` (namespace `jank-lean.deviations-r6-test`) holds 56 deftests: one per prediction, with b–f variants for each path of a multi-path item, two controls predicted to pass (lg1e, lg1f), and one jank-only fix check (fix-v03).
  - Names follow the ids: lg1…lg1f, lg2…lg2f, lg3, then v49–v85.
  - Each test's comment names the path it exercises: [literals]/inlined, [let], or [fn]/fn value.
  - Tests marked "; native" need jank's native typing to show the deviation; they run on Clojure too.
- **No hangs file:** no test predicts a hang. v67 and v69 predict an uncaught C++ exception (`std::range_error`, `std::runtime_error`), so each test must run in its own process.
- **Clojure check.** Translated as rounds 4–5's were (`cpp/jank.runtime.object_ref` → `Throwable`, `(thrown? (` → `(thrown? Throwable (`, `cpp/std.exception` → `Exception`, `cpp/jank.error_ref` → `Error`), with fix-v03 dropped: 55 tests, 123 assertions, all passing on Clojure 1.12.0 (`.r6-scratch/coord/clj-run-1.12.0.txt`).
- **Jank only:** fix-v03 asserts what jank does with `fixes/V3.diff` (round 5's v03 can't pass with any fix, since `thrown?` sees only objects and the fix reports a `std::runtime_error`, as the same function's other failures do). Before the fix it is predicted to return (release build) or abort (debug build).
- **Which test each fix should make pass** is named in its section 4 entry; they are tests of rounds 1–6 (`tests/jank_lean/*.jank`).
- **Rules followed:** each test asserts Clojure's result; every form sits in a deftest body (compiled, not interpreted); values pass through fns where the fn-value path is meant; non-ASCII text is written with `\u` escapes or `(char n)`; run under a UTF-8 locale, each test in its own process.

## 14. Left for round 7

- **Numbers:** BigDecimal division, the non-terminating check and printing with scale (S2–S5, S7; they need a representation with a scale); unchecked-*-int and rationalize (unported, U74); bit operations beyond U75.
- **Native values:** `pow`/`tan`/`sqrt` (jank.math, V24's fix); `zero?` of a char (`(zero? (aget (char-array 1) 0))`, V64's cause); NaN cases on x86-64's default NaN (D9); interop-only producers of unsigned types beyond `count`, `alength`, `hash` (R92's class); `dotimes` past 2^31 iterations (an `int` loop local, R24's class).
- **Strings:** R60 (Unicode's SpecialCasing); the nREPL's `abbreviate`, which cuts strings by bytes; regex positions beyond V75 (R78–R85, V35, V36).
- **CHAMP:** `get_add_other` without the invariant; the transient sequence theorem; non-symmetric or non-transitive `=` (R55, R56, D8) beyond their classes.
- **nREPL:** T3 exactly beyond ≤6 and decided under every schedule (its exact graph is past the memory bound); the unlocked T3/T9 beyond the bounds reached; diverging evals, interrupt (V37) and stdin inside World T; a proof that the counter equals the sdk's walk.
- **Fixes:** a jank build of `fixes/combined/all.diff` and each diff's named test; local fixes described but not written (R4, R6, R7, R15, R40, R47, R68, R102 from F1; R65–R67, V70, V83 from area W; U64's one-token change from F2).
- **The rest of the brief's lesson:** a generated differential test like the brief's, driven from the replica's models (forms drawn per path: literal, let, fn value), so the replica's predictions and the generated tests check each other.

## 15. Files

- **Models:** `Jank/R6/Num/`, `Jank/R6/Native/`, `Jank/R6/Str/`, `Jank/R6/Champ/`, `Jank/R6/Nrepl/`, `Jank/R6/Coord/NativeKernel.lean`.
- **Drivers:** `Run/R6/<Area>.lean`, built as `jank6-num`, `-native`, `-str`, `-champ`, `-nrepl`, `-coord`.
- **Results:** `results/r6-<area>-report.txt` (num, native, str, champ, nrepl, fix1, fix2, fix3), `results/r6-*.txt` (runs and axioms), `results/r6-coord-brief.txt`, `results/r6-coord-axioms.txt`.
- **Tests:** `tests/jank_lean/deviations_r6_test.jank`.
- **Fixes:** `fixes/<id>.diff` (181 diffs), `fixes/combined/` (`all.diff`, the merged groups, `README.txt`).
- **Changed outside round 6's own files:** `lakefile.toml` (6 exes), `README.md`, `NOTICE.md`, `fetch-sources.sh` (the codecvt files), `.gitignore` (`.r6-scratch/`).
- **Scratch:** `.r6-scratch/` holds the rules, each area's drafts, the test mapping and assembly script, the Clojure translation and its run, and the merge tree.
- No commits were made.

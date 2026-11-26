# REPORT-8: jank 94d32623 compared with Clojure 1.12, round 8

(The harness refused REPORT-8.md; this is REPORT-8.txt, in Markdown.)

**Version.** jank main 94d32623 (`upstream-r5/`). Its compiler+runtime is byte-identical to 7135b7708, the commit the real jank was tested at. Every jank path below is under `upstream-r5/compiler+runtime/`.

**Libraries.** Rounds 1–7's pinned sources (`fetch-sources.sh`). Nothing new was fetched.

**Status.**
- Every item is a hypothesis from the Lean replicas, re-read against the source. jank was not built or run.
- Every Clojure result was run on Clojure 1.12.3 (JDK 23), the coordinator's version.
- The exceptions are nREPL 1.8.0's replies, read from its source (`.r5-scratch/nrepl/nrepl-1.8.0`): its Java classes are not in the project, so its server doesn't load.

**Who did what.**
- Five area agents worked in parallel:
  - the nREPL (Q);
  - CHAMP (H);
  - local fixes (F);
  - BigDecimal scale and `with-precision` (D);
  - boost's cpp_dec_float<100> (B).
- I did:
  - the reconciliation of round 7's real run (section 1);
  - S40's fold, and a checker for definitions used before they exist;
  - six fixes the reconciliation called for: Y1, S3c, R99i, V56, X20, and LG1's correction;
  - two small Lean models (`Jank/R8/Coord/`);
  - the merge of the combined patch and its compile checks;
  - CHECK.md, the test assembly, the Clojure check, and this report.
- Area reports: `results/r8-<area>-report.txt` (fix, dec, boost, champ, nrepl).

**Build.**
- `lake build` of the six round-8 targets (`jank8-fix`, `-dec`, `-boost`, `-champ`, `-nrepl`, `-coord`) succeeds: 272 jobs.
- Round 8 adds 22 Lean files (5,726 lines) under `Jank/R8/` and `Run/R8/`.
- No `sorry`, no `native_decide`, no axiom declared. Every main theorem rests on `propext`, `Classical.choice` and `Quot.sound` at most (`results/r8-*-axioms.txt`).
- The directory is about 1.6 GB (1.5 GB before the round), and nothing is left running.

## 1. Round 7 on the real jank, reconciled

### 1.1 The build: S40's `long`

- **The failure.** S40's `dotimes` expands to `(long n)`. core.jank defines `long` at 5773, after `dotimes` (2694) and after its first uses (`map` 2896, `map-indexed`, `keep`, `keep-indexed`, `filter`).
- **Folded.** `fixes/S40.diff` now moves `(defn long ...)` above `dotimes`, as the coordinator's `S40-order.diff` did.
  - The combined core.jank is byte for byte round 7's plus `S40-order.diff`, and no other file changed.
  - S40.diff still applies alone to 94d32623.
  - `S40-order.diff` is no longer in `fixes/combined/`: applied on top it would move `long` twice. Its text is kept in `.r8-scratch/merge/orig/`.
- **A check for the whole class: `.r8-scratch/coord/fwdref.py`.** It reads a .jank file into top-level forms. It lists every symbol a form uses before the form that defines it, directly or through a macro's syntax-quoted or quoted output where the macro is used. It reports only what stock doesn't have (stock's hits are locals and quoted data).
  - On round 7's combined core.jank it finds exactly the real failure: `long` through `dotimes` in the five functions above.
  - On every diff that edits a .jank file, applied alone to 94d32623: nothing new.
  - On round 8's combined core.jank and string.jank (and data.jank, walk.jank): nothing new.
  - Areas F and D ran it on their .jank edits.

### 1.2 CHECK.md's "should pass" against r7c-patched.tsv

Every test CHECK.md said should pass does, except one. Two predictions went the other way.

- **x27 (error; predicted pass).**
  - R4 rejects "1/-2", but with a read error: "uncaught jank error: A ratio denominator must be an integer."
  - A read error is an error_ref, which `thrown?` doesn't see. Round 7 made this point for s17 and missed it for x27.
  - R4 is right. V7r (section 4) makes read-string errors objects.
- **r116 (passes; predicted to keep failing).**
  - `(count (range 2147483646 2147483649.0))` never ended on stock: range.cpp's `force_chunk` steps with `add(val, step)`, which wrapped at 2^31 (D1's cause).
  - LG2a's checked i64 arithmetic fixes D1, and REPORT-6's "not fixed" list already called R116 D1's cause. CHECK.md's error.
- **x8 and x9b (fail, as predicted).** x9b is D4's control; x8 is in 1.5.
- **Also checked:** every "Test that should pass" in REPORT-6 section 4. The ones still failing are those rounds 6 and 7 named: d07 (scale), v64 (char part), r34, s17, u49, u59. The tests of S62, S63, S64 and U28 are in hang files, not run.

### 1.3 The nine fail/error changes

Each is the test's own cause, made visible or turned into another kind of error by a fix. None is a fix's mistake.

- **r34 (fail → error).**
  - R34 turns `(:k)` from an inlined `get` (nil) into a call.
  - The call's arity error is `invalid_arity<0>` (object.cpp 82), a std::runtime_error, which escapes `is`.
  - Round 6's R34 entry predicted "uncaught C++ exception". The test needs arity errors as objects.
- **r89 (error → fail).**
  - Stock analyzes `(do (cpp/raw "enum ...") (if cpp/r89r :t :f))` whole (S71), so `cpp/r89r` is unknown: an analysis error.
  - S71 evaluates a top-level `do` form by form. The enum now exists, and R89 itself shows: an enum zero is falsy (:f).
  - No R89 fix exists.
- **s49 (error → fail).**
  - The same S71 unmasking: the template is now declared.
  - `(#cpp (s49_add double) 1 2)` gives 3, not 3.0: S49, explicit template arguments ignored. No S49 fix exists.
- **b03 (error → fail).**
  - Stock's seq of a cut string walked past the end and threw. R54a stops at the last byte.
  - So `(vec (seq (subs "aé" 0 2)))` is `[\a <the byte C3>]`, not `[\a \é]`: `subs` counts bytes (LG3, design). R54a's entry said exactly this.
- **s17 (fail → error).** S17's lexer check rejects "1e4294967296M" with an error_ref ("Exponent overflow."). Predicted by rounds 6 and 7. V7r makes it an object.
- **u49 (fail → error).** U49a–d make the first two assertions pass. The third, `ns-aliases`, throws ex-info "TODO: port ns-aliases" inside `is`. Predicted.
- **v03 (fail → error).**
  - V3 makes `load_dynamic_library` throw instead of doing nothing, but as a C++ exception ("Unable to load the dynamic library … file too short").
  - fix-v03, which asserts jank's behavior, passes. Predicted by round 6.
- **x27 (fail → error).** See 1.2.
- **a13 (fail → error).**
  - D12a and D12b hash 1 and 1N alike, so the literal duplicate check fires, with a read error_ref ("Duplicate items in set literals are not allowed.").
  - Predicted by round 6. V7r makes it an object.

### 1.4 The 169 generated tests still failing with the patch

On stock all 639 verdicts were as predicted. With the patch, the 24 failure messages recorded (2 or 3 per chunk) show the replica's predicted stock values, except V74+R58's: there `(string/index-of "€€é" "é" -1)` moved from nil to 6, the byte index. That is R58a's documented effect: it fixes V74's start, not R58's bytes. No message contradicts the generator's model. The list, with forms and values: `.r8-scratch/gen-fail.txt`.

**Missing fixes, written this round (118 tests should flip):**
- **S3 (40).** A ratio against a BigDecimal in `<`, `<=`, `min`, `max`, `compare`, `==`; Clojure throws "Non-terminating decimal expansion".
  - S2.diff fixed S3 for division only, so round 7's "S2 (S2, S3, …)" claimed too much.
  - Fixed by S3c (alone) and R72 (combined).
- **V7 (22).**
  - `rem` by zero ("Division by zero is not permitted.", a std::runtime_error);
  - a string's `nth` out of range (a std::runtime_error);
  - `subs` out of range (an error_ref, "end index 8 is less than start 9").
  - Fixed by X20.
- **V64 (17).** A char, or a boxed bool through a fn, used as a number. R33a/b covered native bools only (g346, g347, g424, g425 flipped). Fixed by V64c.
- **V56 (14) and V57 (2).** `min`/`max` with ##NaN on object paths and on two natives of one type, and ties, which must give the second operand. LG1 fixed only the mixed-native branch (g221, g222 flipped). Fixed by V56.
- **R99 (12).** A BigInt against a double compared exactly; Clojure compares them as doubles. R99a/R99b fixed BigDecimal only. Fixed by R99i.
- **V51 (11).** `hash` is a u32. Fixed by V51.

**Missing, and not local (51 tests):**
- Strings are UTF-8 bytes, one design choice: V66 18, R52 9, LG3 6, R58 6, V74+R58 6, V65 3.
- V62 3: `float` is a double. Not written: `(str (float 0.1))` would still differ, since jank has no float box.

**Wrong fixes:** none, beyond the two claims that were too broad (S2 for S3; R99a/b for R99's class). **Model errors:** none in the generator.

### 1.5 x8 on stock: the model corrected (area B)

- **Stock passes.**
  - boost's Newton inverse of P = 2^200 lands above 1/P: 6.22…2125175E-61 against the exact 6.22…2124716….
  - So P·q = 1 + ε with ε < 10^-120. A product of order 0 keeps 121 digits, truncated, so it is exactly 1.
  - `compare` (exact on stock, big_decimal.cpp 182-190) gives 0. The approximate `=` plays no part, so the brief's explanation is close but not exact.
  - Proved for these inputs: `stock_inverse_above`, `x8_stock`.
- **The patch fails.**
  - S2's exact quotient has 140 digits. `rd_string` keeps 124 of them (order −61).
  - P·q is then 1 − 699·10^-128, and `compare` gives 1 (`x8_patched`).
  - My first standalone printout's "125 digits / …993010" counted boost's padded zero.
- **Which model was wrong.**
  - Round 7's. Its x8 comment predicted the product by reasoning from round 3's S2 text ("Newton … stays below 1/v"), never through round 3's limb replica.
  - That text is false: x(2 − t) with a truncated t makes 2 − t too large, so the iterate can end above 1/v.
  - Round 3's replica (`Jank/R3/Boost/DecFloat.lean`) is right and is used unchanged.
- **S2's reach is wider than round 3 said.**
  - Divisors made only of 2s and 5s are inexact on stock too: 18,709 of 29,403 quotients over 2^a·5^b (a ≤ 120, b ≤ 80; numerators 1, 3, 7), 18,175 of them above the exact value.
  - Example: 1/2^17 is 7.62939453124999…9E-6.
  - Over P = 2^k, k = 1..400, x8 fails on stock for k = 17, 18, 19, 25, 26 and 292, and with the patch for every k ≥ 177.

## 2. Deviations at a glance

Clojure's result first, then jank's (stock unless noted). Tests are in `tests/jank_lean/deviations_r8_test.jank`, y1–y52; each comment gives the path, the stock value and the fix.

**New:**
- **Y1 (rem of doubles).** `(rem 1e18 3.0)`: 0.0 vs 1.0. `(str (rem -4.0 2.0))`: "0.0" vs "-0.0". `(rem 1e300 1e-300)`: throws vs a value. Tests y1–y1e. Fix: Y1.
- **H8-1 (CHAMP).** `assoc`/`conj` of a present key reorders a hash map's or set's seq when it shares its full hash with a key stored before it: with `(hash-map 1 :a 7676047846 :a)`, `(= (keys m) (keys (assoc m 1 :b)))` is true vs false. Tests y22–y22e. No fix.
- **DEC8-1.** Unary minus is `(- 0 x)`: `(str (- 0.0))` "-0.0" vs "0.0"; `(str (- 1E+2M))` "-1E+2" vs "-100.0" ("-100" with R72). Tests y37–y38b. No fix.
- **Q1 (nREPL stdin).** The stdin op is answered `#{"done"}` vs unknown-op, and describe lists it vs not. Tests y51, y51b (jank only). No fix: it needs a session `*in*` (R127).
- **Q2 (nREPL eval replies).** An eval that prints nothing reaches the client as 2 messages vs 4, two holding only id and session. Test y52 (jank only). No fix written.
- **R61a's regression.** `(capitalize "AΣ")`: "Aσ" vs "Aς" with R61a; and a supplementary first character stays as it is. Both pass on stock. Tests y14b, y14c. Fix: R60.
- **U72's regression.** `(unchecked-inc-int 2147483647)`: -2147483648 vs 2147483648 with U72. Test y12f. Fix: U74.

**New instances of known causes:**
- **S3, its other operators.** `(+ 1/3 1M)`, `(* 1/3 1M)`: throw vs 1.333…M. Tests y2, y2b, control y2c. Fixes: S3c, R72.
- **R99, its BigInt half.**
  - `(count (sorted-set 9007199254740993N 9007199254740992.0))`: 1 vs 2.
  - `compare` of the two: 0 vs 1.
  - `max` of the two through a fn: the double vs the BigInt.
  - Tests y3–y3c. Fixes: R99i, with V56.
- **V57/V58 with signed zeros.** `((fn [a b] (max a b)) -0.0 0.0)` and the let-bound form: "0.0" vs "-0.0". Tests y4, y4b. Fix: V56.
- **V64.** `(float (aget (char-array "a") 0))`: throws vs 97.0. Test y7. Fix: V64c.
- **S4 and S2 (area B).** Which digits a literal, `+`, `-` and `*` keep, and the Newton division on powers of two. Tests y15–y21; all pass with R72's exact digits.
- **R72 on every operator (area D).** `(str (* 1.5M 2.0M))` "3.00" vs "3.0"; `(str 1E+2M)` "1E+2" vs "100.0"; `(str (/ 0M 5.00M))` "0E+2" vs "0.0"; and more. Tests y23–y36. Fix: R72.
- **X6 (area D).** Each rounding mode, and the operations Clojure rounds. Tests y41–y50. Fix: X6.

**Single-cause tests for this round's fixes:** y5, y6 (control), y8, y9 (control), y10, y11, y11b, y12–y12i, y13–y13d, y14 (area F), and the controls y39–y40 (area D).

## 3. Deviations in full

### Y1 — `rem` of doubles (new)

- **Programs.**
  - `(rem 1e18 3.0)`: Clojure 0.0, jank 1.0.
  - `((fn [a b] (rem a b)) 1e17 3.0)`: 0.0 vs 1.0.
  - `(str (rem -4.0 2.0))`: "0.0" vs "-0.0".
  - `(rem 1e300 1e-300)`: NumberFormatException "Infinite or NaN" vs a value.
  - Control: `(rem 7.5 2.0)` is 1.5 on both.
- **Clojure.** `Numbers.remainder(double, double)` (Numbers.java 223-237) is n − (long)(n/d)·d in doubles. Past the long range it uses the exact integer quotient, through `new BigDecimal(q)`, which throws for a NaN or infinite quotient. The cast to long drops a negative zero.
- **jank.**
  - math.cpp `rem(f64, f64)` 178-202 is C's exact `std::fmod`, and throws a std::runtime_error for a NaN or infinite operand.
  - `rem` always reaches it through `cpp/jank.runtime.rem` with boxed operands (core.jank 1687-1693), so literals and fn values run the same code.
- **Search.** A standalone copy of the fix against Clojure on 20,841 double pairs (special values, 3,000 random magnitudes, 1,000 random bit patterns; `.r8-scratch/coord/y1/`): 0 differences. Stock's fmod differs on 9,055 of them, and gives a value on 1,034 where Clojure throws.
- **Status.** New: no earlier round names it (round 3's S7 is BigDecimal `rem`). Confidence: high. Fix: `fixes/Y1.diff`.

### S3's other operators (y2)

- **Clojure.** BigDecimalOps turns a ratio into a decimal with `numerator.divide(denominator)` for every operator. So `(+ 1/3 1M)`, `(- 1M 1/3)`, `(* 1/3 1M)`, `(rem 1/3 1M)` and `(quot 1/3 1M)` throw; `(+ 1/2 1M)` is 1.5M.
- **jank.** ratio.cpp 510-611 converts with boost's Newton division (`to_native_big_decimal` 12-16), so nothing throws.
- **Proved.** S3c's conversion: ★ `conv_sound`, ★ `conv_complete` (`Jank/R8/Coord/RatioDec.lean`, on round 7's `Decimal.lean`).
- **Checked.** 16,976 ratio/decimal pairs against Clojure's `compare`: 0 differences, 14,084 of them throwing.
- **With R72.** `rem` and `quot` of a ratio and a BigDecimal are BigDecimalOps too; on round 7's tree, `quot` went through doubles.

### R99's BigInt half (y3)

- **Clojure.** A comparison with a double is a double comparison (DoubleOps, through BigInt.doubleValue).
- **jank.** It compares a BigInt and a double exactly in four places:
  - math.hpp `lt`/`lte`/`min`/`max` (boost's exact mixed comparison);
  - big_integer.cpp compare 177-187;
  - number.cpp real::compare 342-350;
  - number.cpp small_real::compare 460-470.
- **Checked.** boost's `convert_to<double>` equals Java's BigInteger.doubleValue on 38,817 values, ties and overflow included (`.r8-scratch/coord/bi2d/`). R99i compares through it.

### V57/V58 with signed zeros (y4)

- **Clojure.** `Numbers.max(Object, Object)` is `gt(x, y) ? x : y`, so `(max -0.0 0.0)` through objects is 0.0 (the second operand). Two primitive doubles take Math.max, which also gives 0.0.
- **jank.** The object max, `l < r ? r : l`, keeps the first operand; `std::max(-0.0, 0.0)` also returns its first.
- **Proved.** Over a model of the object paths (`Jank/R8/Coord/MinMax.lean`):
  - ★ `stock_min_differs_iff`: only a NaN first operand;
  - ★ `stock_max_differs_iff`: a NaN second operand, or a tie of two different numbers;
  - ★ `fixed_eq_clj`: with V56, the paths are Clojure's.
- **Checked.** V56's Math.min/Math.max helpers equal the JVM's on all 64 pairs of special doubles.

### H8-1 — a present key reorders a collision node (area H, new)

- **Programs.** The longs 1 and 7676047846 hash alike (1392991556) in jank and in Clojure (Murmur3.hashLong).
  - `(let [m (hash-map (id 1) :a (id 7676047846) :a)] (= (keys m) (keys (assoc m (id 1) :b))))`: Clojure true, jank false.
  - The same with `:a`, with `conj` on a set, with `assoc!` on a new transient, and between a transient chain and a persistent one.
- **Why.**
  - Two keys of one full hash share a collision node, newest first.
  - `assoc`/`conj` of a present key run immer's `do_add` → `copy_collision_replace` (champ.hpp 575-581, node.hpp 495-523), which writes the new entry first.
  - A transient writes in place only in a collision node it made.
  - Clojure's HashCollisionNode replaces in place, and PersistentHashSet.cons returns the set itself.
- **Shared cause.** S59's path: jank calls immer's replacing add for a present key.
- **Proved.** ★ `addMut_agree`, ★ `inPlace_eq_iff`; the programs themselves by `decide +kernel` over round 1's hash replica.
- **Fix.** None. For sets, returning the set when it holds the element would do. For maps, immer's `do_update` moves the entry too.

### DEC8-1 — unary minus (area D, new)

- **Code.** core.jank 1393-1394: `(- x)` is `(- 0 x)`; `-` inlines only its two-operand form.
- **Clojure.** `Numbers.minus(x)` negates: `(- 0.0)` is -0.0, and `(- 1E+2M)` keeps scale −2.
- **Fix (not written).** `([x] (cpp/jank.runtime.mul -1 x))` would give negate's value, scale and sign of zero.

### Q1 — the nREPL stdin op (area Q, new as a stated deviation)

- **Program.** Through jank's handler, in-process: clone a session, then send `{"op" "stdin" "session" s "stdin" "hi\n"}`.
- **nREPL 1.8.0.** `{:status #{"done"}}`, and the text is appended to the session's `*in*` (session.clj add-stdin 386-397). describe lists "stdin".
- **jank.** `[:error :unknown-op :done]` (handler.jank 5-8, the default method). describe's ops (describe.jank 5-17) have no stdin.
- **In World T8.** An eval of `(read-line)` ends `[done eval-error]` (read-line is unported, G14). nREPL would send need-input and wait for stdin.
- **Shared cause.** R127/R128: no session middleware.

### Q2 — an eval's empty replies (area Q, new)

- **Program.** `(count (responses-for req (handle-message {"op" "eval" "id" "e" "code" "1" "ns" "user"})))`, with core.jank's `responses-for` as handle-client applies it.
- **nREPL.** 2 messages: the value and done (interruptible_eval.clj 156-158, 202).
- **jank.** 4 messages.
  - handler/eval.jank 57-64 returns nil for blank :out and :err.
  - `response-for` merges each nil with the id and session (core.jank 33-45), and handle-client 87-90 writes all of them.
  - A failing eval sends two such messages too.
- **Why no round saw it.** Round 3's judge accepted these replies: it asks only for the id, the session, and one done.

### The others

Area F's (y5–y14), area B's (y15–y21) and area D's (y23–y50) are written out in their reports with every value: `results/r8-fix-report.txt` section 1, `results/r8-boost-report.txt` section 1, `results/r8-dec-report.txt` section 1.

## 4. Fixes

**Folded or corrected:**
- **S40:** `long` moved above `dotimes`.
- **LG1:** `min`/`max` of a native number and a typed BigInt, ratio or BigDecimal ref now take the object branch. Round 6's version failed to instantiate there: 22 errors in `.r8-scratch/dec/cc/tu-stock.cpp` on round 7's combined tree. No build showed it; it would if jank typed such a literal (y40 checks).

**New, written by me.** Each applies alone to 94d32623 and has a combined form. Each was syntax-checked, and gave no new warning under jank's flags.
- **Y1** (math.cpp `rem(f64, f64)`): Clojure's remainder for doubles. Should pass: y1–y1d.
- **S3c** (ratio.cpp): a ratio meeting a BigDecimal outside division converts exactly or throws, for `+ - *`, the comparisons, `==` and `compare`.
  - In the combined patch R72 does the same, and all.diff takes R72's.
  - Should pass: y2, y2b, and the 40 generated S3 tests.
- **R99i** (math.hpp `detail::lt_data`/`lte_data` in `lt`, `lte`, `min`, `max`; number.cpp; big_integer.cpp). Should pass: y3, y3b, the 12 generated R99 tests, and y3c with V56.
- **V56** (math.hpp `min`/`max`): NaN first, a tie gives the second operand, and Math.min/Math.max for two primitives of one type.
  - Should pass: v56, v56b, v57, v57b, v58 (with LG1), y4, y4b, and 16 generated tests.
- **X20** (math.cpp `rem`, persistent_string.cpp `nth`, core.cpp `subs`): they throw objects. Should pass: x20–x20d and 22 generated tests.

**New, written by area F** (`results/r8-fix-report.txt` section 11):
- **V64c** (math.hpp, visit.hpp).
  - A char is no number, and visit.hpp's "not a number" is an object (every caller checked).
  - `(int c)` stays 97.
  - Should pass: x24c, v64, y5, y7, and 17 generated tests.
- **V51** (core.hpp, core.cpp, c_api.cpp).
  - `runtime::to_hash` is an i32, and the run-time `case` key is the signed hash, matching `case-hash`. Internal hashing is unchanged.
  - Should pass: v51, v83 (with V83a/b), y8, and 11 generated tests.
- **V7r** (core.cpp `read_string`).
  - A lex/parse error, or a std::exception from the reader, is rethrown as an ex-info: jank's message, nil ex-data, the error attached.
  - Should pass: v07, y10, x27, s17, a13.
  - Not covered: eval's analysis errors (v07b) and require's load errors (v07c), which jank's own error reporting reads.
- **S17h** (lex.cpp): an `M` after a hex literal is a read error. Should pass: y11, y11b (with V7r).
- **R60** (util/string.cpp, string.jank; supersedes R61a).
  - Complete tables generated from Java 23: 102 multi-character upper mappings, 1 lower, 1,423 and 1,432 one-to-one runs, and 863 final-sigma class runs.
  - glibc's towupper is no longer used, and `capitalize` works as Clojure's does.
  - Checked: every code point (0 mismatches), 8,896,512 sigma contexts (0), and 1,000,000 random texts (81 lower-case mismatches, all in the JDK's word iterator).
  - Should pass: x18–x18h, b09, y14, y14b, y14c.
- **U74** (core.jank, math.cpp, core.hpp; supersedes U72).
  - The eight `unchecked-*-int`, the unchecked long operations, and `rationalize`.
  - 11,507 cases against Clojure: 0 differences.
  - Should pass: x10, x10b, u74, y12–y12i, y13–y13d.
  - In the combined patch its `rationalize` of a BigDecimal reads R72's unscaled value and scale (`.r8-scratch/merge/u74-r72.py`).

**New, written by area D** (`results/r8-dec-report.txt` section 11):
- **R72** (type.hpp, big_decimal.cpp, ratio.cpp, math.cpp, string_builder.cpp).
  - `native_big_decimal` becomes Java's BigDecimal: an unscaled boost cpp_int and an i32 scale, with Java's arithmetic, toString, hasheq and compareTo.
  - The digit cut (S4, S7, X8) and S2's inexact text reading go away.
  - 229,699 cases against the JVM (C++ copy) and 225,700 (Lean model): 0 differences.
  - Should pass: x7–x7d, x9b, b19, s04, s05, s07, x8, d07 (with D7), y15–y21, y23–y36, y39–y40, and the 40 generated S3 tests.
  - Earlier fixes: it subsumes S2's text reading, N7-1, S11, N7-2 and S3c; extends D4 and U2; and keeps D8, S6, S12, R99a, S8, D7, S14, S20 and S21.
- **X6** (contains R72).
  - context.cpp interns `*math-context*`; core.jank gets `with-precision`; math.hpp's `abs` rounds.
  - Should pass: x6, x6b, y41–y50.
  - Proved for every input: rounding correctness (the HALF modes within half a unit, ties, directions, UNNECESSARY), digit bounds, rounding to p digits, the least exact scale, and add/mul/neg/abs scales.

**The combined patch** (`.r8-scratch/merge/stack8.sh`; `fixes/combined/README.txt`).
- `all.diff`: 86 files from the 214 diffs; it applies to 94d32623.
- Round 8's fixes go in after round 7's groups, in their combined forms: R72, X6, V56, R99i, LG1's correction, X20, Y1, V51, V7r, S17h, V64c, U74 (with the R72 merge), R60.
- 59 of 61 changed .cpp files compile; the two exceptions are round 7's. No new warning in the 12 .cpp files round 8 changes.
- math.hpp's templates instantiate over every pair in four TUs, with 0 errors.

**Not written:** H8-1, DEC8-1, Q1, Q2, V62, the UTF-8 string family, R89, S49, V7's analysis and load parts.

## 5. The nREPL (area Q): all of round 6's list

- **A compact state codec.** Hash-consed tables of distinct components; a state is a short array of indices.
  - Proved for every table and state: ★ `decode_encode` (decoding gives each component back, identical or equal under round 6's state equality) and ★ `same_code` (one code means one stored state, component by component).
  - Injectivity with respect to Lean's `=` still rests on round 6's derived BEq (nREPLA6-2).
  - T9's exact graph now takes 14 s (round 6: 83–128 s), and T3's 156 s in about 2 GB.
- **T3, decided under every schedule, with the exact graph.**
  - 3,174,744 states (round 6's hashed count, now confirmed), 14,872,458 step runs, 245 final states, acyclic, no violation, no deadlock.
  - Round 6's log-order check ran at every state and step (0 differ).
  - Exact counts for every budget from ≤0 to ≤24 in one pass: ≤7 1,052,312,021,480,394,247,552; ≤10 about 2.5·10^33; ≤24 about 8.8·10^61. ≤0 … ≤6 equal round 6's.
  - The sdk's own unbounded `interleave` has about 3.24·10^391 timelines on T3, every one without a violation.
- **The unlocked capture** (jank's real code, R125's two properties set aside), beyond round 6's bounds:
  - T9u ≤4 complete, 766,250,832,880 timelines, nothing (round 6: ≤3);
  - T3u ≤3 complete, 322,790,415,360 timelines, nothing (round 6: ≤2);
  - ≤0 … ≤3 (T9u) and ≤0 … ≤2 (T3u) equal round 6's;
  - T9u under every schedule stopped at 22,000,971 states (round 6: 14.3 million), nothing;
  - T9u ≤5 stopped at 18,001,781 scheduler states, and T3u ≤4 at 12,505,525 states (the memory bound): nothing in either.
- **World T8: diverging evals, interrupt and stdin inside World T** (`Jank/R8/Nrepl/Diverge.lean`).
  - **D1:** one connection; clone, a diverging eval, then interrupt and describe pipelined. Every schedule, complete, 229 states. Only the clone is answered (V37, R128).
  - **D2:** jank's capture; a silent diverging eval on connection 0, while connection 1 prints, interrupts and describes.
    - ≤2, ≤3 and ≤4 complete (293,659 states at ≤4, 1,010 quiescent); every schedule stopped at 3,000,135 states.
    - Connection 1's interrupt gets unknown-op (V37). Its `(println "x")` arrives as "x\n", "x" or nothing (390 of 1,010), the lost bytes sitting in connection 0's temp file (R125).
  - **D2L:** under round 3's capture lock, connection 1's eval waits forever behind the diverging eval (16 of 30 quiescent states). A fix of R125 should give each eval its own output, not a lock.
  - **D3:** stdin; every schedule, complete, 321 states: Q1.
  - **D4:** every schedule stopped at 3,000,758 states; ≤3 complete.
  - New deviations: Q1, Q2. Everything else is V37, R128 or R125.
- **The sdk's walk, proved** on the sdk's own definitions, for every finite decision tree:
  - ★ `nextPath_eq` (the `while` loop is a plain recursion);
  - ★ `prog_run`;
  - ★ `walk_paths` and ★ `walk_count` (depth first, each leaf once);
  - ★ `exhaust_complete` (`.complete` with exactly the number of leaves);
  - `leaves_node`.
  - Not proved: that interleavePB over World T is such a tree (nREPLA6-1).
  - Run instead: the sdk's `exhaust` over round 3's runT/runTWith gives exactly the graph counters' numbers. W1: 264,832. W2 ≤0..≤3: 4, 84, 874, 5,974. W3 ≤0..≤3: 4, 336, 11,938, 276,982.

## 6. CHAMP (area H)

- **Law 1 for the transient steps without the invariant.**
  - ★ `addMut_walk`, ★ `get_addMut_other_wf`: `assoc!`/`conj!` on every well-formed champ, for every owner token, on every branch.
  - ★ `subMut_walk`, ★ `get_subMut_other_hp`: `dissoc!`/`disj!` with HP only.
  - `law1_subMut_fails_without_HP`: HP can't be dropped, on the copying or on the mutating path.
  - ★ `reach_wf_HP`: every sequence of add, sub, add_mut and sub_mut from empty keeps well-formedness and HP, for every hash and equality, so no jank program builds the counterexample.
  - ★ `law1_reach`, ★ `get_*_pair`: law 1 for every step a jank program can run, and for one pair of keys under jank's real `=`.
- **Transients against persistent steps, node by node.**
  - ★ `subMut_agree`: exact.
  - ★ `addMut_agree`, ★ `inPlace_eq_iff`: they differ in at most one collision list, exactly when the found position isn't 0 (H8-1).
  - ★ `add_congr`, ★ `sub_congr`, ★ `buildT_agree_empty`: under a lawful equality, any mixed sequence and its all-persistent twin agree up to collision order.
- **Searched.** Every sequence of up to 6 steps (3,257,437) over six keys in three colliding pairs: 0 differences in contents or shape up to collision order; 110,226 differ in collision order.
- **Not proved.** The sequence theorem without a lawful equality (D8's non-transitive `=`).

## 7. Numbers: cpp_dec_float<100> (area B) and S4 past 121 digits

**S4's exact rule.** Proved for every input (`Jank/R8/Boost/Spec.lean`); round 3's limb replica matches boost built for x86-64 on 74,763 operations, 0 differences. A value whose leading digit sits at 10^o keeps (o mod 8) + 121 significant digits.
- **Reading** (literals, `bigdec` of a string, S2's quotient text): the first (o mod 8) + 121 digits, truncated.
- **`*`, and `+` with equal signs:** the exact result, truncated the same way.
- **`−`, or `+` with opposite signs:** rounded away from zero at 10^(e−120) of the larger operand. `(- 1M 0.<121 nines>M)` is 1E-120 where Clojure gives 1E-121.
- **Stock `/`:** the dividend times the Newton inverse, truncated like `*`, on either side of the exact quotient.

**Platform (BoostA8-1).** boost on arm64 with clang's default FMA contraction differs from x86-64 on 14 of 8,509 Newton divisions. jank's x86-64 build is assumed to have no FMA.

## 8. What was replicated, and what is not exact

**Replicated.**
- `Jank/R8/Boost/`: cpp_dec_float<100> on round 3's limb replica.
- `Jank/R8/Dec/`: R72 and X6's arithmetic.
- `Jank/R8/Champ/`: transient steps and agreement, over round 3's CHAMP.
- `Jank/R8/Nrepl/`: the codec, the exact and bounded counters, World T8, and the sdk's walk.
- `Jank/R8/Coord/`: object `min`/`max` (stock, V56, Clojure), and S3c's conversion.

**Not exact.**
- Exceptions are compared by "throws" or by message, not by class.
- R60's final sigma misses the JDK's word iterator in 81 of 1,000,000 random texts.
- `*math-context*` is a map in jank, a MathContext in Clojure.
- World T8's diverging eval is one that exhausts the model's fuel without output.
- nREPL's replies are read from its source, not run.

## 9. Assumptions

**New.**
- **Coordinator:**
  - CoordA8-1: Homebrew's clang 22 headers stand in for LLVM 23 (as CoordA7-1).
  - CoordA8-2: jank's build doesn't fuse Y1's `trunc(q)*r` with the subtraction. The product is its own statement.
- **Area B:** BoostA8-1 (no FMA on x86-64); BoostA8-2 (an lvalue left operand takes boost's exact-conversion division).
- **Area D:** DecA8-1 to DecA8-6: `to_chars` for Double.toString's digits; `strtod` correctly rounded; Java's documented MathContext rules; the map form of `*math-context*`; one runtime context per process; the clang stand-in.
- **Area F:** FixA8-1 to FixA8-3: JDK 23's ROOT-locale case mapping is Clojure's; wchar_t is 32 bits; `to_chars` is shortest.
- **Area H:** in `results/r8-champ-report.txt`.
- **Area Q:** nREPLA8-1 to nREPLA8-3: a fuel-exhausted silent eval diverges; pointer identity implies equality (checked with the fast path off); nREPL's source is the spec of the stdin op.

**Replaced.**
- WA7-1 (glibc's simple case mappings): unused with R60.
- NumA7-3 and CoordA7-3 (cpp_dec_float's text reading): gone with R72.
- nREPLA6-4 (no hash collision in T3): T3 is now exact.

## 10. Properties

Rounds 1–7's 1–33 stand. New:

34. `rem` of doubles is Numbers.remainder(double, double).
35. Every BigDecimal operator converts a ratio exactly or throws.
36. A comparison with a double is a double comparison for every exact number.
37. `min`/`max` choose operands as Numbers.min/max do.
38. `assoc`/`conj` of a present key keep a hash collection's seq order.
39. Unary minus negates.
40. The nREPL answers the stdin op and lists it.
41. An nREPL eval sends no message without content.

## 11. Search runs

- **Coordinator:** Y1 20,841 double pairs; S3c 16,976 ratio/decimal pairs; R99i 38,817 BigInt→double conversions; V56 64 special pairs.
- **Area B:** 74,763 boost operations; x8 over 2^1..2^400; S2's reach over 29,403 quotients.
- **Area D:** 229,699 cases (C++) and 225,700 (Lean) against the JVM.
- **Area F:** R60, every code point, 8,896,512 contexts and 1,000,000 texts; U74, 11,507 cases.
- **Area H:** 3,257,437 sequences.
- **Area Q:** section 5; exact counts in `results/r8-nrepl-t3.txt`, `-t9.txt`, `-unlocked.txt`, `-div.txt`, `-walk.txt`.

## 12. Theorems

★ marks a new for-every-input proof.

- **Coordinator:** ★ `fixed_eq_clj`, ★ `stock_min_differs_iff`, ★ `stock_max_differs_iff`, ★ `conv_sound`, ★ `conv_complete`; `examples` (×2).
- **Area B:** ★ `keepM_digits`, ★ `keepM_trunc`, ★ `keepM_exact`, ★ `mulSpec_norm`, ★ `mulSpec_trunc`, ★ `addSpec_floor`, ★ `addSpec_norm`, ★ `subSpec_ceil`, ★ `subSpec_exact`; single inputs `p_read`, `s2_quotient`, `stock_inverse_above`, `s2_quotient_below`, `x8_stock`, `x8_patched`, `six_over_three_stock`.
- **Area D:** ★ `roundQ_cases`, ★ `roundQ_exact`, ★ `roundQ_unnecessary`, ★ `roundQ_half_choice`, ★ `roundQ_half_ulp`, ★ `roundQ_tie`, ★ `roundQ_down`, ★ `roundQ_up`, ★ `roundQ_ceiling`, ★ `roundQ_floor`, ★ `lt_pow_digits`, ★ `pow_digits_le`, ★ `digits_le_of_lt`, ★ `round_digits_le`, ★ `round_half_ulp`, ★ `exact_scale_least`, ★ `add_scale`, ★ `mul_scale`, ★ `neg_scale`, ★ `abs_scale`, `round_exact`.
- **Area H:** ★ `addMut_walk`, ★ `get_addMut_other_wf`, ★ `subMut_walk`, ★ `get_subMut_other_hp`, `law1_subMut_fails_without_HP`, ★ `step_wf_HP`, ★ `buildT_wf_HP`, ★ `reach_wf_HP`, ★ `law1_reach`, ★ `get_add_pair`, ★ `get_addMut_pair`, ★ `get_sub_pair`, ★ `get_subMut_pair`, ★ `subMut_agree`, ★ `subMut_root_agree`, ★ `addMut_agree`, ★ `addMut_root_agree`, ★ `inPlace_eq_iff`, ★ `add_congr`, ★ `sub_congr`, ★ `buildT_agree_empty`, and the toolkit lemmas.
- **Area Q:**
  - Codec: ★ `intern_spec`, ★ `internH_spec`, ★ `internAt_spec`, ★ `encList_spec`, ★ `decList_holds`, ★ `decList_ext`, ★ `decode_encode`, ★ `decodeC_ext`, ★ `same_code`.
  - The sdk's walk: ★ `nextPath_eq`, ★ `nextPathL_cons`, ★ `next_feeds`, ★ `prog_run`, ★ `walk_lift`, ★ `walk_node`, ★ `walk_paths`, ★ `walk_of_walkFrom`, ★ `walk_count`, ★ `paths_length`, ★ `depth_le_height`, ★ `treeRun_path`, ★ `exh_gen`, ★ `exhaust_complete`.

## 13. Model errors corrected

- **Round 7's CHECK.md:** x27 (R4's rejection is a read error) and r116 (LG2a fixes D1).
- **Round 7's claims too broad:** "S2 fixes S3" (division only), and R99a/b for R99's class (BigDecimal only).
- **Round 7's x8 stock prediction,** made from round 3's false prose ("Newton stays below 1/v"). Round 3's replica was right.
- **Round 7's** "Final_Sigma needs Unicode properties libc lacks": JDK 23 follows its word iterator, not Unicode's Final_Sigma (area F).
- **Round 6's** "T3's exact graph is past the memory bound" and "searched, not decided": T3 is decided exactly in about 2 GB.
- **Round 6's LG1:** typed BigInt, ratio and BigDecimal refs in `min`/`max` didn't instantiate.
- **Round 6's U72 and R61a:** regressions (y12f, y14b, y14c).
- **Round 3's judge** accepted jank's empty nREPL replies (Q2).
- **REPORT-7 1.2's "what remains"** (scale, the digit cut): fixed by R72.

## 14. Tests

- **`tests/jank_lean/deviations_r8_test.jank`:** 102 deftests (y1–y52), one assertion each, each with its path and jank's predicted value (stock and with its fix). Controls have "control" in the name. y51, y51b and y52 are jank only.
- **Clojure check:** 99 of 99 Clojure-runnable tests pass on Clojure 1.12.3 (`.r8-scratch/coord/clj8/`).
- **What each test should do with the round-8 patch:** `fixes/combined/CHECK.md`.

## 15. Left for round 9

- The build of this patch per CHECK.md, and the generated file on it.
- Design changes: H8-1, DEC8-1's fix, Q1 (a session `*in*`), Q2, V62 (a float box), and the UTF-8 string family.
- The analysis and load parts of V7, and arity errors (r34) and the other C++ exceptions as objects.
- R72's speed: every decimal operation allocates.
- **nREPL:** T9u and T3u under every schedule (an on-disk store), and that interleavePB is a decision tree (nREPLA6-1).
- **CHAMP:** the sequence theorem without a lawful equality.

## 16. Files

- **Models:** `Jank/R8/{Coord,Boost,Dec,Champ,Nrepl}/`.
- **Drivers:** `Run/R8/*.lean` (`jank8-<area>`).
- **Results:** `results/r8-*`.
- **Tests:** `tests/jank_lean/deviations_r8_test.jank`.
- **Fixes:**
  - `fixes/`: 214 diffs. New: Y1, S3c, R99i, V56, X20, V64c, V51, V7r, S17h, R60, U74, R72, X6. Corrected: S40, LG1.
  - `fixes/combined/`: `all.diff`, the three group diffs, `README.txt`, `CHECK.md`.
- **Changed outside round 8's own files:** `lakefile.toml`, `README.md`, `NOTICE.md`, `.gitignore`.
- **Scratch:** `.r8-scratch/`:
  - `RULES.txt`;
  - `coord/` (reconciliation notes, fwdref.py, the fix scripts and their standalone checks);
  - `merge/` (stack8.sh, r8.sh, tree/, the compile logs);
  - each area's work.
- No commits.

# REPORT-7: jank 94d32623 compared with Clojure 1.12, round 7

**Version.** jank main 94d32623 (`upstream-r5/`). Its compiler+runtime is byte-identical to 7135b7708, the commit the real jank was tested at. Every jank path below is under `upstream-r5/compiler+runtime/`.

**Libraries.** Rounds 1–6's pinned sources (`fetch-sources.sh`). Nothing new was fetched.

**Status.** Every item is a hypothesis from the Lean replicas, re-read against the source. jank was not built or run. Every Clojure result was run on Clojure 1.12.3, the coordinator's version.

**Who did what.**
- Five area agents worked in parallel:
  - numbers (N);
  - native values and strings (P, W);
  - CHAMP (H); the nREPL (Q) was assigned to the same agent and not done;
  - local fixes (F);
  - the generated differential test (G).
- I did:
  - the three regressions, with the corrected S40, U75, R23, R24, R26 and the new S2;
  - the `case` collision model and its fix X1;
  - the proofs of S2's arithmetic;
  - the merge of the combined patch and its compile checks;
  - CHECK.md, the test assembly, the Clojure checks, and this report.
- Area reports: `results/r7-<area>-report.txt` (num, native, champ, fix, gen). My model: `Jank/R7/Coord/`, driver `jank7-coord`.

**Build.**
- `lake build` of the five round-7 targets (`jank7-num`, `-native`, `-champ`, `-gen`, `-coord`) succeeds: 253 jobs.
- Round 7 adds 28 Lean files (5,278 lines) under `Jank/R7/` and `Run/R7/`.
- No `sorry`, no `native_decide`, no new axiom in a main theorem.
  - Main theorems rest on `propext`, `Classical.choice` and `Quot.sound` (`results/r7-*-axioms.txt`: 84 theorems).
  - Two number lemmas (`test_agree`, `cnt_in_range`) use `bv_decide`, which adds its per-proof certificate axiom, as the rules allow.
- The directory stays at about 1.5 GB.

## 1. The round-6 regressions, fixed

The coordinator's build of round 6's `fixes/combined/all.diff` showed three regressions. Each is traced to its diff and corrected in that diff. Every corrected diff still applies alone to 94d32623, and the combined patch is regenerated.

### 1.1 `case` with a test past the int range: S40 (deviations_main_test did not load)

**What the real jank showed.**
- `(case 2147483648 2147483648 :hit :miss)` (r44) threw "Value out of range for int" while macroexpanding.
- The trace was `clojure_core$int` ← `zipmap` ← `case-map-with-check` ← `case-map` ← `prep-ints` ← `case`.
- The file did not load. r45 and r123, which pass on stock, were lost, and about 30 tests could not run.

**Cause: S40.diff.**
- S40 made `int` check its range, as RT.intCast does, and dropped its `:inline`.
- jank's `case` (core.jank 4465-4531) takes the `:ints` mode whenever every test is an i64 (`i64?` 4300).
- `prep-ints` (4376-4391) then calls `int` on each test: in `(case-map ... int int tests thens)` and in `(maybe-min-hash (map int tests))`.
- So a long test past the int range throws during expansion.
- Round 6's S40 entry ("every use of `int` and `to_int` in core.jank") missed these three, where `int` is passed as a value rather than called.

**It was R44 all along.**
- With stock's `int` (`to_int`, which keeps an i64 as it is), such a `case` expanded but never matched.
- For an integer outside the int range, the switch computes `hash::integer` of it (c_api.cpp `to_case_integer_or_hash` 991-1012). The key stayed the integer itself.
- For 2147483648: key 2147483648, the value's integer 386683422 (`r44_stock_miss`, `Jank/R7/Coord/Case.lean`).
- Round 6 had listed R44 as needing c_api.cpp and the case codegen.

**The corrected change (fixes/S40.diff, core.jank).**
- S40's checked `int` stays.
- `case` takes Clojure's modes: `:ints` only when every test fits an int (`(every? i32? tests)`), otherwise `:hashes`. In `:hashes` mode, `case-hash` keys a long past the int range by its hash, as the switch does.
- `dotimes` takes `(long n)`, as Clojure's does.
- ★ `keyFixed_eq_valueKey`: for every list of integer tests, each test's key equals the integer the switch computes for a value equal to it.

**Now.**
- deviations_main_test loads.
- r44 is predicted to pass with S40 alone: S40 now fixes R44.
- r45 and r123 pass again.

### 1.2 BigDecimal division: D8, which needs a new S2 (s02)

**Cause: D8.diff.** D8 made `=` on BigDecimals exact. Division was never exact:
- boost's cpp_dec_float divides by multiplying with a Newton-iterated inverse (`cpp_dec_float.hpp` `operator/=` 1016-1047, `calculate_inv` 1222-1270).
- A standalone run with jank's type (`cpp_dec_float<100>`, `et_off`) and boost at jank's pin prints exactly the brief's values: 1.999…9 (120 nines) and 0.4999…98.
- `str()` with 0 digits prints every stored digit, so stock printed 1.999…M too. The brief's "2.0M" is not what jank's code computes.
- s02 passed on stock only because `=` compared within 2^-52.
- Round 3's S2 "refutation" came from the same approximate `=`. S2 holds.

**The change: a new fixes/S2.diff (S2, S3, U1, X2, X11).**
- `exact_divide` (big_decimal.cpp, declared in big_decimal.hpp) is BigDecimalOps.divide without a MathContext:
  - both operands are read exactly, as digits × 10^e;
  - the quotient is reduced by the gcd;
  - it terminates exactly when the reduced denominator has only 2s and 5s, and is returned;
  - otherwise it throws the object "Non-terminating decimal expansion; no exact representable decimal result.";
  - a zero divisor throws "Divide by zero".
- math.hpp's four `div` templates divide through `detail::quotient`, which calls `exact_divide` for a BigDecimal with a BigDecimal or a fixed-width integer. Doubles are left to S6.
- big_decimal.cpp's two BigInt operators and ratio.cpp's two ratio operators divide exactly too. A ratio is first made an exact decimal, so `(/ 1M 1/3)` throws, as in Clojure.
- In the combined tree, `quotient` sits in D2's `checked_div`.
- D8 is unchanged; it needs S2.

**Checks.**
- A verbatim copy of `exact_divide` gave Clojure 1.12.3's quotient, or its exception, on 418 of 418 pairs: 18 chosen, plus 400 random decimals of up to 12 digits with exponents ±15.
- Proved for every input (`Jank/R7/Coord/Decimal.lean`):
  - ★ `strip_spec`: stripping the 2s and 5s is a factorization;
  - ★ `exact_sound`: when the rest is 1, the result is the quotient;
  - ★ `exact_complete`: when the rest is not 1 and the digits are coprime, no decimal equals the quotient;
  - `reduced_coprime`.
- `div` was instantiated for 16 operand pairs with a BigDecimal, with S2 alone and in the combined tree. big_decimal.cpp, ratio.cpp and math.cpp compile.

**What remains.** Scale: 2M prints as 2.0M (R72, X7). More than about 121 significant digits are cut (S4, X8).

### 1.3 Five of jank's own suite files: R23, R24, R26 and U75

**cpp/case/pass-common-native-type: R26.**
- The case's `condp` `if` has a `char const[5]` and a `char*`, whose common type is `char const*`.
- R26 boxed the case because that type differs from the default's `char*`.
- `res` became an object, and the file printed "wrong nil".

**cpp/case/pass-implicitly-compatible-native-type: R26.**
- `bar` differs from `foo`, so R26 boxed both.
- `bar` has no conversion to an object, so the case did not analyze.

**cpp/case/pass-implicitly-compatible-primitive-type: R23 (R26 too).**
- R23 boxed `(cpp/int 77)` and `(cpp/float)` as two different built-in types.
- `(= 77.0 res)` was false.

**cpp/loop/pass-native-binding-trait-convertible: R24.**
- R24 made every built-in loop local an object.
- `(cpp/++ i)` no longer analyzes.

**form/case/pass-big-integer: U75.**
- U75 rejects a BigInt in the bit operations.
- `case-hash` (core.jank 4314-4321) keys 1N by itself, and `maybe-min-hash` runs `shift-mask` on it.

**The corrected changes.**
- **R23** (cpp_util.cpp `find_branch_common_type`).
  - Different built-in branch types are boxed unless both branches are C++ values the program asked for with `cpp/`.
  - `is_interop_value` counts as C++ values: constructor calls, C++ functions, members, operators and globals, and locals bound to them.
  - It counts as Clojure values: literals, `jank.runtime.*` calls (clojure.core's inlines), and locals bound to those.
  - r23, u07 and v52 keep their fix; `i`/`f` keep `float`.
- **R26** (processor.cpp `analyze_case`).
  - The case is boxed when two non-recur branches' common types with the default differ.
  - r26's second assertion needs R26 alone; its first needs R23 too.
- **R24** (processor.hpp/.cpp `analyze_loop`, `analyze_let`, `analyze_recur`).
  - This is Clojure's rule (Compiler.java LetExpr.Parser `recurMismatches`, 6875-6975).
  - When a `recur` gives a native local another type, the loop is analyzed again with that local boxed, until no new local needs it. "Another type" is another built-in type, or an object such as `unchecked-inc`'s.
  - The exception: both sides are C++ values.
  - `(recur (cpp/++ i))` gives `int&`, so the local stays native.
  - This also covers `dotimes` past 2^31 (X17).
- **U75** (now also core.jank). `case-hash` gives `(int input)` for an integer in the int range.

**What each correction boxes.** The corrected R23, R24 and R26 box in a subset of the cases where round 6's did (R24's object rule included, which round 6's also covered). Round 6's versions loaded core.jank and passed the rest of the suite.

**Compile checks.** cpp_util.cpp and processor.cpp now syntax-check here, alone and combined, using Homebrew's clang 22 headers, deps/cppinterop, a patched copy of Compatibility.h, and cpptrace stubs.

### 1.4 The other round-6 fixes whose test still failed (area F)

- **D7.** Right; d07 compares `str`, which prints ".0" (R72). x23 compares the values with `compare`.
- **R33a/R33b.** v64's bool assertions throw objects. Its char assertion is another cause (x24c, no fix).
- **S17.** The read error is an `error_ref`, which `thrown?` can't see (V7's read part).
- **R58a.** b07 fails on its first assertion, a byte index, as its entry says.

## 2. Deviations at a glance

Clojure's result first, then jank's. Tests are in `tests/jank_lean/deviations_r7_test.jank`; X17's are in the hangs file.

**Numbers:**
- **X1** (new) `case` with two tests of one hash: `{}` / `#{}` → :map vs :none; 987256456 against a test 4294967296 → :none vs :big.
- **X2** (new as an item) `(/ 1M 0M)`: "Divide by zero" vs inf.0M (nan.0M for 0/0).
- **X3** (extends R23) `(let [a 1 b 2.5] (if (pos? a) a b))`: 1 vs 1.0.
- **X4** (extends R24) `(loop [x 0 n 0] (let [d 1.5] (if (= n 1) x (recur d 1))))`: 1.5 vs 1.
- **X5** (new) `(hash 1.5M)`: 466 vs 154574889.
- **X6** (new as an item) `with-precision`: 0.3333333333M vs "TODO: port with-precision"; `*math-context*` undefined.
- **X7** (R72) `(str (+ 1.50M 1.5M))`: "3.00" vs "3.0"; `(str (/ 6M 3M))`: "2" vs "2.0" with S2.
- **X8** (S4) a quotient past 128 digits is cut.
- **X9** (D4) `(pr-str (quot 7.5M 2))`: "3.0M" vs "3".
- **X10** (U74) unchecked-*-int, `rationalize` unported.
- **X11** (S3) `(/ 1M 1/3)`: throws vs 3.0M.
- **X12** (S6) `(/ 1M 0.1)`: 10.0 vs 10.0M.
- **X13, X14** controls.

**Native values and strings:**
- **X15** (extends V64) `zero?` / `abs` of a char-array element: throws vs true / 97.
- **X16** (D9, new paths) `(NaN? (/ 0.0 0.0))` etc.: true vs SIGSEGV.
- **X17** (R24's cause) `dotimes` past 2^31: ends vs wraps and never ends.
- **X18** (R60) the SpecialCasing classes.
- **X19** (V75's cause) `(replace "é" (re-pattern "") "-")`: "-é-" vs "-\xC3-\xA9-".
- **X20** (V7's class) `(rem 1 0)`, `nth` / `subs` past the end: exceptions vs C++ exceptions.

**CHAMP:**
- **X21** (extends V84) a map seq stops finding its `=` vector after an unrelated `conj`.
- **X22** (extends D8) `1M` and `1.0000000000000000023M` merge in a hash set: 2 vs 1.

**Area F:**
- **X23–X26**: single-cause tests for D7, V64, V79 and V83.
- **X27** (new) `(read-string "1/-2")`: NumberFormatException vs -1/2.

**nREPL:** not done (section 6).

## 3. Deviations in full

### X1 (new)

- **Programs.**
  - `((fn [x] (case x {} :map #{} :set :none)) {})`: :map vs :none.
  - The same with `#{}`: :set vs :none.
  - `((fn [x] (case x {} :map #{} :set 4294967296 :big :none)) 987256456)`: :none vs :big.
  - Control: the case without `{}` and `#{}` gives :none on both.
- **Path.** [fn].
- **Code.**
  - `{}` and `#{}` both hash to 4279838538 (`hash::unordered` of nothing; Clojure's -15128758).
  - `merge-hash-collisions` (4393-4433) keys the merged branch by that hash, and `case-hash` hashes it again (not an i32), so neither test is found.
  - With a collision, `case-map-collison-merged` (4351-4362) leaves the other branches unchecked. 987256456, jank's hash of 4294967296, is taken as itself.
- **Model.** `Case.lean`: `x1_stock`, `x1_control` (`decide +kernel`); ★ `fixed_eq_clj` (with X1, dispatch is Clojure's `case` for every input).
- **Tests.** x1, x1b, x1c, x1d-control.
- **Fix.** `X1.diff`.

### X2

- **Programs.** `(/ 1M 0M)`, `(/ 1.5M 0)`, `((fn [a b] (/ a b)) 0M 0M)`: "Divide by zero" vs inf.0M / nan.0M.
- **Code.** math.hpp `div` 296-406 → boost (`calculate_inv` of 0 is inf). D2 checks integers only.
- **Earlier rounds.** Round 3 left it out as "documented". Under round 6's rule, that is a note on the deviation, not the property.
- **Tests.** x2, x2b, x2c.
- **Fix.** S2 (`N7-2.diff`, the zero check alone, is superseded by it).

### X3

- **Program.** let-bound `int` and `double` locals; the `if` takes their common type `double` (`find_branch_common_type`).
- **Test.** x3. **Fix.** R23 as corrected.

### X4

- **Program.** The loop local keeps the literal's `int` (`mutable_type`), and `recur` converts the double into it.
- **Test.** x4. **Fix.** R24 as corrected.

### X5

- **Values.**
  - `(hash 1.5M)`: 466 vs 154574889.
  - `(apply hash [1M])`: 31 vs 3307139568.
  - 0.1M, 100M and 0M also differ.
- **Code.** big_decimal.cpp `to_hash` 177-180 is boost's limb hash; Clojure strips trailing zeros and takes `hashCode()`.
- **Proof.** ★ `cljHashDec_value_only`: Clojure's hash depends only on the value.
- **Tests.** x5, x5b. **Fix.** `N7-1.diff`.

### X6

- **Code.** core.jank 6487-6502 throws "TODO: port with-precision"; no `*math-context*` is defined.
- **Tests.** x6, x6b.

### X7

- **Why.** cpp_dec_float has no scale; `str()` then ".0".
- **Search.** Of 29,664 terminating quotients (out of 59,040 pairs), 14,368 still print differently after S2. The rule for when the texts agree held on all of them.
- **Tests.** x7–x7d.

### X8

- **Program.** A 140-digit exact quotient is cut to at most 128 digits.
- **Test.** x8.

### X9

- **Program.** `(quot 7.5M 2)`: 3.0M vs the long 3. D4.diff gives 3.0M.
- **Tests.** x9, and the control x9b, which fails once D4 is applied (R72).

### X10

- **Code.** core.jank 1835-1938 and 5783-5841 throw "TODO: port".
- **Tests.** x10, x10b.

### X11, X12

- **X11.** `(/ 1M 1/3)`: throws in Clojure; S2 throws too.
- **X12.** `(/ 1M 0.1)`: 10.0 in Clojure; S6 gives a double.
- **Tests.** x11, x12.

### X13, X14

- **Bit operations.** The hardware takes shift counts modulo 64, which is Java's rule. ★ `test_agree`.
- **NaN min/max.** Agrees where round 6 predicted it does.
- **Tests.** x13–x13d, x14, x14b.

### X15

- **Code.** math.hpp `is_zero` 1340-1350 and `abs` 992-1001 treat a `char` as a number.
- **Tests.** x15, x15b. **Fix.** `P7-1.diff`, merged into the math.hpp group.

### X16

- **Why.** x86's default NaN 0xFFF8000000000000 reads as a null pointer in oref's tagging.
- **New detail.** `##Inf` and `##NaN` are emitted as C `float` macros.
- **Optimization level.** The literal and let forms depend on runtime -O0 (PA7-1).
- **Tests.** x16–x16d, x16e (jank only), x16f-control. **Fix.** D9.diff.

### X17

- **Code.**
  - `dotimes` (core.jank 2694-2709) keeps an `int` counter.
  - `unchecked_inc`'s object is stored back with `static_cast<int>`.
  - `(recur (inc i))` stores the i64 into the int.
- **Tests.** x17, x17b (hangs file). **Fix.** R24 as corrected, plus S40's long count.

### X18

- **Table.** The full JDK 23 table: 102 upper-case entries, 1 lower-case entry, and Final_Sigma.
- **Code.** util/string.cpp maps one `wchar_t` to one.
- **Tests.** x18–x18h, x18i-control.
- **Fix.** None: Final_Sigma needs Unicode properties libc doesn't provide.

### X19

- **Code.** libstdc++'s `regex_iterator` steps one byte after an empty match (regex.tcc 556-584).
- **Tests.** x19, x19b.

### X20

- **The cases.**
  - `rem` by zero: `std::runtime_error` (math.cpp 299-302).
  - `nth` past the end: `std::runtime_error` (persistent_string.cpp 114-117).
  - `subs` past the end: an `error_ref` through `expect_ok`.
- **Control.** `quot` by zero throws a boxed string.
- **Tests.** x20–x20d, x20e-control.

### X21

- **Program.** `[(contains? (hash-set e) ms) (contains? (conj (hash-set e) p) ms) (get (hash-map e :a p :b) ms)]` with `e` = `[[:a 1]]`, `ms` = `(seq {:a 1})`, and `p` a long sharing e's 5 low hash bits: [true true :a] vs [true false nil].
- **Code.** The map seq hashes with `hash::unordered` (2767208205 vs 1242899341; both end in 13).
- **Tests.** x21-control, x21b, x21c. **Fix.** D12d.diff.

### X22

- **Program.** `[(count (hash-set 1M 1.0000000000000000001M)) (count (hash-set 1M 1.0000000000000000023M)) (contains? (hash-set 1M) 1.0000000000000000023M)]`: [2 2 false] vs [2 1 true].
- **Why.** D8's epsilon `=`; the hashes share the low 5 bits. S10's own pair differs in those bits, so S10's conclusion holds only for such pairs.
- **Tests.** x22-control, x22b, x22c. **Fix.** D8.diff.

### X23–X26

- **X23** (D7) `compare`.
- **X24** (V64/R33) bool plus one, `inc` of a bool, char plus one (no fix for the char).
- **X25** (V79) `(char -4294967231)` is fixed by R66; `(char 128512)` is not (design B).
- **X26** (V83) fixed by V83a and V83b; v83 itself also needs V51.

### X27

- **Code.** lex.cpp's `/` branch (870-930) lexes "-2" as the denominator; `parse_ratio` (1965-1986) flips the sign.
- **Test.** x27. **Fix.** R4, extended to reject `-`.

## 4. Fixes

**What changed.**
- **Corrected:** S40, U75, R23, R24, R26, and R4 (extended for X27).
- **New:**
  - S2 and X1 (mine);
  - N7-1 and N7-2 (area N; N7-2 superseded by S2);
  - P7-1 (area P);
  - area F: R4 (supersedes R3), R6, R7, R15, R40, R47, R65, R66, R67, R68, R102, U64, V70, V83a, V83b.
- 201 diffs in all, each applying alone to 94d32623; upstream-r5 is clean.

**The combined patch** (`.r7-scratch/merge/stack.sh`; `fixes/combined/README.txt`).
- `all.diff` has 83 files and applies to 94d32623.
- Groups:
  - math.hpp: round 6's merge, plus S2's `quotient`, plus P7-1;
  - delay;
  - multi_function (R100);
  - analyze_case: S37, then R26 inside its clause loop. A fuzz merge would misplace R26's line.
- Superseded: U19, R3, N7-2.
- Compiles: 58 of 60 changed .cpp files (49 directly, 9 with jank's prelude). Not compiled: `main.cpp` (isocline) and `test/cpp/jank/read/parse.cpp` (fails at 94d32623 too).

**Pairings.**
- D8 needs S2.
- r26 needs R23 and R26.
- r25 needs LG2a and R24.
- X17 needs R24 (and S40's dotimes).
- a07 needs R7 and S16.
- v83 needs V83a, V83b and V51.

**CHECK.md** lists the tests and suite files to look at on the next build.

## 5. The brief's observations, put to the replica

- **max / min with ##NaN through a fn.** Both predicted by round 6's model; no model error (controls x14, x14b).
- **`index-of` / `last-index-of`.** All three predicted exactly (V74).
- **`upper-case` of `(subs "é" 1)`.** The exception was predicted (V67) but labelled "range_error". The real message, "wstring_convert::from_bytes", is now carried by `Brief.jUpper7`; no value changes.
- **`split` on an empty pattern.** Predicted exactly by round 3's regex replica (V75).

## 6. Section 14's other items

**Numbers.** X2 and X5–X14. Searches: 22,549 forms against the JVM, 59,040 exact-division pairs, and 288 probe forms. Bit operations past U75: no deviation.

**Native values.** X15–X17. No new unsigned producer.

**Strings.**
- X18 and X19.
- `abbreviate` sends the client nothing. It never throws (proved), and logs invalid UTF-8 exactly when byte 20 cuts a character (checked on 87,381 texts).
- Regex positions: 7,650 questions, every difference in a known class.

**CHAMP.**
- ★ `get_add_other_wf`: law 1 for add, for every well-formed champ.
- ★ `get_sub_other_hp`: law 1 for sub with the hash-path invariant only. `law1_sub_fails_without_HP` shows the invariant can't be dropped, and jank can't build that champ.
- The transient sequence theorem: ★ `doSubMut_found`, ★ `buildT_keys`, ★ `buildT_from_empty`, ★ `buildT_same_keys`.
- Walks with jank's real `=` and hash: up to length 10 for the number, string and collection pools, 4–6 for maps and the mixed pool, and the BigDecimal and symbol/keyword pools at every length. With every known cause's fix switched on, 0 disagreements.

**nREPL.** Not done: no job ran, and round 6's bounds stand. A compact state codec is needed first.

**Local fixes.** All 15 written. Not written: V64's char part, V51, V7's read part, S17's hex part.

**The generated differential test.**
- 639 deftests drawn from round 6's models, on every path each model distinguishes.
- Predicted on stock: 340 pass, 270 fail, 29 throw.
- Clojure side: 243,540 forms, 0 disagreeing; all 639 tests pass on Clojure.

## 7. What was replicated, and what is not exact

**Replicated.**
- `Case.lean`: jank's case dispatch, stock and corrected.
- `Decimal.lean`: exact_divide's arithmetic.
- Area N: Java BigDecimal and Clojure's BigDecimalOps.
- Area P/W: chars in math.hpp, NaN tagging, loop counters, SpecialCasing, `abbreviate`.
- Area H: law 1 at the walk level, `do_sub_mut`, jank's `=` and hash for every kind, hash sets and maps with transients.
- Area G: the generator.

**Not exact.**
- Exceptions are compared by "throws", not class or message.
- The `case` model omits shift/mask (CoordA7-2).
- exact_divide's text reading is checked, not proved.
- CHAMP's Clojure side is a set model.
- The hash values of keywords, longs and BigDecimals are earlier rounds' replicas; X21 and X22's controls check the premise on jank.
- WA7-1 (glibc's simple case mappings) and PA7-1 (runtime -O0).

## 8. Assumptions

**New.**
- **Coordinator:**
  - CoordA7-1: clang 22 headers stand in for LLVM 23 in syntax checks.
  - CoordA7-2: shift/mask keeps keys equal and distinct.
  - CoordA7-3: `str(0, scientific)` prints every stored digit.
- **Numbers:** NumA7-1 to NumA7-4.
- **Native and strings:** PA7-1 to PA7-4, WA7-1.
- **CHAMP:** champA7-1 to champA7-4.
- **Generator:** GA7-1 to GA7-5.
- **Fixes:** FixA7-1 (Java 23's Double.toString), FixA7-2 (LC_NUMERIC uses '.').

**Replaced.**
- Round 3's "documented" exclusion of BigDecimal division by zero.
- Round 3's S2 refutation.
- Round 6's claim that R24.diff covers `dotimes`: true of round 6's version; the corrected R24 covers it through its object rule.

## 9. Properties

Round 6's 1–25 stand. New:

26. `case` finds the equal test whatever the hashes.
27. BigDecimal division is exact or throws "Non-terminating …"; a zero divisor throws "Divide by zero".
28. A BigDecimal's hash is `stripTrailingZeros().hashCode()`.
29. A BigDecimal result keeps Java's scale.
30. `with-precision` binds `*math-context*`.
31. A primitive loop local that `recur` gives another type is boxed.
32. The case functions follow SpecialCasing.
33. A ratio's denominator is unsigned digits.

## 10. Search runs

- **S2 standalone:** 418 pairs.
- **Numbers:** 22,549 forms; 59,040 pairs; 288 probe forms.
- **Native and strings:** regex, 7,650 questions; `abbreviate`, 87,381 texts; every code point on JDK 23.
- **CHAMP:** the walks above.
- **Generator:** 243,540 forms on Clojure; 639 emitted.

## 11. Theorems

★ marks a new for-every-input proof.

- **Coordinator:** ★ `keyFixed_eq_valueKey`, ★ `fixed_eq_clj`, ★ `strip_spec`, ★ `exact_sound`, ★ `exact_complete`; also `reduced_coprime` and the single inputs `r44_stock_miss`, `x1_stock`, `x1_control`, `x1_fixed`, `examples`.
- **Numbers:** ★ `tz10_mul_pow`, ★ `strip_scale`, ★ `cljHashDec_scale`, ★ `cljHashDec_value_only`, ★ `test_agree`, ★ `cnt_in_range`, `set_clear_flip_agree`.
- **Native:** 35 theorems.
- **CHAMP:** ★ `add_walk`, ★ `get_add_other_wf`, ★ `sub_walk`, ★ `get_sub_other_hp`, `law1_sub_fails_without_HP`, ★ `doSubMut_found`, ★ `subMut_cases`, ★ `inv_addMut`, ★ `inv_subMut`, ★ `keys_addMut`, ★ `keys_subMut`, ★ `get_addMut_other`, ★ `get_subMut_other`, ★ `buildT_keys`, ★ `buildT_from_empty`, ★ `modelT_persist`, ★ `buildT_same_keys`.

## 12. Model errors corrected

- Round 3's S2 refutation (D8 hid it).
- Round 6's S40 entry missed `prep-ints`.
- Round 6's U75 entry missed `case-hash`.
- Round 6's R23, R24 and R26 broke jank's native typing tests.
- Round 6's R44 "more than one unit": one file suffices.
- The brief's "stock gave 2.0M".
- V67's exception label.
- Round 3's `cQuot` and its decimal quot/rem.
- S10's reach (X22).
- D12's map-seq pair (X21).
- Round 6's models on object exceptions, V57 ties, and S3 ratios.

## 13. Tests

- **`deviations_r7_test.jank`:** 69 deftests, x1–x27, one assertion each, each with its path and jank's predicted value. Controls are named "control". x16e is jank only.
- **`deviations_r7_hangs_test.jank`:** x17, x17b.
- **Clojure check:** 70 of 70 pass on Clojure 1.12.3.
- **`generated_r7_test.jank`:** 639 tests, all passing on Clojure; the predicted stock verdicts are in `results/r7-gen-predictions.tsv`.

## 14. Left for round 8

- The build of this patch, per CHECK.md, and the generated test run on stock.
- nREPL: all of round 6's list.
- Not written: V64's char part, V51, V7's read part, S17's hex part, R60, BigDecimal scale, `with-precision`, U74.
- CHAMP: law 1 for transient steps without the invariant.
- Numbers: S4 past 121 digits.

## 15. Files

- **Models:** `Jank/R7/{Coord,Num,Native,Champ,Gen}/`.
- **Drivers:** `Run/R7/*.lean`, built as `jank7-<area>`.
- **Results:** `results/r7-*` (reports, axioms, runs, `r7-gen-predictions.tsv`, `r7-coord-case.txt`).
- **Tests:** `tests/jank_lean/deviations_r7_test.jank`, `deviations_r7_hangs_test.jank`, `generated_r7_test.jank`.
- **Fixes:** `fixes/` (201 diffs); `fixes/combined/` (`all.diff`, the three group diffs, `README.txt`, `CHECK.md`).
- **Changed outside round 7's own files:** `lakefile.toml`, `README.md`, `NOTICE.md`, `.gitignore`.
- **Scratch:** `.r7-scratch/` (the rules, areas' work, `merge/` with its tree, scripts, stubs and the originals of corrected diffs, `bd/` with the S2 check, the Clojure runs).
- No commits.

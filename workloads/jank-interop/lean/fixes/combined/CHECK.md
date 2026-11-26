# What to check on the next build of fixes/combined/all.diff

**The build.** Apply `fixes/combined/all.diff` (round 7: 83 files, from the 201 diffs in `fixes/`) to 7135b7708, which has the same compiler+runtime as 94d32623. Build it with ninja as last time.

Run in this order:
- every `tests/jank_lean/deviations_*_test.jank`, the hangs files left out as before, plus the new `deviations_r7_test.jank`;
- `tests/jank_lean/generated_r7_test.jank`;
- jank's 551 `test/jank/**/pass-*.jank` files.

Each `tests/jank_lean` test runs in its own process. Each new test's comment names its path and jank's predicted value.

The verdicts below are relative to `results/r6c-patched.tsv` (round 6's patch) unless they say "stock".

## 1. The three round-6 regressions should be gone

### 1.1 deviations_main_test.jank loads again (S40)

- Cause: S40's checked `int` threw inside `case`'s int mode.
- Fix: `case` now takes Clojure's modes, int mode only when every test fits an int (`fixes/S40.diff`).
- Should pass again: `r45-var-read-after-redefinition` and `r123-find-returns-the-stored-key`.
- Should newly pass: `r44-case-on-a-long-past-int32`. S40 now fixes R44.
- The tests round 6's patch could not run, with the diff that should make each pass:
  - `r23` (R23)
  - `r24` (R24)
  - `r25` (LG2a + R24)
  - `r26` (R23 + R26: R26 alone gives only the second assertion)
  - `r27` (R27), `r29` (R29), `r30` (R30)
  - `r33` (R33a + R33b)
  - `r37` (R37), `r39` (R39)
  - `r40` (R40, new)
  - `r41` (R41), `r42` (R42)
  - `r47` (R47, new)
  - `r104` (R104), `r105` (R105), `r110` (R110), `r112` (R112), `r114` (R114)
  - `r117` (R117), `r118` (R118), `r120` (R120), `r121` (R121)
  - `r122` (R122a)
- Predicted to still fail: `r28`, `r34` (its error is a C++ exception), `r38`, `r89`, `r108`, `r116`, `r119`.

### 1.2 BigDecimal division (D8, which needs the new S2)

- `deviations_r3_test.jank`:
  - `s02-bigdecimal-division-is-exact` should pass. It printed 1.999…M on stock too: boost divides by a Newton inverse. Stock's `=` within 2^-52 hid it.
  - `s03-non-terminating-quotient-throws` should pass.
- `deviations_r4_test.jank`: `u01-bigdecimal-division-is-exact` should pass.
- Worth a direct look:
  - `(/ 6.0M 3.0M)` should print `2.0M`. jank has no scale (R72), so not `2M`.
  - `(/ 3 6.0M)` should print `0.5M`.
  - `(/ 1M 3)`, `(/ 1M 0)` and `(bigdec 1/3)` should throw objects.

### 1.3 jank's suite: the five files

| File | Cause in round 6 | Fixed by |
|---|---|---|
| test/jank/cpp/case/pass-common-native-type.jank | R26 | corrected R26 |
| test/jank/cpp/case/pass-implicitly-compatible-native-type.jank | R26 | corrected R26 |
| test/jank/cpp/case/pass-implicitly-compatible-primitive-type.jank | R23 (and R26) | corrected R23, R26 |
| test/jank/form/case/pass-big-integer.jank | U75 (`case-hash` passed 1N to bit ops) | corrected U75 |
| test/jank/cpp/loop/pass-native-binding-trait-convertible.jank | R24 | corrected R24 |

- The corrected R23, R24 and R26 box in a subset of the cases where round 6's versions did. Round 6's loaded core.jank and passed the rest of the suite.
- One exception: R24 now also boxes a native loop local that `recur` gives an object. Round 6's version boxed every native loop local, so this is still within what it did.
- Expected: 549 or more of 551, the same set as stock or better.
- Look first, if anything moves: `test/jank/cpp/{if,case,loop}/` and `test/jank/form/{case,loop,if}/`.
  - `cpp/loop/pass-native-binding-object-value.jank`: the local is now boxed, as round 6's R24 also did.
  - `cpp/if/pass-compatible-primitive-type.jank` and `cpp/case/pass-convertible-native-type.jank`.

## 2. Each corrected or new diff: what should pass, what to watch

- **S40** (corrected: `int`'s range check, `case` modes, dotimes takes `(long n)`).
  - Should pass: `s40-int-of-a-long-past-int32-throws` (r3) and `r44`.
  - Watch:
    - `int` is no longer inlined: `(int x)` is an object everywhere.
    - `(dotimes [i 3000000000] ...)` must not throw.
- **U75** (corrected). `u75-bit-operations-reject-bigints` (r4) should pass; so should pass-big-integer.jank.
- **R23** (corrected).
  - Should pass: `r23`, `u07` (r4), `v52` (r6), `x3`.
  - The control `u07b` must still pass.
  - `cpp/case/pass-implicitly-compatible-primitive-type.jank` must give 77.0.
- **R24** (corrected: a loop is analyzed again with a mismatched local boxed).
  - Should pass: `r24`, `r25` (with LG2a), `x4`.
  - In `deviations_r7_hangs_test.jank`: `x17`/`x17b` (dotimes and a loop counter past 2^31) should finish, with S40's dotimes for `x17`. Run them with a time limit: on stock they never end.
  - Watch compile time: a loop whose locals mismatch is analyzed two or more times.
- **R26** (corrected). Should pass: `r26` (with R23), plus the two `cpp/case` suite files above.
- **S2** (new: exact BigDecimal division, "Non-terminating …" and "Divide by zero" thrown as objects).
  - Should pass: `s02`, `s03`, `u01`.
  - Should pass: `x2`, `x2b`, `x2c` (division by zero).
  - Should pass: `x11` (`(/ 1M 1/3)` throws).
  - Should pass: `x12` (with S6: `(/ 1M 0.1)` is 10.0).
  - Still failing: `x7`–`x7d` (scale), `x8` (more than 128 digits).
- **D8**. `d08` (r1) and `s10` (r3) should pass, and so should `x22b`/`x22c` (epsilon-equal BigDecimals in a hash set). The control `x22` must still pass.
- **X1** (new, core.jank `merge-hash-collisions`).
  - Should pass: `x1`, `x1b`, `x1c`.
  - The control `x1d` passes on stock and with the patch.
- **N7-1** (new, BigDecimal hash). `x5`, `x5b` should pass. Watch `test/jank/form/case/pass-big-decimal.jank`.
- **P7-1** (new, merged into math.hpp). `x15`, `x15b` should pass, and `(int (aget (char-array "a") 0))` must stay 97.
- **R4** (new; supersedes R3, also rejects `1/-2`).
  - Should pass: `a04` (reader) and `x27`.
  - `a03` must still pass.
- **R6, R7, R15** (new, lexer).
  - Should pass: `a06`, `a07` (with S16), `a15`.
  - Watch jank's lexer unit tests (test/cpp/jank/read/lex.cpp).
- **R40, R47** (new). `r40`, `r47` should pass. Watch form/fn/named-recur/*.
- **R65** (new: a member added to context.hpp, so rebuild everything that includes it). `v80` should pass.
- **R66** (new). `x25` should pass. `x25b` and v79's second assertion still fail (characters are code points).
- **R67** (new, core.jank `symbol`). `v81` should pass.
- **R68** (new: doubles print as Java's Double.toString). `b15` should pass. Watch any output that prints a double.
- **R102** (new). `c07` should pass, with jank's replacement warning on stdout.
- **U64** (new). `u64` should pass.
- **V70** (new). `v70` should pass.
- **V83a, V83b** (new).
  - Should pass: `x26` (V83a), `x26b` (V83a + V83b).
  - `v83` still needs V51.
- **D7, R33a, R33b** (unchanged; their tests split into single-cause tests).
  - Should pass: `x23` (D7, compared with `compare`), `x24`/`x24b` (bool, R33a + R33b).
  - `x24c` (char + 1) has no fix. d07 and v64 keep failing on their other assertions.
- **D12d**. `x21b`/`x21c` should pass. The control `x21` passes on stock and with the patch.
- **D9**. `x16`–`x16d` (default NaN; SIGSEGV on stock) should pass.
  - `x16e` is jank only and needs V24 + D9.
  - The control `x16f` passes either way.

## 3. The new tests, on stock and on the patch

**tests/jank_lean/deviations_r7_test.jank**: 69 tests (x1–x27). **deviations_r7_hangs_test.jank**: 2 tests (x17, x17b).
- All 70 that Clojure can run pass on Clojure 1.12.3. x16e is jank only.
- Tests with "control" in the name are predicted to pass on stock. Every other test is predicted to fail on stock with the value in its comment.
- Predicted to keep failing with the patch (no fix written):
  - `x6` (with-precision)
  - `x7`–`x7d` (scale), `x8`
  - `x9b`, a control that fails with D4 (R72)
  - `x10`/`x10b` (unported)
  - `x18`–`x18h` (SpecialCasing)
  - `x19`/`x19b` (regex)
  - `x20`–`x20d` (C++ exceptions that `thrown?` misses)
  - `x24c`, `x25b`

**tests/jank_lean/generated_r7_test.jank**: 639 generated forms, one assertion each.
- Each test's comment and `results/r7-gen-predictions.tsv` give the replica's predicted stock verdict: 340 pass, 270 fail, 29 throws.
- Please run it on stock, not only on the patch.
- Every disagreement between the real verdict and the predicted one is a replica error. Please list them.

## 4. Not compiled here (a build is the first check)

- `main.cpp` (U45): isocline.h is not in deps/.
- `test/cpp/jank/read/parse.cpp` (R10's edit): it does not compile here at 94d32623 either.
- The 58 other changed .cpp files compile with `-fsyntax-only`, using Homebrew's clang 22 headers as a stand-in for LLVM 23 (fixes/combined/README.txt). These include analyze/processor.cpp and cpp_util.cpp, now for the first time.

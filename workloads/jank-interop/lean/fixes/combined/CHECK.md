# What to check on the next build of fixes/combined/all.diff

**The build.** Apply `fixes/combined/all.diff` (round 8: 86 files, from the 214 diffs in `fixes/`) to 7135b7708, which has the same compiler+runtime as 94d32623. Build it with ninja as last time. Round 7's `S40-order.diff` is folded into `fixes/S40.diff` and into `all.diff`: don't apply it on top.

Run in this order:
- every `tests/jank_lean/deviations_*_test.jank`, the hangs files left out as before, plus the new `deviations_r8_test.jank`;
- `tests/jank_lean/generated_r7_test.jank`, stock and patched as last time;
- jank's 551 `test/jank/**/pass-*.jank` files;
- if you can: jank's C++ unit tests (`test/cpp/jank/runtime/obj/big_decimal.cpp`, `ratio.cpp`, `read/lex.cpp`, `read/parse.cpp`) and `test/bash/clojure-test-suite`. R72, S17h and R60 touch what they test.

Each `tests/jank_lean` test runs in its own process. Each new test's comment names its path, jank's predicted stock value, and the fix that should make it pass.

Verdicts below are relative to `results/r7c-patched.tsv` (round 7's patch) unless they say "stock".

## 1. The build itself

- **`long` before `dotimes` (S40).** `fixes/S40.diff` now moves `(defn long ...)` above `dotimes`, as your `S40-order.diff` did; the combined core.jank is byte for byte round 7's plus that move. `.r8-scratch/coord/fwdref.py` (every symbol a top-level form uses, directly or through a macro's syntax-quoted output, must be defined before it) finds your failure on round 7's core.jank and nothing new on round 8's core.jank, string.jank, data.jank or walk.jank, nor on any diff alone.
- **The BigDecimal type changed (R72).** `native_big_decimal` (type.hpp) is now a class: an unscaled `cpp_int` and an `i32` scale, Java's BigDecimal arithmetic. Everything that includes type.hpp rebuilds. Watch first: big_decimal.cpp, ratio.cpp, math.cpp, string_builder.cpp, codegen of BigDecimal literals (cpp_processor.cpp 311-315 emits `make_box<big_decimal>("<text>")`), the PCH, and `std::to_chars(double, scientific)` in libstdc++.
- **X6 interns `clojure.core/*math-context*`** in context.cpp (a dynamic var, nil by default).
- **Compiles here:** 59 of the 61 changed .cpp files with `-fsyntax-only` (as round 7; not compiled: `main.cpp`, isocline.h missing, and `test/cpp/jank/read/parse.cpp`, which fails at 94d32623 too). No new warning under jank's flags in the 12 .cpp files round 8 changes. math.hpp's templates instantiate for every operand pair tried (`.r8-scratch/coord/fix/tu-cmp.cpp`, `.r8-scratch/fix/cc/tu-char.cpp`, `.r8-scratch/dec/cc/tu.cpp`, `tu-stock.cpp`).
- **LG1 corrected.** Round 6's LG1 made `min`/`max` of a native number and a typed BigInt, ratio or BigDecimal ref fail to instantiate (22 errors in `tu-stock.cpp` on round 7's combined tree). Those now take the object branch. If jank types a BigDecimal literal as `big_decimal_ref`, `(max 0 1.5M)` (y40, a control) failed to JIT on round 7's patch.

## 2. Round 7's tests that should newly pass

- **R72 (BigDecimal scale; exact digits):**
  - x7, x7b, x7c, x7d (r7), b19 (r2), s04, s05, s07 (r3), x8 (r7);
  - x9b, the control D4 broke;
  - d07 (with D7).
- **X6 (with-precision):** x6, x6b.
- **V7r (read errors reach an object catch):**
  - v07 (r5);
  - x27 (with R4), s17 (with S17), a13 (with D12a/D12b).
  - v07b and v07c still fail: analysis and load errors are not covered.
- **V64c (a char is no number):** x24c (r7) and v64 (r6, all three assertions, with R33a/R33b).
- **V51 (hash is a signed int):** v51 (r6); v83 (r6, with V83a/V83b).
- **V56 (min/max: NaN, ties, -0.0):** v56, v56b, v57, v57b; v58 (with LG1).
- **X20 (rem by zero, nth and subs out of range throw objects):** x20, x20b, x20c, x20d.
- **R60 (Java's case mapping in full):** x18–x18h (x18i stays a passing control), b09 (r2).
- **U74 (unchecked-*-int, unchecked long ops, rationalize):** x10, x10b (r7), u74 (r4).

**Still failing, known:**
- r28, r34, r38, r89, r108, r119;
- s49 and the other C++ interop tests;
- v07b, v07c, u49, u59;
- x19, x19b (regex on bytes), x25b;
- the UTF-8 string family (b01–b03, lg3, v65, v66, ...);
- u84 (json reads a decimal through a double).

## 3. The generated file (generated_r7_test.jank) with the round-8 patch

Of the 169 tests still failing with round 7's patch, 118 should pass:
- S3, 40 (R72, which subsumes S3c in the combined patch): g193–g196, g217–g220, g241–g248, g261–g264, g269–g272, g289–g296, g309–g312, g317–g320.
- V7, 22 (X20): g177–g180, g480–g482, g486–g488, g525–g527, g531–g533, g540–g542, g546–g548.
- V64, 17 (V64c): g333–g335, g348, g361–g363, g375–g377, g399–g401, g426, g441–g443.
- V56 and V57, 16 (V56): g197–g200, g215, g216, g223, g224, g600–g603, g608–g611.
- R99, 12 (R99i): g237–g240, g265–g268, g285–g288.
- V51, 11 (V51): g358–g360, g414–g417, g427–g430.

The other 51 should still fail:
- strings are bytes (one design choice): V66 18, R52 9, LG3 6, R58 6, V74+R58 6 (value 6, the byte index), V65 3;
- V62 3 (`float` is a double).

The 470 passing with round 7's patch (340 on stock plus 130) should still pass. Please list any generated test that moves.

## 4. Each new or corrected diff: what should pass, what to watch

- **R72** (`fixes/R72.diff`; the combined patch uses `.r8-scratch/dec/R72-combined.diff`).
  - Should pass: section 2's list, and y23–y36 and y39–y40 of deviations_r8_test.
  - y28, y31 and y35 need D4 or U2 too, both in the combined patch.
  - Should still fail: y37, y37b, y38, y38b (DEC8-1: `(- x)` is `(- 0 x)`).
  - Every area-B test (y15–y21) should pass: digits are no longer cut.
  - Watch:
    - `form/case/pass-big-decimal.jank`;
    - every output that prints a BigDecimal (now Java's `toString`: `1.50M` prints "1.50", `1E+2M` "1E+2", no ".0" appended);
    - speed: every decimal operation allocates.
  - R72 subsumes S2's text reading, N7-1, S11, N7-2 and S3c in the combined patch.
- **X6** (contains R72). Should pass: x6, x6b, y41–y50.
- **Y1** (new: `rem` of doubles is Clojure's n − (long)(n/d)·d, not `fmod`).
  - Should pass: y1, y1b, y1c, y1d. The control y1e passes on stock too.
  - Stock values: 1.0, 1.0, "-0.0", and a value instead of an exception.
- **S3c** (new, alone: a ratio meeting a BigDecimal converts exactly or throws).
  - Should pass alone: y2, y2b, and the 40 generated S3 tests.
  - In the combined patch R72 does the same; y2c is a control.
- **R99i** (new: a BigInt against a double compares as doubles). Should pass: y3, y3b; y3c needs V56 too (and R68 to print the double).
- **V56** (new). Should pass: y3c, y4, y4b and section 2's v56–v58.
- **X20** (new). Section 2's x20–x20d and 22 generated tests.
  - Watch: anything in jank that catches `std::runtime_error` around `rem`, `nth` or `subs`. None was found by reading.
- **V64c** (area F).
  - Should pass: y5, y7, x24c, v64, and the 17 generated tests. y6 is a control: `(int (aget (char-array "a") 0))` stays 97.
  - Watch: any jank code doing arithmetic or `<` on a char (Clojure throws there too).
  - visit.hpp's "not a number" is now an object.
- **V51** (area F).
  - Should pass: y8, v51, v83 (with V83a/b), and 11 generated tests. y9 is a control: `case` on hashed tests.
  - Watch: `case` (c_api.cpp's run-time key is now the signed hash, matching `case-hash`); `form/case/*.jank`.
- **V7r** (area F). Should pass: y10, v07, x27, s17, a13.
- **S17h** (area F). y11, y11b (with V7r).
- **R60** (area F; supersedes R61a).
  - Should pass: y14, x18–x18h, b09; y14b and y14c (they pass on stock; R61a, in round 7's patch, breaks them).
  - Watch: `clojure.string` upper-case, lower-case and capitalize in jank's clojure-test-suite.
- **U74** (area F; supersedes U72).
  - Should pass: y12–y12i, y13–y13d, x10, x10b, u74.
  - y12f failed with U72: `(unchecked-inc-int 2147483647)` gave a long.
- **LG1** (corrected; section 1). y40 is a control.

## 5. New deviations without a fix (predicted to fail with the patch too)

- **H8-1:** assoc/conj of a present key reorders a collision node (y22, y22b, y22c, y22d, y22e). Its four controls pass.
- **DEC8-1:** unary minus is `(- 0 x)` (y37, y37b, y38, y38b).
- **Q1:** the nREPL stdin op is unknown-op, and describe doesn't list it (y51, y51b; jank only, called in-process like round 5's v37).
- **Q2:** an eval that prints nothing reaches the nREPL client as 4 messages, two holding only id and session (nREPL sends 2) (y52; jank only).

## 6. Not compiled here (a build is the first check)

- `main.cpp` (U45): isocline.h is not in deps/.
- `test/cpp/jank/read/parse.cpp` (R10's edit): it doesn't compile here at 94d32623 either.
- The other 59 compile with `-fsyntax-only`, using Homebrew's clang 22 headers in place of LLVM 23 (README.txt).

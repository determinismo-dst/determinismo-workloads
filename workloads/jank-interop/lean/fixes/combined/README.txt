fixes/combined: every fix as one patch on jank 94d32623 (round 9)
=================================================================

Files
-----
- all.diff: one unified diff from 94d32623 (paths a/compiler+runtime/..., b/compiler+runtime/...)
  to the tree with every fix applied. 114 files, from the 243 diffs in fixes/ (some merged as groups,
  superseded or subsumed, below). `git -C upstream-r5 apply --check ../fixes/combined/all.diff`
  passes; upstream-r5 stays clean.
- immer.diff (round 9): H8-1's half in immer (jank-lang/immer 282629d0, the submodule commit), paths
  relative to the immer repository: `git -C compiler+runtime/third-party/immer apply
  ../../../fixes/combined/immer.diff`. `git -C deps/immer apply --check` passes.
- math-hpp.diff, delay.diff, multi-function.diff: those files' parts of all.diff (groups).
- CHECK.md: what to look at on the next build. Round 8's all.diff, CHECK.md and README.txt are kept in
  .r9-scratch/merge/orig-r8/.

Round 9's changes to the patch
------------------------------
.r9-scratch/merge/r9.sh rebuilds round 9 from round 8's tree (tag r8 of .r9-scratch/merge/tree, which is
round 8's all.diff), applying each round-9 fix in its combined form with `git apply` (no fuzz), in order:
1. Coordinator: V82, U80, U84 (combined variant .r9-scratch/coord/U84-combined.diff: keeps U83, U86 and the
   eof check), U88, U90.
2. Area E: .r9-scratch/err/err-all-combined.diff = A34 (contains V7a) + V9 + V18 + X20b.
3. Area W: W9u-combined, W9h, W9c-combined, W9r-combined (.r9-scratch/str/). W9u replaces R58a's byte
   index-of and R62a's code-point replace; W9c changes R66's 0x10FFFF bound to 0xFFFF.
4. Area H: H8-1 (jank side; also S59 and U81), H9-3. immer's half is immer.diff.
5. Area Q: Q1, then .r9-scratch/nrepl/Q2-on-Q1.diff (Q2 redone on Q1: Q2.diff alone does not apply after
   Q1), then V37i.
6. Coordinator: T9-2, T9-9.
7. Area N: DEC8-1, V55, V60, V61, V62b, V85, R72f (.r9-scratch/num/<id>-combined.diff). V62b supersedes
   V62 (V62.diff, the value-only fix, makes (str (float 0.1)) print 17 digits: not in all.diff). R72f
   (BigDecimal's i64 fast path and digit counting without a string) exists only as a combined variant.
Not in all.diff: V62 (superseded by V62b), V7a (inside A34), Q2.diff (as Q2-on-Q1), and round 8's
exclusions (S3c, U19, R3, N7-2).

How round 9's result was checked
--------------------------------
- Each of the 243 diffs applies alone to 94d32623 (round 9's 29: V82 U80 U84 U88 U90 A34 V7a V9 V18 X20b
  W9u W9h W9c W9r H8-1 H9-3 Q1 Q2 V37i T9-2 T9-9 DEC8-1 V55 V60 V61 V62 V62b V85, and H8-1-immer on immer).
- Every .cpp of the merged tree (207), -fsyntax-only as before: 194 compile; the other 13 fail identically
  on round 8's tree (missing isocline, jankzip, cpptrace's real headers, build defines).
  .r9-scratch/merge/syn9-1.txt, syn9-2.txt.
- jank's warning flags on the 31 changed .cpp files: no new warning (warn9-*.txt; one -Wcomment in V18's
  comment was found and fixed in the diffs).
- .jank files: fwdref.py "new 0" for core.jank, shell.jank, bencode.jank and the nREPL server files.
- Each area's standalone checks are in its report (results/r9-<area>-report.txt).

Round 8's changes to the patch (still in all.diff)
--------------------------------------------------
Folded or corrected (each still applies alone to 94d32623):
- S40: `long` moved above `dotimes` (the build failure of round 7's patch).
- LG1: min/max of a native number and a typed BigInt, ratio or BigDecimal ref take the object
  branch (round 6's version failed to instantiate there: 22 errors in .r8-scratch/dec/cc/tu-stock.cpp).
New, in r8.sh's order after the groups (each in its combined form):
1. R72 (area D): BigDecimal as Java's (unscaled cpp_int, i32 scale). .r8-scratch/dec/R72-combined.diff.
   Subsumes S2's text reading (exact_divide stays, as the class's division), N7-1, S11, N7-2 and S3c;
   extends D4 (divideToIntegralValue) and U2 (bigdec of a double at Double.toString's scale); keeps D8,
   S6, S12, R99a, S8, D7, S14, S20, S21.
2. X6 (area D, on R72): with-precision, *math-context*. .r8-scratch/dec/X6-combined.diff.
3. V56 (coordinator): min/max as Numbers.min/max (NaN first, a tie gives the second operand,
   Math.min/max for two primitives of one type). Script .r8-scratch/coord/fix/v56.py (combined mode).
4. R99i (coordinator): a BigInt against a double compares as doubles (math.hpp lt/lte/min/max through
   detail::lt_data/lte_data; number.cpp, big_integer.cpp compare). Scripts r99i_math.py, r99i_cpp.py.
5. LG1's correction (lg1b.py), 6. X20 (x20.py: rem by zero, a string's nth and subs out of range throw
   objects), 7. Y1 (y1.py: rem of doubles as Numbers.remainder(double, double)).
8. V51, V7r, S17h (area F) as written; V64c, U74, R60 (area F) as .r8-scratch/fix/<id>-combined.diff.
   U74 supersedes U72 and R60 supersedes R61a (their combined variants replace those lines).
9. u74-r72.py (.r8-scratch/merge/): U74's rationalize of a BigDecimal read cpp_dec_float's text; on R72
   it takes the unscaled value and the scale.
Not in all.diff: S3c (R72 does the same in the combined tree; S3c.diff is the fix for 94d32623 alone),
and, as before, U19 (R100), R3 (R4), N7-2 (S2).

How the result was checked
--------------------------
- Each of the 214 diffs applies alone to 94d32623 (`git -C upstream-r5 apply --check`).
- Compiles (Mac, Apple clang 16, -std=c++20 -fsyntax-only; deps/ headers; Homebrew's clang 22 headers in
  place of LLVM 23 for the analyzer files; jank itself not built): 59 of the 61 changed .cpp files, as in
  round 7 (main.cpp: isocline.h missing; test/cpp/jank/read/parse.cpp fails at 94d32623 too).
  .r8-scratch/merge/synall8-1.txt, synall8-2.txt.
- jank's warning flags (CMakeLists 86-103, -Werror in Debug): the 12 .cpp files round 8 changes give no
  warning they did not give on round 7's combined tree (.r8-scratch/merge/warn8-*.txt).
- math.hpp's templates: .r8-scratch/coord/fix/tu-cmp.cpp (min/max/lt/lte over 52 operand pairs),
  .r8-scratch/fix/cc/tu-char.cpp (char operands), .r8-scratch/dec/cc/tu.cpp and tu-stock.cpp (BigDecimal
  operands): 0 errors each.
- .jank files: .r8-scratch/coord/fwdref.py (a symbol used before the top-level form that defines it,
  directly or through a macro's syntax-quoted output): no new hit in core.jank or string.jank.
- Standalone copies of each new fix's arithmetic against Clojure 1.12.3 on JDK 23: Y1 20,841 double
  pairs, S3c 16,976 ratio/decimal pairs, R99i's BigInt->double 38,817 values, V56's Math.min/max 64
  special pairs, all 0 differences; R72/X6 229,699 cases (area D), U74 11,507 (area F), R60 every code
  point and 8,896,512 sigma contexts (area F).

Pairings a build should know
----------------------------
- X6 needs R72. d07 and x23 need R72 and D7; x9, y28, y35 need R72 and D4; s09, y31 need R72 and U2.
- y3c needs R99i, V56 and R68. v58 needs V56 and LG1. v83 needs V51, V83a and V83b.
- V64c's inlined char tests need R33b (its throw is the object); x27 needs V7r and R4; s17 V7r and S17;
  a13 V7r, D12a and D12b; y11/y11b V7r and S17h.
- Round 7's: D8 needs S2 (now R72); r26 needs R23 and R26; r25 LG2a and R24; x17 R24 and S40.

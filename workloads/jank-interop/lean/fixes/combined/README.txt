fixes/combined: every fix as one patch on jank 94d32623 (round 8)
=================================================================

Files
-----
- all.diff: one unified diff from 94d32623 (paths a/compiler+runtime/..., b/compiler+runtime/...)
  to the tree with every fix applied. 86 files, from the 214 diffs in fixes/ (some merged as groups,
  superseded or subsumed, below). `git -C upstream-r5 apply --check ../fixes/combined/all.diff`
  passes; upstream-r5 stays clean.
- math-hpp.diff, delay.diff, multi-function.diff: those files' parts of all.diff (groups).
- CHECK.md: what to look at on the next build.
- Round 7's S40-order.diff is folded into fixes/S40.diff and all.diff; it is no longer here (its text:
  .r8-scratch/merge/orig/S40-order.diff). Applying it on top of this all.diff would move `long` twice.
- The work: .r8-scratch/merge/ (stack8.sh rebuilds everything from fixes/*.diff: round 7's stack.sh
  plus r8.sh; r8-ids.txt lists the round-8 diffs it takes out of the alphabetical pass). Its tree/ is a
  git copy of 94d32623's compiler+runtime with one commit per diff or group (HEAD = all.diff).

Round 8's changes to the patch
------------------------------
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

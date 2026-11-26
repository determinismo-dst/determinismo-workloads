fixes/combined: every fix as one patch on jank 94d32623 (round 7)
=================================================================

Files
-----
- all.diff: one unified diff from 94d32623 (paths a/compiler+runtime/..., b/compiler+runtime/...)
  to the tree with every fix applied. 83 files, from the 201 diffs in fixes/ (16 of them merged
  as groups or superseded, below). `git -C upstream-r5 apply --check ../fixes/combined/all.diff`
  passes; upstream-r5 stays clean.
- math-hpp.diff: include/cpp/jank/runtime/core/math.hpp alone (round 6's merge of D2 D6 LG1 LG2a
  R33a R33b, plus S2's quotient and P7-1's char checks).
- delay.diff: obj/delay.hpp + delay.cpp alone (D19 V10 V11 S64, round 6's merge, unchanged).
- multi-function.diff: obj/multi_function.cpp alone (R100; it supersedes U19).
  Each of the three is exactly that file's part of all.diff.
- CHECK.md: what to look at on the next build (the round-6 regressions, each corrected or new
  diff's tests, the suite files to watch).
- The work: .r7-scratch/merge/ (stack.sh rebuilds everything from fixes/*.diff; filterdiff.py,
  drophunk.py, math-s2.py, math-p71.py, r26-s37.py, dedup-includes.py; syn.sh, synfix.sh,
  synall.sh and stubs/ for the compile checks; cc/ for the template instantiations).
  .r7-scratch/merge/tree is a git copy of 94d32623's compiler+runtime with one commit per diff
  or group (HEAD = all.diff), for bisecting a build failure to a diff.

Round 7's changes to the patch
------------------------------
Corrected (the round-6 regressions; each still applies alone to 94d32623; originals in
.r7-scratch/merge/orig/):
- S40: `case` takes Clojure's modes (ints only when every test fits an int; hash mode
  otherwise), and dotimes takes a long count. Round 6's S40 broke every `case` with a long test
  past the int range (prep-ints calls `int`). Also fixes R44.
- U75: case-hash gives an int for a BigInt in the int range, so shift-mask's bit operations
  never see one (round 6's U75 broke test/jank/form/case/pass-big-integer.jank).
- R23: two branches of different built-in types are boxed unless both are C++ values the
  program asked for with `cpp/` (round 6's broke cpp/case/pass-implicitly-compatible-primitive-
  type.jank).
- R24: a loop is analyzed again with a native local boxed when a `recur` gives it a value of
  another type (Clojure's recurMismatches), instead of every built-in loop local being boxed
  (round 6's broke cpp/loop/pass-native-binding-trait-convertible.jank).
- R26: a case is boxed when two branches' common types with the default differ, instead of
  whenever a branch's type differs from the default's (round 6's broke cpp/case/pass-common-
  native-type.jank and pass-implicitly-compatible-native-type.jank).
- R4 (written this round by area F) also rejects a ratio denominator with a `-` (X27).
New: S2 (exact BigDecimal division; D8 needs it), X1 (case on hash collisions), N7-1
(BigDecimal hash), P7-1 (zero?/abs of a char), R4 R6 R7 R15 R40 R47 R65 R66 R67 R68 R102 U64 V70
V83a V83b (area F). N7-2 (BigDecimal division by zero) is written but superseded by S2, which
throws "Divide by zero" for every divisor its exact division sees.

Order used (.r7-scratch/merge/stack.sh)
---------------------------------------
1. Every fixes/<id>.diff in alphabetical order (`ls fixes/*.diff | sort`), each with plain
   `git apply`, one commit per diff, except the 16 below.
2. Fuzz-needing diffs at their alphabetical place with `patch -p1 -F3`: R59a, S12, S14, S15, U2
   (as in round 6; each was read against its single diff then and lands in the same functions).
3. S2 without its math.hpp part (filterdiff.py), and without its big_decimal.cpp include of
   make_box.hpp when S12 already added that line.
4. S17: as is (its `#include <limits>` lands once; R5a adds the same line).
5. Groups, in place of their members:
   - math.hpp: round 6's merged file (D2 D6 LG1 LG2a R33a R33b, conflicts resolved as round 6's
     README described: .r6-scratch/merge/tree), then math-s2.py (S2's quotient helper in the
     detail namespace, and checked_div's non-integer branch `return quotient(l, r);`), then
     math-p71.py (P7-1's char checks first in abs and is_zero).
   - R100 (U19 superseded).
   - delay: round 6's merged delay.hpp/delay.cpp (D19 V10 V11 S64).
   - analyze_case: S37 applies first (alphabetical order puts R26 earlier, but R26 is held
     back); r26-s37.py then puts R26's recording of each non-recur branch's common type into
     S37's clause loop (S37 moved the common-type computation out of the analysis lambda) and
     its boxing block after that loop. A plain fuzz merge put R26's line where its variable no
     longer exists; this is why R26 is a group.
   - math.cpp: duplicate includes removed (cosmetic, as round 6).
6. Superseded, not applied: U19 (R100), R3 (R4 rewrites R3's one line for both signs), N7-2 (S2).

How the result was checked
--------------------------
- Each of the 201 diffs applies alone to 94d32623 (`git -C upstream-r5 apply --check`).
- Placement: as round 6 (diff3 and reading) for the round-6 diffs; this round's new diffs
  applied without fuzz except where named above; S2, S40, U75, X1, R26 (by hand) and R4's
  neighbours read in the combined tree: core.jank's case region holds S40's mode, U75's
  case-hash, X1's merge-hash-collisions; lex.cpp holds R1 R2 R4 R5a R6 R7 R9 R14 R15 S16 S17
  (area F stacked R4 R6 R7 R15 on round 6's tree with R3 reverted: clean); big_decimal.cpp
  holds S11's to_real, S12's to_integer, D8's equal, R99a's compare, N7-1's to_hash and S2's
  exact_divide with the two BigInt operators.
- Compiles (Mac, Apple clang 16, libc++, -std=c++20 -fsyntax-only; deps/ headers; jank itself
  not built): 58 of the 60 changed .cpp files compile in the combined tree, 49 directly and 9
  with jank's prelude (`-include jank/runtime/visit.hpp -DGC_THREADS`, the JANK_* build macros),
  as the real build gives every file its PCH. Among them, for the first time here, the analyzer
  and runtime files round 6 could not compile (analyze/processor.cpp, analyze/cpp_util.cpp,
  core.cpp, c_api.cpp, read/parse.cpp, codegen/cpp_processor.cpp, ir/processor.cpp,
  evaluate.cpp, jit/processor_dynamic.cpp, exception_info.cpp, deferred_cpp_function.cpp,
  context_dynamic.cpp): Homebrew's clang 22 headers stand in for jank's LLVM 23, with
  deps/cppinterop's headers, a copy of CppInterOp's Compatibility.h with five clang-23-only
  spots removed, and declaration-only cpptrace stubs (.r7-scratch/merge/stubs/). Not compiled:
  main.cpp (isocline.h is not in deps/) and test/cpp/jank/read/parse.cpp (R10's test edit; it
  fails here at 94d32623 too, on lex::token's constructors).
- Template instantiations: math.hpp's div for 16 operand pairs with a BigDecimal (BigDecimal,
  int, long, usize, double, object_ref, integer_ref, real_ref, ratio_ref, big_integer_ref),
  in the combined tree and with S2 alone (.r7-scratch/merge/cc/tu-divonly.cpp).
- S2's exact_divide, copied into a standalone program (boost at jank's pin): Clojure 1.12.3's
  quotient or exception on all 418 pairs tried. Its arithmetic is proved for every input
  (Jank/R7/Coord/Decimal.lean: exact_sound, exact_complete).

Pairings a build should know
----------------------------
- D8 needs S2 (exact `=` shows boost's inexact quotients otherwise: s02).
- r26 needs R23 and R26 (R26 alone gives its second assertion).
- r25's loop needs LG2a and R24; x17 (dotimes past 2^31, hangs file) needs R24, and with S40
  also S40's dotimes change.
- D12a needs R42; D18a with D18b; R59a with R59b; V17a with V17b (round 6).
- R7's a07 needs S16; R4's "+1/2" needs S16.
- v83 needs V83a, V83b and V51 (not written: `hash` is a u32); x26/x26b need only V83a(/V83b).
- Tests no fix here can make pass: r34, u49 (ns-aliases), u59 (U59a), b07's first assertion,
  v03 (use fix-v03), d07's printing (use x23), v64's char assertion (x24c), v79's second
  assertion (x25b), s17 (needs read errors as objects, V7).

What a build must check first
-----------------------------
See CHECK.md. In short: the three round-6 regressions are gone (deviations_main_test loads, s02,
the five suite files); then the analyzer changes (R23, R24, R26) across test/jank/cpp/{if,case,
loop}/ and form/{case,loop,if}/; S40's `int` (no longer inline: an object) and dotimes; R65's new
context member (rebuild everything that includes context.hpp); delay.hpp's members (round 6).

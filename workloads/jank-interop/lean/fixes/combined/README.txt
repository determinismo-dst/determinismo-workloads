fixes/combined: the 181 round-6 fixes as one patch on jank 94d32623
=====================================================================

Files
-----
- all.diff: one unified diff from 94d32623 (paths a/compiler+runtime/..., b/compiler+runtime/...)
  to the tree with every fix applied. 80 files. `git -C upstream-r5 apply --check
  ../fixes/combined/all.diff` passes; upstream-r5 stays clean.
- math-hpp.diff: include/cpp/jank/runtime/core/math.hpp alone (D2 D6 LG1 LG2a R33a R33b merged).
- delay.diff: obj/delay.hpp + delay.cpp alone (D19 V10 V11 S64 merged).
- multi-function.diff: obj/multi_function.cpp alone (R100; it supersedes U19).
  Each of the three applies alone to 94d32623 and is exactly that file's part of all.diff.
- Three single fixes were corrected in place at the coordinator's request (see "Corrected
  fixes"): fixes/U2.diff, fixes/D19.diff, fixes/R33a.diff. Each still applies alone to 94d32623
  (`git -C upstream-r5 apply --check`). The originals are kept in .r6-scratch/merge/orig/.
  all.diff, math-hpp.diff and delay.diff were regenerated with them; the earlier
  compile-fixes.diff is gone (its two corrections are now in U2 and D19).
- The work: .r6-scratch/merge/ (stack.sh, crosscheck.py, mh/resolve.py, S17-noinclude.diff,
  cc/ compile checks, readcheck.clj). .r6-scratch/merge/tree is a git copy of 94d32623's
  compiler+runtime with one commit per diff (branch master = all.diff), for bisecting a build
  failure to a diff.

Order used
----------
1. Every fixes/<id>.diff in alphabetical order (`ls fixes/*.diff | sort`), each with plain
   `git apply`, one commit per diff, except the 12 below.
2. Fuzz-needing diffs at their alphabetical place with `patch -p1 -F3`: R59a, S12, S14, S15,
   S37, U2. (S12, S14, S15 and U2 fail `git apply` only because their first hunk is an include at
   line 1, which git anchors to the file's start and another diff already changed.)
3. S17 without its first hunk (.r6-scratch/merge/S17-noinclude.diff).
4. The three groups merged by hand, in place of their members: math.hpp, delay, multi_function.
5. One cleanup: math.cpp's include block deduplicated (D10, S14, S15 and U2 each added
   <string>/<string_view> etc.; the stack had <string_view> three times). Nothing else differs
   from the diffs' own text.

How the result was checked
--------------------------
- Placement, every file touched by 2+ diffs (32 files outside the groups): each diff applied
  alone to 94d32623, then all of them merged into one file with `git merge-file` (diff3 aligns
  whole files, so each change lands at its own base position, not at the nearest look-alike
  context); re-run after the three corrections (the stack was rebuilt from scratch). 30 files
  are byte-identical to the stack. The other two (math.cpp, processor.cpp)
  have diff3 conflicts only where two diffs touch adjacent lines; both were read in full (below).
  The 44 files touched by one diff are byte-identical to that diff applied alone.
- Fuzz-applied diffs, read against the single diff on 94d32623:
  - R59a (string_native.cpp): fuzz 3 on hunk 1 because R58a rewrote last_index_of's body, R59a's
    leading context. Result: last_index_of (R58a's body) closes, then is_java_whitespace,
    whitespace_at, whitespace_before, then triml_index/trimr_index with R59a's loops. Same as
    R59a alone. diff3 agrees byte for byte.
  - S12 (big_decimal.cpp): to_integer has S12's RT.longCast body; it calls to_real(), which S11
    changed (strtod of the text), as intended by both. Include hunk next to S11's <cstdlib>.
  - S14 (math.cpp): the BigDecimal(String) grammar is in to_big_decimal's persistent_string
    branch. S15: the BigInteger(String) grammar is in to_big_integer's persistent_string branch.
  - U2 (math.cpp): shortest_decimal is defined before is_big_integer; to_big_integer has S15's
    string branch, U2's real/small_real branch, the big_decimal branch, S18's ratio branch, in
    that order; to_big_decimal has D7's integer branch, U2's real branch (shortest_decimal), the
    old big_integer/ratio branch, S14's string branch. (Apple patch reported U2's hunk 3 "at 809",
    a number in its own coordinates; the text landed in to_big_integer, checked by reading.)
  - S37 (analyze/processor.cpp analyze_case): hunk 4 needed fuzz 3 because R26 inserted its
    "box them all" block at the same spot. Result, in this order: clauses analyzed (S37), then
    the default analyzed, then S37's common-type loop over the clauses, then R26's block (which
    reads needs_conversion/chosen_type/default_expr the loop just computed), then the conversion
    loop. That is both intents: Clojure's analysis order (S37) and boxing when branch types differ
    (R26). R26's block must come after S37's loop, and it does.
  - S17 (lex.cpp): the exponent check sits in the found_M branch, before number_literal; R5a's
    strtoull integer path follows. `#include <limits>` comes from R5a.
- Same-function pairs from different agents that applied without conflict, read together:
  R29 + S38 (analyze_call: R29's local/recursion_reference test, then S38's one-step
  macroexpand1); D22 + V12 + V13 (core.cpp future: D22's binding pop guard, V12's error_ref
  handler, V13's exception_info); U48 + U51 + V8 (core.jank load, load-one, load-lib); R99a + S6
  (big_decimal compare: R99a compares doubles explicitly, S6's operators are for math.hpp; same
  answers).
- Compiles (Mac, Apple clang 16, libc++, -std=c++20 -fsyntax-only, deps/ headers +
  /opt/homebrew/include for boost preprocessor; jank itself was not built). Re-run after the
  three corrections:
  - 45 of the 58 changed .cpp files compile in the combined tree, every one that compiles at
    94d32623 here: 40 directly, 5 with `-include jank/runtime/visit.hpp` standing for jank's
    prelude PCH (base needs it too). math.cpp (U2) and delay.cpp (D19) failed before the
    corrections and compile now; U2 and D19 also compile applied alone.
  - 13 cannot be compiled here (LLVM/clang/CppInterOp/cpptrace/isocline headers): analyze/
    cpp_util.cpp, analyze/processor.cpp, c_api.cpp, codegen/cpp_processor.cpp, evaluate.cpp,
    ir/processor.cpp, jit/processor_dynamic.cpp, read/parse.cpp, runtime/context_dynamic.cpp,
    runtime/core.cpp, obj/deferred_cpp_function.cpp, obj/exception_info.cpp, main.cpp. Plus the
    .jank files and test/cpp/jank/read/parse.cpp (R10's test edit).
  - The .jank files read whole with Clojure 1.12's reader, no read error: core.jank 698 -> 702
    forms (one new top-level form each from R73, U48, U49b, U74b-c), data.jank 10 -> 11;
    walk.jank, string.jank, math.jank, completions.jank keep their counts.
  - The merged math.hpp templates: .r6-scratch/merge/cc/tu.cpp instantiates add sub mul div lt
    lte min max for (int, usize), (usize, int), (int, long), (long, double), (double, long),
    (float, int), (unsigned int, int), (char, int), (long long, long long), (int|usize|double,
    object_ref), (object_ref, int|double|object_ref), (int, integer_ref), (integer_ref, int),
    (double, real_ref), (real_ref, usize), (integer_ref, real_ref), (object_ref, integer_ref),
    inc/dec/abs/is_zero/to_int/to_real, bool with add sub div lt min max inc abs, and (with
    -DMUL_BOOL) runtime::mul and runtime::pow of (bool, int), (bool, double), (int, bool) and
    mul (bool, object_ref): compiles, in the combined tree and with R33a alone.
  - Values, merged math.hpp linked with the combined tree's ratio.cpp, big_integer.cpp,
    object.cpp, number.cpp, persistent_string.cpp and string_builder.cpp (GC stubbed to calloc;
    cc/values.cpp, divs.cpp, throws.cpp; outputs cc/out-*.txt):
      (< -1 (count [1])) true; (< (count [1]) -1) false; (<= -1 (count [1])) true;
      (< -2 u32 3323962100) true; (max (count [1]) -1) 1; (min (count [1 2 3]) -1) -1;
      (+ 2147483647 1) 2147483648 (an i64); (- (count [1]) 2) -1; (* 65536 65536) 4294967296;
      (inc (- (count []) 1)) 0; (dec (count [])) -1; float 0.1 / 2 in f64;
      (/ (count [1 2 3]) -1) -3; (/ -6 (count [1 2])) -3; (/ 6 4) 3/2; (/ -2147483648 -1)
      2147483648; (/ Long/MIN_VALUE -1) 9223372036854775808N; (/ 0 5) 0; (/ 3 -2) -3/2;
      (/ 1 0) throws the object "Divide by zero"; (+ Long/MAX_VALUE 1), (* -3 Long/MAX_VALUE),
      (- 0 Long/MIN_VALUE) throw the object "integer overflow"; (min 1 2.5) the long 1;
      (max 1 0.5) the long 1; (max 9007199254740993 1.0) the long 9007199254740993;
      (max 1 ##NaN) NaN; (abs -0.0) through an object +0.0.
    The bool throw paths were compiled, not run (their util::format needs more of jank). These
    values were run before R33a gained its two `else`s, which change only the bool branches of
    mul and pow, none of the paths above.

Conflicts and how each was resolved
-----------------------------------
1. math.hpp (D2, D6, LG1, LG2a, R33a, R33b). Merged with a diff3 chain (R33b, R33a, D6, LG2a, D2,
   LG1, each applied alone to 94d32623 first) and 6 conflict regions resolved by hand
   (.r6-scratch/merge/mh/resolve.py); then every template read. Line numbers below are the
   combined tree's.
   - R33a (primitive_number excludes bool, 29-31) and LG1's widen/primitive_min/primitive_max
     (35-101, after typed_object) are adjacent; both kept.
   - LG2a's checked_add/sub/mul and D2's checked_div were each a new `namespace detail` block at
     the same place (after type_name). Now one block (133-241): LG2a's helpers, then D2's
     integral_operand, exact_integer_operand, checked_div. Text unchanged.
   - add, sub, mul (249-679): LG2a's checked ops on every operand pair, R33b's object throws.
   - div (465-573): D2 and LG1 both rewrote the same lines (LG1's div hunks 2-4). Merged: every
     native operand is widened (LG1) and then divided by D2's checked_div:
       div(prim, object_ref):  make_box(checked_div(widen(l), typed_r->data))
       div(prim, typed):       checked_div(widen(l), r->data)
       div(object_ref, prim):  make_box(checked_div(typed_l->data, widen(r)))
       div(typed, prim):       checked_div(l->data, widen(r))
       div(prim, prim):        checked_div(widen(l), widen(r))
     (and the unreachable primitive/other branches the same way). Object/object div is D2's.
   - lt, lte, min, max (683-1121): LG1's, with R33b's throws. abs (1123): D6's fabs, R33b's
     throw. tan, sqrt, pow, is_zero, to_int, to_real: R33b. inc/dec (1318, 1396): LG1's widen in
     the overflow check, R33b's throw.
   R33a's two `else`s (mul and pow, 656 and 1289) are in the merged file too.
   Where two intents meet:
   - D2's exact division x LG1's unsigned operands. D2 alone already divides a usize exactly (it
     builds cpp_ints from both operands, and cpp_int takes an unsigned long long exactly), so for
     every count/alength/hash the merged code gives the same value as D2 alone. The merged code
     widens first, which changes two things only: a float operand divides in f64 (LG1's intent;
     D2 alone kept C++ float division), and a usize at or above 2^63 (only a wrapped
     subtraction can make one; LG2a's checked_sub now returns i64, so + - * no longer make one)
     reads as the negative long it boxes to, as LG1 intends, where D2 alone would read it as a
     huge positive. Long/MIN_VALUE handling (to BigInt) is D2's, on the widened i64.
   - R33's bool rejection x LG2a's/D2's helpers that let bool through. With R33a, bool is not a
     primitive_number, so add/sub/mul/div/lt/lte/min/max/inc/dec/abs/to_int/to_real/is_zero with
     a native bool select a template whose first branch is !valid_boxed_math<bool> and throws
     R33b's string object ("Can't add a bool to int." etc.). No bool can reach checked_add/sub/
     mul (bool -> `l + r`) or checked_div (bool not exact_integer_operand): those branches are
     now unreachable from the templates and are left as written (defensive, same result as
     before for any direct caller). LG1's widen requires primitive_number, so it never sees a
     bool either. mul and pow with (bool, number) throw too, through R33a's two `else`s.
   - LG1 x LG2a on + - *: LG1 does not touch + - * (its report: "+ - * are LG2a's lines"). LG2a
     computes exactly in i64 from the usize's value, so (- (count [1]) 2) is -1 without LG1's
     widen. Not covered by either: float operands of + - * stay C++ float (P8, not confirmed).
2. delay (D19, V10, V11, S64). Started from fix3's .r6-scratch/fix3/merged/D19+V10+V11.diff
   with D19's correction (`fn = jank_nil;`, see Corrected fixes),
   checked against the three reports: realized flag set on value, nil, std::exception (kept as
   exception_ptr, rethrown as is: V10), object (D19) and error_ref (kept as error_ref: V11); fn
   cleared after the run (D19); later derefs rethrow the stored error in that order (only one is
   ever set). S64 merged into it: `realized` is std::atomic<bool> (header includes <atomic>),
   written under the mutex as before, and is_realized reads it with acquire and no lock (S64's
   intent: (realized? d) inside d's own body). S64's own has_val (= val.is_some()) is not kept:
   it answered "has a value", which D19 replaces with "the body has run" (S64's report leaves
   that answer to D19/V10/V11). s64's test (`(def s64-d (delay (realized? s64-d)))`, @s64-d is
   false) and d19's (runs once for nil, realized? true) both hold by reading.
3. multi_function (U19 vs R100). R100 kept, U19 superseded. Every use read:
   cached_hierarchy is assigned in reset (nil) and reset_cache, compared in get_method, and
   passed to is_a/is_dominant in find_and_cache_best_method; is_dominant calls is_preferred and
   is_a; prefer_method calls is_preferred with hierarchy.deref(). With R100 the cache holds the
   hierarchy's value (Clojure's MultiFn: cachedHierarchy = hierarchy.deref(), isA(ch, ...)), so:
   - get_method compares value with value, so an unchanged hierarchy no longer resets the cache
     under the mutex on every call. That is U19's whole fix: u19's future calls (ua12-mm :a)
     while defmethod holds the mutex, finds :a in method_cache without locking, and returns.
     U19 got the same by adding a second member (cached_hierarchy_value).
   - is_preferred now gets a map at every call site, so `parents` finds the ancestors and a
     preference on an ancestor applies (R100). U19 left is_preferred with the var (R100 unfixed).
   - is_a takes the value as is at both call sites; it is a private static, no other caller.
   R100 alone fixes both; U19's header member is not needed. Tests: u19 (deviations_r4_hangs_
   test.jank) and R100's, which is c05b-prefer-method-on-an-ancestor in deviations_r2_test.jank
   (deviations_main_test.jank has no r100 deftest).
4. S17 vs R5a: both add `#include <limits>` to lex.cpp. R5a's kept, S17's first hunk dropped.
5. math.cpp includes: see Order used, step 5.

Superseded or partly dropped
----------------------------
- U19.diff: entirely, by R100.diff (both of U19's files; multi_function.hpp is unchanged).
- S17.diff hunk 1 (#include <limits>): by R5a.diff.
- S64.diff's has_val member and its store: replaced by D19's flag made atomic (same lock-free read).
- LG1.diff hunks 2-4 (div) and D2.diff's 6 div hunks: replaced by their merged form (above).
- .r6-scratch/fix3/merged/D19+V10+V11.diff: used, plus S64.
- Already in the reports, all present here: V48 = R55a; D12a needs R42; D18a with D18b;
  U36 = U37; V38 covers V39 V40 V45; V41 covers V42; V19 covers V20's dynamic runtime.
- R100's test is c05b-prefer-method-on-an-ancestor in tests/jank_lean/deviations_r2_test.jank
  (not deviations_main_test.jank, which has no r100 deftest). U19's is
  u19-defmethod-with-a-lazy-dispatch-value-realized-by-a-caller-thread in
  deviations_r4_hangs_test.jank; R100 fixes both.

Corrected fixes (found while merging; corrected in place at the coordinator's request)
---------------------------------------------------------------------------------------
- U2 (fixes/U2.diff hunk 3; math.cpp to_big_integer, real/small_real branch; combined line
  1046): `d` is `auto const d{ shortest_decimal(typed_o->data) }` inside a generic lambda, so its
  type is dependent and `d.convert_to<native_big_integer>()` needs the `template` keyword
  (clang: "use 'template' keyword to treat 'convert_to' as a dependent template name"; the base
  line used native_big_decimal(typed_o->data), not dependent). Now
  `d.template convert_to<native_big_integer>()`. It failed alone on 94d32623; it compiles now.
- D19 (fixes/D19.diff, 3 lines; 4 in the merged delay.cpp, lines 49, 56, 63, 67): `fn = {};`
  converts `{}` to jtl::nullptr_t by identity, so overload resolution picked oref's deleted
  `operator=(jtl::nullptr_t)` (oref.hpp 360; clang: "overload resolution selected deleted
  operator '='"). Now `fn = jank_nil;` (nil, the member's initial value; reset() in
  multi_function.cpp assigns jank_nil the same way). It failed alone; it compiles now.
  .r6-scratch/fix3/merged/D19+V10+V11.diff (fix3's file, not edited) still has `fn = {}`; the
  combined delay.diff carries the correction. V10.diff, V11.diff and S64.diff never assign fn
  (checked), and no other fix adds a `= {}` assignment (grep of fixes/*.diff).
- R33a (fixes/R33a.diff, two new hunks): R33a now also adds `else` before
  `if constexpr(jtl::is_same<L, object_ref>)` in the `requires detail::primitive_number<R>`
  overloads of mul and pow (94d32623 math.hpp 495 and 1155; combined 656 and 1289). Why: those
  two overloads, unlike their siblings, had `if constexpr(!valid_boxed_math<L>) { throw ...;
  return object_ref{}; }` followed by a separate `if constexpr` chain. Once R33a makes bool not
  a primitive_number, mul(bool, int) and pow(bool, int) select that overload with L = bool, both
  chains' returns were instantiated, and `auto` deduced object_ref and int: a compile error at
  JIT time for `(* (nil? x) 2)`. With the `else`, a native bool reaching `*` or pow takes the
  throwing branch and throws R33b's string object, as `+`, `-`, `/`, comparisons, inc and dec
  already did. Nothing else in R33a changed.
- Not bugs, worth a look in review: LG2a, D2 and R33b lines exceed jank's 100 columns
  (clang-format will reflow them); S38's lambda declares `auto const source{ object_source(o) }`,
  shadowing analyze_call's `source` (no warning under -Wall -Wextra).

What a build must check first
-----------------------------
1. math.hpp: every instantiation jank makes (core.jank's inlines through the JIT, and the C++
   runtime's object_ref calls). Return types changed and the analyzer reads them: div of two
   integers is object_ref (D2); min/max of a long and a double is object_ref, of a same-type
   pair i64 or f64 (LG1); + - * of two ints is i64 (LG2a). libstdc++ + jank's clang, not checked
   here (the checks above are libc++ and Apple clang 16).
2. The 13 files that could not be compiled here, first analyze/processor.cpp (R26 R27 R29 R34
   S37 S38 together), core.cpp (15 diffs), read/parse.cpp (6) and c_api.cpp (5).
3. delay: delay.hpp gained members (exception_ptr, option<error_ref>, atomic<bool>); rebuild
   everything that includes it. multi_function.hpp is unchanged.
4. Then the tests each report names, and jank's own suites (test/cpp, test/jank, test/bash).

On a build (2026-11-26)
-----------------------
all.diff applied to jank main 7135b7708 (94d32623's compiler+runtime), built with ninja on Linux
x86-64; every replica test (deviations_*_test.jank, the hangs files left out) and jank's 551
pass- files, each in its own process, on the stock build and on this one:
- Replica tests: 16 of 358 pass on stock, 182 with all.diff: 169 now pass.
- Regressions to fix before the patch is whole:
  - deviations_main_test no longer loads (its tests give no report): a `case` with the test
    constant 2147483648 throws "Value out of range for int" while macroexpanding. core.jank's
    `case` (prep-ints) calls `int` on every integer test, and `int` now checks its range as
    Clojure's does; Clojure's case takes its hash mode for tests outside int's range.
  - s02: (/ 6.0M 3.0M) gives 1.9999...M (120 digits) and (/ 3 6.0M) 0.4999...M, not 2.0M and 0.5M.
  - jank's own suite: 549 of 551 pass on stock, 544 with all.diff. Now failing:
    cpp/case/pass-common-native-type, cpp/case/pass-implicitly-compatible-native-type,
    cpp/case/pass-implicitly-compatible-primitive-type, form/case/pass-big-integer and
    cpp/loop/pass-native-binding-trait-convertible (the branch typing of R23/R26, R24's loop
    locals, and `case` with the checked `int`).


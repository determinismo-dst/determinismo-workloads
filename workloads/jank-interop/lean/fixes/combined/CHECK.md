# What to check on the next build of fixes/combined/all.diff

**The build.**
- Apply `fixes/combined/all.diff` to 7135b7708, which has the same compiler+runtime as 94d32623. In round 9 it covers 114 files: round 8's 86 plus the round-9 fixes.
- **New this round:** apply `fixes/combined/immer.diff` inside the immer submodule.
  - The command: `git -C compiler+runtime/third-party/immer apply ../../../fixes/combined/immer.diff`.
  - immer.diff is H8-1's half that lives in immer (jank-lang/immer 282629d0, the commit the submodule pins). A diff on jank's repository can't reach a submodule's files.
  - Without it, y22, y22d, y22e and z29b still fail; everything else below is unchanged.
- Build with ninja as before.

**Run, in this order:**
1. Every `tests/jank_lean/deviations_*_test.jank`, hangs files left out, plus the new `deviations_r9_test.jank` (181 deftests).
2. `generated_r7_test.jank`, stock and patched, in chunks as before.
3. jank's 551 `test/jank/**/pass-*.jank` files.
4. If you can, also:
   - jank's C++ unit tests (`test/cpp/jank/runtime/obj/*.cpp`, `read/lex.cpp`);
   - `test/bash/nrepl-proof`: describe now lists stdin (Q1).

Each test runs in its own process. Each round-9 test's comment names:
- its path;
- jank's predicted stock value;
- the fix that should make it pass.

Verdicts below are relative to `results/r8c-patched.tsv`, round 8's patch.

## 1. The build itself

**Headers every file includes changed:**
- `runtime/object.hpp`: a new `object_type::single_real` (V62b);
- `visit.hpp`;
- `obj/persistent_string.hpp`: a cached unit count (W9u);
- `jank/error.hpp`: `base::thrown` (V9);
- `core/math.hpp`;
- `obj/number.hpp`, `obj/re_pattern.hpp`, `obj/re_matcher.hpp`, `obj/exception_info.hpp`;
- `jtl/utf8.hpp`, `jtl/immutable_string.hpp`.

Everything rebuilds. Watch the PCH first.

**Compiles here.** Mac, `-fsyntax-only`, deps/ headers, Homebrew's clang 22 headers in place of LLVM 23.
- **Every .cpp of the tree, not only the changed ones:** 194 of 207 compile.
  - The other 13 fail identically on round 8's tree. They need isocline, jankzip or the real cpptrace, or build-time defines: main.cpp, terminal_repl_client.cpp, error.cpp, util/clang.cpp, util/environment_dynamic.cpp, util/try.cpp, jtl/panic.cpp, jtl/assert.cpp, aot/processor.cpp, environment/check_health.cpp, jit/object_dynamic.cpp, ui/highlight.cpp, module/loader_dynamic.cpp.
  - Logs: `.r9-scratch/merge/syn9-*.txt`.
- **jank's warning flags** (with -Wswitch-enum) on the 31 changed .cpp files: no new warning.
  - One `-Wcomment` from a `/*` inside V18's comment was found and removed.
  - seq.cpp's existing -Wswitch-enum warning now counts 66 enumerators instead of 65.
  - Logs: `.r9-scratch/merge/warn9-*.txt`.

**.jank files.** fwdref.py reports "new 0" for every changed .jank file: core.jank, shell.jank, bencode.jank, nrepl server core.jank, handler/eval.jank, describe.jank, clone.jank.

**Things a build must settle:**
- The JIT compiles the try that A34 emits: an inner `try` with rethrowing handlers, converting `jank::error_ref` and `std::exception` to an ex-info.
- `std::to_chars(float)` in jank's standard library (V62b).
- `std::countl_zero` and boost's `integer_modulus` (R72f).
- The JIT resolves W9u's two new natives (`byte_count`, `byte_substring`) from bencode.jank's `:include`.
- The AOT build of the four nREPL files (Q1).
- `cpp/cast (std.vector std.string)` in jank.shell (U88).

## 2. Round 8's 186 failures that should now pass (109)

- **H8-1:** y22, y22b, y22c, y22d, y22e.
  - y22b and y22c need only H8-1's jank side; the other three need immer.diff.
- **DEC8-1:** y37, y37b, y38, y38b.
- **Q1, Q2:** y51, y51b, y52.
- **X20b:** g480, g481, g482.
- **Strings (W9u, W9h, W9c, W9r):** b01, b02, b03, b07, b27, lg3, v65, v66, v67, v68, v71, v75, v76, v77, v78, v79, x19, x19b, x25b.
  - b27 is R81: W9r's matcher keeps one input and a position.
  - Generated (48): g465–g473, g483–g485, g495–g503, g510–g518, g528–g530, g543–g545, g558–g563, g573–g575, g619–g621.
- **Numbers (V55, V60, V61, V62b, V85):** v55, v60, v61, v62, v63, v85; generated g452–g454.
- **Errors (A34 with V9, V18):** r34 (with R34), v07b, v07c, v09, v09b, v18, d15, u79, v03 (with V3).
- **CHAMP (H8-1's jank side):** s59, u81.
- **nREPL (V37i):** v37, v37b.
- **Coordinator's fixes:** v82 (V82), u80 (U80), u84 (U84), u88 (U88), u90 (U90).

**Still failing (77), unchanged:**
- regex 20: b24, b25, b30, s22–s35, u35, v35, v36;
- C++ interop 25;
- analyzer 6: r28, r38, r108, r119, s36, s42;
- printing 4: b16, b21, b23, v46;
- reader 4: a11, a17, a20, a21;
- runtime 11: u12, u18, u33, u40, u40b, u49, u59, u67, d21, d23, d25;
- library 5: u65, u85, u91, u92, v47;
- u40c, v15.

**The failure kind changes (error stays error) for:**
- b30, s24, s27, s28, s32, s35: A34 turns libstdc++'s regex_error into an ex-info that `is` reports. The process no longer ends, but the value still differs: Clojure accepts those patterns.

## 3. Predicted to flip from pass to fail: one, by design

- **fix-v03 (deviations_r6_test).**
  - It asserts what jank did with V3: the error is a std::exception that only a `cpp/std.exception` handler sees (`:native`).
  - With A34, an object handler written first sees it as an ex-info (`:object`), which is Clojure's behavior; v03 itself now passes.
- No other test is predicted to move from pass to fail. Please list any that does.

## 4. The generated file (generated_r7_test.jank)

- 54 failed with round 8's patch. All 54 should pass: the 48 string tests, g452–g454 and g480–g482.
- The other 585 pass with round 8's patch and should still pass.
- R58a's byte index in V74+R58 (g561–g563, g619–g621) is replaced by W9u's unit index.

## 5. deviations_r9_test.jank (181 tests, z1–z70)

173 run on Clojure 1.12.3 and pass (`results/r9-coord-clj.txt`). 8 are jank only: z7c (C++ exception types), z26 (bencode) and z33–z38 (nREPL handler, in-process).

Each group: what stock should do, then what the round-9 patch should do.

**Area E, z1–z7c (errors as objects).**
- Stock: z1–z5 fail or err; z6 errs; the controls z7, z7b, z7c pass.
- Patch: z1–z5 pass (A34, V9, V18, X20b).
  - z6 (E9-1: the runtime throws strings, so `ex-message` is nil) still fails.

**Area N, z8–z14e (numbers).**
- Stock: the non-controls fail.
- Patch: everything passes but two.
  - z12j: `(double? (float 1))` is true, because core.jank defines `double?` as `float?`.
  - z14e: the same NaN object `=` itself (no identity for NaN-boxed doubles).
- z8b needs R72 for the scale. z8c is D1, fixed by LG2a.

**Area W, z15–z28 (strings).**
- Stock: z16, z17, z20–z25, z27, z28 fail.
- Patch: all of them pass.
  - z15 (W9-1: `char-array` is bytes) still fails.
- Controls z18, z19, z26 pass on both.

**Area H, z29–z32 (CHAMP).**
- Stock: the non-controls fail.
- Patch: all pass, with immer.diff for z29b.
  - z29 also passes on the combined tree without immer.diff: R72's exact `=` leaves no non-transitive triple.

**Area Q, z33–z38 (nREPL, jank only).**
- Stock: z33–z37 fail, z38 passes.
- Patch: z36 (Q1) and z37 (Q2) pass.
  - Q9-1 to Q9-3 have no fix: z33 (empty code answers no-code), z34 (no code: no error), z35 (missing ns: no error, no :ns).

**Area T, z39–z54b (sequences).**
- With the patch, these pass:
  - z40, z40b (T9-2);
  - z47, z47b (T9-9);
  - z51 (D12a/D12b: `(distinct [1 1N])`);
  - the controls: z39d, z39e, z40c, z41f, z43c, z48e, z49c, z52, z52b, z53, z53b, z54b.
- These still fail:
  - z39, z39b, z39c: T9-1, std::stable_sort against TimSort with NaN;
  - z41–z41e: T9-3, vectors and `(range n)` not chunked;
  - z42–z42c: T9-4, iterate one step early;
  - z43, z43b: T9-5, apply realizes 12;
  - z44: T9-6, dedupe;
  - z45: T9-7, cycle's realized?;
  - z46, z46b: T9-8, drop past the int range;
  - z48–z48d: T9-10, sorted collections and NaN;
  - z49, z49b: T9-11, realized? of an unwrapped lazy seq;
  - z50: T9-12, a re-forced lazy-seq body keeps its locals;
  - z54: T9-13, str of a lazy seq.

**Area M, z55–z70d (collections).**
- With the patch, these pass:
  - z58–z58d (R121), z60 and z60c (R120's cons);
  - z61–z61d (H9-3: M9-5 is the same deviation);
  - z62c (H8-1: the kwargs hash-map keeps the stored key);
  - the controls: z55f, z57e, z58e, z60e, z61e, z62d, z64c, z66c, z68b, z70d.
- These still fail:
  - z55–z55e: M9-1, an index past 32 bits;
  - z56–z56d: M9-2, a string index that is not an integer;
  - z57–z57d: M9-3, `contains?` of a list;
  - z59, z59b: M9-4, `select-keys` meta;
  - z60b, z60d: R120's repeat;
  - z62, z62b: M9-6, kwargs order;
  - z63–z63d: M9-7, `assert`'s message;
  - z64, z64b: M9-8, walk demos;
  - z65, z65b: M9-9, `update-vals` sorted;
  - z66, z66b: M9-10, `empty` of a seq keeps meta;
  - z67: D10, Unicode digits;
  - z68: zipmap's transient hash map;
  - z69, z69b: U67;
  - z70–z70c: M9-11, CHAMP order against Clojure's HAMT order.

## 6. Each new diff: what should pass, what to watch

- **A34** (codegen `try`, exception_info, util/try.cpp, context.cpp; contains V7a). Analysis, load and arity errors, and the runtime's std::exceptions, reach an object catch as an ex-info.
  - Should pass: the tests in section 2's errors item; z1–z4b; g480–g482 with X20b.
  - Watch:
    - clojure.test now reports these errors instead of the process ending;
    - load-lib removes a half-made namespace and rethrows;
    - the CLI prints the attached error's report for such an ex-info;
    - jank's 57 suite files with `catch` (read: they hold), cpp/try/pass-catch-mixed.jank above all.
- **V9, V18.** A module's or a macro's ex-info is the cause, and compile errors get Clojure's CompilerException shape (message "Syntax error … at (file:line:col).", `:clojure.error/*` data). Watch u44 (should still pass) and nREPL's eval-error text (unchanged by reading).
- **X20b.** nth's checks in seq.cpp, persistent_vector, array_chunk and transient_vector throw an ex-info.
- **W9u, W9h, W9c, W9r.** Strings are UTF-8 (WTF-8 for lone surrogates); every index a program sees is a UTF-16 unit; `hash` is String.hashCode; `char` takes 0..0xFFFF; an empty regex match steps one unit.
  - Watch:
    - suite files pass-string.jank and pass-unicode-char.jank;
    - the nREPL with non-ASCII output (bencode now counts bytes through byte_count);
    - the speed of nth loops over non-ASCII strings (O(n) per index).
- **H8-1** (jank side) and **immer.diff**.
  - The jank side: assoc keeps the stored key, assoc of the identical value returns the map, conj of a member returns the set.
  - immer.diff: a replaced collision entry keeps its place.
  - Watch: the cost of one extra lookup per hash-map assoc.
- **H9-3.** An 8-entry array map promotes only when the key is absent. Watch: test/cpp array-map promotion unit tests (they add a new key: still promote).
- **Q1, Q2 (on Q1), V37i.** Watch: nrepl-proof's stdin checks may now switch on.
- **DEC8-1, V55, V60, V61, V62b, V85, R72f** (area N's stack). Watch:
  - **V62b:** a new object type (single_real) wired through visit, number.cpp and codegen. C++ floats stay small_real; suite file cpp/if/pass-typed-object.jank relies on that.
  - **R72f:** bit-for-bit R72 (1,474,900 checks and round 8's 229,699 cases); the speed of BigDecimal compare and hash.
- **V82, U80, U84, U88, U90, T9-2, T9-9** (coordinator).
  - **U84:** data.json reads through nlohmann's SAX events. key-fn and value-fn, duplicate keys, parse errors and eof behave as before.
  - **U88:** jank.shell passes an argument vector; the program is found on the parent's PATH.
  - **T9-2:** sort's comparator result is read as Java's intValue.
  - **T9-9:** partition-all's transducer casts n to a long and refuses a negative n.

## 7. Not compiled here

- The same 13 files as round 8 (section 1).
- `test/cpp/jank/read/parse.cpp` (fails at 94d32623 too).

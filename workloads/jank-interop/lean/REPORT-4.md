# REPORT-4: jank 7135b7708 compared with Clojure 1.12, round 4

**Version.** jank `7135b770857d625630ab6f9abe5861c618d67b82` (`upstream-main/`). Every jank path below is under `upstream-main/compiler+runtime/` and uses its line numbers.

**Libraries.** Round 3's pinned libraries, plus three submodules shallow-fetched at the commits jank pins (added to `fetch-sources.sh`):
- boost-process e4d0d405 (`jank.shell`);
- json (nlohmann) 02dfbea3 (`clojure.data.json`);
- stduuid 3afe7193 (`parse-uuid`).

No history was read.

**Status.** Every item is a hypothesis from Lean replicas, re-read against the source. jank was not built or run.

**Who did what.**
- Seven area agents worked in parallel: runtime (A), interop (B), immer and collections (C), regex (D), nREPL (E), modules/AOT/CLI (F), core functions (G).
- I did the feedback on S2, S9 and S44, `jank.shell`, `clojure.pprint`/`clojure.stacktrace`, the residual runs, reproducibility, the test merge, and this report.
- I re-read the source for U8–U12 (lazy compilation), U34, U40 and U61. Each holds as stated.
- Area reports: `results/r4-<area>-report.txt`; run outputs: `results/r4-<area>*.txt`.

**Build.**
- `lake build` of all 28 targets (rounds 1–4) succeeds: 774 jobs.
- Round 4 adds 59 files and 14,852 lines under `Jank/R4/` and `Run/R4/`, with 8 exes `jank4-<area>` (feedback, runtime, interop, immer, regex, nrepl, modules, core).
- No `sorry`, no `native_decide`, no new axiom. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.

**Keeping rounds 1–3 building.**
- The pinned sdk (b8f9cc9) added `Stop.nodeDown`. I added 22 arms, each a copy of the `.limit` arm, in 16 round-3 files.
- `Run/R3/Codegen.lean` now qualifies `mixSeed`, because the sdk exports `Determinismo.mixSeed`.
- Reruns:
  - jank-model, jank-reader: every exhaustive line is identical. The seeded explores draw other timelines, so their first examples differ; 4 round-1 explore verdicts changed (2 find nothing, 2 find deadlocks), and their exhausts give the old verdicts.
  - jank3-proofs and jank3-boost checks: identical.

## Deviations at a glance

Clojure's result comes first, then jank's. "S n", "R n", "D n" refer to earlier rounds.

**Re-stated from round 3 (feedback):**
- **U1** (S2) `(compare 2M (/ 6M 3M))`: Clojure 0, jank 1. u01.
- **U2** (S9) `(compare 0.1M (bigdec 0.1))`: Clojure 0, jank -1. u02.
- **U3** (S44) `(eval (list 'quote v))` turns `v`'s `{}` metadata into nil. u03.
- **U4** (S49) `(#cpp (add double) 1 2)`: C++ 3.0, jank 3. u04.
- **U5** (S50) a call through a fn pointer with a `long const &` parameter: C++ 42, jank rejects it. u05.
- **U6** (S53) `(cpp/+ meters 1.0)`: C++ 2.5, jank rejects it. u06.
- **U7** (S57, narrowed) inside a fn, `(if c 1 cpp/gd)` gives 2 where Clojure gives 2.5. At the top level, jank gives Clojure's result. u07, control u07b.

**Lazily compiled fns and the runtime:**
- **U8** an `alter-var-root` wrapper is lost at the wrapped fn's first call. u08.
- **U9** `with-redefs`: the stub is replaced when the original first runs. u09.
- **U10** calling an old fn value for the first time reverts its var's redefinition. u10.
- **U11** a defn'd fn's identity changes at its first call. u11.
- **U12** `with-meta` on a defn'd fn not yet called throws. u12.
- **U13** `alter-var-root` whose fn first-calls the var's fn hangs (a variant of S63). Hangs file: u13, u13b.
- **U14** a defn'd fn gets `{:name "ns/f"}` metadata after its first call. u14.
- **U15** `get-thread-bindings` maps each var to a box, not its value. u15.
- **U16** an unbound root prints `unbound@0x… for var #'x`, not `Unbound: #'x` (from S70). u16.
- **U17** `push-thread-bindings` rejects an array map. u17.
- **U18** `pop-thread-bindings` without a push returns nil instead of throwing. u18.
- **U19** `defmethod` with a lazy dispatch value realized by a thread calling the multimethod hangs. Hangs file: u19.

**C++ interop:**
- **U20** enum operands: jank's analysis ignores the user's operator, the JIT calls it, and the result is narrowed (0.5 becomes 0). u20.
- **U21** a scoped enum's user operators can't be used. u21.
- **U22** a derived class's operator doesn't hide its base's: jank calls it ambiguous. u22.
- **U23** (low) operator lookup follows using-directives. u23.
- **U24** (low) a user operator that C++ finds ambiguous with a built-in one is accepted. u24.
- **U25** `(cpp/wrap. 2.5)` uses the template's default arguments instead of deducing them: `.-v` is 2. u25.
- **U26** `cpp/delete` of a pointer from C++'s own `new` crashes (`GC_free`). u26.

**Collection objects:**
- **U27** `with-meta` on an infinite `repeat` writes the metadata into the original object. u27.
- **U28** `with-meta` on `iterate` or `(range)` never returns. Hangs file: u28, u28b.
- **U29** `(nth [1 2 3] 1.0)` throws instead of giving 2. u29.
- **U30** `(realized? (iterate inc 0))` throws. u30.
- **U31** `pop` of a one-element list drops the list's metadata. u31.
- **U32** `seq` of a list drops the list's metadata. u32.
- **U33** `transient` of a sorted map is accepted. u33.
- **U34** `array-map` with more than 8 pairs keeps only the first 8 keys. u34.

**Regex:**
- **U35** a capture made inside a lookahead at an earlier start position: Clojure keeps it (`["b" "a"]`), jank loses it (`["b" ""]`). u35.
- **U36** `nth` on a matcher without groups indexes the match string's bytes. u36.
- **U37** `nth` on a matcher with no current match gives nil instead of throwing. u37.
- **U38** `re-pattern` stops at the first NUL. u38.
- **U39** `print` writes a pattern as its bare text. u39.

**nREPL and REPL:**
- **U40** no `:line`, `:column`, `:file`, `:name` or `:ns` metadata on read lists and defined vars; the nREPL's line/column fields never reach it. u40, u40b, u40c.
- **U41** `completions` gives each var the searched namespace as its `:ns`. u41.
- **U42** `jank repl` never sets `*e`. No test (shell repro).
- **U43** `jank repl` evaluates each line alone. No test (shell repro).
- **U44** after a read or analysis error, `(ex-message *e)` is `""`. u44.

**Modules, AOT, CLI:**
- **U45** `run-main` calls `-main` with `*ns*` = clojure.core (Clojure: user). u45.
- **U46** (extends R109) an AOT module that shadows a core name it uses fails at start-up. No test.
- **U47** an AOT binary with the static runtime exits 0 after an uncaught exception. No test.
- **U48** `load` takes a module name, not a resource path. u48.
- **U49** `load-string`, `requiring-resolve`, `ns-aliases`, `ns-refers` and others are unported, and `load-file` doesn't exist (the class of R113/R124, new names). u49.
- **U50** (low) `refer :only` accepts a set. u50.
- **U51** (low) `:verbose` prints nothing. u51.
- **U52** the last module-path element wins; a class path takes the first. No test.
- **U53** a ZIP file on the module path registers nothing. No test.
- **U54** (low) a file name holding a munge escape can't be required. No test.
- **U55** (extends R21) `(ns x)` gives the namespace `:jank/source` metadata. u55.
- **U56** (low) `--gc-incremental` is documented but never parsed. No test.
- **U57** (low) an unused flag silences the extra-positional-arguments error. No test.
- **U58** `jank compile` fails for namespaces without a module (`:as-alias`, `create-ns`). No test.
- **U59** `(compile 'clojure.set)` throws at run time and would return nil. u59.
- **U60** (low) `run-main` evaluates a self-requiring module twice. No test.

**clojure.core and bundled namespaces:**
- **U61** `clojure.data/diff` never subdiffs maps, vectors or sets. u61.
- **U62** `ex-message`, `ex-data`, `ex-cause` of a non-exception throw instead of returning nil. u62.
- **U63** `Throwable->map` gives the outer exception's `:cause` and `:data`, not the root's. u63.
- **U64** a printed chain of 3 or more exceptions repeats the first cause. u64.
- **U65** `format` follows std::format: `(format "%d" 5)` is `"%d"`. u65.
- **U66** `counted?` is true for strings, arrays and map seqs; `(bounded-count 1 "abc")` is 3. u66.
- **U67** `map-entry?` is true for any 2-vector. u67.
- **U68** (extends R120) `shuffle` throws on `cons`, `repeat` and `sort` results. u68.
- **U69** `clojure.walk` drops list metadata (a Clojure 1.12 behavior). u69.
- **U70** a tagged literal prints its form with `str`. u70.
- **U71** (low) `parse-uuid` accepts undashed and braced text. u71.
- **U72** `areduce` throws on any non-empty array. u72.
- **U73** `newline` and `flush` throw "TODO: port". u73.
- **U74** more unported names (`unchecked-*`, `into-array`, `reversible?`, `indexed?`, …). u74, u74b.
- **U75** (low) bit operations accept BigInts. u75.
- **U76** `(spit f 42)` throws. u76.
- **U77** `slurp` takes no options. u77.
- **U78** `spit` to a path it can't open returns nil. u78.
- **U79** `slurp` of a missing file throws a native error an object catch misses. u79.
- **U80** (low) `reduce-kv` rejects a seq of entries. u80.
- **U81** (extends S59) `zipmap` replaces an equal key at any size. u81.
- **U82** `#inst "2020"` is a read error. u82.
- **U83** `json/read-str` wraps integers in [2⁶³, 2⁶⁴). u83.
- **U84** (extends S9) `:bigdec` reads through a double. u84.
- **U85** `write-str` writes BigInts and BigDecimals as strings. u85.
- **U86** (low) `write-str` writes NaN as null. u86.
- **U87** `:eof-error? false` throws on empty input. u87.
- **U88** `jank.shell/sh` splits an argument at a space that follows an odd number of `"`. u88.
- **U89** `sh` hangs when the child writes more than a pipe holds. Hangs file: u89.
- **U90** (low) `sh`'s `:env` takes only strings. u90.
- **U91** `clojure.pprint/pprint` is `prn`: no line breaking at the right margin. u91.
- **U92** `clojure.pprint` and `clojure.stacktrace` lack most of their documented functions. u92.

## Feedback from the real jank (prompted)

**S2, S9 (refuted on jank).**
- **Where it departed:** the tests, not the replica. Both used `=`. jank's `=` on BigDecimals is `big_decimal::equal` (obj/big_decimal.cpp 146–155, `abs(a−b) < f64 epsilon`, round 1's D8), reached through core/equal.cpp 19–22.
- **The replica on the tests' exact forms:** round 3's replica has that epsilon (`jEqual`). Run on the forms, it answers true for `(= 2M (/ 6M 3M))`, `(= 0.5M (/ 3 6M))` and `(= 0.1M (bigdec 0.1))` (results/r4-feedback.txt). It predicted that the tests pass.
- **The values stand:**
  - `(/ 6M 3M)` is `1.999…9` (121 digits), `(/ 3 6M)` is `0.4999…98`, `(bigdec 0.1)` is the binary value.
  - Cross-check: boost `cpp_dec_float<100>`, compiled from `deps/boost-multiprecision` with Apple clang (`.r4-scratch/boostcheck/`), prints exactly the replica's strings for 6/3, 3/6, 1.5/3 and `D(0.1)`.
- **Fix:** the re-tests (U1, U2) observe with `compare` (big_decimal.cpp 182–190, exact) and `str`.
- **What else it changes:** I re-read every round-3 BigDecimal test.
  - S4, S7 and S8 are confirmed by the values jank printed. S4's `not=` alone could not have told.
  - S10 uses `=` on purpose.
  - G's U84 uses `compare`.

**S44 (refuted on jank).**
- The test gave `{:m 1}`. `strip_source_from_meta` (core/meta.cpp 229–239) leaves it; round 3's own theorem `strip_changes_iff` says so.
- New theorems: `s44_round3_test_meta_kept`, `s44_round4_cases`.
- The re-test (U3) uses `{}` and `{:jank/source 1 :m 1}`.

**S49, S57 (failed in another way).**
- **Cause:** the tests ran `(ev "(do (cpp/raw …) use)")`.
  - context::eval (context_dynamic.cpp 220–226) analyzes the whole form.
  - analyze_do analyzes every sub-form, while evaluate.cpp eval(cpp_raw) (633–637) declares the C++ only at evaluation.
  - So the use failed in analyze_cpp_symbol as an unresolved name: S71's mechanism. The new top-level replica (`Jank/R4/Interop/TopLevel.lean`) gives exactly that error for all four round-3 shapes.
- **Corrected order** (cpp/raw in its own eval):
  - S49 stands (3; world XII rerun, still 69 of 75).
  - S57 is refuted at the top level. evaluate.cpp eval(if) 594–606 interprets the chosen branch alone and gives 2.5, so REPORT-3's example was wrong there. It stands inside a fn (gives 2).
  - World XVI rerun in both contexts: 36 of 324 deviate, all in compiled fns (26 S57-class, 10 R23).
- **Not prompted:** S50 and S53 used the same shape, so their round-3 "confirmations from an error" are not evidence. Both still hold in the replica; re-tested as U5 and U6.

**S69 (jank gave Clojure's result).**
- **Where it departed:** round 3's GC replica dropped a frame's words when the frame returned (RTA8). The test also threw inline in the fn that runs the finally (gen(throw) 1023–1051, gen(try) 1053–1101). REPORT-3's program used a separate `boom` fn.
- **Why the value survives:** at jank's default -O0 (util/cli.cpp 205–206) the thrown local's slot is in the live frame, and bdwgc scans it (pthread_stop_world.c `GC_push_all_stacks` 836–947).
- **Fix:** `Jank/R4/Runtime/Gc4.lean` models the stack conservatively. Live frames are scanned; a returned frame leaves stale words that may be scanned or overwritten (a decision per collection); at -O1+ a local may live only in a register.
- **Rerun:**
  - The test's shape at -O0: a freed read is never reachable (complete over 64/128/256 timelines), which is what jank did.
  - A separate thrower: both a freed read and survival are reachable.
- **Outcome:** S69 is withdrawn as a prediction (possible, not certain). RT8's other-thread variant is weakened the same way.

**S70 (jank printed `unbound@0x… for var …`).**
- The test asserted Clojure's text, which jank never prints (var.cpp 351–354).
- The freed read also rested on RTA8. After ns-unmap, the var is held by the pointer-free root and by stale stack words of the defining and ns-unmap frames. No registry or JIT global holds it.
- With the fix, a freed read and survival are both reachable, so the freed read is withdrawn. The print difference is its own deviation, U16.
- The validation evidence cuts every line at 259 characters, so the S70 line can't show what followed "for var".

**Related notes (not prompted).**
- `jank run-main` binds `*ns*` to clojure.core (U45). So every round's `ev` helper evaluated in clojure.core, which explains S71's evidence naming `clojure.core/s71-m` and S73 printing `"clojure.core"`.

## Deviations in full

Each item gives the program (Clojure's result, then jank's), the path, the test, and status/confidence. Full traces, tapes and searches are in the area reports.

### Re-stated (U1–U7)
- **U1 (already S2).** `(compare 2M (/ 6M 3M))`: Clojure 0, jank 1. `(= (str 2M) (str (/ 6M 3M)))`: Clojure true, jank false. `(compare 0.5M (/ 3 6M))`, `(compare 0.5M (/ 1.5M 3))`: 0 vs 1. Path as S2. Test u01. High.
- **U2 (already S9).** `(compare 0.1M (bigdec 0.1))`: 0 vs -1. Path math.cpp 817 → `operator=(double)`. Test u02. High.
- **U3 (already S44).** `(let [v (with-meta [1] {})] (eval (list 'quote v)) (meta v))`: `{}` vs nil. With `{:jank/source 1 :m 1}`, the `:jank/source` entry is removed. Test u03. High.
- **U4 (already S49).** With `template <typename T> T add(T,T)` declared in its own eval, `(#cpp (add double) 1 2)`: 3.0 vs 3. Test u04 (C++ only). High.
- **U5 (already S50; round 3's confirmation was not evidence).** `(cpp/twice_ptr 21)`: 42 vs "argument 0 is not convertible". Test u05 (C++ only).
- **U6 (already S53; same).** `(cpp/+ (cpp/mk) 1.0)`: 2.5 vs "operator is not supported". Test u06 (C++ only).
- **U7 (S57, narrowed).**
  - `((fn [c] (if c 1 cpp/gd)) false)`: 2.5 vs 2 (cpp_util.cpp find_branch_common_type 1909–1995, compiled `if`).
  - At the top level jank gives 2.5. Test u07, control u07b (predicted to pass). C++ only. High.

### Lazy compilation and runtime (area A; plus B's B1)

The root of U8–U14:
- jank compiles top-level fns lazily by default (util/cli.hpp 141, `--lazy` default, `--eager` opt-out; the book doesn't mention it).
- evaluate.cpp eval(def) 333–362 sets `current_def_var`; eval(function) 522–555 makes a `deferred_cpp_function(meta, current_def_var, …)`.
- Its `realize` (deferred_cpp_function.cpp 46–73) compiles on the first call and does `var->bind_root(compiled_fn)` unconditionally (69–70), whatever the var holds by then.
- Reach: every defn evaluated by the interpreter, which covers the REPL, the nREPL, `jank run` and every module loaded from source (test namespaces included). Not reached: AOT and `--eager`.
- Clojure: a fn is a value, and calls never touch vars.
- Searches: complete over 2,613,659 programs; with the mechanisms set aside, nothing. `--eager`: only U14's class.
- Theorems ★ `realize_rebinds`, ★ `realize_inside_alter_hangs`, ★ `clojure_call_keeps_roots`; B's ★ `eager_agrees_clojure`.

Items:
- **U8 (new).** `(defn twice [x] (* 2 x)) (alter-var-root #'twice (fn [o] (fn [x] (+ 100 (o x)))))`. `(twice 1)` twice: 102, 102 vs 102, 2. Test u08. High.
- **U9 (new).** `(defn greet [] :orig) (let [o greet] (with-redefs [greet (fn [] :stub)] [(o) (greet)]))`: `[:orig :stub]` vs `[:orig :orig]` (also core.jank with-redefs-fn 4549–4566). Test u09. High.
- **U10 (new; found by A and B).** `(defn v [] :old) (def s v) (defn v [] :new) (s) (v)`: `:new` vs `:old`. Test u10. High.
- **U11 (new).** `(defn f [] 1) (def h f) (f) (identical? h f)`: true vs false. Test u11. High.
- **U12 (new).** `(meta (with-meta f {:k 1}))` with f never called: `{:k 1}` vs throws (deferred_cpp_function.hpp 32–35 has no with_meta). Test u12. High.
- **U13 (new; a variant of S63).**
  - Program: `(defn inc1 [x] (inc x)) (alter-var-root #'inc1 (fn [g] (g 1) g))` returns in Clojure and hangs in jank. Also across threads via `@(future (g 1))`.
  - Path: var.cpp alter_root 108 holds write_mutex; realize → bind_root 101 re-takes it.
  - Tape: 10 steps on one thread, 12 on two (Mutexes.lean). Tests u13, u13b (hangs file). High.
- **U14 (new, low).** `(defn f [] 1) (f) (meta f)`: nil vs `{:name "user/f"}` (processor.cpp 2064–2067, realize 66). Test u14. High.
- **U15 (new).** `(binding [*x* 1] (= 1 (get (get-thread-bindings) #'*x*)))`: true vs false.
  - Path: context.cpp get_thread_bindings 765–775 returns `var_thread_binding` boxes (push 706–750); a box has no `equal`.
  - Theorem ★ `getTB_bound_differs`. Test u15. High.
- **U16 (new; from S70).** `(def x) (str @#'x)`: `"Unbound: #'user/x"` vs `"unbound@0x… for var #'user/x"` (var.cpp 351–354). Theorem ★ `unbound_str_differs`. Test u16. High, low impact.
- **U17 (new).** `(push-thread-bindings {#'*x* 1})`: ok vs throws "must be hash map" (context.cpp 694–703). Theorem ★ `pushArray_rejected`. Test u17. High.
- **U18 (new, low).** `@(future (pop-thread-bindings))`: throws vs nil (context.cpp 752–763). Theorem ★ `future_pop`. Test u18. High.
- **U19 (new).**
  - Program: `(defmulti mm identity) (defmethod mm :a [_] 1) (let [l (lazy-seq (cons @(future (mm :a)) nil))] (defmethod mm l [_] 2) (mm l))`: 2 vs hangs.
  - Path: multi_function.cpp add_method 145–153 holds the recursive mutex while hashing (realizing) `l`. get_method 248–260 takes the mutex on every call, because `cached_hierarchy` stores the var and is compared with its value, so the cache never matches.
  - Tape: 7 steps. Test u19 (hangs file). Medium.

### C++ interop (area B)
- **U20 (new).** `enum ue {ua=1,ub=2}; double operator*(ue,ue){return 0.5;}`, then `(cpp/* cpp/ua cpp/ub)`: 0.5 vs 0.
  - Path: processor.cpp build_cpp_call 367–410 (`is_primitive` counts enums) → built-in operator type int; codegen 1794–1821 calls the user operator and boxes as int.
  - Theorem ★ `jank_primitive_operands_builtin_only`. Test u20. High (path), medium-high (value).
- **U21 (new).** With a scoped enum and a user `operator|`, `(cpp/| cpp/se.a cpp/se.b)`: `se(3)` vs an analysis error. Theorem ★ `jank_primitive_operand_unary_builtin_only`. Test u21. High.
- **U22 (new).** `struct B{int operator*(int)const;}; struct D:B{int operator*(double)const;}`, then `(cpp/* d 1)`: 4 vs "ambiguous".
  - Path: CppInterOp.cpp GetOperator 6977–7064 adds the operators of every associated class; Clang's member lookup would hide the base's.
  - Test u22. High.
- **U23 (new, low).** Operator lookup follows using-directives inside associated namespaces (GetOperator 7017–7030), so jank accepts code C++ rejects. Test u23.
- **U24 (new, low; S53's root).** A user operator that C++ finds ambiguous with a built-in candidate is accepted (BestOverloadMatch 2203 adds no built-ins). Test u24.
- **U25 (new).** `template <typename T = int> struct wrap {T v; wrap(T x):v(x){}};`, then `(cpp/.-v (cpp/wrap. 2.5))`: 2.5 vs 2.
  - Path: build_cpp_value 3738–3752 → `instantiate(scope, {})` → CompleteTemplateArguments (CppInterOp.cpp 6644) fills the defaults.
  - Theorem ★ `jank_ctor_specialization_is_defaults`. Test u25. High.
- **U26 (new, low-medium).** `(cpp/delete (cpp/make))` with `make` returning `new int(5)`: freed vs SIGSEGV.
  - Path: codegen 1894–1919 emits `GC_free`; bdwgc GC_free 824–850 reads the header of non-GC memory.
  - Read and tabled, not searched. Test u26 (predicted segfault).

### Collection objects (area C)
- **U27 (new).** `(let [r (repeat 7)] (with-meta r {:a 1}) (meta r))`: nil vs `{:a 1}` (repeat.cpp with_meta 124–130 over fresh_seq 53–60, which returns `this` when infinite). Theorem `c1_repeat_meta_written`. Test u27. High.
- **U28 (new).** `(meta (with-meta (iterate inc 0) {:a 1}))`, also `(range)`: `{:a 1}` vs never returns (iterator isn't metadatable; meta.cpp 50–53 builds the error text from the infinite seq). Theorem `c2_iterate_with_meta`. Tests u28, u28b (hangs file). High.
- **U29 (new; medium-low as a defect).** `(nth [1 2 3] 1.5)`: 2 vs throws (persistent_vector.cpp nth 322–348 with the original index; lists truncate). Theorem `c3_nth_double`. Test u29. High.
- **U30 (new, low).** `(realized? (iterate inc 0))`: true vs throws (core.cpp is_realized 719–737). Test u30.
- **U31 (new, low).** `(meta (pop (with-meta '(1) {:a 1})))`: `{:a 1}` vs nil (persistent_list.cpp pop 180–189). Test u31.
- **U32 (new, low).** `(meta (seq (with-meta '(1 2) {:a 1})))`: `{:a 1}` vs nil (persistent_list.cpp 100–112). Test u32.
- **U33 (new, low).** `(transient (sorted-map 1 2))`: throws vs a transient. Test u33.
- **U34 (new).** `(count (array-map 0 0 1 1 2 2 3 3 4 4 5 5 6 6 7 7 8 8))`: 9 vs 8. An update after 8 entries is also lost.
  - Path: persistent_array_map.cpp create_from_seq 36–55 discards `assoc_in_place`'s promoted map (transient_array_map.cpp 67–89).
  - Theorem `jank_array_map_at_most_8`; contradicts round 3's IMA7 for jank's own code. Test u34. High.

### Regex (area D)
- **U35 (new).** `(re-find #"(?=(a))x|b" "ab")`: `["b" "a"]` vs `["b" ""]`. Also `(re-find #"(?!(a))$" "a")`, and replace with `$1`.
  - Mechanism: Java clears its groups once per `find`; libstdc++ restarts each position from `_M_results` (regex_executor.tcc 41–57, 84–92).
  - Censuses: 13,144 of 1,717,065 (≤3 tokens), 178,668 of 39,495,600 (≤4).
  - Test u35. High on jank's side.
- **U36 (new).** `(let [m (re-matcher #"ab" "xaby")] (re-find m) (nth m 0))`: `"ab"` vs `\a` (re_matcher.cpp 14–22 → string nth). Theorem ★ `nth_no_groups_never_the_match`. Test u36. High.
- **U37 (new).** `(nth (re-matcher #"(a)" "a") 0)`: throws vs nil. Theorem ★ `nth_without_match_nil`. Test u37. High.
- **U38 (new; distinct from R83).** `(re-find (re-pattern (str "x" (char 0) "y")) "xz")`: nil vs `"x"` (re_pattern.cpp 6–11 uses `c_str()`). Theorem ★ `jankEval4_pattern_nul`. Test u38. High.
- **U39 (new, low; R69/R75's root).** `(print-str #"a")`: `"#\"a\""` vs `"a"`. Theorem ★ `print_pattern_differs`. Test u39.

### nREPL and REPL (area E)
- **U40 (new).**
  - Program: `(meta '(a b))` gives `{:line … :column …}` in Clojure and nil in jank. `(:name (meta #'f))`, `:ns`, `:line`, `:file`: present vs nil. An eval request with line 7 and code `(:line (meta '(a)))` returns "7" vs "nil".
  - Path: positions only reach `{:jank/source …}` (core/meta.cpp 171–228), which strip_source_meta then removes; var.cpp set_meta 307–311 adds nothing.
  - Theorems `jank_has_no_line_meta`, ★ `jankPos_eq_cljPos`. Tests u40, u40b, u40c (jank only). High.
- **U41 (new; medium-low, rests on EA4-3).** `completions` prefix "mapv" from ns user: `:ns "clojure.core"` vs `:ns "user"` (completions.jank 54–64). Test u41 (jank only).
- **U42 (new as an item; round 3 noted it).** `jank repl`: `(throw (ex-info "e" {}))` then `(nil? *e)`: false vs true (terminal_repl_client.cpp 283–379). Shell: `printf '(throw (ex-info "e" {}))\n(nil? *e)\n' | jank repl`.
- **U43 (new).** `jank repl`, piped input `(+ 1` then ` 2)`: 3 vs two errors (read_line 223–244; each line is `eval_file`d alone). Shell: `printf '(+ 1\n 2)\n' | jank repl`.
- **U44 (new).** At the nREPL, `(ue5-undefined)` then `(ex-message *e)`: the compiler message vs `""` (evaluate.cpp safe_eval 750; exception_info(error_ref) sets no message). Test u44 (jank only). High.

### Modules, AOT and CLI (area F)
- **U45 (new).** Under `run-main`, `-main` sees `*ns*` = clojure.core (`read-string "::k"`, `eval`, `resolve` act there); `clojure -M -m` uses user.
  - Path: main.cpp run_main 83–115; context.cpp 107–113.
  - Corroborated by round 3's S73/S71 evidence. Test u45. High.
- **U46 (extends R109).** An AOT module that defines `update` and uses it fails at start-up with "update already refers to #'app.core/update" (cpp_processor.cpp gen_cpp 2092–2180 interns lifted vars before `(ns …)`). Shell steps in the area report.
- **U47 (new).** An AOT binary on the static runtime exits 0 after an uncaught exception (c_api.cpp jank_init_static 1168 `return 0;`). Theorem ★ `aot_static_status_zero`.
- **U48 (new).** `(load "/clojure/walk")`: loads vs "module could not be found" (core.jank load 4801). Test u48.
- **U49 (R113/R124 class, new names).** `load-string`, `load-reader`, `requiring-resolve`, `ns-aliases`, `ns-refers`, `ns-imports` throw "TODO: port"; `load-file` doesn't exist. Test u49.
- **U50 (new, low).** `(refer 'clojure.string :only #{'join})`: throws vs accepted. Test u50.
- **U51 (new, low).** `(require … :reload :verbose)` prints nothing (load-lib 4846). Test u51.
- **U52 (new).** With the same module in two module-path elements, jank loads the last (loader_dynamic.cpp register_entry 181–241). Theorem ★ `upsert_jank_last_wins`.
- **U53 (new, low-medium).** A ZIP file on the module path registers nothing, though `--help` lists ZIP files (register_path 297–325).
- **U54 (new, low).** `x/a_PLUS_b.jank` is indexed as `x.a+b` (path_to_module 36–50).
- **U55 (extends R21).** `(meta (find-ns 'x))` after `(ns x)`: nil vs `{:jank/source …}` (core.jank ns 5633–5637). Test u55.
- **U56 (new, low).** `--gc-incremental` is never parsed (cli.cpp).
- **U57 (new, low).** An unused flag silences "Extra positional args" (cli.cpp 533–557).
- **U58 (new, medium-low).** `jank compile` fails with "Compiled module … not found" for `:as-alias`/`create-ns` namespaces (aot/processor.cpp 429–476).
- **U59 (new).** `(compile 'clojure.set)`: returns the lib vs throws "Unable to write module" (and core.cpp 1361 returns nil). Test u59.
- **U60 (new, low).** `run-main` of a self-requiring module evaluates it twice (main.cpp 95; `*pending-paths*`).

### clojure.core and bundled namespaces (area G and mine)
- **U61 (new).** `(clojure.data/diff {:a 1 :b 2} {:a 1 :b 3})`: `({:b 2} {:b 3} {:a 1})` vs `[{:a 1 :b 2} {:a 1 :b 3} nil]` (data.jank 66: equality-partition is always `:atom`). Theorem ★ `jankDiff_is_atomDiff`. Test u61. High.
- **U62 (new).** `(ex-message "boom")`: nil vs a native error (core.cpp 1338–1352). Test u62.
- **U63 (new).** `(:cause (Throwable->map (ex-info "a" {} (ex-info "b" {}))))`: "b" vs "a" (exception_info.cpp 116–148). Theorem ★ `jank_cause_not_root`. Test u63.
- **U64 (new).** A printed 3-link chain lacks "c" and repeats "b" (exception_info.cpp 80–83). Theorem ★ `jank_printed_via_wrong`. Test u64.
- **U65 (new).** `(format "%d" 5)`: "5" vs "%d"; `(format "{}" 5)`: "{}" vs "5" (core.cpp 237–378; jank's docstring says std::format, but the book's differences page doesn't list it). Theorem ★ `scan_no_braces`. Test u65.
- **U66 (new).** `(bounded-count 1 "abc")`: 1 vs 3; `counted?` true on strings, arrays and map seqs (seq.cpp 131–141). Theorem ★ `bounded_count_agree`. Test u66.
- **U67 (new).** `(map-entry? [1 2])`: false vs true. Theorems ★ `jank_map_entry_any_pair`, ★ `map_entry_agree`. Test u67.
- **U68 (extends R120).** `(shuffle (repeat 3 :x))`: works vs throws (seq.cpp 1178–1201). Test u68.
- **U69 (new; a 1.12 behavior).** `(meta (postwalk identity (with-meta '(1 2) {:m 1})))`: `{:m 1}` vs nil (walk.jank 3–12). Theorems ★ `jank_walk_drops_list_meta`, ★ `walk_vec_meta_agree`. Test u69 (passes on 1.12.0, not 1.11.1).
- **U70 (new).** `(pr-str (tagged-literal 'foo "bar"))`: `#foo "bar"` vs `#foo bar`. Test u70.
- **U71 (new, low).** `(parse-uuid "000…0")` (32 hex digits) and the braced form: nil vs a uuid (stduuid uuid.h 503–547). Test u71.
- **U72 (new).** `areduce` over `(long-array [1 2 3])`: 6 vs throws ("TODO: port unchecked-inc-int"). Test u72.
- **U73 (new).** `(newline)`, `(flush)`: work vs throw "TODO: port". Test u73.
- **U74 (new names; R113/R124 class).** Unported: `unchecked-*` (except `unchecked-inc`), `into-array`, `reversible?`, `indexed?`, `special-symbol?`, `instance?`, `class`, `with-open`, `line-seq`, the struct and stream functions, `reader-conditional`, and others. Tests u74, u74b.
- **U75 (new, low).** `(bit-not 5N)`: throws vs -6 (math.cpp to_i64 22–25). Test u75.
- **U76 (new).** `(spit f 42) (slurp f)`: "42" vs throws (core.jank 7350). Test u76.
- **U77 (new).** `(slurp f :encoding "UTF-8")`: the text vs an arity error. Test u77.
- **U78 (new).** `(spit "/no-dir/x" "a")`: throws vs nil. Test u78.
- **U79 (new; medium-high).** `(try (slurp "/no-dir/x") (catch object_ref _ :caught))`: `:caught` vs an uncaught native error (`file_size` at 7331 runs before `is_open`). Test u79.
- **U80 (new, low).** `(reduce-kv f [] (seq {:a 1}))`: works vs throws (seq.cpp 923–972). Test u80.
- **U81 (extends S59).** `(first (keys (zipmap [[1] '(1)] [:a :b])))`: `[1]` vs `(1)` (core.jank 2411–2423 uses a hash-map transient). Test u81. Medium-high.
- **U82 (new).** `(read-string "#inst \"2020\"")`: an inst vs a read error (parse.cpp 948–975, inst.cpp). Test u82.
- **U83 (new).** `(json/read-str "18446744073709551615")`: the BigInt vs -1 (json_native.cpp 142). Theorem ★ `jank_reads_u64_wrapped`. Test u83.
- **U84 (extends S9).** `(compare 0.1M (json/read-str "0.1" :bigdec true))`: 0 vs nonzero (json_native.cpp 147). Test u84.
- **U85 (new).** `(json/write-str 123N)`: `"123"` vs `"\"123\""` (json_native.cpp 69–72). Test u85.
- **U86 (new, low).** `(json/write-str ##NaN)`: throws vs `"null"`. Test u86.
- **U87 (new).** `(json/read-str "" :eof-error? false :eof-value :none)`: `:none` vs a native parse error (json_native.cpp 198–202). Test u87.
- **U88 (new).** `(:out (sh "echo" "a\" b"))`: `"a\" b\n"` vs `"a\\ b\"\n"`.
  - Path: shell.jank `shell-escape` 78–79 and the joined command line (98–103) go through boost-process v1 `build_args` (detail/posix/basic_cmd.hpp 55–100). Every `"` toggles the quote state, including an escaped `\"`, so a space after an odd number of quotes splits the argument. A lone `"` piece makes `make_entry` build an invalid range.
  - Census: 116,622 argument lists, 68,497 differ, all in that class; 14,295 have a lone-quote piece.
  - Theorems: ★ `jankArgv_noquote` (for every argument list without `"`, the child gets exactly the arguments), `quote_then_space_splits`, `balanced_quotes_kept`.
  - Test u88. High.
- **U89 (new).** `(count (:out (sh "seq" "1" "100000")))`: 588,895 vs hangs.
  - Path: shell.jank 52–73 writes `:in`, closes stdin, calls `process.wait()`, then reads stdout. A child writing more than the pipe holds (Linux: 65,536) blocks forever. Clojure reads in futures before `waitFor` (java/shell.clj 118–130).
  - Theorems ★ `seq_past_capacity_never_returns`, ★ `seq_past_capacity_stuck` (every capacity, every n > cap).
  - Test u89 (hangs file). High.
- **U90 (new, low; Clojure's behavior is its source, not its docs).** `(:out (sh "printenv" "N" :env {"N" 1}))`: `"1\n"` vs throws (`cpp/cast std.string` of a non-string, convert/builtin.hpp 333–336). Test u90.
- **U91 (new).** `(with-out-str (pprint (vec (range 30))))`: 30 lines vs 1 (pprint.jank is `prn`; dispatch.clj 92–101, right margin 72). Census: n = 0..60, 33 differ from n = 28. Test u91.
- **U92 (new names).** `clojure.pprint/print-table`, `cl-format`, `pp`, … and `clojure.stacktrace/root-cause`, `print-stack-trace`, … are missing. Theorems `pprint_missing`, `stacktrace_missing`. Test u92.

## Corrections to rounds 1–3
- **Withdrawn as predictions:** S69, and S70's freed read (possible, not certain; RTA8 replaced). RT8 weakened.
- **S57** refuted at the top level; holds for compiled code (U7).
- **S50, S53:** their round-3 confirmations were not evidence (re-tests U5, U6).
- **S2, S9, S44 stand.** The round-3 tests could not observe them.
- **Round 3's replicas, corrected in round-4 copies:**
  - regex: `re-pattern` must cut at NUL (U38); the Java model kept captures through continuations (replaced by Java's mutable groups); `#"(?)"` slip (no effect).
  - interop: derived-object member candidate scored exact instead of derived-to-base (no result change).
  - nREPL: primitive casts in loops were missing; the spec did not intern vars before a failed analysis (EA4-6).
  - immer: IMA7 is contradicted by jank's own `create_from_seq` (U34).
- **Contradicted:** round 3's "no callbacks under the JIT and multimethod recursive mutexes" (U19; cpp/raw initializers run under the JIT lock).
- **Round 3's 143 undecided two-thread programs:** decided at ≤ 400,000 states. 131 have no jank-only deadlock; 12 are known classes (D16, S65/S66). The 37,488-program census is complete. The stopped fine-replica validator scenario deadlocks after 117 steps (683,406 states).
- **Every round's `ev`** evaluated in clojure.core (U45).

## What was replicated
- **Runtime** (`Jank/R4/Runtime/`):
  - Census2: round 3's census decided.
  - Gc4: bdwgc's conservative stack scan, pthread_stop_world.c 836–947.
  - Deferred: evaluate.cpp eval(def)/eval(function), deferred_cpp_function realize/call, var bind/alter_root, with-redefs-fn, meta of deferred fns.
  - Bindings4: context.cpp 678–775 and futures' conveyance.
  - Mutexes: multi_function's mutex and cache, MultiFn's RW lock, the JIT lock, compilation_mutex, realization locks.
  - Proofs4: swap-vals!/reset-vals!.
- **Interop** (`Jank/R4/Interop/`):
  - TopLevel: context::eval, analyze_do, analyze_cpp_raw, evaluate.cpp's top-level forms, compiled `if`, `into_object`.
  - Operators: GetOperator 6977–7064, the jank operator path, BestOverloadMatch with object conversions, and the C++ side ([over.match.oper], ADL, [over.built], hiding).
  - Templates: build_cpp_value's class-template path and C++17 CTAD.
  - Deferred, Worlds.
  - Read and tabled: analyze/cppinterop.cpp, typed params, cpp/box/unbox/new/delete, opaque_box, native wrappers, the nREPL's native exceptions.
- **Immer and collections** (`Jank/R4/Immer/`):
  - TransientGet/TransientTake/TransientTakeWf: rbts `push_back_mut`, `push_tail_mut_visitor`, `take_mut`, `slice_right_mut_visitor` (with and without collapse), as `conj!`/`pop!` reach them.
  - SeqObjects: list, vector, repeat, iterate, cons and sorted-map objects with identity, Clojure's classes.
  - ArrayMapCtor: create_from_seq, createAsIfByAssoc.
  - Read and found to agree: chunk/array_chunk/chunked_cons/sequence objects, subvec, transient sorted.
- **Regex** (`Jank/R4/Regex/`, GPL-3.0+ with the GCC runtime exception):
  - JavaM: java.util.regex with one mutable groups array, lookbehind with Java's length study, every inline and scoped flag, named groups.
  - Compare4: the NUL cut.
  - Matcher: re-matcher/re-groups/nth and pattern printing.
  - JVM checker: 911,713 answers rerun on OpenJDK 23, all identical.
- **nREPL** (`Jank/R4/Nrepl/`):
  - JEval/CEval etc.: round 3's World S stack with jank try/catch/finally, binding, dotimes and push/pop on both sides.
  - Pos: lexer positions vs LineNumberingPushbackReader.
  - Term: `jank repl` vs clojure.main/repl.
  - Seg: Knuth estimator and resumable segments.
- **Modules, AOT, CLI** (`Jank/R4/Modules/`):
  - Munge: munge/demunge, path↔module.
  - Loader: loader_dynamic.cpp registration and find.
  - Load/LoadWorld: core.jank alias, refer, load, load-one, load-all, load-lib, load-libs, require, use, ns; context load_module; ns.cpp refer/intern; Clojure's core.clj and Namespace.
  - Aot: gen_entrypoint, build_executable, module load fn, var lifting, jank_init_static/dynamic.
  - Cli: cli.cpp parse_opts in full.
- **Core** (`Jank/R4/Core/`):
  - Value; Diff (clojure.data both sides); Exceptions (exception_info).
  - Format: core.cpp format vs java.util.Formatter.
  - Uuid: stduuid and JDK UUID.fromString.
  - Preds; Walk; Json (nlohmann lexer and get<i64>, data.json); Seqfns (cycle, nthrest, UTF-8 string fns).
  - 65 definitions read as textually identical to Clojure's and 12 more equal up to class-only branches; these inherit only earlier rounds' primitives.
- **Coordinator** (`Jank/R4/Feedback/`):
  - Numbers: S2/S9/S44 run as written.
  - Control: the codegen depth-2 world's size.
  - Shell: jank.shell's argv through boost build_args, and pipes with capacity as a step relation.
  - Pprint: pprint vector layout, namespace inventories.

## What no round has replicated yet (source tree survey)

`.r4-scratch/survey/coverage.txt` lists every file of compiler+runtime (478) with how many round sources and reports cite it. Being cited doesn't mean being replicated; this list is by reading.

- **Replicated by rounds 1–3:** lexer/parser, analyzer, IR/codegen, numbers and boost, immer collections, strings/printing/regex, interop, runtime locks/GC, nREPL.
- **Replicated by round 4:** deferred_cpp_function, thread bindings, multimethod and JIT mutexes, GC stack scanning, operator lookup, class templates, collection objects, re_matcher, positions, the terminal REPL, the module loader, AOT, the CLI, 228 core names, set/walk/data/template/test/data.json/pprint/stacktrace/shell, exception_info/uuid/inst/tagged_literal.
- **Not replicated:**
  - error reporting (error.cpp, error/*.cpp, report_dynamic.cpp: message text, no Clojure counterpart);
  - jit/object_dynamic.cpp and parse_ld_script.cpp (native object loading);
  - environment/check_health.cpp, util/clang*.cpp, util/environment*.cpp (toolchain discovery);
  - ui/highlight.cpp;
  - jank.perf;
  - jank.math (noticed: it cannot load, since `native/raw` is no longer a special form; undocumented, not reported);
  - the C API beyond AOT entry points; cpptrace; lein-jank and clojure-cli.

## What is still left out, and why
- **Runtime:** JIT code frame layouts and register allocation, so no freed read is predicted; Clojure's non-fair RW lock queueing; unported agents, refs/STM, `with-local-vars`, `pmap`, `seque`, `future?`/`future-done?`; macOS futures.
- **Interop:** C++20 rewritten comparisons (documented as unsupported); operator templates and `[]`/`()`/assignment operators; explicit deduction guides and partial specializations; global namespace declarations (InteropA4-1).
- **Immer:**
  - CHAMP laws beyond get-after-add (need an equivalence agreeing with the hash; jank's isn't, D12/R55).
  - M4 (4 steps, ≈5.06·10⁹) and S3 (≈1.19·10⁸) are out of reach.
  - M4-3 stopped at 13,750,000; its Knuth estimate of 1.63·10⁷ is below what remains (the walk is still in the first decision's third branch).
- **Regex:** CANON_EQ, `\X`, `\N{}`, Unicode properties under `(?U)`. The proof that a position without a solution leaves `_M_results` unchanged did not check (kept aside in `.r4-scratch/regex/ExecInv.lean.unfinished`).
- **nREPL:** T7 (≈3.2·10¹¹) out of reach; T3 stopped at 1,206,000; T9 not rerun (round 3's numbers stand); isocline's interactive multi-line mode; interrupt.
- **Modules:** JAR contents and mtimes as data; the `.cpp` module type; the clang/linker invocations.
- **Core:** `#inst` time-zone forms (libstdc++ chrono parser not fetched); data.json escaping and `:value-fn`; random functions (properties only).
- **Codegen:** round 2's depth-2 control is ≈3.3·10¹¹ timelines (Knuth, 2,000 samples, 20 partitions), so it can't be completed; round 3's 186,717 stand.
- **jank.shell:** SIGPIPE when the child ignores a large `:in`. The outcome depends on the inherited signal disposition, so it isn't decided.

## Assumptions

**Replaced:**

| Assumption | Replaced by |
|---|---|
| RTA8 | conservative stack (Gc4) |
| "no callbacks under JIT/multimethod mutexes" | contradicted (U19) |
| CXA10 | GetOperator replica |
| round 3 "derived object = exact" | ICK_Derived_To_Base |
| "every `if` compiled" | top-level interpretation (S57) |
| "a cpp/raw declaration exists when its use is analyzed" | contradicted inside one form |
| IMA7 | contradicted for jank's own create_from_seq |
| RXJ2, RXJ3, RXJ4 | JVM measurement; mutable groups |
| round 3's "lookbehind/inline flags parsed, not matched" | matched |

**Still standing or new:**
- **Runtime:** RTA4-1 lazy eagerness in the runner; RTA4-2 -O0 default JIT; RTA4-3 stale-word survival unknown; RTA4-4 RW lock fairness; RTA4-5 realize's JIT steps run no user code. Round 3's RTA1–RTA7 and RTA9–RTA11 stand.
- **Interop:** InteropA4-1 to A4-7, including the runner loading sources lazily and `into_object(int)` truncation. CXA1–CXA13 stand.
- **Immer:** IMMA4-1 `(range)` is `(iterate inc 0)`; IMMA4-2 double index truncation; IMMA4-3 the error text is built eagerly; IMMA4-4 quoted lists carry no runtime meta. IMA1–IMA6 stand.
- **Regex:** RXJ5 JDK 23 behavior where the javadoc is silent; RXJ6 simple case mapping. RXA1–RXA5 and RXJ1 stand.
- **nREPL:** NA9 object catch = Clojure catch of what was thrown; EA4-1 to EA4-6. NA1–NA8 stand.
- **Modules:** MODA4-1 to MODA4-8.
- **Core:** coreA4-1 `file_size(path)` overload; coreA4-2 to A4-5.
- **Coordinator:**
  - FBA4-1: `jank.shell` loads (its source and boost-process headers are installed, install.cmake 48–51, 107–108).
  - FBA4-2: Linux pipe capacity 65,536 (the theorems hold for every capacity).
  - FBA4-3: SIGPIPE disposition undecided.
  - FBA4-4: the arm64 Apple-clang boost cross-check stands for x86-64 (decimal limb arithmetic is portable).
- **Earlier rounds:** round 2's RA/RB/RC assumptions and round 1's stand.

## Properties
- **GC:** an object Clojure keeps alive is never read freed (and its opposite, to tell certain from possible).
- **Lazily compiled fns:** every observation equals Clojure's.
- **Thread bindings:** push/pop/get results.
- **Mutexes:** no deadlock Clojure lacks.
- **Operators:** `cpp/<op>` calls what `[over.match.oper]` selects, is ill-formed when C++ is, and gives C++'s value.
- **Class templates:** a constructor gets CTAD's specialization.
- **`if`:** keeps the chosen branch's value in both contexts.
- **Transients:** `nth` after any `conj!`/`pop!` chain.
- **Seq objects:** values and every live value's metadata.
- **array-map:** keeps the entries.
- **Regex:** every capture, every call, re-matcher `nth`/`re-groups`, pattern printing.
- **nREPL:** World S properties with try/binding/loops; positions; terminal REPL sequences.
- **Loader and loading:** files, order, outputs, namespaces, aliases, `*loaded-libs*`, `*ns*`; run-main, AOT, CLI parse.
- **Core functions:** diff, exceptions, format, parse-uuid, predicates, walk, data.json.
- **jank.shell:** the child's argv equals the arguments; `sh` returns the child's whole output.
- **pprint:** layout within the right margin.

## Search runs ("complete n" = every timeline within the bounds)

**Coordinator:**
- Reader numbers table, length 7: the 11 partitions round 3 skipped, 11 × 34,012,224 complete. The 18-partition table (612,220,032) is now complete; only R3, R4, R6, R7 and counted accepts-invalid.
- jank.shell argv: complete 116,622 (68,497, all class Q).
- jank.shell pipes: 160 cases (caps 1–4), 114 differ (78 hangs, 36 SIGPIPE undecided).
- pprint: n = 0..60 complete (33).
- Codegen depth-2 control: size estimate only (≈3.3·10¹¹).

**Runtime:**
- Census2: all 143 decided.
- Fine validator: deadlock at 683,406 states.
- GC: the test shape at -O0 is complete 64/128/256 with nothing (as jank did); a separate thrower makes both outcomes reachable; Clojure complete up to 1,312,768.
- Deferred: 137,560 and 2,613,659 complete (residual nothing; eager: U14 only).
- Bindings: 58,821 complete.
- Mutex census: 64,330 complete (residual nothing).

**Interop:**
- XVI′ 324 (36).
- XII 75 (69).
- XVIII 588 (61).
- XIX 105 (34).
- XX: lengths 1–4 complete with nothing; census 4/7,776 and 84/46,656.

**Immer:**
- M5 complete 7,572,128 (with round 3's 4,750,000), nothing.
- M4-2 complete 61,642.
- M4-3 stopped at 13,750,000, nothing.
- S3-3 complete 838,319.
- A1 337,041 and A2 2,396,744 (U34 only).
- Q1/Q2/Q3: 180 / 4,072 / 119,019.
- Residuals: Q3r 132,600, Q3m 76,320, Q4r 5,290,440, nothing.

**Regex:**
- look ≤3: 1,717,065.
- look ≤4: 39,495,600.
- flags ≤2: 71,808.
- NUL: 70,600.
- matcher: 6,120.
- core4 keeping captures: 5,600.
- Round 3 vs round 4 Java models: 12,794,600.
- JVM: 911,713 identical.
- All complete, 0 unexplained.

**nREPL:**
- pos ≤5: 149,792; pos ≤6: 1,198,368.
- term k=3: 1,000; k=4: 10,000.
- gTry: 35,531; gBinding: 11,991; gLoop: 5,184; gExMsg: 70,808.
- gTryRes: 571,536; gTryRes3: 19,683 ×2.
- T3 stopped at 1,206,000.

**Modules:**
- loader: 598,899.
- load1: 114,224; load2: 6,853,440.
- runmain: 7,744.
- aot: 384.
- cli4: 406,901; cli5: 10,172,526.
- All complete, 0 unexplained.

**Core:**
- diff: 441.
- format: 46,655.
- parse-uuid: 1,596,458.
- exceptions: 17.
- predicates: 154.
- map-entry: 10.
- walk: 9.
- strings: 24,336.
- cycle: 52.
- json ints: 50; `:bigdec`: 804.
- All complete.

## Theorems (no sorry, no native_decide, no new axiom; ★ = new for-every-input proof)
- **Immer:** ★ `get_bangs` (nth after any chain of `conj!`/`pop!` equals Clojure's list, for every well-formed vector, token and chain below 2³⁵), ★ `takeMut_wfT`, ★ `sliceMut_nc_wf`/`sliceMut_c_wf`, ★ `get_pushBackMut`, ★ `pushBackMut_wfT`, ★ `get_conjs`, ★ `get_takeMut`, ★ `get_popBang`, `get_conjBang`; `jank_array_map_at_most_8`, `nine_keys`, `update_dropped`; `c1_repeat_meta_written`, `c2_iterate_with_meta`, `c3_nth_double`.
- **Runtime:** ★ `swapVals_linearizable`, ★ `realize_rebinds`, ★ `realize_inside_alter_hangs`, ★ `clojure_call_keeps_roots`, ★ `getTB_bound_differs`, ★ `pushArray_rejected`, ★ `future_pop`, ★ `future_conveys`, ★ `unbound_str_differs`.
- **Interop:** ★ `jank_primitive_operands_builtin_only`, ★ `jank_primitive_operand_unary_builtin_only`, ★ `jank_ctor_specialization_is_defaults`, ★ `deferred_call_returns_body`, ★ `eager_agrees_clojure`; `old_object_rebinds_var`, `clojure_keeps_new_root`, `getOperator_includes_hidden_base_member`, `cpp_member_lookup_hides_base`, `getOperator_follows_using_directive`, `delete_cxx_new_crashes`.
- **Regex:** ★ `jankEval4_pattern_nul`, ★ `nth_no_groups_never_the_match`, ★ `nth_without_match_nil`, ★ `print_pattern_differs`; `searchFromFirst_starts_clean`.
- **nREPL:** ★ `try_agree_unless_terminate` (D24 is the only place try differs), ★ `binding_frames_restored`, ★ `jankPos_eq_cljPos`; `completions_ns_is_searched`, `jank_has_no_line_meta`.
- **Modules:** ★ `upsert_jank_last_wins`, ★ `get_upsert_self`, ★ `firstHaving_first`, ★ `checkFlag_prefix`, ★ `aot_static_status_zero`.
- **Core:** ★ `jankDiff_is_atomDiff`, ★ `jank_printed_via_wrong`, ★ `jank_cause_not_root`, ★ `scan_no_braces`, ★ `jank_map_entry_any_pair`, ★ `map_entry_agree`, ★ `bounded_count_agree`, ★ `jank_walk_drops_list_meta`, ★ `walk_vec_meta_agree`, ★ `jank_reads_u64_wrapped`, ★ `cycle_agrees`, ★ `nthrest_agrees`; `jank_format_percent_d`.
- **Coordinator:** ★ `jankArgv_noquote`, ★ `seq_past_capacity_never_returns`, ★ `seq_past_capacity_stuck`; `quote_then_space_splits`, `balanced_quotes_kept`, `s44_round3_test_meta_kept`, `s44_round4_cases`, `pprint_missing`, `stacktrace_missing`.

## Library gaps (built in the project; sdk/lean untouched)
- A conservative-stack GC model, and opposite-property pairs because `exhaust` stops at the first counterexample.
- A reentrant RW lock.
- Object identity (heaps) for sequence objects; "never returns" as an outcome.
- A top-level evaluation model, and an operator-lookup world (namespaces, using-directives, hidden friends).
- Fuel-bounded, kernel-decidable walks.
- A spec model checked against a JVM (EDN dumps and a checker script).
- Classification by spec-side toggles; a mutable-state backtracking matcher over StateT.
- Knuth's tree-size estimator and resumable census segments.
- A module-path/file-system model, and a namespace state with exception-safe `binding`.
- A process/pipe step relation with capacity.
- Equation lemmas by `rfl` where Lean 4.36 can't generate them.

## Tests
- **`tests/jank_lean/deviations_r4_test.jank`** (`jank-lean.deviations-r4-test`, 81 deftests u01–u92) and **`deviations_r4_hangs_test.jank`** (u13, u13b, u19, u28, u28b, u89).
- **Clojure check:** translated (`.r4-scratch/clj-final/`, jank.shell → clojure.java.shell, data.json 2.5.2 on the classpath). 72 tests, 127 assertions, all passing on Clojure 1.12.0. On 1.11.1, all except u69 (a 1.12 change).
- **Jank only, and why:**
  - u04–u07b and u20–u26 use `cpp/raw` and `cpp/` forms;
  - u40c, u41, u44 call jank's nREPL handler namespace in-process;
  - u26 predicts a segfault.
- **No test-file form:** U42, U43 (`jank repl` stdin), U46, U47, U52–U54, U56–U58, U60 (CLI, AOT builds, files, exit status). Shell steps are in the area reports.
- **Rules followed:** each test asserts Clojure's result (C++'s for interop); values pass through fns; `cpp/raw` runs in its own eval; BigDecimals are observed by `compare` and `str`.

## Files
- **Models:** `Jank/R4/<Area>/`. **Drivers:** `Run/R4/<Area>.lean` (exes `jank4-feedback`, `-runtime`, `-interop`, `-immer`, `-regex`, `-nrepl`, `-modules`, `-core`).
- **Results:** `results/r4-<area>-report.txt` (each area's full report) and `results/r4-*.txt` (runs; coordinator: `r4-feedback*.txt`, `r4-search-reader-numbers7.txt`).
- **Pinned sources:** `deps/boost-process`, `deps/json`, `deps/stduuid` (in `fetch-sources.sh`).
- **Changed outside round 4's own files:**
  - `lakefile.toml` (8 exes);
  - 16 round-3 files (`.nodeDown` arms; originals in `.r4-scratch/nodedown-orig/`);
  - `Run/R3/Codegen.lean` (qualified `mixSeed`);
  - `README.md`, `NOTICE.md`, `fetch-sources.sh`, `.gitignore` (`.r4-scratch/`).
- **Scratch:** `.r4-scratch/`.
- **Rule notes:**
  - The regex area reran one ~20 s JVM check outside the job queue.
  - Area G read `clojure.data.json` 2.5.2 from its jar in `~/.m2` as the specification.
  - Machine-wide slot contention held some builds for up to an hour.
- No commits were made.

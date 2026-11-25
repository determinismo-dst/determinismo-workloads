# REPORT-5: jank 94d32623 compared with Clojure 1.12, round 5

**Version.** jank main `94d32623e3e6f0f40c412d41802fe02693aec094` (2026-11-25, `upstream-r5/`, with its git history). Its `compiler+runtime/` tree is byte-identical to round 4's 7135b7708. Every jank path below is under `upstream-r5/compiler+runtime/`, and every line number is the same at both commits.

**Libraries.** Rounds 3–4's pinned libraries, plus files fetched this round (added to `fetch-sources.sh`):
- libstdc++ 15.3.0's `<chrono>` parser (`chrono_io.h`, `chrono.h`, `include/std/chrono` as `chrono.std`, `istream.tcc`) into `deps/libstdcxx-15.3.0/`;
- GNU ld 2.45's script grammar and manual (`ldgram.y`, `ldlex.l`, `ld.texi`, `ldfile.c`, `ldlang.c`) into `deps/binutils-ld/`;
- six LLVM 23.1.0 files (`Error.h`, `ErrorHandling.h`, `OrcIncrementalExecutor.cpp`, …) into `deps/llvm-23.1.0-native/`;
- as specifications only (scratch, not pinned): nREPL 1.8.0 from Clojars and OpenJDK 23's `java.util.regex` sources.

**Status.** Every item is a hypothesis from Lean replicas, re-read against the source. jank was not built or run.

**Who did what.**
- Seven area agents worked in parallel:
  - native objects and the C API (A);
  - errors (B);
  - codegen proofs (C);
  - nREPL (D);
  - regex (E);
  - C++ operators (F);
  - `#inst` and CHAMP (G).
- I did the catch-up, `jank.math`, the test merge, the Clojure check and this report.
- I re-read the source behind V7, V17, V19, V20, V25 and V38; each holds as stated.
- Area reports are `results/r5-<area>-report.txt`; run outputs are `results/r5-<area>-*.txt`.

**Build.**
- `lake build` of all 36 targets (rounds 1–5) succeeds: 905 jobs.
- Round 5 adds 41 files and 10,098 lines under `Jank/R5/` and `Run/R5/`, with 8 exes `jank5-<area>` (native, errors, codegen, nrepl, regex, interop, core, coord).
- No `sorry`, no `native_decide`, no new axiom. `#print axioms` of every main theorem shows only `propext`, `Classical.choice` and `Quot.sound` (`results/r5-*-axioms.txt`).

## 1. Catching up to 94d32623

**Verdict: nothing a round replicated changed.** Every earlier prediction holds on 94d32623 exactly as it held on 7135b7708, at the same lines. Details are in `results/r5-catchup.txt`.

**7135b770 → 94d32623.**
- One commit, 94d32623 "Automatically set DEVELOPER_DIR (#1244)". It touches only `lein-jank/src/jank_build/util.clj` (+26 −2: the Leiningen plugin sets `DEVELOPER_DIR` for its children on macOS). No round replicates lein-jank.
- `diff -rq upstream-main/compiler+runtime upstream-r5/compiler+runtime` is empty, and every third-party submodule pin is the same.

**f3d82d654 → 94d32623 (what rounds 1–3 replicated).**
- There are 33 commits, and every compiler+runtime change falls in f3d82d654..7135b770, which round 2 compared as trees.
- git's list of changed non-test files (50) is inside round 2's list. The one addition is the CppInterOp pin f7e840b4 → 28b0830d, which round 3 replicated at 28b0830d.
- The commits behind each change round 2 recorded:
  - D11 gone: 18b30dcf "Fix sequence equality with nil (#1222)" (seq.cpp `sequence_equal` 881–893, seq_ext.hpp `equal` 13–23).
  - D14 gone: f4ba1985 "Clone array maps when making them transient (#1232)" (transient_array_map.cpp 24–27).
  - D15 gone: 607de3f9 "Check transient vector state on nth (#1237)" (transient_vector.cpp 53–56).
  - D20 gone: 9149241e "Return nil when a promise is already delivered (#1231)" (promise.cpp 24–37).
  - F1 gone: 7a1936cf "Fix `sort` of empty values (#1182)".
  - F2–F8 gone, R126, R131, R132, R135 and R137 changed, R138–R140 introduced: 44eea86f "Various nREPL compatibility/robustness fixes per "proof" (#1175)".
  - R24 and R86 changed (truncation instead of a throw): 7fb70c1c "Allow implicit numeric trait conversions (#1206)" (convert/builtin.hpp 236–238, 286–288).
  - R120 changed: 2a4777bd "Fix `coll?` for lazy/persistent_string sequence (#1192)".
  - R26 introduced: 1b468573 "Improve `case` special form branch analysis for C++ interop (#1116)".
  - The other files round 1 cites have no commit in the range, or (lazy_sequence.cpp, cpp_processor.cpp) none in the cited lines. So D1–D10, D12, D13, D16–D19 and D21–D25 hold.

**The 59 citations flagged in `drift-94d32623.txt`.**
- Each was read at 94d32623 against the Lean comment that cites it. All 59 already use 7135b7708's numbering, which is 94d32623's, and the code at each cited line is what the replica describes.
- Two reasons explain the flags:
  - The list takes rounds 1–3's citations as f3d82d654's. Round 2 re-cited its models at 7135b7708, and round 3 cites 7135b7708 throughout.
  - Bare file names were resolved to the wrong file. `processor.hpp:75-101` is ir/processor.hpp's `struct module`, not jit/processor.hpp. The `processor.cpp` ranges in `Jank/Codegen/Ir.lean` and `Processor.lean` are ir/processor.cpp (`find_block` 48, `arity_flags` 339, `gen(function)` 371, `gen(let)` 510, `gen(if)` 647, `gen(try)` 727).
- No replicated behavior changed.

**Corrections to earlier rounds made this round (jank's code did not change):**
- **U47.**
  - REPORT-4's text said `jank_init_dynamic` returns the status when `-main` throws, and round 4's AOT replica (`aotRun p false`) gave 1.
  - In fact the AOT main calls `-main` through `jank_call2`, which catches everything (V20). A throwing `-main` exits 0 under both runtimes.
  - U47's own claim (the static runtime exits 0) stands, now with a second cause.
- **Round 4's load replica** (`Jank/R4/Modules/Load.lean`) caught every failure in jank's `load-lib`. jank catches only objects, so a failed require leaves its namespace (V8). Round 4's load censuses never drew a failing module.
- **Round 2's reader replica** (`Jank/Read.lean` `readString`) answered an EOF error for an empty text. core.jank's `read-string` returns nil (V17).
- **Round 1's D19** modeled a delay's error cache as one flag. jank keeps a native error as a string and keeps no `error_ref` at all (V10, V11).
- **Round 4's Java regex model** lacked `\b`'s non-spacing-mark rule and (?U)'s marks, letter numbers and join controls. Round 4's searches drew no such code point, so none of its counts change.
- **Rounds 3–4's World T counts** include a factor of 2 per blocking read, from an unused `net.read.eintr` draw (Threads.lean 251). Their verdicts are unchanged.
- **Round 4's codegen size estimate** (≈3.3·10¹¹) is replaced by the exact 354,197,993,668 (★ `world2`).
- **Round 4's evidence for U88–U90** (`jank.shell`) is "uncaught jank error" for each.
  - Round 4's predicted analysis and load errors carry the same label (u05, u06, u21, u22, u48), and V7 says what such an error is. So `jank.shell` most likely failed to load or analyze before `sh` ran.
  - The code does not say which step failed, and U89's hang was never reached.

## 2. Deviations at a glance

Clojure's result comes first, then jank's. "V n" is this round's; U, S, R and D refer to earlier rounds.

**Native object loading (jit/processor_dynamic.cpp, parse_ld_script.cpp, the module loader):**
- **V1** A GNU ld script naming several files: ld links all of them, jank's JIT maps only the first.
- **V2** (low) The ld-script reader drops backslashes and single quotes in names. After an unterminated comment it drops the rest of the file, where ld fails.
- **V3** A library file jank cannot dlopen goes to `llvm::cantFail`, instead of an error: undefined behavior in a release build, an abort in a debug one. v03.
- **V4** `-lfoo`: the JIT takes `libfoo.so` from any directory before `libfoo.a` from any. The AOT link searches directory by directory, so the two can link different files.
- **V5** `-l` with a path or file name works under the JIT, as `--help` says, and fails the AOT link.
- **V6** A module loaded from its compiled `.o` never runs its C++ global initializers: 7 from source, 0 from the object.

**Errors, as a program sees them (error.cpp, jtl/result.hpp, context.cpp, core.cpp, delay.cpp):**
- **V7** Read, analysis and load errors are `jank::error_ref`. No `(catch cpp/jank.runtime.object_ref e …)` sees them, and so no `thrown?` does. v07, v07b, v07c.
- **V8** A require whose module fails leaves the namespace it created; Clojure's load-lib removes it. v08.
- **V9** An ex-info thrown while a module loads, or by a macro, loses its data: Clojure keeps `{:vb3 1}` reachable, jank raises no object at all. v09, v09b.
- **V10** A failed delay throws a native error at the first deref and a string at the second; Clojure rethrows the same exception. v10.
- **V11** A delay whose body raises an `error_ref` runs its body at every deref: 1 run vs 2. v11.
- **V12** `@(future (read-string "("))`: an ExecutionException vs `std::terminate`. v12.
- **V13** A failed future's deref throws a native error as a string. v13.
- **V14** (low) A top-level `def` whose value throws leaves the def's metadata on the var. v14.
- **V15** `(ex-message (ex-info nil {}))`: nil vs a native error. v15.
- **V16** (low) `(ex-data (ex-info "m" nil))`: `{}` (1.12) vs nil. v16.
- **V17** `(read-string "")`, a comment, and `(read-string {} " ")`: "EOF while reading" vs nil. v17, v17b, v17c.
- **V18** (extends U44) After a compile error at the nREPL, `(ex-data *e)` and `(ex-cause *e)` are nil. v18.

**The C API (c_api.cpp, c_api.h, aot/processor.cpp):**
- **V19** `jank_call2` catches and prints what the fn throws, and returns nil. `jank_call1` and `jank_call3`–`11` let it through, as IFn.invoke does. v19, control v19b.
- **V20** (corrects U47's text) An AOT program whose `-main` throws exits 0 under the dynamic runtime too; Clojure exits 1.
- **V21** (low) `jank_symbol_create(nil, "a")` is `nil/a` and `jank_keyword_intern(nil, "a")` is `:nil/a`; Clojure gives `a` and `:a`. v21, v21b.
- **V22** `c_api.h` is not C: it uses `bool` without `<stdbool.h>`, so a C17 file including it fails to compile.
- **V23** (low) `jank_eval_file_c` prints a debug line on stdout.

**jank.math:**
- **V24** The bundled `jank.math` cannot load. Its bodies are `(native/raw …)`, removed as a special form in 529718a6, so the first defn fails with "The symbol `native/raw` could not be resolved." v24.

**C++ operators (analyze/processor.cpp, CppInterOp, cpp_processor.cpp):**
- **V25** Assigning a temporary of a move-only class: C++ moves (5), jank picks the deleted copy assignment. v25.
- **V26** A forwarding operator template sees a temporary as an lvalue: jank deduces `T = W&` (1) where C++ deduces `T = W` (2). v26.
- **V27** A member operator taking `int&&`, given a literal: C++ 1, jank a JIT compile error. v27.
- **V28** A member operator template with `T&&`, given a literal: C++ 2, jank 1. v28.
- **V29** A `let`-bound int is an rvalue to jank's overload resolution: C++ 1, jank 2. It also can't be an out-parameter (`int&`): C++ 2, jank an analysis error. v29, v29b.
- **V30** (low) Built-in `=`, `+=`, `++` and unary `&` accept a prvalue (`(cpp/= 1 2)` is 2); C++ rejects them. v30.
- **V31** An operator brought into an argument's namespace by a using-declaration isn't found: C++ 9, jank "not supported". v31.
- **V32** (extends U22) A base `operator()` re-exported with `using`, beside the derived class's own: C++ 3, jank "ambiguous". v32.
- **V33** (low) An object converting to a function pointer can't be called: C++ 42, jank an error. v33.
- **V34** (extends S53) `aget` on a class converting to `int*`: C++ 2, jank an error. v34.

**Regex (libstdc++ against java.util.regex):**
- **V35** `\b` next to a combining mark: `(re-find #"e\b" "e\u0301")` is nil vs `"e"`. v35.
- **V36** (extends R78, R79) Java's line terminators U+0085, U+2028 and U+2029: `(re-matches #".*" "\u2028")` is nil vs a match, and `(re-find #"a$" "a\u2028")` is `"a"` vs nil. v36.

**nREPL:**
- **V37** (makes R128 precise) `interrupt`. nREPL answers `session-idle`, `session-ephemeral`, `interrupt-id-mismatch` or `interrupted`; jank answers `unknown-op`. On the eval's own connection jank answers only after the eval returns, so an interrupt of an eval that never returns is never answered. v37, v37b.

**`#inst` (read/parse.cpp, runtime/obj/inst.cpp, libstdc++ `<chrono>`):**
- **V38** A `Z` offset (`#inst "2020-01-01T00:00:00Z"`) is a read error. v38.
- **V39** A leap second (`…23:59:60`) is a read error. v39.
- **V40** A fraction of more than 9 digits is a read error, or moves the instant (11 digits: 12 hours earlier). v40.
- **V41** Before 1970, a sub-millisecond fraction moves the instant 1 ms toward 1970: `(inst-ms #inst "1969-12-31T23:59:59.9995")` is −1 vs 0. v41.
- **V42** `=` on insts compares nanoseconds, so an inst is not `=` to the read of its printed form. v42.
- **V43** `compare` and `sort` of insts throw. v43.
- **V44** `*default-data-reader-fn*` takes `#inst` and `#uuid` before the built-in readers. v44.
- **V45** (extends U82) An offset after a date (`"2020-01-01-05:00"`) and an hour alone (`"…T10"`) are read errors. v45.
- **V46** (low; extends U39) `print` writes an inst without `#inst`. v46.
- **V47** (low; U49/U92's class) There is no `clojure.instant`. v47.

**CHAMP:**
- **V48** (extends R55) A value jank finds unequal to itself, such as `(seq "é")`, is never found in a hash set or map, and is stored twice. v48.

## 3. Deviations in full

Each item gives the program (Clojure's result, then jank's), the property and its source, the path at 94d32623, the test, and whether it is new.

### Native object loading (area A)

**How jank loads native code:**
- `-l`, `-L` and the other library options feed `load_libs` (jit/processor_dynamic.cpp 873–895).
- `resolve_libs` (787–871) and `find_lib` (737–785) turn each name into a file.
- `load_dynamic_library_impl` (897–954) reads a non-ELF file as a GNU ld script through `parse_ld_script` (parse_ld_script.cpp 20–324) and follows it to depth 8. Otherwise it dlopens through `llvm::cantFail(Interpreter::LoadDynamicLibrary)`.
- Modules come from source, or from a compiled `.o` through `load_o` (module/loader_dynamic.cpp 779–814) and `load_object` (processor_dynamic.cpp 610–676).
- jit/object_dynamic.cpp only keeps stack-trace symbol tables; nothing a program sees depends on it.

**Spec:**
- GNU ld 2.45: `ld.texi` 724–738 for `-l` and 4417–4474 for INPUT/GROUP/AS_NEEDED; `ldgram.y` 310–408; `ldlex.l`.
- jank's own `--help` (util/cli.cpp 160–161).
- jank's own comment at aot/processor.cpp 357–359: the AOT link's directories are Clang's "so the same libs are found as during JIT".
- The C++ standard for initializers ([basic.start.dynamic]).

**V1. A script naming several files: the JIT maps only the first.** New.
- Program: `libfoo.so` is the text `INPUT ( /x/libfoo_core.so /x/libfoo_extra.so )`, run with `jank -lfoo run-main m`.
- ld links both files. jank maps only `libfoo_core.so`, so `libfoo_extra.so`'s symbols are unresolved under the JIT while the AOT link has them.
- Also: only the first INPUT/GROUP command counts (parse_ld_script.cpp 83–149, "Real-world ld scripts only ever contain one"), and when every file is inside AS_NEEDED, the first is loaded anyway.
- Path: parse_ld_script.cpp `parse_ld_script` 234–324 returns one path; processor_dynamic.cpp 905–948 loads it.
- Theorems: `two_files_first_only`, `second_directive_ignored`, `as_needed_fallback` (kernel-checked).
- Test: none (needs shared objects). Shell steps are in `results/r5-native-report.txt` A7.

**V2 (low). The ld-script reader's lexing.** New.
- `GROUP ( "a\b.so" )`: ld reads `a\b.so`, jank reads `ab.so`.
- `GROUP ( a ) /* x`: ld fails ("EOF in comment"), jank reads `a`.
- Single quotes inside names differ as well.
- Path: parse_ld_script.cpp `read_token` 161–182 and `strip_comments`; ld's rules are `ldlex.l` 440–444 and 711–714.
- Census classes: C5 and part of C3. Test: none.

**V3. A file jank cannot dlopen ends in `llvm::cantFail`.** New.
- Program: `(spit "/tmp/x.so" "hello\n")`, then load it as a library (`-lx` with `-L/tmp`, or `load_dynamic_library`).
- Expected: an error naming the library. ld says "file format not recognized"; Clojure's `System/load` throws UnsatisfiedLinkError.
- jank calls `cantFail` on dlopen's failure, which is `llvm_unreachable`:
  - in release builds (NDEBUG, CMakeLists.txt 142–143) that is undefined behavior, likely no error and no library;
  - in debug builds it aborts with LLVM's message.
- The same happens for:
  - an ELF that dlopen refuses;
  - a script entry missing where jank looks (relative to the script's directory only, `-lz`, `=/path`);
  - an unbalanced script;
  - a quoted name holding a parenthesis.
- Path: processor_dynamic.cpp 946–947; LLVM `Error.h` 769–781 and `OrcIncrementalExecutor.cpp` 108–120. jank reports "Failed to find library" only when no file exists (856).
- Test: v03-loading-a-file-that-is-not-a-library-is-an-error. It is jank only: it calls `jit_prc.load_dynamic_library` through cpp/raw. Predicted: no exception, or an abort.

**V4. `-lfoo`: the JIT and the AOT link can use different files.** New.
- Setting: `-L dirA -L dirB`, with `dirA/libfoo.a` and `dirB/libfoo.so`.
- ld searches directory by directory (ld.texi 731–738) and takes `dirA/libfoo.a`.
- jank's JIT looks for `libfoo.so` in every directory before `libfoo.a` in any, so it takes `dirB/libfoo.so`.
- `jank compile` passes `-lfoo` to the linker, which takes `dirA/libfoo.a`.
- Path: processor_dynamic.cpp `resolve_libs` 846–866; aot/processor.cpp 246–249, 356–394.
- Test: none. Shell steps are in A5 of the area report (predicted: 2 under `run-main`, 1 from the compiled binary).

**V5. `-l` with a path or a file name fails the AOT link.** New.
- Programs: `-l/abs/libfoo.so`, `-l./libfoo.so`, `-llibfoo.so`. `--help` promises "absolute or relative paths".
- The JIT loads them (`find_lib`'s literal step, 798–806).
- `jank compile` passes `-l/abs/libfoo.so` to the linker (aot/processor.cpp 389–391), which looks for `lib/abs/libfoo.so.so` and fails.
- A static library given by path works (387).
- Test: none.

**V6. A module loaded from its `.o` never runs its C++ global initializers.** New.
- Program, `src/m.jank`: `(ns m) (cpp/raw "inline int m_x = std::getenv(\"PATH\") ? 7 : 8;") (defn -main [] (println (cpp/m_x)))`.
- From source, `jank run-main m` prints 7.
- After `jank compile-module m`, the loader prefers `m.o` (find 591–635, mtime ≥ source), and the same `run-main` prints 0.
- Path: loader_dynamic.cpp `load_o` 779–814 → processor_dynamic.cpp `load_object` 610–676. It adds the object to ORC and never runs `.init_array`. Its own comment at 672–673 says so: "Object files won't be able to use global ctors until jank is on the ORC runtime".
- Property: [basic.start.dynamic]. Clojure's AOT classes run their static initializers when loaded.
- Test: none (needs compile-module and a second process). Shell steps are in A9. Confidence: medium-high.

### Errors: what a program can see (area B)

**The mechanism.** Every read and analysis result in jank is a `jtl::result<_, error_ref>`. `expect_ok` throws the `error_ref` itself as a C++ exception (jtl/result.hpp 41–68, line 56). `error_ref` is `jtl::ref<error::base>` (error.hpp 291–293): neither an `object_ref` nor a `std::exception`.

**Spec:**
- Compiler.java: CompilerException 7346–7430, DefExpr 417–575, macroexpand1 7509–7560, eval 7658–7720, load 8130–8180.
- LispReader.read 196–208.
- ExceptionInfo.java and Delay.java.
- core.clj: ex-info 4832, ex-data 4841, ex-message 4849, ex-cause 4857, load-lib 5981–6026, future-call, deref-future 2315.
- clojure/main.clj.

**V7. Read, analysis and load errors escape every object catch.** New as an item; round 4's nREPL area remarked on it without an item.
- `(try (read-string "(") (catch cpp/jank.runtime.object_ref e :caught))`: Clojure returns `:caught`; in jank the `error_ref` escapes. The same holds for `(eval 'nope)` and `(require 'no.such.ns)`.
- So clojure.test's `thrown?` (clojure/test.jank 493–504, an object handler) and every program's catch miss them.
- Only an undocumented `(catch cpp/jank.error_ref e …)` sees one, and what it binds is a C++ `error::base`, not data.
- Path: context.cpp `read_string` 271/281, context_dynamic.cpp eval 220–226, core.jank load 4801–4812. The handler is generated as `catch(object_ref e)` (cpp_processor.cpp `gen(catch)` 1105–1123).
- Theorem: ★ `object_catch_misses_error_ref`.
- Tests: v07-a-read-error-reaches-an-object-catch, v07b-an-analysis-error-from-eval-reaches-an-object-catch, v07c-a-missing-namespace-reaches-an-object-catch (jank predicted `[:error]`).

**V8. A failed require leaves the namespace it created.** New; corrects round 4's load replica.
- Fixture `tests/jank_lean/r5_errors_fixture_a.cljc`: `(ns jank-lean.r5-errors-fixture-a) (def loaded-before-the-error 1) (throw (ex-info "…" {:vb3 1}))`.
- `(try (require 'jank-lean.r5-errors-fixture-a) (catch …))`, then `(find-ns 'jank-lean.r5-errors-fixture-a)`: Clojure nil; jank the half-loaded namespace.
- Path:
  - core.jank `load-lib` 4836–4873 removes the namespace, but in an object handler.
  - `context::load_module` (context.cpp 324–354) turns every failure into an `error_ref` (342–353).
  - `load`'s `.expect_ok` (core.jank 4812) throws that `error_ref` past the handler.
  - Clojure: core.clj load-lib 5999–6007.
- Theorems: ★ `jank_failed_require_keeps_ns`, ★ `clj_failed_require_removes_ns`, ★ `load_module_converts`.
- Test: v08-a-failed-require-removes-the-namespace-it-created.

**V9. An ex-info raised while loading, or by a macro, loses its data.** New.
- `(require 'jank-lean.r5-errors-fixture-b)`, whose top level throws `(ex-info "…" {:vb3 1})`:
  - Clojure: the ex-info is the CompilerException's cause, and `{:vb3 1}` is reachable through `ex-cause`.
  - jank: an `error_ref` holding the ex-info's printed text.
- `(defmacro m [] (throw (ex-info "x" {:k 1}))) (eval '(m))`:
  - Clojure: the cause is the ex-info.
  - jank: the `error_ref`'s message is the ex-info's printed form, with no cause.
- Path: context.cpp `load_module` 346–349 (`runtime_unable_to_load_module(e.to_code_string())`); processor.cpp 3502–3530 and error/analyze.cpp 184–195. Clojure: Compiler.load 8174–8179, macroexpand1 7540–7545.
- Tests: v09-an-ex-info-thrown-while-loading-keeps-its-data, v09b-an-ex-info-thrown-by-a-macro-keeps-its-data.

**V10. A failed delay throws another kind of exception at its second deref.** New; refines D19's model.
- `(let [d (delay (nth [1 2] 5))] …)`, deref twice: Clojure rethrows the same IndexOutOfBoundsException. jank throws the native error the first time and a string object holding its message the second.
- Path: delay.cpp deref 19–45: `error = make_box(e.what()); throw;` at 36–40, then `if(error.is_some()) throw error;` at 27–30.
- Theorems: ★ `jank_delay_native_then_string`, ★ `clj_delay_once`.
- Test: v10-a-failed-delay-throws-the-same-kind-each-deref.

**V11. A delay whose body raises an `error_ref` runs at every deref.** New.
- `(let [n (atom 0) d (delay (swap! n inc) (read-string "("))] …)`, two caught derefs, then `@n`: Clojure 1, jank 2.
- Path: delay.cpp 32–45 has handlers for `std::exception` (36) and `object_ref` (41) only, so nothing is cached.
- Theorem: ★ `jank_delay_err_runs` (n derefs run the body n times).
- Test: v11-a-delay-whose-body-fails-to-read-runs-once.

**V12. A future whose body raises an `error_ref` ends the process.** New.
- `@(future (read-string "("))`: Clojure's deref throws an ExecutionException. jank calls `std::terminate` when the thread ends, whether or not anything derefs it.
- Path: core.cpp `future` 1091–1171. Its `catch(...)` (1163–1169) records "Unknown exception." and rethrows out of the thread function, which calls terminate ([thread.thread.constr]).
- jank's book (differences-from-clojure.md) says such exceptions are "forwarded as Unknown exception".
- Theorem: ★ `jank_future_terminates`.
- Test: v12-a-future-whose-body-fails-to-read-can-be-dereferenced (predicted abort).

**V13. A failed future's deref throws a string.** New; low-medium.
- `(try @(future (nth [1 2] 5)) (catch Throwable e (string? e)))`: Clojure false (an ExecutionException); jank true.
- Path: core.cpp future 1143–1148; future.cpp deref 26–29.
- Theorem: ★ `jank_future_native_string`.
- Test: v13-a-failed-futures-deref-throws-an-exception-not-a-string.

**V14 (low). A top-level `def` whose value throws keeps the def's metadata.** New.
- `(eval '(def ^{:vb8 1} vb8-x (throw (ex-info "e" {}))))`, caught, then `(:vb8 (meta (find-var …)))`: Clojure nil, jank 1. Both leave the var interned and unbound.
- Path: evaluate.cpp eval(def) 333–362 sets the metadata (336–340) before evaluating the value (351, 357). Clojure's DefExpr.eval 456–479 sets it after.
- Theorems: ★ `jank_def_meta_always`, ★ `clj_def_meta_none_on_raise`.
- Test: v14-a-def-whose-value-throws-sets-no-metadata.

**V15. `ex-info` rejects a nil message.** New.
- `(ex-message (ex-info nil {}))`: Clojure nil. jank throws a native error: "…`persistent_string` was expected here, but a `nil` was provided".
- Path: core.jank ex-info 113–121 → core.cpp `ex_info` 1321 (takes `immutable_string const &`), through convert/builtin.hpp 323–341.
- Test: v15-ex-info-takes-a-nil-message.

**V16 (low). `ex-info` with nil data.** Round 4's unreported note, reported now that the check runs on 1.12.0.
- `(ex-data (ex-info "m" nil))`: Clojure 1.12 gives `{}` (ExceptionInfo stores `PersistentArrayMap.EMPTY`); jank nil.
- Path: core.cpp `ex_info` 1321–1336.
- Test: v16-ex-info-with-nil-data-has-empty-data (passes on 1.12.0, not 1.11).

**V17. `read-string` of a text without a form returns nil.** New; corrects round 2's reader replica.
- `(read-string "")`, `(read-string "; c")`, `(read-string {} " ")`: Clojure throws "EOF while reading"; jank returns nil.
- Path:
  - core.jank `read-string` 5974–5984 passes `{}` as the options.
  - context.cpp `read_string` reads `:eof` with a nil default (257–261), so `throw_on_eof` is false (285–296).
  - Only the C++ default overload passes `:eofthrow`, and no clojure.core function calls it.
  - Clojure: LispReader.read 196–208 (`valAt(OPT_EOF, EOFTHROW)`) and `read`'s docstring.
- Theorems: ★ `clj_read_string_throws_iff`, ★ `jank_read_string_never_object`.
- Tests: v17-read-string-of-an-empty-text-throws, v17b-read-string-of-a-comment-throws, v17c-read-string-with-options-but-no-eof-throws.

**V18 (extends U44). After a compile error at the nREPL, `*e` has no data and no cause.**
- An nREPL eval of `(vb12-undefined)`, then `(some? (ex-data *e))` and `(some? (ex-cause *e))`:
  - nREPL over Clojure: "true", "true". `*e` is a CompilerException with `:clojure.error/phase`, whose cause is the "Unable to resolve symbol" exception.
  - jank: "false", "false".
- Path: evaluate.cpp `safe_eval` 750 → `exception_info(error_ref)` (exception_info.cpp 23–27), which sets message "" (U44), data nil and cause nil.
- Theorem: ★ `star_e_of_error_ref`.
- Test: v18-ex-data-and-cause-of-a-compile-error-in-star-e (jank only).

**What a reported error leaves behind, besides V8 and V14** (read; not deviations):
- No lock is left held. Every lock on these paths is a scope guard: var.cpp, delay.cpp, lazy_sequence.cpp, multi_function.cpp, the loader's Synchronized locks, and the JIT lock.
- No binding frame stays pushed except a future's (D22). `binding` and `with-bindings*` pop in `finally`, and `binding_scope` is RAII.
- `*ns*` and `*loaded-libs*` behave as in Clojure.
- A throwing lazy seq, or a throwing `alter-var-root` fn, leaves the same state as in Clojure.
- Positions follow a different rule, which is not a defect. jank names the offending token (an unresolved symbol at 1:6 in `(foo nope)`); Clojure names the enclosing list (1:1). In jank the position exists only in the report text (V7, V18), never as data a program can read.

### The C API (area A)

**Spec:** Clojure's Java API (`clojure.java.api.Clojure`, IFn.invoke, Symbol/intern, Keyword/intern), `clojure.main`'s exit status, and `c_api.h`'s own contract (its `extern "C"` guard, lines 3–6).

**V19. `jank_call2` swallows the called fn's exception.** New.
- A C caller, or jank through an `extern "C"` declaration, calls `jank_call2(f, a, b)` with `f` throwing.
- Clojure: `IFn.invoke` throws to the caller. jank prints the exception and returns nil.
- `jank_call0`, `jank_call1` and `jank_call3`–`jank_call11` let the exception through. `jank_eval_file_c` (65–75) also swallows.
- Path: c_api.cpp 168–181 wraps the call in `cpptrace::try_catch`, with printing handlers for `std::exception`, `object_ref`, `error_ref` and `...`. Compare 155–166 and 183–379, which have none.
- Tests: v19-c-api-call2-lets-the-fns-exception-reach-the-caller; control v19b-control-c-api-call1-lets-the-fns-exception-reach-the-caller (predicted to pass).

**V20. An AOT program exits 0 when `-main` throws, under both runtimes.** New for the dynamic runtime; a second cause of U47; corrects REPORT-4's U47 text.
- Program: `(ns app.core) (defn -main [& _] (throw (ex-info "boom" {})))`, compiled with `jank compile app.core`, then the binary run.
- Clojure (`clojure -M -m app.core`) exits 1. jank prints the exception and exits 0.
- Path:
  - aot/processor.cpp 119–127 writes `jank_call2(jank_deref(apply), jank_deref(fn), command_line_args); return 0;`, and `jank_call2` catches everything (V19).
  - So nothing reaches `jank_init_dynamic`'s handlers (c_api_dynamic.cpp 103–129) or `jank_init_static`'s (c_api.cpp 1140–1166).
  - A throw during module loading still gives 1 under the dynamic runtime and 0 under the static one (U47, c_api.cpp 1168).
- Theorems: ★ `aot_main_throw_status_zero`, ★ `aot_dynamic_differs_iff`, ★ `aotRunR5_main_zero` (round 4's whole AOT world).
- Test: none (the exit status of a built binary). Shell, predicted 0:
  ```sh
  printf '(ns app.core)\n(defn -main [& _] (throw (ex-info "boom" {})))\n' > app/src/app/core.jank
  cd app && jank --module-path src compile app.core && ./target/a.out; echo $?
  ```

**V21 (low). A nil namespace in the C API is the namespace "nil".** New.
- `jank_symbol_create(jank_const_nil(), jank_string_create("a"))` gives `nil/a`, and `jank_keyword_intern(nil, "a")` gives `:nil/a`.
- Clojure gives `a` and `:a`, as jank's own `keyword` does (core.cpp 521–542).
- Path: c_api.cpp 433–438 → obj/symbol.cpp 60–65 (stores `ns.to_string()`); c_api.cpp 139–147 → context.cpp `intern_keyword` 561–586.
- Theorem: ★ `symbol_create_agrees_iff`.
- Tests: v21-c-api-symbol-with-a-nil-namespace-is-unqualified, v21b-c-api-keyword-with-a-nil-namespace-is-unqualified.

**V22. `c_api.h` does not compile as C.** New; verified.
- A C17 file with `#include <jank/c_api.h>` fails with "unknown type name 'bool'" at lines 358 and 367, since the header doesn't include `<stdbool.h>`.
- Checked with Apple clang 16 on a copy of the header (`results/r5-native-capi-header.txt`). C23 accepts it.
- Test: none.

**V23 (low).** `jank_eval_file_c` prints `jank_eval_file_c <path>` on stdout (c_api.cpp 67). Test: none.

### jank.math (coordinator)

**V24. The bundled `jank.math` cannot load.** New as an item (REPORT-4 noticed it).
- `(require 'jank.math)` has no Clojure counterpart. The property is jank's own: a namespace jank installs on its module path loads.
  - cmake/install.cmake 48–51 installs `src/jank/*`.
  - loader_dynamic.cpp 403 puts the installed `src/jank` on the module path.
- jank: an analysis error at math.jank line 4, "The symbol `native/raw` could not be resolved."
- Why, from the code:
  - math.jank, unchanged since ae555143 (2024-07-20), is four `defn`s whose bodies are `(native/raw "…")`.
  - `native/raw` was a special form until 529718a6 "Remove native/raw" (2024-11-27), which deleted its analyzer case. Nothing replaced it.
  - The module's `ns` form runs and creates `jank.math`.
  - The first `defn` expands to `(def tan (fn* tan ([o] (native/raw "…"))))`. `context::eval` analyzes the whole form, body included (S71), even though code generation is deferred (U8–U14).
  - `analyze_call` (processor.cpp 3459–3465) finds no special form `native/raw`.
  - `analyze_symbol` (1583–1696) then fails at each step:
    - the namespace `native` is not `cpp` (1589);
    - the symbol is no local and no named recursion;
    - `qualify_symbol` (context.cpp 116–134) finds no namespace or alias `native`;
    - `find_var` (136–159) returns nil;
    - `find_referred_global` finds nothing.
  - So analysis ends in `analyze_unresolved_symbol` (1693–1696).
  - No test or document in jank refers to `jank.math`.
- Replica: `Jank/R5/Coord/JankMath.lean` runs the module's first form through round 2's analyzer replica (`runJank`). It gives "analysis error: analyze/unresolved-symbol: The symbol `native/raw` could not be resolved." The same defn with `(str o)` as its body analyzes (`results/r5-coord-math.txt`).
- Test: v24-jank-math-loads (jank only).
- After the failure, the namespace `jank.math` exists and is empty (V8's mechanism).

### C++ operators (area F)

**Scope.** Round 4 replicated operator lookup (GetOperator) and class templates. This round adds operator templates, `=`, compound assignment, `aget` (`[]`), the call operator, `++` and unary `&`. The C++ side follows [over.match.oper], [over.ass], [over.sub], [over.call.object], [over.built], [temp.deduct.call] and [basic.lookup.argdep].

**The finding is one family: jank gives operands value categories C++ doesn't.**
- A class argument is always `T&` (processor.cpp `build_cpp_call` 565–572).
- A builtin argument is always a prvalue.
- Member calls pass their arguments as named lvalues.

Every program below runs its `cpp/raw` in its own eval and the use inside a fn.

**V25. Assigning a temporary of a move-only class.** New.
- Declarations: `struct mo { int v{}; mo() = default; mo(int x) : v(x) {} mo(mo &&) = default; mo &operator=(mo &&) = default; }; inline mo g;`
- `((fn [] (cpp/= cpp/g (cpp/mo. 5)) (cpp/.-v cpp/g)))`: C++ move-assigns, giving 5. jank: "The `operator=` function cannot be called, since it's deleted."
- Path: build_cpp_call 461–462 → CppInterOp GetOperator 7040–7050 → 565–572 (`mo` becomes `mo&`) → BestOverloadMatch picks the deleted copy assignment → cpp_util.cpp `find_best_overload`.
- Theorem: ★ `class_temporary_is_lvalue`.
- Test: v25-cpp-assigning-a-temporary-moves-it.

**V26. A forwarding operator template deduces `T = W&` for a temporary.** New.
- Declaration: `template <typename T> int operator+(V const &, T &&)`, returning 2 for a non-reference T and 1 for `T&`.
- `(cpp/+ cpp/vf2.gv (cpp/vf2.W.))`: C++ 2, jank 1.
- Path: as V25 up to BestOverloadMatch, which deduces from an lvalue. The emitted call names no template arguments (GetQualifiedCompleteName, CppInterOp.cpp 991–1013), so Clang deduces `W&` again.
- Theorem: ★ `temporary_forwarding_deduces_lref`.
- Test: v26-cpp-a-forwarding-operator-template-sees-a-temporary-as-an-rvalue.

**V27. A member operator taking `int&&`, given a literal: a JIT error.** New.
- Declaration: `struct vr { int operator*(int &&) const { return 1; } }`.
- `(cpp/* cpp/g 1)`: C++ 1. jank's analysis accepts the call, but the emitted `t0.operator*(t1)` binds `int&&` to the lvalue `auto t1(1);`, a compile error.
- Path: cpp_processor.cpp `gen(cpp_member_call)` 1730–1775 and `gen(cpp_literal)` 1278–1285.
- The same holds for every member function with an rvalue-reference parameter.
- Theorem: ★ `member_call_args_lvalue`.
- Test: v27-cpp-a-member-operator-takes-a-literal-by-rvalue-reference.

**V28. A member operator template with `T&&`, given a literal.** New.
- Declaration: `struct R { template <typename T> int operator/(T &&) const; }`, returning 2 for a non-reference T.
- `(cpp// cpp/vf4.g 1)`: C++ 2. jank analyzes it with `T = int`, then emits `t0.operator/(t1)`, where Clang deduces `T = int&`: 1.
- Path: GetOperator 7044–7050 → AddMethodTemplateCandidate (2071–2073) → the member-call codegen.
- Test: v28-cpp-a-member-operator-template-forwards-a-literal-as-an-rvalue.

**V29. A `let`-bound builtin is an rvalue to overload resolution.** New.
- Declarations: `operator-(V const &, int const &)` returning 1 and `operator-(V const &, int &&)` returning 2.
- `(let [x (cpp/int. 1)] (cpp/- cpp/vf5.gv x))`: C++ 1, jank 2, and the call moves `x`.
- The visible effect, with `inline void inc(int &i)`: `(let [x (cpp/int. 1)] (cpp/inc x) x)` is C++ 2 and a jank analysis error (no viable overload). The same holds for `(cpp/>> in x)`.
- Path: analyze_let 2414–2421 gives the binding type `int`, and build_cpp_call 565–572 leaves builtins as prvalues.
- Theorem: ★ `named_builtin_local_is_prvalue`.
- Tests: v29-cpp-a-named-local-is-an-lvalue-to-overload-resolution, v29b-cpp-a-named-local-binds-a-non-const-reference.

**V30 (low). Built-in assignment needs an lvalue.** New.
- `(cpp/= 1 2)` gives 2, `(cpp/+= 1 2)` 3, `(cpp/++ 1)` 2, and `(cpp/& 1)` a pointer that dangles once the fn returns. Each is ill-formed C++.
- Path: build_cpp_call 392–411 → build_builtin_operator_call 196–249 → CppInterOp GetBuiltinOperatorType 7080–7087, which makes every operand an lvalue → codegen 1794–1821, over the mutable `auto t1(1);`.
- jank rejects a const left operand (its own test operator/equal/fail-const.jank), so C++'s rule is the intended one.
- Test: v30-cpp-built-in-assignment-needs-an-lvalue. It observes with `vb-kind`, because a rejection would be an `error_ref` (V7) that `thrown?` misses.

**V31. Argument-dependent lookup misses an operator brought in by a using-declaration.** New.
- Declarations: `namespace lib { struct P {}; } namespace ext { int operator+(lib::P const &, lib::P const &) { return 9; } } namespace lib { using ext::operator+; }`.
- `(cpp/+ cpp/p cpp/p)`: C++ 9 ([basic.lookup.argdep]/4). jank: "The operator `+` is not supported for the type `lib::P`."
- Path: CppInterOp.cpp GetOperator 7022–7031 keeps only FunctionDecl and FunctionTemplateDecl, while the lookup result holds the UsingShadowDecl (SemaLookup.cpp 1139–1143).
- Theorem: ★ `jank_getOperator_ignores_namespace_using`.
- Test: v31-cpp-argument-dependent-lookup-finds-a-using-declaration.

**V32 (extends U22). A using-declared base `operator()` beside the derived class's own.**
- Declarations: `struct b { int operator()(int) const { return 3; } }; struct d : b { using b::operator(); int operator()(long) const { return 4; } };`.
- `(cpp/g 1)`: C++ 3, because the using-declared member counts as d's for the implicit object parameter ([over.match.funcs]/4). jank: "ambiguous".
- Path: build_indirect_cpp_call 930–965 → GetOperator 7044–7050 (the shadow is skipped, and b's member is found through b as an associated class) → AddMethodCandidate with b as the acting context, which costs a derived-to-base conversion.
- Theorems: ★ `base_acting_context_not_exact`, ★ `using_member_acting_context_exact`.
- Test: v32-cpp-a-using-declared-base-call-operator.

**V33 (low). An object converting to a function pointer can't be called.** New.
- Declaration: `struct sf { using fp = int (*)(int); operator fp() const; }`, returning `twice`.
- `(cpp/g 21)`: C++ 42, through a surrogate call function ([over.call.object]/2). jank: "The operator `()` is not supported".
- Path: build_indirect_cpp_call 930–965 → GetOperator(OP_Call) → 513–523.
- Test: v33-cpp-calling-an-object-through-its-conversion-to-a-function-pointer.

**V34 (extends S53). `aget` through a conversion to a pointer.**
- Declaration: `struct bf { int d[3]{1, 2, 3}; operator int *() { return d; } }`.
- `(cpp/aget cpp/g 1)`: C++ 2, through the built-in `int &operator[](int *, std::ptrdiff_t)` ([over.built]). jank: "not supported".
- The same holds for `+` (pointer arithmetic), `=` and `+=` through conversions.
- Path: build_cpp_call 495–523; BestOverloadMatch adds no built-in candidates.
- Test: v34-cpp-aget-through-a-conversion-to-a-pointer.

Re-found, not new: U22 for assignment. A derived class's implicit `operator=` hides the base's in C++; jank calls it ambiguous.

### Regex (area E)

**Spec:** java.util.regex in JDK 23 (Pattern.java), as round 4's model plus this round's corrections, checked on the JVM.

**V35. `\b` next to a combining mark.** New.
- Programs (Clojure first, then jank):
  - `(re-find #"e\b" "e\u0301")`: nil vs `"e"`.
  - `(re-seq #"\b\w+\b" "cafe\u0301 x")`: `("x")` vs `("cafe" "x")`.
  - `(clojure.string/replace "nai\u0308ve" #"\b" "|")`: `"|nai\u0308ve|"` vs `"|nai|\u0308|ve|"`.
  - `(re-find #"\b" "\u0661\u0301")`: `""` vs nil.
- Property: Java's `Bound.check` (Pattern.java 5543–5613) counts a non-spacing mark after a letter or digit as a word character, in every mode.
- jank: libstdc++'s `_M_word_boundary` (regex_executor.tcc 551–571) tests each byte with `ctype<char>`. Bytes 0x80–0xFF have no class, so a boundary falls between a letter and its accent.
- Not R78: a spec-side switch (Java without the mark rule) removes the whole class.
- Test: v35-word-boundary-and-a-combining-mark.

**V36 (extends R78, R79). Java's Unicode line terminators.**
- `(re-matches #".*" "\u2028")`: Clojure nil, jank the match. `(re-find #"a$" "a\u2028")`: `"a"` vs nil.
- Property: `.` excludes U+0085, U+2028 and U+2029, and `$` matches before them (Pattern.java Dot and Dollar; the javadoc's "Line terminators").
- jank: `_AnyMatcher` for `char` excludes only `\n` and `\r` (regex_compiler.h 368–398), and `$` matches only at the end (R79).
- Round 3 had counted these questions under R78.
- Test: v36-unicode-line-terminators.

**(?U) itself adds nothing new to report.**
- Every pattern holding (?U) is a read error in jank (R18).
- `\p{…}` is S31 and `[[:alpha:]]` is S29.
- `\w`, `\d` and `\s` without (?U) are ASCII on both sides.
- A Clojure program reaches Java's Unicode classes only through (?U) or `\p`, and jank rejects both.

### nREPL interrupt (area D)

**V37 (makes R128 precise). The `interrupt` op.**
- nREPL 1.8.0, measured on OpenJDK 23 (`results/r5-nrepl-interrupt-jvm.txt`), answers:
  - an idle session: `#{session-idle done}`;
  - no session: `#{error session-ephemeral done}`;
  - an unknown session: `#{error unknown-session done}`;
  - a running eval, with another id: `#{error interrupt-id-mismatch done}`;
  - a running eval, with its id or none: `#{done}`, and the eval ends with `#{interrupted done}`.
- jank answers every interrupt `{:status [:error :unknown-op :done] :op "interrupt"}` (handler.jank 5–8; describe.jank lists no interrupt).
- Ordering:
  - On the eval's own connection, jank reads the next message only after the eval returns (core.jank `handle-client` 79–106).
  - So an interrupt sent after an eval that never returns is never answered. nREPL answers it in every race.
  - On a second connection, jank answers unknown-op at once while the eval runs on.
- Spec: nREPL's session.clj `interrupt-session` 282–289 and its docstring 367–373.
- World I: 72 cases.
  - 54 get unknown-op where nREPL gives a status.
  - 9 are never answered.
  - 9 agree (no interrupt was sent).
  - jank's side of the 36 whose eval ends was rerun through round 3's World T: 1,535,724 schedules.
- Tests: v37-nrepl-interrupt-of-an-idle-session, v37b-nrepl-interrupt-without-a-session (jank only: they call jank's handler in-process). The never-answered case has shell steps in `results/r5-nrepl-report.txt`.

### `#inst` (area G)

**How jank reads `#inst`.** `inst_from_string` (runtime/obj/inst.cpp 31–57) tries four `std::chrono::parse` formats, `"%FT%T%Oz"`, `"%FT%T%z"`, `"%FT%T"` and `"%F"`. A format is accepted only if it consumes the whole text (44). The replica follows libstdc++ 15.3.0's `chrono_io.h` parser and the `istream` peek/sentry bits.

**Spec:** clojure/instant.clj (parse-timestamp, validated, read-instant-date), print-method of Date (UTC, milliseconds), and RFC 3339.

Every test reads its literal at run time, so a read error fails only its own test.

**V38. A `Z` offset is a read error.** New.
- `(inst-ms #inst "2020-01-01T00:00:00Z")`: Clojure 1577836800000; jank "Unrecognized date/time syntax".
- Path: `%z` and `%Oz` need a digit (chrono_io.h 4020–4060), and `"%FT%T"` leaves `Z` unread. Clojure: instant.clj 50–51, `(?:[Z]|…)`.
- Test: v38-inst-reads-a-z-offset.

**V39. A leap second is a read error.** New.
- `#inst "2016-12-31T23:59:60"`: Clojure 1483228800000 (parse-timestamp's docstring allows 60, and the calendar rolls over); jank a read error.
- Path: chrono_io.h `%S` 3767–3858 sets `_M_is_leap_second` (4429–4430), and `from_stream(sys_time)` 2889–2890 fails on it.
- Test: v39-inst-reads-a-leap-second.

**V40. A fraction of more than 9 digits.** New.
- `#inst "2020-01-01T00:00:00.12345678912"`: Clojure 1577836800123; jank 1577793600123, 12 hours earlier.
- By the number of digits after the 9th:
  - 1: a read error;
  - 2: read as an `%Oz` hour offset;
  - 3: a read error;
  - 4: read as an `%z` hhmm offset;
  - 5 or more: a read error.
- Path: chrono_io.h 3827–3839 stops after 9 fractional digits, and the offset directive takes the rest (its sign is optional, 4040–4043). Clojure keeps 9 digits (instant.clj 42–48, 115).
- Test: v40-inst-fraction-of-more-than-nine-digits.

**V41. Before 1970, a sub-millisecond fraction moves the instant 1 ms.** New.
- `(inst-ms #inst "1969-12-31T23:59:59.9995")`: Clojure −1, jank 0.
- `(pr-str #inst "1969-01-01T00:00:00.0001")` prints `….000` vs `….001`.
- Path: core.cpp `inst_ms` 1056–1066 and inst.cpp `to_string_impl` 77–81 truncate toward zero ([time.duration.cast]). Clojure floors (instant.clj 247).
- Test: v41-inst-before-1970-keeps-its-millisecond.

**V42. `=` on insts compares nanoseconds.** New.
- `(= #inst "2020-01-01T00:00:00.0001" #inst "2020-01-01T00:00:00")`: Clojure true (Date.equals compares getTime), jank false.
- So an inst `x` is not `=` to `(read-string (pr-str x))`.
- Path: inst.cpp `equal` 66–75.
- Test: v42-inst-equality-is-to-the-millisecond.

**V43. Insts don't compare.** New.
- `(compare #inst "2020-01-01" #inst "2021-01-01")`: Clojure −1 (Date is Comparable); jank throws. `sort` fails the same way.
- Path: obj/inst.hpp 12–30 declares no compare, and object.cpp 228–233 throws.
- Test: v43-insts-compare.

**V44. `*default-data-reader-fn*` takes `#inst` and `#uuid` first.** New.
- `(binding [*default-data-reader-fn* tagged-literal] (inst? (read-string "#inst \"2020-01-01\"")))`: Clojure true; jank false, since it returns a tagged literal. The same holds for `#uuid`.
- jank's own docstring (core.jank 7699–7703) says the default fn is for "When no data reader is found".
- Path: read/parse.cpp `parse_reader_macro_tagged` 1008–1124 checks `*data-readers*` (1037), then the default fn (1080–1102), then the built-in tags (1104–1124). Clojure: LispReader.readTagged 1435–1451.
- Theorem: ★ `dispatch_differs_iff`.
- Test: v44-default-data-reader-fn-leaves-inst-and-uuid.

**V45 (extends U82). An offset after a date, or an hour alone.**
- `#inst "2020-01-01-05:00"`: Clojure 1577854800000. `#inst "2020-01-01T10"`: Clojure 1577872800000. jank: read errors for both.
- Path: every format needs `%F`, then nothing or `T%T`, and `%T` needs hh:mm:ss (3728–3765).
- Test: v45-inst-reads-an-offset-after-a-date.

**V46 (low; extends U39's root).**
- `(print-str #inst "2020-01-01")`: Clojure `#inst "2020-01-01T00:00:00.000-00:00"`; jank prints it without the tag.
- Path: core.cpp print 141–159 → `inst::to_string`.
- Test: v46-print-of-an-inst-keeps-its-tag.

**V47 (low; U49/U92's class).**
- `clojure.instant` does not exist (there is no `src/jank/clojure/instant.jank`), so `read-instant-date`, `parse-timestamp`, `validated` and the rest are missing.
- Test: v47-clojure-instant-exists.

### CHAMP (area G)

**V48 (extends R55). A self-unequal value is lost in hash collections.**
- `(let [x (seq "é")] [(contains? (hash-set x) x) (count (hash-set x x)) (get (hash-map x 1) x)])`: Clojure `[true 1 1]`; jank `[false 2 nil]`.
- Path:
  - persistent_string_sequence.cpp `equal` 34–37 → seq_ext.hpp `equal` 13–34, which is false for non-ASCII text (R55).
  - CHAMP's `get` compares the stored value with the query.
  - `do_add`'s equality check fails, so `make_merged` puts both values into one collision node (round 3's replica).
  - persistent_hash_set.cpp 45–53 and 186–189.
- Theorems: `r55_stored_twice`, `r55_never_found`.
- Test: v48-a-set-finds-its-own-string-seq.

## 4. Proofs for the spaces too big to search

### Codegen's depth-2 control (area C)

**The world.** Round 2's control world (`Jank/Codegen/ProgSearch.lean`, `run cfg 2 src true`).
- A program drawn by the clean grammar runs through Clojure's meaning (`Spec.run`) and through jank's pipeline (`jankRun`): the analyzer replica, IR, passes, the emitted C++ text, its parse and check, and its run.
- The property is that both outcomes agree.
- The clean grammar leaves out every production of R37–R42, R44, R47 and R26, but keeps R43 in AOT.
- Modes: eval -O0 (JIT) and module (AOT).

**Proved** (`Jank/R5/Codegen/`):
- The generator is `partial`, so nothing could be proved about it directly. `Tree.lean` defines a decision-tree monad `DT` with leaf counts and counting lemmas.
- `Gen.lean`'s `genT` restates the clean branches of ProgSearch.lean 60–181, with the same decisions in the same order and option counts. It is checked against the original, not proved equal (CodegenA5-1):
  - every depth-1 timeline;
  - every timeline of the small depth-2 partitions;
  - 3,000 random depth-2 timelines;
  - identical forms and decisions; the verdict copy against `ProgSearch.run` in both modes gives 0 differences.
- ★ `leaves_genT`: the exact number of timelines for every depth and context, as a closed recurrence. It also shows that the clean grammar never builds a recur target.
- ★ `world1`: depth 1 has exactly 3,464 timelines, which is round 2's complete walk.
- ★ `world2`: depth 2 has exactly 354,197,993,668 timelines. Round 4's Knuth estimate was 7% low. Depth 3 has 1.78·10³⁶.
- ★ `subWorld_size`: the sub-world below has exactly 9,246,393 timelines.

**The reduction used.** The verdict is a function of the drawn program alone. Counting distinct programs gives 181,450,370,757 at depth 2. This count is computed and checked on depth 1 and the small depth-2 partitions, not proved (CodegenA5-2).

**Not done: a for-every-input proof, or a reduction that completes the world.**
- Two root productions hold 99.97% of the world:
  - `let` with two bindings (312,527,871,808 timelines);
  - `if` (41,565,561,344).
- A for-every-input proof would be a compiler-correctness proof. `jankRun` runs about 100 `partial` definitions, and it includes a print/parse round trip of the emitted C++ text.
- A compositional reduction fails because sibling expressions share code-generator state through five mechanisms, each a place an earlier round found a deviation:
  - lifted constants shared by one map per module (R42);
  - `local_to_loop_shadow`, never restored (R39);
  - the branch common type and propagated positions (R23, S57);
  - the locals map keyed by munged name (R38);
  - the process-wide `unique_string` counter.
- Symmetry (x↔y, :a↔:b) would at most quarter the count, and can't be proved to leave jank's outcome unchanged.
- No subexpression is dead for jank: even a branch Clojure never evaluates is compiled.
- Reduced estimate: about 230 core-days in eval mode and 300 in AOT.

**Run instead.** Complete in both modes unless noted:
- every root kind with at most one depth-1 subexpression (kinds 0–5, 9, 13, 15–19): 47,501 timelines per mode;
- the sub-world, `let`-with-two-bindings or `if` over the one-leaf productions: 9,246,393 per mode;
- root kind 6 (vector a b): eval mode only, 11,999,296.

Totals: eval complete over 21,293,190 timelines and AOT over 9,293,894, where round 3 stopped at 186,717. Eval found nothing. AOT found only R43 (7,076 in the small kinds, 1,307,080 in the sub-world). Not run: kind 6 in AOT, kinds 7, 11, 12 and 14 in both modes, and `let`/`if` beyond the sub-world.

**Verdict.** Neither a proof nor a completing reduction worked; the world's exact size is proved, and the complete parts found nothing new.

### The nREPL's T7 (area D)

T7 is round 3's World T with one client, partial reads and every op: ≈3.2·10¹¹ timelines at ≤1 preemption and ≈1.2·10¹³ at ≤2. Rounds 3 and 4 stopped at about 1.5 million.

**Proved:**
- ★ `chunking_independent`, ★ `readLoop_prefix`, ★ `readLoop_empty`, ★ `chunking_independent_all` (`Jank/R5/Nrepl/Chunk.lean`). For every message whose proper prefixes all parse to nil, every chunking of it gives exactly the message a whole read gives, once, and leaves an empty buffer.
- ★ `k_agrees`, ★ `parseK_sound` (`ParseK.lean`). Round 2's bencode parser is `partial`, so a copy the kernel can evaluate was written. It is proved to give, for every input and fuel, either an out-of-fuel or exactly the original's result.
- `t7_k` is a kernel evaluation of T7's 261 prefixes, for both `char` signednesses. It gives `t7_hyps` and ★ `t7_chunking_independent`: for every chunking of each of T7's six requests, the server reads what a whole read gives.

**The reduction:**
- Steps 1–2 say a partial read is a stutter step, and the read that completes a message equals a whole read. They were checked by running round 3's `tConnStep` at every reachable pre-read state, every split point and every chunk length: 6 states, 13,227 step runs.
- Cross-check on T7 itself, over every timeline with at most one partial read:
  - ≤0: complete, 16,384;
  - ≤1: complete, 1,392,512;
  - nothing found, and every timeline ends in the reduced world's one final state.
- Steps 3–5 are argued from the code, not proved:
  - no other thread reads a connection's buffered bytes;
  - the judge sees only the reduced state;
  - deleting stutter steps adds no preemption.
- The sdk can't state independence or a process-level simulation, and World T's states have no decidable equality.

**The reduced world, with whole-message reads:**
- ≤0: 64; ≤1: 5,312; ≤2: 218,400. Each walk is complete, ends in one final state, and finds nothing.
- With the unused `net.read.eintr` draw held at 0: ≤2 complete at 3,335, ≤3 complete at 89,835, ≤4 stopped at 688,909. That draw happens on every blocked read even with EINTR off (Threads.lean 251) and its value is never used.

**Verdict.** T7 at ≤1, ≤2 and ≤3 preemptions is decided with nothing found, provided steps 3–5 hold as argued. ≤4 is incomplete. The two-client scenarios T3 and T9 were not reduced, because their connections share fd 1 and the evaluator, so their steps don't commute.

### The regex proof round 4 kept aside (area E)

`.r4-scratch/regex/ExecInv.lean.unfinished` now checks, as `Jank/R5/Regex/ExecInv.lean`:
- ★ `dfs_keeps_res`: for every NFA, input, flag set, fuel and state, a run of libstdc++'s `_M_dfs` replica that starts and ends without a solution leaves `_M_results` unchanged.
- ★ `searchFromFirst_fail_keeps_res` and ★ `search_fail_keeps_res`: a start position, or a whole search, that finds nothing leaves `_M_results` unchanged.
- ★ `search_found_from_initial_results` and `loop_found`: a match `regex_search` finds comes from one start position's run, which began from the search's initial results.

What it makes complete: jank's side of U35 now holds for every input, not just round 4's censuses. A capture made inside a lookahead at an earlier, failed start position never appears in jank's match. Java's side stays a model checked on the JVM.

Why round 4's attempt failed: one `simp` over the whole body is too slow, and at default transparency `get >>= ?f` unifies with an `if`, so the walk loops. This proof takes one lemma per kind of step and unifies at reducible transparency only.

### Other for-every-input proofs this round

- **CHAMP laws** (area G: `Jank/R5/Core/ChampLaws5.lean`, `ChampWf5.lean`, `ChampSub5.lean`). They are proved over round 3's replica of immer's champ.hpp, for every well-formed champ, every hash and every equality linked to the query:
  - ★ `added_doAdd`, ★ `size_add`: the count after add grows by one exactly when `get` found nothing.
  - ★ `added_doAddMut`, ★ `size_addMut`: the transient add sets the same flag, so transient and persistent counts agree.
  - ★ `sub_absent`, ★ `subMut_absent`: removing an absent key returns the same champ and allocates nothing.
  - ★ `doSub_found`, ★ `size_sub`: removing a present key drops the count by one.
  - ★ `makeMerged_wf`, ★ `doAdd_wf`, ★ `add_wf`: add keeps the champ well formed, so every champ built by adds meets the premise of these laws and of round 3's `get_add`.
  - ★ `size_add_add`, ★ `get_add_add`: adding the same value twice changes neither the count nor `get`.
  - ★ `get_sub`: after removing k, `get` of k finds nothing, given at most one stored value equal to k.
  - Collision nodes are covered inside each proof.
  - These make the count, absent-removal, transient-count and idempotence laws complete for every length, where rounds 3–4's searches (M4-2, M4-3, M5, S3-3) stopped at 3–4 steps.
  - Not proved: `get` of another key after add or remove, and "iteration yields each key once and exactly the keys added" (which would discharge `get_sub`'s premise). Both need a hash-path invariant through `make_merged`, `do_sub`'s collapse cases and collision reordering, plus an equality that agrees with the hash, which jank's doesn't (D12, R55).
- **Errors** (area B): 17 for-every-input theorems (section 3).
- **ld scripts** (area A):
  - ★ `parseText_total`: the `parse_ld_script` replica finishes within its fuel on every text, built from per-loop fuel lemmas.
  - ★ `aot_main_throw_status_zero` and ★ `symbol_create_agrees_iff`.
  - Not done: the reader's agreement with ld on every well-formed script; the complete census stands in for it.
- **Operators** (area F): 10 for-every-input theorems on value categories and lookup (section 3).

## 5. What was replicated, and what is not exact

**Replicated this round:**
- **Native** (`Jank/R5/Native/`):
  - `LdScript`: parse_ld_script.cpp 20–324, whole, with fuel proved sufficient.
  - `LdSpec`: GNU ld 2.45's reading of INPUT, GROUP, AS_NEEDED and OUTPUT_FORMAT scripts.
  - `Libs` and `LibsWorld`: processor_dynamic.cpp's library naming, `build_library_dirs`, `find_lib`, `resolve_libs`, `load_libs`, `load_dynamic_library_impl` and `load_static_library`; the AOT link (aot/processor.cpp 246–249, 356–394); and ld's `-l` search.
  - `CApi`: the exception boundary of c_api.cpp's call functions; the AOT main's status (with c_api.cpp 1133–1169 and c_api_dynamic.cpp 84–130); `jank_symbol_create` and `jank_keyword_intern`.
  - Read, not modeled: object_dynamic.cpp, object_static.cpp, `load_object`, `load_o`, the rest of the C API.
- **Errors** (`Jank/R5/Errors/`):
  - jank's side: thrown values and C++ handler matching (`gen(catch)`, `analyze_try`), the ex-info family, `read-string`'s EOF, `load`/`load-one`/`load-lib`/`load_module`, macro-expansion errors, top-level `def`, `delay`, `future`, and `*e`.
  - Clojure's side, beside each: Compiler.java, LispReader, ExceptionInfo, Delay and core.clj.
  - Read, not modeled: report_dynamic.cpp's printed report.
- **Codegen** (`Jank/R5/Codegen/`): round 2's clean generator restated as a decision tree, with counting lemmas; no new jank C++.
- **nREPL** (`Jank/R5/Nrepl/`): chunking independence over round 2's bencode reader, a kernel-evaluable copy of the parser, the World T reduction, and the interrupt op on both sides (World I).
- **Regex** (`Jank/R5/Regex/`):
  - the executor invariant proofs;
  - `JavaM5`, round 4's Java model plus `\b`'s mark rule, the (?U) word class, `\p{…}` under (?U), and Java's surrogate-pair start rule;
  - `Compare5`.
- **Interop** (`Jank/R5/Interop/`):
  - jank's side: operator templates, `=`, compound assignment, `aget`, the call operator, `++` and unary `&`, through GetOperator, BestOverloadMatch and GetBuiltinOperatorType, with the value categories jank gives operands;
  - the C++ side per the standard (World XXII).
- **Core** (`Jank/R5/Core/`):
  - `Inst`: libstdc++ 15.3.0's `chrono_io.h` `_Parser` and `from_stream`, the `istream` peek/sentry bits, jank's `inst_from_string`, `inst-ms`, `=` and printing; Clojure's instant.clj beside them.
  - The CHAMP law proofs and `ChampR55`.
- **Coordinator** (`Jank/R5/Coord/JankMath.lean`): jank.math's first form through round 2's analyzer replica.

**Not exact:**
- The C API's arity and type errors were read, not modeled. A wrong type raises a `std::runtime_error` out of an `extern "C"` function, which ends a C caller that has no C++ handler.
- macOS library paths (the dlopen fallback, Mach-O) are not modeled; the `-l` world is Linux only.
- The printed error report and its positions were read, not modeled.
- The codegen restatement is checked against the original, not proved equal (CodegenA5-1).
- The nREPL reduction's steps 3–5 are argued, not proved (nREPLA5-3).
- `#inst` years before 1583 are kept out of value comparisons, because of Clojure's Julian calendar (round 1's A10).

## 6. Still left out, and why

- **Native:**
  - the reader's agreement with ld on every well-formed script (only censused);
  - ORC's behavior for duplicate definitions between a `.o` module and a static library;
  - macOS.
- **Errors:**
  - the printed report, which is text for a human with no Clojure counterpart;
  - foreign native exception types, reachable only through cpp/raw.
- **C API:** `jank_to_integer` of a non-integer returns its hash (c_api.cpp 981–989, 1015–1019). It is unused inside jank and not reported; the rest of the C API was read.
- **Codegen:** the depth-2 control beyond what section 4 records; -O1 and -O3.
- **nREPL:**
  - T7 at ≤4;
  - T3 and T9, whose two clients share fd 1 and the evaluator;
  - diverging evals inside World T (its evaluator has fuel), taken from reading instead.
- **Regex:** CANON_EQ, `\X` and `\N{}`. jank rejects every escape of this kind and every inline flag, so nothing can reach Java's behavior through them.
- **Operators:**
  - C++20 rewritten comparisons (documented as unsupported);
  - C++23 operators (jank compiles as C++20);
  - ref-qualified members and `->`;
  - operators with jank objects as operands.
  - V25's and V29b's effect on ordinary calls was found by reading, not searched.
- **`#inst`:** the many timestamps jank accepts and Clojure rejects (2-digit years, minute 60, offsets out of range) are counted, not reported, by round 2's rule.
- **CHAMP:** `get` of another key after add or remove, and iteration, for the reason in section 4.
- **jank.shell:** why U88–U90 failed (section 1).

## 7. Assumptions

**Rounds 1–4's assumptions stand**, except those replaced below.

**Replaced:**
- Round 4's AOT model, in which a throwing `-main` reached `jank_init_dynamic`: replaced by the `jank_call2` boundary (V20).
- Round 4's model of jank's `load-lib` catching every failure: replaced (V8).
- Round 2's `readString`, which gave an EOF error for an empty text: replaced (V17).
- Rounds 3–4's implicit "a builtin argument is a prvalue, a class argument an lvalue" as C++'s categories: these are jank's synthesis, while C++'s come from the expression (V25–V29).
- Round 4's codegen size estimate: replaced by ★ `world2`.
- Round 4's Java model's `boundAt` and (?U) word class: corrected (V35).

**New:**
- **Native:**
  - NatA5-1: release builds define NDEBUG, so `cantFail` on a failure is undefined behavior.
  - NatA5-2: scripts and paths are ASCII.
  - NatA5-3: dlopen accepts exactly the loadable ELF shared objects.
  - NatA5-4: jank's install directories hold no library with the user's name.
  - NatA5-5: the AOT link's `-L` order is the user's directories, then Clang's.
  - NatA5-6: GNU ld 2.45 is the spec; lld follows the same rules for these inputs.
  - NatA5-7: LLJIT without the ORC runtime runs no initializers of an added object (jank's own comment).
- **Errors:**
  - errA5-1: NA9's mapping of jank's object handler to Clojure's catch.
  - errA5-2: [except.handle]/3.
  - errA5-3: [thread.thread.constr], terminate.
  - errA5-4: the tests' `*ns*` is clojure.core (U45).
  - errA5-5: jank finds the `.cljc` fixtures on `--module-path .` (loader_dynamic.cpp 188–207).
- **Codegen:**
  - CodegenA5-1: the restated generator is the original (checked, not proved).
  - CodegenA5-2: the distinct-program rule (checked on depth 1 and the small depth-2 partitions).
- **nREPL:**
  - nREPLA5-1: nREPL 1.8.0 is the interrupt op's spec.
  - nREPLA5-2: every race position in World I is reachable.
  - nREPLA5-3: the reduction's steps 3–5, argued.
  - nREPLA5-4: `net.read.eintr` is unused when EINTR is off.
  - nREPLA5-5: chunked runs stay within the step bound.
- **Regex:**
  - RXA5-1: JDK 23's java.util.regex is the spec, including `Bound`'s mark rule, which has been the same since JDK 1.4.
  - RXA5-2: character data is as JDK 23 reports it (checked on the JVM).
- **Interop:**
  - OpA5-1: a `let`-bound native local is a named variable in C++'s sense; jank's own tests assign to them.
  - OpA5-2: iterating a LookupResult yields the UsingShadowDecl.
  - OpA5-3: no two templates in the world tie.
  - OpA5-4: a surrogate call function's object conversion is user-defined.
- **Core:**
  - coreA5-1: the host has the en_US.UTF-8 locale (inst.cpp 41); without it every `#inst` is a read error.
  - coreA5-2: libstdc++, not libc++ (inst.cpp 18–29 disables `#inst` parsing under libc++), with a long double of at least 64 mantissa bits and a nanosecond `system_clock`.
  - coreA5-3: Clojure's calendar is Gregorian from 1583.
  - coreA5-4: `from_chars` accepts `5.` and `.5`.
- **Coordinator:** the validation machine's jank installs `src/jank/*` (install.cmake 48–51), as every installed jank does.

## 8. Properties, with their sources

- **Libraries:**
  - The files jank loads for a library are the files ld links (ld.texi 724–738, 4417–4474; ldgram.y 310–408).
  - The JIT and the AOT link agree (aot/processor.cpp 357–359).
  - `-l` takes paths (util/cli.cpp 160–161).
  - A library that can't be loaded is reported (jank's "Failed to find library"; book jank-build/packaging-system-lib.md 123).
  - A loaded module's initializers run ([basic.start.dynamic]).
- **Errors:**
  - Anything a Clojure program can catch, jank's object handler catches (the special form `try`; jank's book cpp-interop/native-exceptions.md).
  - The root cause's data is reachable through `ex-cause` (core.clj docstrings; Compiler.java 7381).
  - A failed require leaves no namespace behind (core.clj 5999–6007).
  - A delay runs once and rethrows the same exception (the delay docstring; Delay.java).
  - A future's failure is reported by deref (the future docstring; jank's book).
  - A def whose value threw leaves no metadata (DefExpr.eval).
  - `ex-info` takes a nil message and gives `{}` for nil data (ExceptionInfo.java 1.12).
  - `read-string` throws at EOF unless `:eof` is given (core.clj 3776; LispReader.read).
  - `*e` carries the compiler's data (clojure.main).
  - No reported error leaves a lock held or a frame pushed.
- **C API:**
  - An exception from a called fn reaches the caller (IFn.invoke).
  - An uncaught exception gives a non-zero exit (clojure.main).
  - nil names no namespace (Symbol/intern, Keyword/intern).
  - `c_api.h` compiles as C (its `extern "C"` guard).
- **jank.math:** a namespace jank installs on its module path loads.
- **Codegen:** the emitted program means what Clojure means (round 2's property 7: clojure.org's evaluation and special forms pages, Compiler.java).
- **nREPL:** every request gets replies ending in `done`, with no hang (rounds 2–3); `interrupt` answers as nREPL's session.clj does.
- **Regex:** every match equals java.util.regex's (Pattern.java; the javadoc's line terminators and boundaries).
- **Operators:** `cpp/<op>` calls what [over.match.oper] selects with C++'s value categories, is ill-formed when C++ is, and gives C++'s value.
- **`#inst`:** the accepted texts, the instant, `=`, `compare`, printing and the round trip are what clojure/instant.clj, java.util.Date and RFC 3339 give.
- **CHAMP:** the count, lookup and removal laws of a set or map (immer's documented semantics).

## 9. Search runs

"Complete n" means every timeline within the bounds was run.

- **Native:**
  - ld scripts against GNU ld, every script of ≤5 tokens over a 16-token alphabet: complete 1,118,481; 868 violate.
    - C3 (ld rejects the script, jank reads a file from it): 578.
    - C1 (several files, jank loads only the first): 108.
    - C4 (a quoted name with a parenthesis, jank reads nothing): 50.
    - C4e (a script naming no file): 42.
    - C2 (`-lz` taken as a path): 30.
    - C2s (`=/path` taken as relative): 30.
    - C5 (a backslash, jank loads another file): 30.
  - ≤4 tokens: complete 69,905; 19 violate.
  - Control, glibc-shaped scripts of ≤6 tokens: complete 137,257; nothing.
  - `-l` world: complete 82,944; 50,520 violate.
    - J1 (the AOT link rejects a `-l` the JIT loads): 23,464.
    - J4t (cantFail on a text file that is not an INPUT/GROUP script): 10,992.
    - J4m (cantFail on a script entry missing where jank looks): 10,976.
    - J4e (cantFail on an ELF dlopen refuses): 3,664.
    - J2s (the AOT link has files the JIT never maps): 1,202.
    - J2 (the JIT and the AOT link use different files): 222.
  - Round 4's AOT world, corrected: complete 384; 42 violate (27 V20, 15 U46).
- **Errors:**
  - World: complete 180; 57 disagree; 0 unexplained.
  - Nested world: complete 155; 136 disagree (V7 95, V12 34, the known native class 7); 0 unexplained.
- **Codegen:**
  - Restatement checks: every depth-1 timeline (3,464), the small depth-2 partitions, and 3,000 random depth-2 timelines; 0 differ.
  - Root kinds with ≤1 depth-1 subexpression: complete 47,501 per mode. eval: nothing. AOT: 7,076 violate, all R43.
  - Sub-world: complete 9,246,393 per mode, in two segments each. eval: nothing. AOT: 1,307,080 violate, all R43.
  - Root kind 6, eval: complete 11,999,296; nothing.
- **nREPL:**
  - Reduced T7: ≤0 64, ≤1 5,312, ≤2 218,400, all complete.
  - With eintr held at 0: ≤2 3,335 and ≤3 89,835 complete; ≤4 stopped at 688,909.
  - Stutter checks: 13,227 step runs.
  - T7 with at most one partial read: ≤0 16,384 and ≤1 1,392,512, complete.
  - World I: 72 cases; its World T rerun: 1,535,724 schedules.
  - Nothing was found anywhere.
- **Regex:**
  - uni2: 475,800 questions. V35 214, V36 479, R78 22,780, R81 1,594, S29 1,384; jank rejects 264,984.
  - mn3: 1,310,400 questions. V35 8,312, V36 4,200, R78 30,646, R81 1,132, S25 44.
  - Both are complete with 0 unexplained, and every answer was rerun on Clojure 1.12.0 / JDK 23: all identical.
- **Interop:**
  - World XXII: complete 3,056; 106 deviate, in 11 classes.
  - With every switch set to C++'s rule, 0 deviate.
  - The residual exhaust is complete over 3,056 with nothing found.
- **Core:**
  - `#inst` census: complete 3,512,418; 254,820 disagree; 0 unexplained.
  - Every string of length ≤6 over 10 characters: complete 1,111,111; 965 disagree.
  - Equality pairs: 128; 20 disagree.
  - Clojure's side was checked against 1.12.0's `read-instant-date` on all 3,512,418 inputs: 0 mismatches.

## 10. Theorems

No sorry, no native_decide, no new axiom. ★ marks a new for-every-input proof.

- **Native:**
  - Totality: ★ `parseText_total`, ★ `findClose_fuel`, ★ `findInputDirective_fuel`, ★ `readBare_fuel`, ★ `readQuoted_fuel`, ★ `scan_fuel`, `tryDirectives_some`, `skipSeps_ge`, `readQuoted_bounds`, `readBare_bounds`, `readToken_some`, `readToken_adv`.
  - Kernel-checked readings: `glibc_libc`, `two_files_first_only`, `lname_is_a_path`, `unbalanced_nothing`, `quoted_paren_nothing`, `as_needed_fallback`, `second_directive_ignored`.
  - C API: ★ `aot_main_throw_status_zero`, ★ `aot_dynamic_differs_iff`, ★ `aotRunR5_main_zero`, ★ `symbol_create_agrees_iff`, `symbol_nil_ns`, `keyword_nil_ns`, `clj_nil_ns`.
- **Errors:**
  - Handlers: ★ `object_catch_misses_error_ref`, `object_catch_misses_std`, ★ `default_catch_binds_nil`.
  - read-string: ★ `jank_read_string_never_object`, ★ `clj_read_string_throws_iff`, `read_empty_differs`.
  - Loading: ★ `load_module_converts`, ★ `jank_failed_require_keeps_ns`, ★ `clj_failed_require_removes_ns`, `jLoadLib_instance`.
  - delay: ★ `jank_delay_native_then_string`, ★ `jank_delay_err_runs`, ★ `clj_delay_once`, `clj_delay_once_after`.
  - future: ★ `jank_future_terminates`, ★ `jank_future_native_string`, ★ `clj_future_wraps`.
  - def: ★ `jank_def_meta_always`, ★ `clj_def_meta_none_on_raise`.
  - ex-info and `*e`: `ex_info_nil_message`, ★ `ex_data_of_nil_data`, ★ `star_e_of_error_ref`.
- **Codegen:**
  - Tree.lean: `DT.sumFin_congr`, `DT.sumFin_mul`, `DT.sumFin_const`, ★ `DT.leaves_bind_const`, `DT.leaves_pure`, `DT.bind_eq`, `DT.leaves_bind_const'`, ★ `DT.leaves_dec`, ★ `DT.leaves_pick`.
  - Gen.lean: `leaves_bind_eq`, `leaves_dec_bind`, ★ `leaves_localT`, ★ `leaves_leafT`, `ext_count`, ★ `leaves_fnKindT`, ★ `leaves_fnCallT`, ★ `leaves_kindT`, ★ `leaves_genT`, `world1`, `world2`.
  - Sub.lean: `bind_assoc`, ★ `leaves_pick_bind`, ★ `leaves_genK1`, `subWorld_size`.
- **nREPL:** ★ `chunking_independent`, ★ `readLoop_prefix`, ★ `readLoop_empty`, ★ `chunking_independent_all`, ★ `k_agrees`, ★ `parseK_sound`, `t7_k`, `t7_hyps`, ★ `t7_chunking_independent`.
- **Regex:** ★ `dfs_keeps_res`, ★ `searchFromFirst_fail_keeps_res`, ★ `search_found_from_initial_results`, ★ `search_fail_keeps_res`, `loop_found`.
- **Interop:** ★ `class_temporary_is_lvalue`, ★ `forwarding_deduction_record`, ★ `forwarding_deduction_builtin`, ★ `temporary_forwarding_deduces_lref`, ★ `member_call_args_lvalue`, `nonmember_call_moves`, ★ `named_builtin_local_is_prvalue`, `usingTargets_append`, ★ `jank_getOperator_ignores_namespace_using`, `norm_record`, ★ `base_acting_context_not_exact`, ★ `using_member_acting_context_exact`, ★ `templates_pass_arity`.
- **Core:**
  - `#inst`: `z_rejected`, `z_clojure`, `leap_rejected`, `leap_clojure`, `frac11_shifts`, `frac11_clojure`, `prefrac_jank`, `prefrac_clojure`, `submilli_jank_ne`, `submilli_clojure_eq`, `offset_agrees`, `date_agrees`, ★ `dispatch_differs_iff`.
  - CHAMP: ★ `added_doAdd`, ★ `size_add`, ★ `added_doAddMut`, ★ `size_addMut`, ★ `doSub_absent`, ★ `sub_absent`, ★ `doSubMut_absent`, ★ `subMut_absent`, ★ `doSub_found`, ★ `size_sub`, ★ `makeMerged_wf`, ★ `doAdd_wf`, ★ `add_wf`, `empty_wf`, ★ `size_add_add`, ★ `get_add_add`, ★ `doSub_ok`, ★ `get_sub`, `r55_stored_twice`, `r55_never_found`, `control_stored_once`.

## 11. Library gaps (built in the project; sdk/lean untouched)

- An exception model: thrown values with C++ handler matching, and a process-ending outcome (`std::terminate`) beside value and exception.
- A file-system model with kinds (loadable ELF, refused ELF, ld script, text, archive), and a two-linker comparison.
- Fuel-indexed loops with sufficiency proofs, so byte-level C++ loops reduce in the kernel.
- A decision-tree monad (`DT`) with exact timeline counts and resumable depth-first visiting. A generator written with the sdk's `EStateM` decisions can't be counted or reasoned about, and a `partial` one blocks every proof.
- Kernel-evaluable copies of `partial` parsers, proved to agree with the originals.
- Independence, simulation and process-state equality, which World T's reduction needs, can't be expressed with the sdk's `Threads`, so steps 3–5 stay argued.
- A JVM checker for every census answer (EDN dumps rerun on Clojure 1.12.0).

## 12. Tests

- **The test file.** `tests/jank_lean/deviations_r5_test.jank` (namespace `jank-lean.deviations-r5-test`) holds 49 deftests, one per prediction, with b/c variants for multi-program items and one control (v19b). v08 and v09 load the fixture modules `tests/jank_lean/r5_errors_fixture_a.cljc` and `_b.cljc`.
- **No hangs file**, because no test predicts a hang.
  - The one never-answered case (V37, after a diverging eval) needs a socket and has shell steps.
  - v12 predicts an abort, so each test must run in its own process.
- **Clojure check.** Translated as round 4's was:
  - `cpp/jank.runtime.object_ref` → `Throwable`;
  - `(thrown? (` → `(thrown? Throwable (`;
  - `cpp/std.exception` → `Exception`;
  - `cpp/jank.error_ref` → `Error`;
  - jank-only deftests dropped (`.r5-scratch/clj-final/`).
  - Result: 29 tests, 43 assertions, all passing on Clojure 1.12.0 (`.r5-scratch/clj-final-run-1.12.0.txt`).
- **Jank only, and why:**
  - v03, v19, v19b, v21 and v21b reach jank's C++ (the JIT, the C API) through cpp/raw. Their Clojure counterparts (System/load, IFn.invoke, Symbol/intern, Keyword/intern) pass on 1.12.0 (`results/r5-native-clj.txt`).
  - v18, v37 and v37b call jank's nREPL handler in-process; nREPL 1.8.0's answers were measured on the JVM.
  - v24 is about jank's own namespace.
  - v25–v34 are C++ interop.
- **No test-file form**, with shell steps in the area reports instead:
  - V1, V2, V4, V5, V6 (libraries, scripts, objects, a second process);
  - V20 (an exit status);
  - V22 (a C compile);
  - V23 (process stdout);
  - V37's never-answered case.
- **Rules followed:**
  - each test asserts Clojure's result (C++'s for interop, nREPL's for the nREPL);
  - values pass through fns;
  - each `cpp/raw` runs in its own eval;
  - error predictions observe which handler sees the error (`vb-outcome`), since `thrown?` sees only objects (V7);
  - `#inst` literals are read at run time;
  - strings with combining marks or U+2028 are written as `\u` escapes. Run them under a UTF-8 locale with en_US.UTF-8 installed (coreA5-1).

## 13. Files

- **Models:** `Jank/R5/<Area>/` (Native, Errors, Codegen, Nrepl, Regex, Interop, Core, Coord).
- **Drivers:** `Run/R5/<Area>.lean`, built as the exes `jank5-native`, `-errors`, `-codegen`, `-nrepl`, `-regex`, `-interop`, `-core` and `-coord`.
- **Results:** `results/r5-<area>-report.txt` (each area's full report), `results/r5-*.txt` (the runs), `results/r5-catchup.txt`, `results/r5-coord-math.txt`.
- **Licenses:** `Jank/R5/Regex/` and the `#inst` files of `Jank/R5/Core/` translate libstdc++, so they are GPL-3.0-or-later with the GCC Runtime Library Exception (each folder's README.md, LICENSE and COPYING.RUNTIME). See NOTICE.md.
- **Changed outside round 5's own files:**
  - `lakefile.toml` (8 exes);
  - `README.md`;
  - `NOTICE.md`;
  - `fetch-sources.sh` (upstream-r5, the chrono files, binutils ld);
  - `.gitignore` (`.r5-scratch/`, `upstream-r5/`);
  - section 7 of `results/r5-codegen-report.txt`, filled from its run files.
- **Scratch:** `.r5-scratch/` holds the area scratch, the test assembly script and map, and the Clojure translation and its run.
- **Rule notes:**
  - Area agents fetched nREPL 1.8.0 from Clojars and OpenJDK 23's regex sources, as specifications.
  - Machine-wide job-slot contention held several builds for 40 minutes or more. T7 ≤4 and part of the codegen walk stopped for that reason.
  - The directory grew by about 0.1 GB this round.
- No commits were made.

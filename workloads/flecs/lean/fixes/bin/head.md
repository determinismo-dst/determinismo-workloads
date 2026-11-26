# Fixes for the flecs v4.2.0 findings

Proposed changes to flecs v4.2.0 for the findings in `REPROS.md` (F1–F58, from the Lean replica's reports `REPORT.md` to `REPORT-8.md`). Each patch is a `git diff` against the release's `src/` (and `include/` where a public header changes) and applies to a clean v4.2.0 with `git apply`.

Not patched here, as asked: F10 (open issue #2363), F15 (fixed by PR #2417, after v4.2.0) and F24 (open PR #2397).

## Summary

- **Fixed, one patch each:** F1 (also F2), F3, F4, F5, F6, F7, F8, F11, F12, F16, F17, F18 (also F19), F20, F21, F22, F23, F25 (also F27), F26, F27, F29 (also F34), F31, F32, F33, F36, F38, F39, F40, F41, F42, F43, F44, F45, F46, F47, F48, F49, F50, F51, F52, F53, F54, F55, F56, F57, F58.
- **Patches shared by two findings:**
  - `F1.diff` fixes F1 and F2;
  - `F18.diff` fixes F18 and F19;
  - `F29.diff` fixes F29 and F34;
  - `F25.diff` contains `F27.diff`'s change. Apply one of them: `F25.diff` fixes both.
  - `F48.diff` is a copy of `F42.diff`: F42's change fixes F48 too. Apply one of them.
  - `F55.diff` is a copy of `F46.diff`: F46's change fixes F55 too. Apply one of them.
- **F47** is fixed in the code (the pipeline sorts before the workers start), not only in the documentation; its section says why.
- **F53** is fixed in the code too (the pipeline computes the changed state before the workers start), with the comments of `ecs_iter_changed` and `ecs_iter_skip` in flecs.h updated; its section says why not only the documentation.
- **No fix:** F9, F13, F14, F28, F30, F35 and F37 (see "Findings without a fix" at the end).

## Layout

- `fixes/F<n>.diff`: one patch per finding (or per shared change).
- `fixes/checks/*.c`: extra programs used to check a fix beyond the finding's own test (each section names its own).
- `fixes/attempts/*.diff`: changes that were tried and dropped, for F9 and F37.
- `tests/`: unchanged copies of `tests/flecs_lean` and its `README.txt` (rounds 1–8).
- `orig/flecs-4.2.0/`: the untouched release (read-only), from `https://github.com/SanderMertens/flecs/archive/refs/tags/v4.2.0.tar.gz` (sha256 `4107b0a36aa25f80ddcd6f939451ccfe1bacafcccdd2695840a4a8c413d05b40`).
- `work/F<n>/`: the edited `src/` and `include/` copies the patches were made from; `work/ALL/` is the combined tree of `fixes/all-fixes.diff`.
- `bin/`: the scripts named below. `bin/chk.sh` runs a program of `fixes/checks` against a build; `bin/run-check.sh` runs one on v4.2.0 and on a patch's build. `bin/build-diff.sh` builds a patch's amalgamation and object, `bin/build-mode.sh` an object with extra flags, `bin/runtests-mode.sh` runs tests built with those flags. Compiles and suite runs hold one of the machine's four job slots (`bin/slot.sh` calls `~/dev/.lean-jobs/job`).
- `build/asan/` and `build/tsan/`: the AddressSanitizer builds used for F46, F55 and F56 (`ASAN_MODE=` selects the default allocator instead of `FLECS_USE_OS_ALLOC`) and the ThreadSanitizer release builds used for F47 and F53 (`bin/asan-build.sh`, `bin/asan-run.sh`, `bin/tsan-build.sh`, `bin/tsan-run.sh`, `bin/tsan-pairs.py`).
- `build/modes/<name>/summary.txt`: round 8's tests in the build modes they need (`bin/verify-modes.sh`), for v4.2.0 (`orig`), F53, F55, F56, F58 and every patch (`together`).
- `build/verify/F<n>/summary.txt` and `build/verify/together/summary.txt`: the output of the final checks. `build/orig/suites/*.log` holds the baseline runs.

## How each patch was checked

Every patch was checked from its final `fixes/F<n>.diff` alone (`bin/verify-one.sh`):

1. `git apply --check` against a fresh copy of v4.2.0's `src/` and `include/`.
2. The same hunks applied to the amalgamation: `bin/apply2distr.py` finds each hunk's old text in `distr/flecs.c` (or `distr/flecs.h`), widening it with the source file's surrounding lines until it occurs once, and replaces it.
3. The finding's C tests, built against the patched amalgamation in two ways: linked with a patched `flecs.o`, and with the one-step command `cc -std=gnu99 -O1 -g -I distr <test>.c distr/flecs.c -lm -lpthread`. Both builds of every test exit 0.
4. The same tests built against the unpatched release still fail. The section of each finding gives the output.
5. flecs's own test suites, built against the patched amalgamation (see "flecs's suites").
6. For memory and thread findings, sanitizer builds of the same amalgamation: AddressSanitizer with `FLECS_USE_OS_ALLOC` (F46, F55, F56) and with the default allocator (F55, F56), ThreadSanitizer in a release build (F47, F53).
7. Round 8's tests that need other builds were also run in them, on v4.2.0 and on the patch (`bin/verify-modes.sh`): `-DNDEBUG` for F53, F55, F56 and F58, `-DFLECS_USE_OS_ALLOC` and `-DFLECS_SANITIZE` for F55's leak test.

The test programs are the ones in `tests/` (debug builds, asserts on, macOS arm64, Apple clang). One test checks two findings: `parent_storage_dont_fragment_events.c` has the Parent forms of F48 (part b) and F50 (part a), so it exits 0 only with both patches; each section gives its own part's output.

## flecs's suites

- **Suites run:** core, query, addons, collections and cpp (the C++ API). They are built from the release's `test/` sources and their generated `main.c` files, against the amalgamation compiled with `-O1 -g` (asserts on), and run with `-j 2`.
- **Test harness:** bake 3's standalone harness (`templates/test_harness/bake_test.c` from a local bake 3 checkout). The bake 2 runtime installed on this Mac lacks `test_param`, which v4.2.0's suites use.
- **Not run:** meta, script and cpp_addons. No patch touches the meta, script or C++ addon sources.
- **Baseline on unpatched v4.2.0:**
  - core 3870 pass / 0 fail;
  - query 4798 pass / 6 fail;
  - addons 643 / 0;
  - collections 97 / 0;
  - cpp 1919 / 0.
- **The 6 query failures:** `Sparse.ecs_field_on_sparse_self`, `Sparse.ecs_field_on_sparse_up` and `DontFragment.ecs_field_on_dont_fragment_up`, each with `cache_kind` default and auto. Each test calls `test_expect_abort()` and then reaches flecs's documented INVALID_OPERATION assert. This harness counts the abort as a failure. They fail identically on every build here.
- **"Unchanged" in a section** means the same pass and fail counts and the same failing tests as this baseline. The per-patch results are in `build/verify/F<n>/summary.txt`.

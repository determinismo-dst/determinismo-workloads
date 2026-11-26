# A Lean replica of jank

jank (jank-lang/jank) replicated in Lean 4 from its sources, function by function, and searched
against Clojure's documented behavior under determinismo's Lean library (`sdk/lean` of
determinismo-dst/determinismo, pinned in `lakefile.toml`). It was written blind: from jank's
code and documentation, without our earlier findings. Each deviation it predicts was then tested
on the real jank.

## Rounds

- **Round 1** (jank f3d82d654, then main 7135b7708): numbers, hashing, equality, transients,
  atoms, delays, dynamic bindings, `try` (D1–D25), and the reader (R1–R21).
  [REPORT.md](REPORT.md).
- **Round 2** (main 7135b7708): the analyzer, the code generator, C++ interop, strings,
  printing and regex, core functions, the nREPL server (R22–R140). [REPORT-2.md](REPORT-2.md).
- **Round 3** (main 7135b7708): the libraries jank runs on, replicated from their pinned sources
  (Boost.Multiprecision, immer, libstdc++'s regex, folly, bdwgc, CppInterOp and Clang), the
  compiler's flags, and the nREPL server wired to the reader and evaluator (S1–S76), with
  corrections to rounds 1 and 2. [REPORT-3.md](REPORT-3.md).
- **Round 4** (main 7135b7708): the feedback from round 3's run, what round 3 left out, and the
  parts no round had touched: lazily compiled fns and thread bindings, C++ operator lookup and
  class templates, collection objects, regex captures and matchers, the nREPL's positions and the
  terminal REPL, module loading, AOT and the CLI, the clojure.core functions and bundled
  namespaces no round covered, jank.shell and clojure.pprint (U1–U92). [REPORT-4.md](REPORT-4.md).
- **Round 5** (main 94d32623, whose compiler+runtime tree is 7135b7708's): the catch-up (no
  replicated function changed), native object and ld-script loading, what a program sees of an
  error, the C API, jank.math, C++ operator templates and value categories, Unicode in regex, the
  nREPL's interrupt, `#inst`, CHAMP laws, and proofs for the codegen control, the nREPL's T7 and the
  regex executor (V1–V48). Tests: [tests/jank_lean/deviations_r5_test.jank](tests/jank_lean/deviations_r5_test.jank).
- **Round 6** (main 94d32623): the lesson of three deviations the generated differential tests found
  (LG1: `count`'s unsigned `usize` in `<`, `min`, `max`; LG2: long overflow; LG3: `subs` on bytes),
  the numeric tower whole on every path a number takes (literal, `let`, fn value, native producers
  such as `count`, `hash`, `int`, `float`), strings and characters against UTF-16, CHAMP's `get` of
  another key and iteration (proved), the nREPL's T7, T3 and T9 by exact state graphs, and 181 local
  fixes for confirmed deviations of rounds 1–5 and LG1–LG2 as diffs against 94d32623 (`fixes/`, with one combined
  patch in `fixes/combined/`). LG1–LG3 extended, V49–V85. [REPORT-6.md](REPORT-6.md). Tests:
  [tests/jank_lean/deviations_r6_test.jank](tests/jank_lean/deviations_r6_test.jank).
- **Round 7** (main 94d32623): the three regressions the real jank showed in round 6's combined patch, traced
  and fixed in their diffs (S40's checked `int` against `case`'s int mode, which also fixes R44; D8's exact
  `=` exposing inexact BigDecimal division, now exact in a new S2; R23, R24, R26 and U75 against five of
  jank's own suite files), BigDecimal arithmetic with Java's scale, unchecked ops and bit operations, native
  values (`zero?`/`abs` of a char, x86-64's default NaN on new paths, `dotimes` past 2^31), Unicode's
  SpecialCasing in full, CHAMP's law 1 without the invariant and the transient sequence theorem (proved),
  jank's `=` and hash across kinds in hash sets, `case` on hash collisions, local fixes round 6 left
  unwritten, and a differential test generated from the replica's models (639 forms, each verdict
  predicted). [REPORT-7.md](REPORT-7.md). Tests:
  [tests/jank_lean/deviations_r7_test.jank](tests/jank_lean/deviations_r7_test.jank) (and its hangs file),
  [tests/jank_lean/generated_r7_test.jank](tests/jank_lean/generated_r7_test.jank); what to check on the next
  build of the combined patch: [fixes/combined/CHECK.md](fixes/combined/CHECK.md).
- **Round 8** (main 94d32623): round 7's patch on the real jank reconciled with every prediction (the
  build failure, `long` used before its definition, folded into S40 with a checker for the whole class;
  each "should pass", each fail/error change, the 169 generated tests still failing, and x8's stock
  model, now boost's cpp_dec_float<100> replicated limb by limb with S4's exact digit rule); BigDecimal
  as Java's own (unscaled integer and scale) with `with-precision`; Java's case mapping in full; local
  fixes for chars and bools as numbers, the signed hash, read errors as exceptions, unchecked int ops and
  `rationalize`, `rem` of doubles, min/max, BigInt-double comparison; CHAMP's law 1 for the transient
  steps and transients against persistent steps node by node (proved); the nREPL's T3 decided under
  every schedule by an exact graph, diverging evals, interrupt and stdin inside World T, and the sdk's
  walk proved. [REPORT-8.md](REPORT-8.md). Tests:
  [tests/jank_lean/deviations_r8_test.jank](tests/jank_lean/deviations_r8_test.jank).

## What the real jank said

- **Rounds 1 and 2**: 120 predictions as tests ([tests/](tests/)), run on jank main 7135b7708
  (x86-64 Linux, UTF-8 locale, each test in its own process with a 600 s limit) and on Clojure
  1.11.1.
  - 104 confirmed: jank did exactly what the replica predicted.
  - 8 refuted: D3, D11, D14, D16b, D20, R45, R123, and one control. D11, D14 and D20 were fixed
    after jank 0.1, as round 2 predicted.
  - 3 failed in another way than predicted: D15, D23, R89. 1 unclear: R54.
  - 4 left without a result: b01, b11, b24, b29. Their failure reports hold invalid UTF-8 or a
    NUL, which the test runner's `grep` read as a binary file and dropped (fixed since).
  - Each test's evidence: [validation/round-1-2-evidence.txt](validation/round-1-2-evidence.txt).
- **Round 3**: 57 tests run on jank main 7135b7708 (UTF-8 locale, each test in its own process
  with a 120 s limit), each passing on Clojure 1.11.1 except the C++ interop ones.
  - 48 confirmed (4 of them from an error whose text the report doesn't carry: S1, S36, S37,
    S42). Among them a crash (S34: a long input to a regex segfaults) and the five predicted
    hangs (S62, S63, S64, S65, S67).
  - S50 and S53 also failed with an error, first counted as confirmations: their tests ran a
    `cpp/raw` and its use as one form, which jank analyzes whole (S71), so the error says
    nothing about them. Round 4 re-tests them (U5, U6).
  - 4 refuted: S2, S9, S44, S69 (jank gave Clojure's result).
  - 3 failed in another way than predicted: S49 and S57 (an error where a wrong value was
    predicted), S70 (jank prints an unbound root its own way; no freed memory seen).
  - b01, b11, b24, b29 again without a result, for the same reason: to rerun.
  - Each test's evidence: [validation/round-3-evidence.txt](validation/round-3-evidence.txt).
- **Round 4** re-read the round-3 feedback: S2, S9 and S44's tests could not see the predicted
  values (jank's `=` on BigDecimals is D8's epsilon; S44's test used metadata the strip pass keeps),
  S49 and S57's tests (and S50, S53's) analyzed a `cpp/raw` and its use as one form (S71), S69's
  test threw inside the fn that runs the finally, and S70's asserted a text jank never prints. Its
  87 tests ([tests/jank_lean/deviations_r4_test.jank](tests/jank_lean/deviations_r4_test.jank) and
  the hangs file) are not yet run on jank; the 72 that need no C++ interop or jank-only namespace
  pass on Clojure 1.12.0 (1.11.1: all but u69, a 1.12 change).

- **Round 4**: 91 tests run on jank main 7135b7708 (round 4's 87 and round 2's 4 left without a
  result), UTF-8 locale, each in its own process with a 120 s limit.
  - Round 2's b01, b11, b24, b29: all 4 confirmed, so rounds 1 and 2 stand at 108 of 120.
  - Round 4, 82 with a result: 61 confirmed by the value or error predicted (U7b, a control,
    passed as predicted), the 5 predicted hangs (U13, U13b, U19, U28, U28b) and U26's segfault;
    8 failed with an error whose text the runner didn't record (U5, U6, U12, U17, U21, U22, U48,
    U59) and 3 with a cut text (U72, U73, U74b), each where an error was predicted; U74's
    evidence was another test's, and U88-U90 (jank.shell) failed with an error, none predicted.
  - U64, U79, U80, U81, U82 left no result: a failure text spanning lines broke the runner's
    report and swallowed the next testcase (fixed since). They, and the errors without text,
    are rerun with the runner reporting jank's error text.
  - Each test's evidence: [validation/round-4-evidence.txt](validation/round-4-evidence.txt).

- **Round 5**: its 40 predictions with a test, run on jank main 7135b7708 (compiler+runtime
  byte-identical to 94d32623; a coverage build on Linux, each test in its own process): all behaved as
  predicted.
- **Generated differential tests** (random clojure.core forms against Clojure 1.12) found three
  deviations no round's test had shown: LG1 (`count`'s `usize` compared unsigned in `<`, `>`, `min`,
  `max`), LG2 (long overflow wraps or gives a BigInt where Clojure throws) and LG3 (`subs` indexes
  bytes; round 2's R52 had predicted it, but its test recorded only its first assertion). Round 6
  starts from that lesson.
- **Round 6**: on jank main 7135b7708 (Linux x86-64, each test in its own process), 53 deviations of
  deviations_r6_test.jank confirmed, both controls passing, and all 55 Clojure-runnable tests passing on
  Clojure 1.12.3. With fixes/combined/all.diff applied, 182 of 358 replica tests passed (16 on stock), with
  three regressions that round 7 traces and fixes: deviations_main_test no longer loaded (S40), s02 failed
  (D8), and 5 of jank's 551 pass- files failed (R23, R24, R26, U75).
- **Round 7**: with round 7's combined patch (after moving `long` above `dotimes`), 737 of 1,068 replica
  and generated tests passed (370 on stock); jank's suite 549 of 551 on stock and patched alike. All 639
  generated verdicts on stock were as predicted; round 7's 71 new tests as predicted on stock except x8.
  Round 8 reconciles every difference (REPORT-8 section 1).

The confirmed findings, each with a minimal example and jank's and Clojure's results, are in
jankifier's [specs/unreported.md](https://github.com/pfeodrippe/jankifier/blob/main/specs/unreported.md#found-by-a-lean-replica-of-jank).

## Building and running

With [elan](https://github.com/leanprover/elan) installed (it takes the Lean version from
`lean-toolchain`; Lake fetches determinismo's Lean library at the commit `lakefile.toml` pins):

```sh
lake build
lake exe jank-model          # round 1's searches
lake exe jank-reader         # round 2's drivers: jank-<component>
lake exe jank3-boost         # round 3's: jank3-<area>
lake exe jank4-runtime       # round 4's: jank4-<area> (feedback, runtime, interop, immer, regex,
                             # nrepl, modules, core)
lake exe jank5-errors        # round 5's: jank5-<area> (native, errors, codegen, nrepl, regex,
                             # interop, core, coord)
lake exe jank6-coord         # round 6's: jank6-<area> (num, native, str, champ, nrepl, coord)
lake exe jank7-coord         # round 7's: jank7-<area> (num, native, champ, gen, coord)
lake exe jank8-coord         # round 8's: jank8-<area> (fix, dec, boost, champ, nrepl, coord)
```

`./fetch-sources.sh` puts the sources the replica translates next to it, at the commits it was
written against (git-ignored): jank in `upstream/` (f3d82d654), `upstream-main/` (7135b7708) and
`upstream-r5/` (94d32623),
and in `deps/` the libraries jank pins (immer 282629d0, boost-multiprecision 2b3ab082, bdwgc
327ef1f8, CppInterOp 28b0830d, folly e54ca53d, and since round 4 boost-process e4d0d405, json
02dfbea3, stduuid 3afe7193), libstdc++ 15.3.0's regex, (since round 5) `<chrono>` and (since round 6)
`codecvt` files, and
GNU ld 2.45's script grammar. Only
`jank3-boost`'s header check reads one of them at run time; the others are for following the
reports' line numbers. The LLVM 23.1.0 files CppInterOp reaches are read only (llvm-project at
llvmorg-23.1.0).

One test on jank, in its own process:

```sh
cd tests
jank --module-path . run-main run-one -- jank-lean.deviations-test d02-integer-division-is-a-ratio
```

The tests assert Clojure's result, so they fail on jank where it deviates. On Clojure they pass
once `cpp/jank.runtime.object_ref` becomes `Throwable` and `(thrown? (…))` becomes
`(thrown? Throwable (…))`.

## License

Mozilla Public License 2.0 ([LICENSE](LICENSE)), as jank's. The regex replica
(`Jank/R3/Regex/`, `Jank/R4/Regex/`, `Jank/R5/Regex/` and their drivers) and the `#inst` replica
(`Jank/R5/Core/Inst.lean`, `InstSearch.lean`, `Run/R5/Core.lean`) and the `codecvt` replica
(`Jank/R6/Str/Cut.lean`, `Search.lean`, `Run/R6/Str.lean`) translate libstdc++ and are under
GPL-3.0-or-later with the GCC Runtime Library Exception (each folder's README.md). [NOTICE.md](NOTICE.md) lists every
project translated here.

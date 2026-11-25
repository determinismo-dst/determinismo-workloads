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

## What the real jank said

- **Rounds 1 and 2**: 120 predictions as tests ([tests/](tests/)), run on jank main 7135b7708
  (x86-64 Linux, UTF-8 locale, each test in its own process with a 600 s limit) and on Clojure
  1.11.1.
  - 104 confirmed: jank did exactly what the replica predicted.
  - 8 refuted: D3, D11, D14, D16b, D20, R45, R123, and one control. D11, D14 and D20 were fixed
    after jank 0.1, as round 2 predicted.
  - 3 failed in another way than predicted: D15, D23, R89. 1 unclear: R54.
  - 4 left unrun (their time went to tests that hung).
  - Each test's evidence: [validation/round-1-2-evidence.txt](validation/round-1-2-evidence.txt).
- **Round 3**: 57 tests, each passing on Clojure 1.11.1 except the 4 C++ interop ones; not yet
  run on jank.

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
```

`./fetch-sources.sh` puts the sources the replica translates next to it, at the commits it was
written against (git-ignored): jank in `upstream/` (f3d82d654) and `upstream-main/` (7135b7708),
and in `deps/` the libraries jank pins (immer 282629d0, boost-multiprecision 2b3ab082, bdwgc
327ef1f8, CppInterOp 28b0830d, folly e54ca53d) and libstdc++ 15.3.0's regex files. Only
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
(`Jank/R3/Regex/`, `Run/R3/Regex.lean`) translates libstdc++ and is under GPL-3.0-or-later with
the GCC Runtime Library Exception (that folder's README.md). [NOTICE.md](NOTICE.md) lists every
project translated here.

# License of this folder: GPL-3.0-or-later with the GCC Runtime Library Exception 3.1

The files in this folder, and `Run/R5/Regex.lean`, extend round 3's and round 4's regex replicas
(`Jank/R3/Regex/`, `Jank/R4/Regex/`), which replicate libstdc++ 15.3.0's regex implementation line
by line as jank reaches it through `std::regex`. They import and reuse those replicas, so they are
distributed under the same terms: [LICENSE](LICENSE) (GPL-3.0) and
[COPYING.RUNTIME](COPYING.RUNTIME) (the exception).

- `ExecInv.lean`: proofs about the replica of libstdc++'s DFS executor (`_M_results` is kept until
  a solution).
- `JavaM5.lean`: round 4's java.util.regex specification model (written from the `Pattern`/`Matcher`
  documentation and JDK 23's behaviour, checked against a JVM; it copies no JDK code), with Java's
  word-boundary rule for non-spacing marks, `(?U)`'s word class and `\p{…}` properties.
- `Compare5.lean`: the questions, both sides, and the classifying toggles.

The rest of the project is under the Mozilla Public License 2.0 (`../../../LICENSE`), as jank is.

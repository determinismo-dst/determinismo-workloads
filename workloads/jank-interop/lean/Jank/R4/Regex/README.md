# License of this folder: GPL-3.0-or-later with the GCC Runtime Library Exception 3.1

The files in this folder, and `Run/R4/Regex.lean`, extend round 3's regex replica
(`Jank/R3/Regex/`), which replicates libstdc++ 15.3.0's regex implementation line by line as jank
reaches it through `std::regex`. They import and reuse that replica, so they are distributed under
the same terms: [LICENSE](LICENSE) (GPL-3.0) and [COPYING.RUNTIME](COPYING.RUNTIME) (the
exception). The java.util.regex side (`JavaM.lean`) is a specification model written from the
`Pattern`/`Matcher` documentation and checked against a JVM; it copies no JDK code.

The rest of `lean/` is under the Mozilla Public License 2.0 (`../../../LICENSE`), as jank is.

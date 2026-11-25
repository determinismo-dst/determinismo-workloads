# Licenses of this folder

- `Inst.lean`, `InstSearch.lean` (and the driver `Run/R5/Core.lean`, which imports them):
  GPL-3.0-or-later with the GCC Runtime Library Exception 3.1 ([LICENSE](LICENSE),
  [COPYING.RUNTIME](COPYING.RUNTIME)). `Inst.lean` replicates, line by line as jank reaches it,
  libstdc++ 15.3.0's `std::chrono::parse` (`bits/chrono_io.h`: `_Parser::operator()`, its digit and
  character readers, `from_stream` for `sys_time`) and `basic_istream::peek` with its sentry
  (`bits/istream.tcc`). The Clojure side (`clojure.instant`, `LispReader.readTagged`) is a
  specification model checked against Clojure 1.12.0 on the JVM; it copies no Clojure code.
- `ChampLaws5.lean`, `ChampWf5.lean`: proofs over round 3's replica of immer's CHAMP; Mozilla Public
  License 2.0 (`../../../LICENSE`), as the rest of the project and jank.

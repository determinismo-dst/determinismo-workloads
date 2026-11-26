# Licenses of this folder

- `Cut.lean` (and `Search.lean` and the driver `Run/R6/Str.lean`, which import it): GPL-3.0-or-later
  with the GCC Runtime Library Exception 3.1 ([LICENSE](LICENSE), [COPYING.RUNTIME](COPYING.RUNTIME)).
  `Cut.lean` replicates, as jank's `upper-case` and `lower-case` reach it, libstdc++ 15.3.0's
  `std::wstring_convert<std::codecvt_utf8<wchar_t>>::from_bytes` (`bits/locale_conv.h`:
  `__do_str_codecvt`, `from_bytes`; `src/c++11/codecvt.cc`: `read_utf8_code_point`, `ucs4_in`).
- `Proofs.lean`, `SeqCount.lean`, `Fixes.lean`: jank's string functions and Java's String and
  Character side by side (Java's side is a specification model checked against Clojure 1.12.0 on the
  JVM; it copies no JDK code); Mozilla Public License 2.0 (`../../../LICENSE`), as the rest of the
  project and jank.

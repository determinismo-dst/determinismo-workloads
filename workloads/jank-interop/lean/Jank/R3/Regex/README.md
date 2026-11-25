# License of this folder: GPL-3.0-or-later with the GCC Runtime Library Exception 3.1

The files in this folder, and `Run/R3/Regex.lean`, replicate libstdc++ 15.3.0's regex
implementation (`regex_scanner`, `regex_compiler`, `regex_automaton`, `regex_executor`,
`regex.tcc`, `regex_traits`) line by line, as jank reaches it through `std::regex`. libstdc++ is
licensed under the GNU General Public License version 3 or later with the GCC Runtime Library
Exception, version 3.1, so these files are distributed under the same terms: [LICENSE](LICENSE)
(GPL-3.0) and [COPYING.RUNTIME](COPYING.RUNTIME) (the exception).

The rest of `lean/` is under the Mozilla Public License 2.0 (`../../../LICENSE`), as jank is.

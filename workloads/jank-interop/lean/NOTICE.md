# Notice

This replica translates, function by function, code from these projects (pinned versions in
README.md). Each part follows its project's license:

- **jank** (jank-lang/jank, Mozilla Public License 2.0): the whole replica; `lean/` is under the
  same license ([LICENSE](LICENSE)).
- **libstdc++** (GCC 15.3.0, GPL-3.0-or-later with the GCC Runtime Library Exception 3.1): the
  regex replica, `Jank/R3/Regex/` and `Run/R3/Regex.lean`, under those terms (that folder's
  README.md, LICENSE and COPYING.RUNTIME).
- **Boost.Multiprecision** (Boost Software License 1.0): `Jank/R3/Boost/` (cpp_int and
  cpp_dec_float).
- **immer** (Boost Software License 1.0): `Jank/R3/Immer/` (the RRB vector and CHAMP).
- **folly** (Apache License 2.0): `Jank/R3/Runtime/` (SharedMutex, fbvector).
- **bdwgc** (the Boehm-Demers-Weiser GC license, MIT-style): `Jank/R3/Runtime/` (reachability,
  descriptors).
- **CppInterOp** and **Clang/LLVM** (Apache License 2.0 with LLVM exceptions):
  `Jank/R3/Interop/` and `Jank/R3/Codegen/`.
- **Clojure** (Eclipse Public License 1.0): the specification side, Clojure's behavior as
  documented and as its sources implement it.

# Notice

This replica translates, function by function, code from these projects (pinned versions in
README.md). Each part follows its project's license:

- **jank** (jank-lang/jank, Mozilla Public License 2.0): the whole replica; `lean/` is under the
  same license ([LICENSE](LICENSE)).
- **libstdc++** (GCC 15.3.0, GPL-3.0-or-later with the GCC Runtime Library Exception 3.1): the
  regex replica, `Jank/R3/Regex/`, `Jank/R4/Regex/`, `Run/R3/Regex.lean` and `Run/R4/Regex.lean`,
  under those terms (each folder's README.md, LICENSE and COPYING.RUNTIME).
- **Boost.Multiprecision** (Boost Software License 1.0): `Jank/R3/Boost/` (cpp_int and
  cpp_dec_float).
- **immer** (Boost Software License 1.0): `Jank/R3/Immer/` and `Jank/R4/Immer/` (the RRB vector
  and CHAMP, and their `_mut` paths).
- **folly** (Apache License 2.0): `Jank/R3/Runtime/` (SharedMutex, fbvector), reused by
  `Jank/R4/Runtime/`.
- **bdwgc** (the Boehm-Demers-Weiser GC license, MIT-style): `Jank/R3/Runtime/` (reachability,
  descriptors) and `Jank/R4/Runtime/` (stack scanning).
- **CppInterOp** and **Clang/LLVM** (Apache License 2.0 with LLVM exceptions):
  `Jank/R3/Interop/`, `Jank/R3/Codegen/` and `Jank/R4/Interop/` (GetOperator, BestOverloadMatch,
  InstantiateTemplate, TryObjectArgumentInitialization).
- **Boost.Process** (Boost Software License 1.0): `Jank/R4/Feedback/Shell.lean` (v1's
  `build_args` and its POSIX pipe handling, as `jank.shell` reaches them).
- **stduuid** (MIT): `Jank/R4/Core/Uuid.lean` (`uuid::from_string`).
- **nlohmann json** (MIT): `Jank/R4/Core/Json.lean` (the number lexer's outcome, `get<i64>`,
  `dump_float`).
- **Clojure** (Eclipse Public License 1.0): the specification side, Clojure's behavior as
  documented and as its sources implement it; **clojure.data.json** 2.5.2 (EPL 1.0) likewise for
  jank's port of it.

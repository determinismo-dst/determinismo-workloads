# Notice

This replica translates, function by function, code from these projects (pinned versions in
README.md). Each part follows its project's license:

- **jank** (jank-lang/jank, Mozilla Public License 2.0): the whole replica; `lean/` is under the
  same license ([LICENSE](LICENSE)).
- **libstdc++** (GCC 15.3.0, GPL-3.0-or-later with the GCC Runtime Library Exception 3.1): the
  regex replica, `Jank/R3/Regex/`, `Jank/R4/Regex/`, `Jank/R5/Regex/`, `Run/R3/Regex.lean`,
  `Run/R4/Regex.lean` and `Run/R5/Regex.lean`, and the `#inst` replica of `<chrono>`'s parser,
  `Jank/R5/Core/Inst.lean`, `Jank/R5/Core/InstSearch.lean` and `Run/R5/Core.lean`, under those terms
  (each folder's README.md, LICENSE and COPYING.RUNTIME).
- **Boost.Multiprecision** (Boost Software License 1.0): `Jank/R3/Boost/` (cpp_int and
  cpp_dec_float).
- **immer** (Boost Software License 1.0): `Jank/R3/Immer/` and `Jank/R4/Immer/` (the RRB vector
  and CHAMP, and their `_mut` paths); `Jank/R5/Core/Champ*.lean` prove laws over round 3's CHAMP.
- **folly** (Apache License 2.0): `Jank/R3/Runtime/` (SharedMutex, fbvector), reused by
  `Jank/R4/Runtime/`.
- **bdwgc** (the Boehm-Demers-Weiser GC license, MIT-style): `Jank/R3/Runtime/` (reachability,
  descriptors) and `Jank/R4/Runtime/` (stack scanning).
- **CppInterOp** and **Clang/LLVM** (Apache License 2.0 with LLVM exceptions):
  `Jank/R3/Interop/`, `Jank/R3/Codegen/`, `Jank/R4/Interop/` and `Jank/R5/Interop/` (GetOperator,
  BestOverloadMatch, InstantiateTemplate, TryObjectArgumentInitialization, GetBuiltinOperatorType,
  AddMethodCandidate's acting context); `Jank/R5/Native/` reads LLVM's `cantFail` and ORC's
  `LoadDynamicLibrary`.
- **Boost.Process** (Boost Software License 1.0): `Jank/R4/Feedback/Shell.lean` (v1's
  `build_args` and its POSIX pipe handling, as `jank.shell` reaches them).
- **stduuid** (MIT): `Jank/R4/Core/Uuid.lean` (`uuid::from_string`).
- **nlohmann json** (MIT): `Jank/R4/Core/Json.lean` (the number lexer's outcome, `get<i64>`,
  `dump_float`).
- **GNU ld** (binutils 2.45, GPL-3.0-or-later): `Jank/R5/Native/LdSpec.lean` re-expresses the
  linker-script grammar (ldgram.y, ldlex.l) and ld.texi's search rules as the specification of
  jank's `parse_ld_script`; no ld code is copied.
- **nREPL** 1.8.0 (EPL 1.0) and **OpenJDK**'s `java.util.regex` (23): specification models
  (`Jank/R5/Nrepl/Interrupt.lean`; `Jank/R4/Regex/JavaM.lean`, `Jank/R5/Regex/JavaM5.lean`),
  written from their documentation and the behavior read in their sources; no code copied.
- **Clojure** (Eclipse Public License 1.0): the specification side, Clojure's behavior as
  documented and as its sources implement it; **clojure.data.json** 2.5.2 (EPL 1.0) likewise for
  jank's port of it.

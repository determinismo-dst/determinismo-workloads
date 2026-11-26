# Proposed fixes to jank

Patches to jank main 7135b7708 (`compiler+runtime/`), one per finding in jankifier's
specs/repros.md. Each was built into jank (an incremental build of main on Linux) and its
finding's forms run on that build:

- [R97.diff](R97.diff): `keyword::compare` checks the other value's type, as `symbol::compare` does.
  `(compare :a 1)` throws "The value for comparison must be a `keyword`, not a `small_integer`"
  instead of crashing; `(compare :a :b)` is still -1.
- [LG5.diff](LG5.diff): `quot` of two integers (a long or a small integer each) divides as integers.
  `(quot 9223372036854775807 3)` is 3074457345618258602, `(quot 9223372036854775806 7)`
  1317624576693539400, as in Clojure; `(quot -7 2)` is -3; doubles go through `to_real` as before.
- [LG1.diff](LG1.diff): `count` returns an `i64`, not the `usize` of `sequence_length`.
  `(< -1 (count "a"))` is true, `(max (count [1]) -1)` 1, `(min (count [1 2 3]) -1)` -1.

From jank's checkout: `git apply <file>` (paths are `compiler+runtime/...`).

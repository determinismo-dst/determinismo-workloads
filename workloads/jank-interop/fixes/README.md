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

- [LG7.diff](LG7.diff): an empty lazy sequence hashes as the empty list (`persistent_list::empty()`'s
  hash), not 1. `(= #{()} (set [(lazy-seq)]))` is true, `(hash (lazy-seq))` 2277397642 like `(hash ())`;
  on the build without it, false and 1.
jank's own tests with all three patches applied: its 551 `pass-` files under test/jank, each in
its own process, read whole and its forms evaluated in order (jank has no `load-file`; its test
runner passes a file whose last form is `:success`): 549 pass on the original build and 549 on the
patched one, the same files. The two others, test/jank/syntax-quote/pass-resolve-alias.jank and
pass-unaffected.jank, fail alike on both: an alias read by `read-string` and `eval` instead of the
runner's `eval_file`.

From jank's checkout: `git apply <file>` (paths are `compiler+runtime/...`).

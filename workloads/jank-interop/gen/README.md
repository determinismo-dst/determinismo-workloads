# Generated differential tests of jank

`gen.clj` draws random forms from a typed grammar over clojure.core (edge values, sequence and
map functions, strings, `let`, `if`, higher-order calls), takes Clojure 1.12's outcome for each
as the expected one, and writes jank tests from them. Every mismatch on jank is a deviation found
without anyone writing its case: a second source of jank findings beside the Lean replica's
rounds (ephyra's method; [jankifier](https://github.com/pfeodrippe/jankifier) keeps the
confirmed ones).

Three stages, with a determinismo-ci run (examples' ci-jank) after each of the first two:

```sh
clojure -M gen.clj gen 1 500                  # tests/jank_gen/gen_1_test.jank, results/gen-1-forms.edn
python3 failures.py <serve> <run> f1.json     # the run's failed tests and what the runner said
clojure -M gen.clj shrink 1 f1.json           # tests/jank_gen/shrink_1_test.jank: suspects' subforms
python3 failures.py <serve> <run> s1.json
clojure -M gen.clj group 1 s1.json            # results/gen-1-groups.md: minimal cases by signature
```

- Kept: forms with a call whose Clojure outcome is deterministic, short, and reads back equal to
  itself, or that throw both times (the jank case then asks for any throw).
- Ten cases a test and one assertion over them: the runner reports a test's first failure only,
  so a failure lists every mismatch as `{:i case :jank outcome}`.
- `ev` reads and evaluates each case at run time and realizes its value; any throw (an object, a
  native exception, a `jank::error_ref`) comes back as `[:jank-gen/threw message]`, so every
  case gets its own verdict.
- No case depends on a set's or map's element order, which Clojure leaves unspecified: keys are
  sorted by `str`, sets appear only as results or a predicate's argument, and `str`/`pr-str`
  print ordered values only.
- Shrinking: each suspect form (a mismatch, or every case of a test that crashed or hung) becomes
  a test of its own with its subforms as cases; the minimal case is a failing subform with no
  failing subform inside it, and a crash or hang there is the whole form's.
- The same seed gives the same files.

Seed 1 on jank main 7135b7708 (2026-11-25, each test in its own process, run directly in podman):
20 of 50 tests differ from Clojure 1.12; the shrink stage's 44 suspect forms gave 25 failing
subform tests, grouped in [results/gen-1-groups.md](results/gen-1-groups.md). New findings, filed in
jankifier's specs/repros.md: LG1 (`<`, `>`, `min`, `max` treat `count`'s result as unsigned against a
negative number), LG2 (long overflow wraps or promotes where Clojure throws), LG3 (`subs` indexes
bytes). The rest are known (R53, R96) or Clojure's own printing of a LazySeq. Regrouped 2026-11-26
after the harness fix below: its two "no verdict" cases were the harness's, and now pass or join
LG2.

Seed 2 (2026-11-26, same jank): 13 of 50 tests differ; 32 suspect forms, 14 failing subform tests,
8 signatures in [results/gen-2-groups.md](results/gen-2-groups.md), all known (LG2, LG3, a
LazySeq's printing). Its first run failed every test at load: one expected value printed as
`#:k{:v 3}`, the namespaced map syntax jank's reader refuses (jankifier's R17, known); maps are
now printed whole.

Seed 3 (2026-11-26, grammar 2): 39 of 50 tests differ; 64 suspect forms, 74 minimal cases, 24
signatures in [results/gen-3-groups.md](results/gen-3-groups.md), none new. Most are jank's
unported `unchecked-*` (jankifier's LU74) and strings indexed by bytes (`count`, `subs`, `get`,
`nth`, `compare`, `rest`: R53's and LG3's design). The rest: LG1 (`max` and `/` against `count`'s
unsigned result), D2 and D4b (`/` without ratios, `quot` of doubles a long), R68 (doubles printed in
C++'s form), and R5: the literal `-9223372036854775808` reads as a BigInt, which also explains
`abs` of it and the first report's BigInt results under LG2 (corrected in jankifier). `max` of
-0.0 and 0 returning -0.0 (Clojure: 0) is a tie, not filed.

Seeds 4 and 5 (2026-11-26, grammar 3, which leaves out what seeds 1-3 found and covers sequences,
maps, sets, higher-order functions and ASCII strings): 1 and 3 of 50 tests differ. New: LG4 (seed 4's
g0033 died, SIGSEGV: `compare` with a keyword first and a number second, through a sorted map of
mixed keys; withdrawn: it is jankifier's R97, which now has its extra cases) and LG5 (seed 5's g0040:
`quot` of two longs past 2^53 divides as doubles). Their fixes, and LG1's, verified on a build of
jank: [../fixes](../fixes).

Seeds 6-9 (2026-11-26, grammar 3): 12 of 200 tests differ. New: LG6 (seed 8: an exception thrown
while a set hashes a lazy element ends the process) and LG7 (seed 8: an empty lazy seq hashes as 1,
so sets holding one aren't `=` to ones holding `()`). The rest: LG5 again (seed 9: `(quot
9223372036854775807 1)` gives Long/MIN_VALUE), R96, Clojure's own LazySeq printing, and two
cases where jank accepts what Clojure refuses (a sorted set of seqs, `split-at` given a function),
not filed. The rest are R96 (booleans not comparable, in a sorted
map's keys).

The harness: a thrown string is its own message (`ev`). `ex-message` of a non-exception throws in
jank (jankifier's LU62), and an overflowing `inc` throws a string, so such a case ended its whole
test with no verdict (seed 1's g0000, seed 2's g0032 and g0042).

Grammars: seeds 1 and 2 are grammar 1 (they regenerate byte for byte), seed 3 grammar 2, seeds 4
on grammar 3. Grammar 2
adds what the first seeds showed the blind replica missed: bit and unchecked arithmetic, the
primed (promoting) operators, ratios, doubles' special values, and strings past ASCII (two-byte
letters, surrogate pairs, combining marks) through the functions that index or compare them.

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
20 of 50 tests differ from Clojure 1.12; the shrink stage's 44 suspect forms gave 26 failing
subform tests, grouped in [results/gen-1-groups.md](results/gen-1-groups.md). New findings, filed in
jankifier's specs/repros.md: LG1 (`<`, `>`, `min`, `max` treat `count`'s result as unsigned against a
negative number), LG2 (long overflow wraps or promotes where Clojure throws), LG3 (`subs` indexes
bytes). The rest are known (R53, R96) or Clojure's own printing of a LazySeq.

Next: the grammar steered toward jank code the coverage build reports unreached (an agent
rewriting the generator from the uncovered lines, ephyra's loop).

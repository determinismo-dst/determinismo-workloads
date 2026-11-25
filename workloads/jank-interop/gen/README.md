# Generated differential tests of jank

`gen.clj` draws random forms from a typed grammar over clojure.core (edge values, sequence and
map functions, strings, `let`, `if`, higher-order calls), evaluates each on Clojure 1.12, and
writes a jank test namespace whose assertions are Clojure's outcomes. Every failure on jank is a
deviation found without anyone writing its case: a second source of jank findings beside the Lean
replica's rounds (ephyra's method; [jankifier](https://github.com/pfeodrippe/jankifier) keeps
the confirmed ones).

```sh
clojure -M gen.clj <seed> <forms> tests     # tests/jank_gen/gen_<seed>_test.jank, results/gen-<seed>-forms.edn
```

- Kept: forms whose Clojure result is deterministic, finite and reads back equal to itself, or
  that throw (the jank test then asks for any throw its handlers can see: an object, a native
  exception or a `jank::error_ref`).
- Each form is read and evaluated at run time (`ev`), so a form jank refuses fails only its own
  assertion; ten forms a test, each test in its own jank process (examples' ci-jank runner).
- The same seed gives the same file.

Runs go through determinismo-ci (examples/ci-jank, `ci-gen-<seed>.json`), as the Lean tests do.
Next: failures grouped by signature, and the grammar steered toward jank code the coverage build
reports unreached.

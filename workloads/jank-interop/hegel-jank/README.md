# Hegel for jank

Property-based testing for [jank](https://jank-lang.org) on [Hegel](https://hegel.dev)'s engine:
libhegel, its C ABI, through jank's C++ interop. Two packages, as jank's book packages a system
library:

- **`hegel-sys`** (`hegel-jank/hegel-sys "0.51.1-0"`): libhegel itself, its header and prebuilt
  libraries (Linux x86-64 and arm64, macOS arm64) carried in the jar. Its `jank-build.bb` declares
  the platform's library to jank's build (no network there). `fetch.sh` downloads them from
  libhegel's release, each checked against the release's checksum: run it before `lein install`.
  libhegel is MIT (`LICENSE-libhegel`).
- **`hegel`** (`hegel-jank/hegel "0.1.0"`): the binding, `hegel.core`.

```clojure
(require '[hegel.core :as hegel])

(hegel/run! {:test-cases 200}
            (fn [tc]
              (let [xs (hegel/collection tc #(hegel/integer % -100 100))]
                (= (reverse (reverse xs)) xs))))
;; => {:passed? true :failures []}
```

A property is a function of a test case: it draws its inputs from it and returns true when it
holds. False, or an exception, is a failure: its origin (an exception's `:origin`, else its
message) groups failures into distinct bugs, each shrunk by Hegel to a minimal case and given a
reproduction blob.

| Function | What it draws or does |
|---|---|
| `integer tc low high` | an integer in [low, high] |
| `boolean tc` / `boolean tc p` | true with probability p (1/2) |
| `floating tc opts` | a float: `:width` 32 or 64, `:low`, `:high`, `:nan?`, `:infinity?` |
| `element tc items` | one of the items, shrinking toward the first |
| `collection tc opts draw` | a vector of `(draw tc)`, `:min-size`, `:max-size`, its length shrunk like a list's |
| `text tc opts` | a string: `:min-size`, `:max-size`, `:codec`, `:min-codepoint`, `:max-codepoint`, `:include`, `:exclude` |
| `regex tc pattern` | a string matching the pattern (Python `re` syntax) |
| `swarm tc items` | the items this test case enables (each left out with probability 1/2, at least one): swarm testing for a choice |
| `state-machine tc machine` | runs `:rules` from `:initial`, checking `:invariants`; Hegel picks the rules and swarm-tests which ones a case enables |
| `assume tc condition` | rejects the case unless the condition holds |
| `run! opts property` | runs the property: `:profile`, `:test-cases`, `:seed`, `:key`, `:location` |

Swarm testing: Hegel applies it to a state machine's rules on its own; `swarm` brings it to any
other choice (which constructs, operations or types a test case uses), so a bug that needs one
of them is not drowned by the others.

Failures are kept in libhegel's example database (`.hegel/examples/`) by `:key`, and replayed
first by the next run under the same key: name each property's run. Only the `development`
profile keeps a database: `default` resolves to it locally, but to `workload` under a fuzzer
(`ANTITHESIS_OUTPUT_DIR`) and to `ci` on a CI server, which keep none. `:location` (`{:file :line :module :function}`) says where the property lives: under a fuzzer
setting `ANTITHESIS_OUTPUT_DIR`, libhegel reports its verdict as an `always` assertion there.

`:profile` is one of libhegel's: `"default"`, `"ci"`, or `"workload"` for a program under a
fuzzer that sets `ANTITHESIS_OUTPUT_DIR`, where libhegel draws its choices through the fuzzer's
libvoidstar (`fuzz_get_random`), so the fuzzer replays and steers them.

## Tests

`lein test` in `hegel/` (each draw, runner and failure on properties that hold and that fail).
Natively without Leiningen:

```
jank -I hegel-sys/include -L hegel-sys/lib/linux-amd64 -lhegel \
  --module-path hegel/src:hegel/test run-main hegel.core-test
```

## Notes

- jank 0.1 fails to compile an inner `loop` that rebinds an outer `loop`'s name and recurs (the
  generated C++ uses a variable it never declared), so `state-machine`'s inner loop has its own name.

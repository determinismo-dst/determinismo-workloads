# jank's compiler and C++ interop, Hegel generating the cases

A jank node whose driver runs [Hegel](https://hegel.dev)'s test cases, each evaluated as jank's
REPL evaluates: the case's generated C++ compiled by `cpp/raw`, then its jank form read, compiled
by the JIT and run.

## What is generated

| Construct | The property |
|---|---|
| A C++ function of 1–6 scalar parameters answering what it received | jank passes C++ scalar arguments unchanged |
| A C++ function returning a scalar built from its bits | jank receives C++ scalar results unchanged |
| A struct of 1–5 scalar fields, built by aggregate initialization in jank, passed by value | jank passes a C++ struct by value unchanged |
| The same struct's fields read back with `.-f<i>` | jank reads a C++ struct's fields as stored |
| Overloads of one name on distinct scalar types, an argument cast to one of them | jank calls the C++ overload C++ would |
| A C++ exception thrown and caught in jank by `std::exception` | jank catches a C++ exception by its base type, its message intact |
| `+`, `-`, `*` on 64-bit values C++ computes without overflow | jank's integer arithmetic is 64-bit |
| A struct made by `cpp/new`, its fields read through the pointer, then `cpp/delete` | jank reads a C++ struct's fields through a pointer as stored |
| A struct's fields assigned through their references (`cpp/=` on `.-f<i>`) | jank writes a C++ struct's fields through their references |
| A member function on a value or through a pointer, answering fields and arguments | jank calls a C++ member function with its object and arguments intact |
| Generated text through `std::string const &` or `const char *` and back | jank strings cross to C++ and back unchanged |
| Nested lets of values counting their constructions and destructions | jank destroys a let's C++ values at its end, once each |
| A pointer in `cpp/box` through jank functions, `cpp/unbox`ed as its type or another | jank's opaque boxes give back their pointer, and refuse another type |
| A type with `operator()` or a function pointer, called with jank's call syntax | jank calls C++ callables with their arguments intact |
| `cpp/+` ... `cpp/<<` ... `cpp/>=` on two scalar types (C++'s undefined cases skipped) | jank's C++ operators compute what C++ computes |
| A `#cpp (std.vector T)` filled with `.push_back`, read with `.at`, `.at` past its end | jank fills and reads a C++ std::vector, its range checked |
| `#cpp (:member (std.numeric_limits T) max)`, `min`, `lowest`, `digits`, `is_signed` | jank reaches std::numeric_limits as C++ does |
| `+ - * /` on doubles (infinities, signed zeros, subnormals, division by zero), as constants or built from bits | jank's double arithmetic is IEEE's |
| let, loop/recur, fn and if forms over names that shadow each other, top level or in a function | jank evaluates let, loop, fn and if forms as Clojure does (a model's answer) |
| A value (numbers, strings, keywords, symbols, characters, collections) quoted in an evaluated form | a constant in an evaluated form keeps its value |
| The same values printed and read back | jank reads back what it prints |
| The same values thrown through a `finally` | jank catches the value thrown, its finally run once |
| Hash, array and sorted maps under assoc, dissoc and transient batches, a Hegel state machine | jank's persistent maps hold what a std::map holds, every version kept |

The scalar types: `int8_t` to `int64_t` and `uint8_t` to `uint64_t` across their ranges, `char`,
`bool`, `float` and `double` (finite, signed zeros and infinities included, NaN left out: its
payload is no interop guarantee). Every value is drawn as its own bits, so a difference is the
interop's, never a printing round trip's. Every case also asserts that it compiles and runs.

## Scenarios, swarm testing and Hegel

The constructs follow what jank's book promises (C++ interop, its DSL, exceptions, casts,
boxes, the differences from Clojure), each in an area, and each area is a scenario of its own:
`interop` (C++ interop), `language` (binding forms, constants, printing and reading, thrown
values), `programs` (generated jank programs: differential and grammar forms), `collections`
(maps, vectors and sets as state machines against C++ models; transducers against lazy seqs;
sorting against `std::stable_sort`; `=` and `hash`), and `mixed` (all of them in one process,
for what one construct leaves behind for another). A run explores one area: its properties are
not diluted by the other areas' cases, nor hidden behind their failures, and a generated program
that hangs jank (the `count` loop) stops only the programs scenario's driver.

Within the scenario, each timeline keeps its own constructs and scalar types, weighted (determinismo's `swarm-index`:
the `interop_swarm` event says which), and Hegel draws within them: a bug that needs one family
is not drowned by the others, and triggers and suppressors name the family a failure needs.

Within a timeline, each test case also enables its own subset of the kept constructs (hegel-jank's
`swarm`), and the binding forms construct its own subset of form kinds.

Hegel is [hegel-jank](hegel-jank) (libhegel's C ABI through jank's interop), with its
`workload` profile. The node has determinismo's libvoidstar (`:antithesis-library`), so Hegel's
backend draws through `fuzz_get_random`: each choice is a determinismo decision, replayed exactly
and steered by the explorer. Hegel groups failures by construct and shrinks each one.

## jank's coverage and assertions

The default profile's jank is built with determinismo's coverage: jank's LLVM fork and jank at
a pinned commit, jank's C and C++ compiled with trace-pc-guard against libvoidstar, so every edge
of the compiler and runtime reports itself (and thread pausing pauses there); the `packaged`
profile runs jank's own package, without it. `jank-coverage/assertions.patch` adds the SDK's
assertions to jank's own source (assertions only): `sometimes` an array map grows into a hash map
(persistent and transient), one at its size becomes a hash map on an existing key's update, and
an interop argument converted through a trait reaches an overload. `jank-coverage/build.sh
<platform tree>` builds it (hours: LLVM); the result is kept on this repository's release
[jank-coverage-44eea86f7](https://github.com/determinismo-dst/determinismo-workloads/releases/tag/jank-coverage-44eea86f7),
which the Dockerfile fetches by its checksum.

## Debugging a failure

The node's jank runs with `--perf`: its JIT writes a jitdump file naming what it compiles, so
`determinismo stacks` at a moment of a timeline names REPL-compiled frames, and `gdb` is in the
image for a closer look there.

## Findings (jank 0.1-noble, 2026-11-11)

- **Integer multiplication wraps at 32 bits.** Hegel shrank the arithmetic property's failures, found
  in the first timeline that kept the construct, to `(* 2 1073741824)`: jank answers
  `-2147483648`, Clojure `2147483648`. The same natively (`jank run`), with literals, in a `let`
  and through a function's parameters. Known before: this run rediscovered it blind.
- **`-9223372036854775808` is read as a `big_integer`**, where Clojure reads a long:
  `(type -9223372036854775808)` is `big_integer`, `(dec -9223372036854775807)` the same value an
  `integer`; so the literal cannot be passed to an `int64_t` parameter (its conversion throws). The
  workload takes the value from C++ (`cpp/INT64_MIN`).

- **An inner `loop` rebinding an outer `loop`'s name, recurring, does not compile.**
  `(defn f [n] (loop [x n] (let [y (loop [x x] (if (odd? x) x (recur (inc x))))] (if (> y 9) y (recur (inc y))))))`:
  the generated C++ uses `s11`, never declared (`codegen/internal-failure`); Clojure answers 11.
  The inner loop under another name compiles and answers 11. Found writing hegel-jank's state
  machine runner (natively, jank's rolling build of 2026-11-11), before the binding forms
  construct generates its class; no issue in jank's tracker.

- **A C++ callable of two or more arguments cannot be called.** `(let [g (cpp/c2.)] (g 5 6))` on
  `struct c2 { long operator()(long a, long b) const; }` fails to compile:
  `analyze/invalid-cpp-operator-call`, "Operator calls may only take one or two arguments" (the
  callable counted as an operand); 0 and 1 arguments work, and a function pointer of two. The book
  promises arbitrary callables with jank's call syntax. No issue in jank's tracker.
- **A `static` global from `cpp/raw` is another variable in code jank compiles later.** A
  constructor incrementing `static int64_t g` and a `read()` beside it, both in one `cpp/raw`: a
  `let` binding the type (compiled after) increments a copy, `read()` answers 0. Plain and
  `inline` globals answer 1. No issue in jank's tracker.
- **A C++ `char` outside ASCII loses its value in jank.** Read from a field or returned, `(char)-5`
  becomes a jank character whose `int` is 0 in compiled code. ASCII is kept. No issue in jank's
  tracker.
- **`std::vector<T>` beyond what jank's precompiled header instantiates does not link** =
  [#1071](https://github.com/jank-lang/jank/issues/1071) (open), rediscovered blind: `(#cpp
  (std.vector double))` with `.push_back` fails with `Symbols not found:
  __new_allocator<double>::deallocate`; `std::vector<int>` works.
- **A `let` answering `(.size v)` of a `std::vector<int>` does not compile** = jank
  [#1185](https://github.com/jank-lang/jank/issues/1185) (open), met writing the reproductions:
  the generated C++ declares `std::vector::size_type`, its template argument dropped.

- **A transient of an array map writes into the persistent map it came from.** Found by the
  persistent maps property under determinismo CI (the private examples' ci-jank, run 4: failing in each of its
  shard's timelines), Hegel's shrunk case `[:assoc 0 0] [:snapshot] [:transient [assoc! 0 1]]`: the
  kept version then held `{0 1}`. `(let [m1 {:a 1} m2 (persistent! (assoc! (transient m1) :a 2))] m1)`
  answers `{:a 2}`, and `dissoc!` leaves the original with a key twice (`{1 1, 1 1}`); Clojure keeps
  `{:a 1}`. Every small map is an array map, and `into`, `update-vals` and friends use transients.
  Hash maps are not affected. Not jank-lang/jank#274 (persistent operations on transients, closed).

- **A thrown number, string or boolean cannot be caught: the program aborts.** Found by the thrown
  values property under determinismo CI (run 4: every timeline of its shard, jank killed by
  `SIGABRT` 29 s in, "terminate called after throwing an instance of 'int'", its core kept).
  `(try (throw 5) (catch cpp/jank.runtime.object_ref e e))` throws a C++ `int`, `1.5` a `double`,
  `true` a `bool`, `"s"` a `char const*`, through a local too (`(let [v 5] (throw v))`); a keyword
  and nil are caught. The book: a thrown value of any type is type-erased into an `object_ref`. Not
  jank-lang/jank#996 (a throw beside a native local, closed).

- **Reading a string that holds a NUL character never returns.** Found as a hang under
  determinismo CI (run 4: the shard with print and read hung in each of its timelines until the
  hour's limit); its stacks at a moment 10 minutes in (the timeline replayed, `det-profile jank
  --stacks`): `read_string -> lex::processor::peek -> convert_to_codepoint -> mbrtowc`.
  `(read-string (pr-str (str "a" (char 0) "b")))` hangs natively too, in any locale: `mbrtowc`
  answers 0 bytes for a NUL and the lexer does not advance. No issue in jank's tracker.
- **One failed link poisons the symbols it needed for the rest of the process.** After a
  `std::vector<uint32_t>` case fails to link (jank-lang/jank#1071), a plain `uint32_t` result
  from C++, which links in a fresh process, fails every time ("Failed to materialize symbols:
  `jank::runtime::convert<unsigned int>::into_object`"); an `int32_t` result still works. Found by
  the interop scenario's hunt (phoenixNAP run 1909): scalar results, pointer fields and field
  writes failing to link in a process that ran many cases, though they pass alone (each CI test
  its own process); the timelines' records ordered a failing `std::vector` case before them, and
  the order reproduces natively (the same cases the other way round all work). LLVM's ORC JIT
  keeps a symbol whose materialization failed in its error state: the conversion was first asked
  for by the module that failed. So #1071's one failure becomes failures of unrelated code in a
  long-lived process (a REPL, nREPL). It reaches jank's own calling machinery too: in the guided
  programs hunt (phoenixNAP run 1922, 5 of 70 timelines) a generated program that failed to link
  had asked for `oref<jit_function>::call`, after which the workload's own lazily compiled
  `failure-origin` could not be loaded ("Failed to find symbol: 'jank_interop_cases$failure_origin_...'")
  and jank died with a panic in `jit::processor::create_function` (exit 1): one failed link can
  take a whole program down, not only unrelated C++ calls. No issue in jank's tracker beyond #1071
  itself. Repro: `repro/failed-link-poisons-symbols.jank`.
- **The literal `-2147483648` cast to `int32_t` reaches C++ as a `long`.** With C++ overloads
  `f(int8_t)` and `f(int32_t)`, `(cpp/f (cpp/cast cpp/int32_t -2147483648))` does not compile ("call
  to 'f' is ambiguous"), directly or bound in a `let`; C++ calls `f(int32_t)` for an `int32_t`. Any
  other `int32_t` literal, or the same value computed (`(dec -2147483647)`), calls `f(int32_t)`.
  Found by the overload construct under determinismo CI (runs 1898 and 1899 on the phoenixNAP host:
  failing in 1 of 3 timelines each, the timeline that drew `INT32_MIN`; its case whole once
  `det-assert` kept failures' texts). In C++ source `-2147483648` is unary minus on `2147483648`,
  which does not fit an `int`: a `long`. jank's `cpp_processor.cpp` writes an unboxed integer
  literal as its bare digits; its boxed path casts `INT32_MIN` explicitly ("The literal min value
  of an integer is treated as a long"), the unboxed one does not (main 44eea86). No issue in jank's
  tracker. Repro: `repro/int32-min-literal-is-a-long.jank`.
- **`INT64_MIN` as an unboxed literal turns a signed operation unsigned.** With `a` an `int64_t`
  -2048 and `b` an `int64_t` `INT64_MIN` given as a literal, `(cpp// a b)` answers 1, C++ 0, with no
  error; `INT64_MIN + 1`, or the same value computed, answers 0. Found by the native operator
  construct in a hunt on a c5.metal
  ([aws-hunt run 17](https://determinismo-dst.github.io/determinismo-workloads/runs/17-aws/),
  2026-11-22: 1 of its first 873 timelines, one the tree branched by returning to an earlier
  timeline for a rare coverage edge). The same root as the `INT32_MIN` finding above, here a silent
  wrong value: `cpp_processor.cpp` writes an unboxed integer literal as its bare digits, and
  `-9223372036854775808` is unsigned in C++. The same natively on x86-64 Linux with jank's PPA
  build, 44eea86 and main 774d02f (2026-11-19); a macOS arm64 build of 2026-11-09 answers 0. No
  issue found in jank's tracker. Repro: `repro/int64-min-literal-is-unsigned.jank`.
- **An empty lazy seq is `=` to `[]` and hashes differently.** With `e` `(filter odd? [2])`,
  `(= [] e)` is true and `(contains? (conj (set (range 20)) []) e)` false; a hash map keyed by `[]`
  does not find `e` either, and `(distinct [[] e])` keeps both. `take 0`, `concat` and `lazy-seq`
  answer the same; a seq with elements hashes right. Found by the equality and hashing construct in
  the same hunt ([aws-hunt run 17](https://determinismo-dst.github.io/determinismo-workloads/runs/17-aws/),
  2026-11-22: 366 evaluations in 55 of its 1,773 timelines). `lazy_sequence::to_hash` answers a bare
  1 when the seq is empty, where `hash::ordered` mixes that 1 with the length. The same natively
  with jank's PPA build and main 774d02f (2026-11-19) on x86-64 Linux, and on macOS arm64. Nothing
  found searching the text of jank's issues and pull requests. Repro:
  `repro/empty-lazy-seq-hash.jank`.
- **A NaN made by arithmetic crashes jank when used.** `(NaN? (/ 0.0 0.0))`, `(str (- ##Inf
  ##Inf))`, `(= 1.0 (/ 0.0 0.0))`, `(type (/ 0.0 0.0))`: a segmentation fault each, natively too;
  the literal `##NaN` (and its negation) is fine. Found by the float arithmetic construct under
  determinismo CI (run 1896: failing in 1 of 3 timelines, the first run whose timelines drew
  their own cases), the process gone with no report (exit 139); traced natively to its last case,
  `(/ ##-Inf ##-Inf)`. jank NaN-boxes its values: a double is a real only below
  `0xFFF8000000000000` (`max_real`, runtime/oref.hpp), and x86's default NaN, what `0.0/0.0` and
  `inf-inf` produce, is exactly `0xFFF8000000000000`. Boxing a double is a plain bit cast
  (`tag(f64)`), so that NaN is taken for an object; `core/math.cpp` returns its own `jank_nan` on
  its promoting paths only. Main 44eea86. No issue in jank's tracker. Repro:
  `repro/computed-nan-crashes.jank`.
- **A vector or list is `=` to anything seqable with the same elements: `nil`, maps, sets,
  strings.** `(= [] nil)`, `(= [1] #{1})`, `(= [[1 2]] {1 2})`, `(= [\a \b] "ab")` and
  `(= (list 1) #{1})` are true; the other way round (`(= nil [])`, `(= {1 2} [[1 2]])`) false.
  Clojure answers false to all: `=` with a sequential collection needs the other side to be
  sequential. A map keyed by `[]` answers `(get m nil)` with that key's value. A set literal loses an element to it:
  `(read-string "#{[] {}}")` answers `#{{}}` (native fuzzing on macOS, print and read; Clojure reads
  `#{[] {}}`, the two not equal). Found by the
  sequence laws (equal collections of different kinds must hash alike: `(= [] nil)` held while
  their hashes differed). `persistent_vector::equal` (and the list's) fall back to
  `runtime::sequence_equal` for any object not of its own type, which checks only that both sides
  are seqable (runtime/obj/persistent_vector.cpp, core/seq.cpp, main 44eea86); `nil` is seqable and
  empty. No issue in jank's tracker. Repro: `repro/sequential-equals-any-seqable.jank`.
- **`count`'s result compares as an unsigned number.** `(< (count [1 2]) -9)` is true,
  `(> (count []) -1)` false, `(max (count [1 2]) -9)` is -9, with the negative number a literal, a
  local or `(- 9)`; `+` and `=` are right, and so is a count boxed by a call (`(identity (count
  ...))`). A `loop` counting from a count up to a negative bound never ends. Found as a hang by the
  grammar forms (a test still running at its 600 s limit; the program, written to a file before
  each evaluation, ran at 100% CPU in its generated `clojure_core$let_...`), then reduced by hand.
  `count` is inlined as `jank.runtime.sequence_length`, which answers `usize`, and `<` as
  `jank.runtime.lt`, whose overload for two primitives is C++'s `l < r` (core/math.hpp, main
  44eea86): the usual arithmetic conversions make the negative `i64` a huge unsigned value. No issue
  in jank's tracker. Repro: `repro/count-compared-unsigned.jank`.
- **`-0` before a delimiter is refused by the reader.** `[-0]`, `(+ 1 -0)`, and `-0` followed by a
  comma or a newline are "lex/invalid-number: This base-8 number literal ended unexpectedly";
  `-0` followed by a space or the end of input, and `0` alone, read fine. Clojure reads all as 0.
  Found by the grammar forms (a Lark grammar of jank code through hegel-jank, `NUM: /-?[0-9]/`):
  every case with a `-0` before a closing bracket. In `read/lex.cpp` (main 44eea86, 2026-11-11), a
  `-` followed by `0` and a non-space starts an octal number (radix 8, more digits expected); the
  check that lets a lone `0` end before a delimiter tests the token's first character, which for
  `-0` is the sign. Not jank-lang/jank#620 (leading zeros read as octal, open). Repro:
  `repro/read-negative-zero-before-delimiter.jank`.
- **Under the C locale, non-ASCII text is an "Unterminated string".** `LANG=C jank run` on
  `(read-string (pr-str "café"))`, or a source file with one; C.UTF-8 reads it. jank decodes UTF-8
  through the process's locale, and a container sets none unless told. Clojure reads UTF-8 in any
  locale. jank-lang/jank#277's symptom (closed), still under the C locale.

- **`locking` does not compile.** `clojure.core/locking` is defined, but its expansion calls
  `monitor-enter`, which jank does not define, so `(locking lock (+ 1 1))` is "unresolved symbol".
  Found writing the concurrency tests (the private examples' ci-jank, its jank_concurrency tests). No issue in jank's
  tracker.
- **A second `deliver` answers non-nil.** `(deliver p 2)` after `(deliver p 1)` answers the
  promise again; Clojure answers nil, so a caller can tell whether its delivery won. The value
  stays 1. Found by the concurrency tests, no thread needed.

Each finding is a runnable file in [repro/](repro/) (`jank run repro/<file>.jank`): it prints what
it expects and what jank answers, the working variant first.

Under determinismo CI (the private examples' ci-jank: 45 tests, each in a jank process of its own, 6 shards
of 3 timelines, timing faults; phoenixNAP host run 1893, 2026-11-12): every test has a verdict,
none flaky. Failing in every timeline, each a finding above: arithmetic, callable, characters,
differential forms (#984's case), persistent maps, print and read (the NUL hang, its test's error
after 300 s), static globals, std vector, thrown values (the abort, its test's error) and deliver's
answer. Passing in every timeline: the other constructs (scalar arguments and results, structs,
pointer fields, field writes, member functions, overloads, native operators, opaque boxes, let
destructors, exceptions, numeric limits, IEEE doubles, binding forms, constants), every
concurrency test (no update lost, no torn version, one compare-and-set winner, one promise value,
GC keeping what is held) and hegel-jank's own tests.

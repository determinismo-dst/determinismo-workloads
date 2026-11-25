# REPORT-2: jank 7135b7708 compared with Clojure 1.12, from a Lean replica of jank's own code

**Version.** jank `7135b770857d625630ab6f9abe5861c618d67b82` (main on 2026-11-24). It is shallow-cloned, with no history, at `upstream-main/`. The work began on the old checkout `f3d82d654` (`upstream/`). Every model was then re-read against 7135b7708 and updated where the code changed, and every search was run again. The source diff, without jank's tests, is in `results/upstream-f3d82d654-to-7135b7708.diff`. Files absent from it are unchanged.

**Paths.** Every path is under `upstream-main/compiler+runtime/` and uses 7135b7708 line numbers.

**Status of each item.** Every item is a hypothesis: the C++/jank code was modeled as written, then re-read. jank was never built or run. The status column says:
- **both**: holds on f3d82d654 and on 7135b7708;
- **changed**: holds on both, with different behavior on 7135b7708;
- **f3d only**: held only on f3d82d654 (fixed in 7135b7708);
- **7135 only**: introduced by the newer code.

**Who did what.** Three earlier forks covered the reader (A), strings/printing/regex (B) and core/nREPL (C); their saved reports are in `results/fork-*.txt`. Seven agents covered the analyzer, code generator, C++ interop, sequences, the rest of core, the nREPL server and strings extras. I merged the duplicates below. Round 1's D1–D25 were re-checked on 7135b7708 as well.

## Deviations at a glance

| # | Area | jank (predicted) | Clojure | Status |
|---|---|---|---|---|
| R1 | reader | a NUL byte hangs `read-string`, or overflows the stack | reads it | both |
| R2 | reader | `[1"a"]`, `(str"a")` are errors (expecting whitespace) | read | both |
| R3 | reader | `[-0]`, `-0` before a newline: error | `0` | both |
| R4 | reader | `+5` is a symbol | `5` | both |
| R5 | reader | `-9223372036854775808` reads as a BigInt; `9223372036854775808/2` as a long | long; BigInt | both |
| R6 | reader | `36rN` is `0N`, `16re` is an error, `258r11` is `3` | 23, 14, error | both |
| R7 | reader | `08M` error; `-010/3` is `-8/3`; `-09/3` throws | 8M, -10/3, -3 | both |
| R8 | reader | `"\0"`, `"\101"` are errors | octal escapes | both |
| R9 | reader | a comment ends only at `\n` | also at `\r` | both |
| R10 | reader | `@x` reads as unqualified `(deref x)`; a local `deref` captures it | `clojure.core/deref` | both |
| R11 | reader | `^"S"` and `^[long]` are errors; `^foo` gives `{:tag (quote foo)}` | `{:tag "S"}`, param-tags, `{:tag foo}` | both |
| R12 | reader | `#(… %10 …)` is an error | 10 params | both |
| R13 | reader | `{1 :a 1N :b}`, `#{0.0 -0.0}` are accepted | duplicate key error | both |
| R14 | reader | `a@b` is one symbol; `~é` is an error | `a`, `@b`; unquote | both |
| R15 | reader | U+2003, U+001C… are not whitespace | whitespace | both |
| R16 | reader | `:/` has the name `""` | `"/"` | both |
| R17 | reader | `#:a{:b 1}` and `#^:a x` unsupported | supported | both |
| R18 | reader/regex | `#"(?i)a"`, lookbehind, named groups are read errors | valid | both |
| R19 | reader | syntax quote: `` `clojure.set `` is qualified; `~@#{a b}` keeps duplicates | not qualified; set value | both |
| R20 | reader | `read-string` also parses the 2nd form (data readers run, hangs) | 1st only | both |
| R21 | reader | read collections and symbols carry `{:jank/source …}` meta | nil | both |
| R22 | reader/strings | C locale: non-ASCII source unreadable, `"\u00e9"` is `"?"` | UTF-8 | both |
| R23 | analyzer | `if` with native branches of different types: `(if true 1 2.5)` is `1.0`, `(or true 0)` is `1` | `1`, `true` | both |
| R24 | analyzer | loop locals keep a literal's C++ type; `recur` converts into it | locals hold any value | changed |
| R25 | analyzer | literal arithmetic is 32-bit: `(+ 2147483647 1)` is `-2147483648` | `2147483648` | both |
| R26 | analyzer | `case` branches forced to one C++ type: `(case 5 1 1.5 0)` is `0.0`; `(case 1 1 "one" 2 :two :other)` throws | `0`, `"one"` | 7135 only |
| R27 | analyzer | `recur` in a fn inside a `loop` targets the loop | the fn | both |
| R28 | analyzer | an outer local shadows a named fn's own name | fn name innermost | both |
| R29 | analyzer | a named fn's name does not shadow a macro | shadows | both |
| R30 | analyzer | macros get `&form = ((args))`, `&env = <macro symbol>` | the form; locals | both |
| R31 | analyzer | macro-built collections carry `{:jank/macro-expansion …}` meta at run time | nil | both |
| R32 | analyzer | private vars accessible inside any macro expansion | error | both |
| R33 | analyzer | `(+ true 1)` is `2` | ClassCastException | both |
| R34 | analyzer | `(:k)` is nil | arity error | both |
| R35 | analyzer | `(try 1 (catch :default))` is UB | compile error | both |
| R36 | analyzer | an object loop local given a native `recur` value fails to compile (low confidence) | works | both |
| R37 | codegen | a call evaluates its operands before its operator | operator first | both |
| R38 | codegen | `a-b` and `a_b` are one local; `a.b` param is a C++ error | distinct | both |
| R39 | codegen | a nested loop rebinding a name breaks the outer `recur` (C++ error) | works | both |
| R40 | codegen | a nested fn referring to `my-f` crashes the compiler | works | both |
| R41 | codegen | two `letfn`s in one fn (first with a forward ref): invalid C++ | works | both |
| R42 | codegen | `=` literal constants share one object: `[[]]` then `['()]` | distinct | both |
| R43 | codegen | `def` meta stored as code text (AOT `:arglists` is `(quote …)`; JIT loses locals) | evaluated | both |
| R44 | codegen | `case` on a long outside i32 misses; `Long/MIN_VALUE` key won't compile | works | both |
| R45 | codegen | -O3 merges var reads across a redefinition | `[1 2]` | both |
| R46 | codegen | -O1/-O3: compiler crash on a deduped `case` value or loop binding | works | both |
| R47 | codegen | `((fn f [f] y) 5)` reads the closure context from the argument (UB) | `y` | both |
| R48 | codegen | -O1/-O3: a constant in two branches of a catch/finally breaks the `try` | works | both |
| R49 | codegen | AOT: NUL truncates string/char literals | kept | both |
| R50 | codegen | AOT: ratio literal parts outside i64 are wrong | exact | both |
| R51 | codegen | AOT: `#inst` literals cannot be compiled | work | both |
| R52 | strings | `count`/`nth`/`get`/`subs` work on UTF-8 bytes | chars | both |
| R53 | strings | `seq` walks code points, disagreeing with `count` | consistent | both |
| R54 | strings | `seq` of a truncated string reads past the end | — | both |
| R55 | strings | `(let [x (seq "é")] (= x x))` is false | true | both |
| R56 | strings | `(seq "a")` and `[\a]` hash differently | same | both |
| R57 | strings | `compare`/`sort` use UTF-8 byte order | UTF-16 order | both |
| R58 | strings | `index-of` returns byte indices, mishandles negative starts | char index | both |
| R59 | strings | `trim`/`blank?` use C `isspace` | `isWhitespace` | both |
| R60 | strings | `upper-case "ß"` is `"ß"`; final sigma not handled | `"SS"`, `ς` | both |
| R61 | strings | `capitalize "Éa"` is `"éa"` | `"Éa"` | both |
| R62 | strings | `replace` with an empty match splits UTF-8 bytes | per char | both |
| R63 | strings | `escape` never matches non-ASCII keys | matches | both |
| R64 | strings | `char`/`int` depend on the locale; `(char 55296)` throws | `\uD800` | both |
| R65 | strings | `(namespace (keyword "a/b" "c"))` is `"a"` | `"a/b"` | both |
| R66 | strings | `(char -4294967231)` is `\A` | throws | both |
| R67 | strings | `(namespace (symbol nil "b/c"))` is `"b"` | nil | both |
| R68 | printing | `(str 100000.0)` is `"1e+05"` | `"100000.0"` | both |
| R69 | printing | `(str ["a" \b])` is `"[a b]"` | `"[\"a\" \\b]"` | both |
| R70 | printing | `pr-str` writes `\a`, `\v` | raw chars | both |
| R71 | printing | `(pr-str #"\"")` does not read back | `#"\""` | both |
| R72 | printing | `(str 1M)` is `"1.0"`; scale lost | `"1"`, `1.50M` | both |
| R73 | printing | `pr-str` takes exactly one argument | variadic | both |
| R74 | printing | `*print-length*` etc. missing or ignored | honored | both |
| R75 | printing | `print-method` is never called | dispatches | both |
| R76 | printing | `(print-str (seq "ab"))` is `"(\\a \\b)"` | `"(a b)"` | both |
| R77 | printing | `(print-str ##Inf)` is `"Infinity"` | `"##Inf"` | both |
| R78 | regex | regexes match UTF-8 bytes | chars | both |
| R79 | regex | `$` does not match before a final `\n` | matches | both |
| R80 | regex | a group that did not participate is `""` | nil | both |
| R81 | regex | `re-seq`: `^` matches again; an empty match repeats forever | finite | both |
| R82 | regex | `(re-matches #"a\|ab" "ab")` is nil | `"ab"` | both |
| R83 | regex | input cut at the first NUL | whole string | both |
| R84 | regex | replacement strings follow ECMAScript, fn gets the match string | Java rules, groups | both |
| R85 | regex | `split`/`replace` retry a non-empty match after an empty one | next position | both |
| R86 | interop | number objects to native `char`/`bool` params throw; literals convert | consistent | changed |
| R87 | interop | a string literal to a `char const *` param is rejected | array-to-pointer | both |
| R88 | interop | `(cpp/new (std.vector cpp/int) 3)` holds `[3]` | 3 zeros | changed |
| R89 | interop | `(if cpp/red :t :f)` is `:f` (enum 0 is false) | `:t` | both |
| R90 | interop | `cpp/cast` accepts invalid and rejects valid `static_cast`s | C++ rules | both |
| R91 | interop | box type names lose cv/function-pointer-ness; wrong `cpp/unbox` succeeds | exact type | both |
| R92 | interop | `UINT64_MAX` comes back as -1; a char param takes one byte | lossless | both |
| R93 | interop | `char *` param accepted, then JIT error | consistent | both |
| R94 | interop | DSL accepts `(:unsigned cpp/bool)` etc. | error | both |
| R95 | interop | a char to an int param is 0 in the C locale (by reading) | code point | both |
| R96 | core | `(compare true false)` throws; `(compare true 1)` is 0 | 1; CCE | both |
| R97 | core | `(compare :a 1)` is UB | CCE | both |
| R98 | core | `(let [x '(1)] (compare x x))` throws | 0 | both |
| R99 | core | `(compare 0.1M 0.1)` is -1 | 0 | both |
| R100 | core | `prefer-method` on ancestors ignored at dispatch | honored | both |
| R101 | core | `get-method` throws when nothing applies | nil | both |
| R102 | core | `(intern 'user 'map 7)` rebinds `clojure.core/map` | new var | both |
| R103 | core | `(remove-ns 'clojure.core)` succeeds | throws | both |
| R104 | core | `=` on sorted colls with incomparable keys throws | false | both |
| R105 | core | sorted `find` returns the queried key | stored key | both |
| R106 | core | `reset-meta!` on `(sorted-map)` mutates the shared empty | CCE | both |
| R107 | core | `((fn [& {:as m}] m) :a 1 (seq {:d 4}))` throws | `{:a 1 :d 4}` | both |
| R108 | core | `defn` recursion bypasses the var | through the var | both |
| R109 | core | `(ns user)` again after `(def inc 1)` throws | nil | both |
| R110 | core | `find-var` accepts unqualified names and returns referred vars | qualified only | both |
| R111 | core/nREPL | `ns-resolve` uses `*ns*`'s aliases, so nREPL `lookup` misses `str/join` | the given ns | both |
| R112 | core | `in-ns` returns nil | the ns | both |
| R113 | core | `sorted-map-by`, `subseq`, `rseq`, … throw "TODO: port" | implemented | both |
| R114 | seq | `(take 2 (range 9223372036854775807))` throws | `(0 1)` | both |
| R115 | seq | `range` loses elements when `end - start` wraps | exact | both |
| R116 | seq | `(count (range 2147483646 2147483649.0))` never ends | 3 | both |
| R117 | seq | `doseq` mutates seqs the program holds (hang, wrong values, UB) | no mutation | both |
| R118 | seq | `partition-by` transducer sends a partition twice after `reduced` | once | both |
| R119 | seq | `chunk-cons` realizes its rest: `(first (map inc (range 0.0 ##Inf)))` overflows the stack | 1.0 | both |
| R120 | seq | `(coll? (cons 0 [1]))` false; `(empty (cons …))` nil | true; `()` | changed |
| R121 | seq | `(get-in 5 [])` is nil | 5 | both |
| R122 | seq | `(aget (byte-array [-1]) 0)` is 255 | -1 | both |
| R123 | seq | `(key (find {[1] :v} '(1)))` is `(1)` | `[1]` | both |
| R124 | seq | `sequence` with xform, `eduction`, `iteration`, `make-array`, … unported | implemented | both |
| R125 | nREPL | stdout capture is process-global (`dup2` on fd 1) and races | per session | both |
| R126 | nREPL | an error while printing the value gives a handler error, not eval-error; `*e` unset | eval-error | changed |
| R127 | nREPL | sessions keep no state (`*1`, `*ns*`, `*e` shared or lost) | per session | both |
| R128 | nREPL | no `interrupt`; one connection is strictly sequential | interruptible | both |
| R129 | nREPL | a stack overflow or crash in an eval kills the server | eval-error | both |
| R130 | nREPL | per-connection socket/thread and per-eval JIT code never freed | released | both |
| R131 | nREPL | `lookup` of a var whose arglists hold `nil`/`false` errors (`iteration`) | info | changed |
| R132 | nREPL | eval of only comments replies `value "0.0"` (release) or aborts (debug) | no value | changed |
| R133 | nREPL | malformed bencode bytes stall the connection forever | error | both |
| R134 | nREPL | deep `l`/`d` nesting overflows the stack (client bytes alone) | error | both |
| R135 | nREPL | leaked sockets exhaust fds: eval error with fd 1 left on a temp file, then accept dies | — | changed |
| R136 | nREPL | whitespace-only output (`(println)`) is dropped | `"\n"` | both |
| R137 | nREPL | `inspect "true"` drops output and merges value and done | — | changed |
| R138 | nREPL | `lookup`/`info` fails for every var outside core modules | info | 7135 only |
| R139 | nREPL | EINTR on `read_some` ends the connection, socket left open (low confidence) | retry | 7135 only |
| R140 | nREPL | a request without `op` gets a handler error | `unknown-op` | 7135 only |

**Held only on f3d82d654 (fixed in 7135b7708):**
- F1. `(sort [])` gave a broken seq (fork C16).
- F2. Unknown eval `ns` ran in `user` (C12).
- F3. `write_some` dropped part of a reply (N4).
- F4. `describe` omitted `close` (N9).
- F5. A non-string `inspect` killed the connection (N10a).
- F6. Eval of `""` gave `0.0` (part of N3).
- F7. `lookup` killed the connection: now an error reply (part of N1).
- F8. A printing error killed the connection (part of C10).
- From round 1: D11 (`=` across non-sequential seqables), D14 (array-map transients wrote into their source), D15 (transient vector `nth` after `persistent!`) and D20 (`deliver` returned the promise every time).

## Deviations in full

### Reader (read/lex.cpp, read/parse.cpp, runtime/context.cpp `read_string`)

Fork A's searches compare jank's lexer and parser replica with a Lean replica of Clojure's LispReader (`ReadClj.lean`). The 7135b7708 lexer change (lex.cpp 828–836 and 840–844: early errors for `0x…` and radix denominators of ratios) changes only error messages. The searches give the same results; only line citations moved.

**R1. A NUL byte hangs or crashes the reader.** Status: both.
```clojure
(read-string "\"\u0000\"")       ; Clojure "\u0000"   jank never returns (100% CPU)
(read-string (pr-str (char 0)))  ; Clojure \u0000     jank never returns
(read-string "a\u0000")          ; Clojure a\u0000    jank never returns
(read-string "#\u0000")          ; Clojure throws     jank unbounded recursion, SIGSEGV
(read-string "1 ;\u0000")        ; Clojure 1          jank never returns (see R20)
```
- **Path:**
  - lex.cpp `convert_to_codepoint` 452: `mbrtowc` returns length 0 for NUL.
  - These loops then do `pos += 0` forever: symbols 1183, keywords 1282, characters 612, strings 1325, `;` comments 635, `#!` 1411.
  - `#` (1384/1442) and `~` (1466) return zero-width tokens, and parse.cpp `parse_reader_macro_symbolic_values` 840 / `parse_unquote` 1761 recurse on them without end.
- **Reachable:** a `"\u0000"` literal (escape.cpp → `to_char(0)`), `(char 0)`, or a source file with a NUL. jank's own `pr-str` prints NUL raw (escape.cpp 148–201; character.cpp 12–37), so printing a value and reading it back hangs.
- **Search:**
  - `exhaust` over bytes ≤ 3 found `"\0` after 265 timelines.
  - `explore` found `"(\0(` after 80.
  - Without NUL, `exhaust` is complete over 1,222,981 byte strings of length ≤ 4 with nothing found.
- **Theorems:** `peek_nul`, `symbol_loop_stuck_on_nul`, `string_loop_stuck_on_nul`, `comment_loop_stuck_on_nul`: one loop step maps the state to itself.

**R2. Adjacent atoms need whitespace.** Status: both.
```clojure
(read-string "[1\"a\"]")  ; Clojure [1 "a"]   jank error "expected whitespace"
(println"hi")             ; Clojure prints    jank fails to load
```
- **Path:** lex.cpp sets `require_space` at 1073, 1198, 1297 and 1350; `check_whitespace` is at 442–450.
- **Search:** residual `exhaust` found `""u` after 160 timelines.
- **Caveat:** jank's error reference (book `reference/error/lex/expecting-whitespace.md`) describes this error, so it can be read as documented.

**R3. `-0` followed by anything but a space or the end is an error.** Status: both.
```clojure
[-0]       ; Clojure [0]   jank "This base-8 number literal ended unexpectedly."
(- 5 -0)   ; Clojure 5     jank: the same error
```
`-0` at the end of a line fails too.
- **Path:** lex.cpp 691–707: `peek(2)` is not `' '`, so `radix = 8` and `++pos`. The single-`0` escape at 1030 compares `pos == token_start`, which is now false, so 1056–1067 raises the error.

**R4. A leading `+` makes a symbol.** Status: both.
```clojure
(+ +5 1)   ; Clojure 6   jank: unable to resolve symbol +5
```
- **Path:** lex.cpp 1168 (`case '+'` goes to symbols); the TODO comment is at 1070.
- **Search:** `exhaust` found `+0` after 146 timelines.

**R5. INT64_MIN reads as a BigInt; integral big ratios read as longs.** Status: both.
```clojure
(pr-str -9223372036854775808)   ; Clojure "-9223372036854775808"   jank "-9223372036854775808N"
(pr-str 9223372036854775808/2)  ; Clojure "4611686018427387904N"   jank "4611686018427387904"
```
- **Path:** lex.cpp 1145–1156 runs `strtoll` on the digits after the `-`, gets ERANGE and builds a `big_integer`. `ratio.cpp` `create` 88–101 narrows to an i64.
- **Consequence:** the hash differs from the long's (round 1 D12).
- **Theorem:** `negated_digits_never_min`.

**R6. Radix literals.** Status: both.
```clojure
36rN    ; Clojure 23    jank 0N
36rZN   ; Clojure 1283  jank 35N
16re    ; Clojure 14    jank error
36rr    ; Clojure 27    jank error
258r11  ; Clojure error jank 3
```
- **Path:** lex.cpp:
  - `N`/`M` are always taken as suffixes (955–1012);
  - `e` and `r` after the radix `continue` past the reset of `expecting_more_digits` (785, 845–847, 1056–1063);
  - the radix is `static_cast<i8>(std::stoi(…))` (1083).
- **Theorem:** `radix_258_is_2`.

**R7. Leading zeros.** Status: both.
```clojure
08M     ; Clojure 8M     jank error
-010/3  ; Clojure -10/3  jank -8/3
-09/3   ; Clojure -3     jank throws (boost)
```
- **Path:**
  - A leading `0` or `-0` sets radix 8 (lex.cpp 691–723), and `M` keeps it (1107–1122).
  - A ratio numerator is passed whole to boost `cpp_int::assign` (906–910), which reads a leading `0` as octal.
- **Caveat:** RA5 (boost's prefix rule; the submodule was not checked out).

**R8. Octal string escapes are rejected.** Status: both.
```clojure
"\0"     ; Clojure "\u0000"   jank error "invalid escape sequence"
"\101"   ; Clojure "A"        jank error
```
- **Path:** util/escape.cpp `unescape` 35–145 has no octal case.
- jank also accepts `"\a"`, `"\v"` and `"\?"`, which Clojure rejects.

**R9. Comments end only at `\n`.** Status: both.
```clojure
(read-string ";x\r42")   ; Clojure 42   jank EOF error
```
- **Path:** lex.cpp 643 (and 1419 for `#!`).
- **Theorem:** `comment_continues_past_cr`.

**R10. `@x` reads as an unqualified `(deref x)`.** Status: both.
```clojure
(let [deref (fn [_] :shadowed)] @(atom 1))   ; Clojure 1   jank :shadowed
```
- **Path:** parse.cpp `parse_deref` 1803. In the analyzer, locals are looked up first (processor.cpp `analyze_symbol` 1583, locals at 1599).

**R11. Metadata hints.** Status: both.
```clojure
(meta '^"String" x)   ; Clojure {:tag "String"}       jank read error
(meta '^[long] x)     ; Clojure {:param-tags [long]}  jank read error
(meta '^foo x)        ; Clojure {:tag foo}            jank {:tag (quote foo)}
```
- **Path:** parse.cpp `parse_meta_hint` 590–674 (quotes the tag at 614–625).

**R12. `#()` rejects `%10`, `%20`, ….** Status: both.
```clojure
(#(+ %10 %1) 1 2 3 4 5 6 7 8 9 10)   ; Clojure 11   jank "invalid shorthand function parameter"
```
- **Path:** parse.cpp `parse_symbol` 1856–1860 (`all_digits &= isdigit(c) && c != '0'`).
- jank's own book (`reference/error/parse/invalid-shorthand-function-parameter.md`) documents `%n` for any n ≥ 1.

**R13. Literal duplicates that Clojure rejects are accepted.** Status: both.
```clojure
{1 :a 1N :b}        ; Clojure "Duplicate key"   jank {1 :b}
(count #{0.0 -0.0}) ; Clojure error             jank 2
```
- **Path:** the duplicate check in parse.cpp `parse_map` 432/449–459 and `parse_reader_macro_set` 722–743 hashes, and `1` and `1N` hash differently (D12).

**R14. `@` does not end a token, and `~` before a non-ASCII character breaks.** Status: both.
```clojure
(read-string "a@b")   ; Clojure a, then (deref b)   jank the symbol a@b
`(f ~λ)               ; Clojure works               jank error (invalid UTF-8)
```
- **Path:** lex.cpp `is_special_char` 493–497 lacks `@`. At 1467–1468, `~` adds the peeked character's length, so for a multi-byte character the next token starts mid-character.

**R15. Unicode whitespace is not whitespace.** Status: both.
```clojure
(read-string "(\u2003a)")   ; Clojure (a)    jank (\u2003a), a symbol starting with EM SPACE
(read-string "[1\u001c2]")  ; Clojure [1 2]  jank error
```
- **Path:** lex.cpp 558 skips whitespace with byte-level `isspace`. Java's `isWhitespace` also counts U+001C–1F, U+2000–200A and others.
- **Search:** `exhaust` found U+2003 after 16 timelines. Without it, `exhaust` is complete over 579,195 timelines.

**R16. `:/` reads as a keyword with an empty name.** Status: both.
```clojure
(name (read-string ":/"))   ; Clojure "/"   jank ""
```
- **Path:** parse.cpp `parse_keyword` 1912–1929.

**R17. Namespaced map literals and `#^` are unsupported.** Status: both.
```clojure
#:a{:b 1}   ; Clojure {:a/b 1}   jank "unsupported reader macro"
```
- **Path:** parse.cpp `parse_reader_macro` 690–706.

**R18. Java-only regex syntax is rejected at read time.** Status: both.
```clojure
#"(?i)abc"   ; Clojure: case-insensitive   jank read error (std::regex_error)
```
The same holds for `(?<=…)`, `(?<n>…)`, `a*+` and `(?>…)`.
- **Path:** parse.cpp `parse_regex` 888–913 → re_pattern.cpp 6–10 (`std::regex` ECMAScript).
- (Fork B's B30.)

**R19. Syntax quote.** Status: both.
```clojure
`(require 'clojure.set)       ; Clojure (… (quote clojure.set))   jank (… (quote user/clojure.set))
(let [a 1 b 1] `(~@#{a b}))   ; Clojure (1)                       jank (1 1)
```
- **Path:** parse.cpp 1489–1500 (qualification) and 1364–1371 (literal-set fold).
- **Search:** `exhaust` found it after 17 timelines (`` `a.b ``). A residual search found the set case after 305.

**R20. `read-string` also parses the second form.** Status: both.
```clojure
(binding [*default-data-reader-fn* (fn [t v] (println "ran") v)] (read-string "1 #x 2"))
; Clojure prints nothing   jank prints "ran"
(read-string "1 \"\u0000\"")   ; Clojure 1   jank never returns
```
- **Path:** context.cpp `read_string` 261–283: the range-for's `++it` parses the next form before the `nth_form` check.

**R21. Every read collection and symbol carries `{:jank/source …}` metadata.** Status: both.
```clojure
(meta (read-string "[1 2]"))   ; Clojure nil   jank {:jank/source {...}}
```
- **Path:** parse.cpp 387–418, 487–507, 745, 1897; core/meta.cpp `source_to_meta` 171–228.

**R22. Under the C locale (LANG unset), non-ASCII text fails.** Status: both.
```clojure
(str "é")   ; Clojure "é"   jank "unterminated string"
"\u00e9"    ; Clojure "é"   jank "?"
```
- **Path:** c_api.cpp 1110 sets `std::locale::global(std::locale(""))`; then lex.cpp 453 (`mbrtowc`) and escape.cpp 60 (`to_char(cp, "?")`).
- (Merged with fork B's B14.)
- **Caveat:** RA1 (glibc's ASCII C locale).

### Analyzer (analyze/processor.cpp, analyze/cpp_util.cpp, runtime/context.cpp)

**R23. An `if` whose branches have different native C++ types returns their common type.** Status: both.
```clojure
(if true 1 2.5)                 ; Clojure 1     jank 1.0
(or true 0)                     ; Clojure true  jank 1
(if (and false 5) :yes :no)     ; Clojure :no   jank :yes
((fn [x] (if (and (pos? x) 5) :pos :non-pos)) -1)   ; Clojure :non-pos   jank :pos
```
- **Path:**
  - Literals are native `cpp_literal`s: cpp_util.cpp `literal_type` 615/653 and processor.cpp `analyze_primitive_literal` 3241.
  - `analyze_if` 2740–2782 calls cpp_util.cpp `find_branch_common_type` 1907–1995.
  - ir/processor.cpp 659 assigns each branch to one typed local.
- **Search:** `explore` found it after 136 timelines; the depth-1 tally has 288 programs; interop world IX has 24 of 196.
- **Theorem:** `if_merges_distinct_natives`.
- (Analyzer A1, interop I12.)

**R24. A `loop` local keeps a literal's native type, and `recur` converts into it.** Status: changed.
```clojure
(loop [x 0 n 0] (if (= n 1) x (recur 1.5 1)))               ; Clojure 1.5         jank 1
(loop [x 2147483647 n 0] (if (= n 1) x (recur (inc x) 1)))  ; Clojure 2147483648  jank -2147483648
(loop [x 0] (if (< x 10) (recur (+ x 0.5)) x))              ; Clojure 10.0        jank never ends
(defn g [x] (loop [acc 0 i 0] (if (< i 2) (recur (+ acc x) (inc i)) acc))) (g 1.5)
; Clojure 3.0   jank 2 (it threw on f3d82d654)
```
- **Path:** processor.cpp `analyze_let` 2397–2400, `analyze_recur` 2183–2219, `apply_implicit_conversion` 1074/1088; cpp_util.cpp `mutable_type` 1064; convert/builtin.hpp 238/288. On 7135b7708, `from_object` uses `to_integer()`/`to_real()`, so it truncates instead of throwing. nil and keywords still throw.
- **Theorems:** `loop_local_native`, `int_local_wraps`.
- (Analyzer A2, interop I2.)

**R25. Arithmetic on literals is 32-bit.** Status: both.
```clojure
(+ 2147483647 1)   ; Clojure 2147483648   jank -2147483648
(* 65536 65536)    ; Clojure 4294967296   jank 0
(loop [i 0 acc 0] (if (< i 100000) (recur (inc i) (+ acc i)) acc))   ; Clojure 4999950000   jank 704982704
```
- **Path:** cpp_util.cpp `literal_type` 629–666 types literals that fit 32 bits as `int`. `:inline` expansion (processor.cpp 3554; core.jank 1372, 1405) reaches core/math.hpp `add` 117 / 173–178 on two `int`s.
- This answers round 1's assumption A6: literals take the same wrapping path as D1, without passing through a function parameter.
- The book says overflow wraps, but these operands are well inside the long range.
- **Theorems:** `literal_add_exact_iff`, `literal_mul_exact_iff`.
- (Interop I1, analyzer A14.)

**R26. A `case` gets one C++ type, chosen from its last branch.** Status: 7135 only.
```clojure
(case 5 1 1.5 0)                 ; Clojure 0      jank 0.0
(case 1 1 1.5 2 7 0)             ; Clojure 1.5    jank 1
(case 1 1 "one" 2 :two :other)   ; Clojure "one"  jank throws a non-object std::runtime_error (try_object), which object catches miss
```
- **Path:** processor.cpp `analyze_case` 1483–1581 with cpp_util.cpp 1908; expr/case.cpp 71; ir/processor.cpp 808; cpp_processor.cpp 1321.
- **Search:** codegen seed 312; `exhaust` found `(case 1 1 :k 2 7 7)` after 3,466 timelines.
- **Theorems:** `case_last_branch_wins`, `case_order_matters`.
- (Analyzer A13, codegen G16.)

**R27. `recur` in a fn inside a `loop` (or in the loop's bindings) targets the loop.** Status: both.
```clojure
((loop [a 1 b 2] (fn [y] (if y (recur nil) :done))) 5)   ; Clojure :done   jank "recur … requires exactly 2"
```
- **Path:** `analyze_recur` 2143–2158 checks `loop_details`, which only `analyze_loop` 2611–2613 sets and restores; `analyze_let` 2340–2342 sets it too.
- **Search:** `explore` found it after 246 timelines.

**R28. An outer local shadows a named fn's own name.** Status: both.
```clojure
((fn [f] ((fn f [n] (if (= n 0) :done (f 0))) 1)) 7)   ; Clojure :done   jank "7 is not callable"
```
- **Path:** `analyze_symbol` looks up locals at 1599 before the fn name at 1660.
- **Theorem:** `outer_local_wins_over_fn_name`.

**R29. A named fn's name does not shadow a macro of the same name.** Status: both.
```clojure
((fn when [n] (if (= n 0) :done (when 0))) 1)   ; Clojure :done   jank nil
```
- **Path:** `analyze_call` 3501.

**R30. Macros get the wrong `&form` and `&env`.** Status: both.
```clojure
(defmacro form-of [& _] (list 'quote &form)) (form-of 1 2)   ; Clojure (form-of 1 2)   jank ((1 2))
(defmacro n [] (count &env)) (let [a 1] (n))                 ; Clojure 1               jank macroexpansion exception
```
- **Path:** context.cpp `macroexpand1` 634 builds `cons(cons(rest(o), {}), o)`, with a TODO about `&env`.
- **Theorem:** `macro_arguments`.

**R31. A collection returned by a macro carries `{:jank/macro-expansion …}` metadata at run time.** Status: both.
```clojure
(defmacro mk [& xs] (vec xs)) (meta (mk 1 2))   ; Clojure nil   jank {:jank/macro-expansion (mk 1 2)}
```
- **Path:** context.cpp 642–653; processor.cpp `analyze_collection_meta` 167.
- **Caveat:** only for code loaded from a file.

**R32. Private vars are accessible anywhere inside a macro expansion.** Status: both.
```clojure
(when true other/secret)   ; Clojure "not public"   jank 42
```
- **Path:** processor.cpp `can_access_var` 130–135, checked at `analyze_symbol` 1699.
- **Caveat:** file-loaded code only.

**R33. Boolean literals are C++ `bool`, so inlined arithmetic accepts them.** Status: both.
```clojure
(+ true 1)   ; Clojure ClassCastException   jank 2
```
- **Path:** cpp_util.cpp `literal_type` 615; core.jank 1372, 1646.

**R34. `(:k)` returns nil.** Status: both.
```clojure
(:k)   ; Clojure ArityException   jank nil
```
- **Path:** processor.cpp `analyze_call` 3571–3578.

**R35. A `catch` without a binding is undefined behavior.** Status: both.
```clojure
(try 1 (catch :default))   ; Clojure compile error   jank: unwrap() of an empty option in release (UB)
```
- **Path:** processor.cpp `analyze_try` 3048.

**R36. An object loop local given a native `recur` value fails to compile.** Status: both. Low confidence.
```clojure
(loop [x nil n 0] (if (= n 1) x (recur 5 1)))   ; Clojure 5   jank compile error
```
- **Path:** processor.cpp `analyze_recur` 2183–2211.
- **Caveat:** holds only if CppInterOp's `GetBuiltinOperatorType(=, object_ref, object_ref)` returns null.

### Code generator (ir/, codegen/cpp_processor.cpp, evaluate.cpp)

On 7135b7708, cpp_processor.cpp was edited in place (no line moved), and ir/processor.cpp is one line lower from line 520 on. The control search with every known class excluded finds nothing: 0 of 2,000 seeds, and `exhaust` at depth 1 is complete over 3,464 timelines.

**R37. A call evaluates its operands before its operator.** Status: both.
```clojure
(let [] ((do (println :f) identity) (do (println :a) 1)))   ; Clojure :f then :a   jank :a then :f
```
- **Path:** ir/processor.cpp `gen(call)` 110–121. The interpreted top level (evaluate.cpp 376) evaluates the operator first, so only compiled code is affected.

**R38. Local names that munge alike are the same local.** Status: both.
```clojure
(let [a-b 1 a_b 2] a-b)   ; Clojure 1   jank 2
((fn [a.b] a.b) 1)        ; Clojure 1   jank C++ syntax error
```
- **Path:** ir/processor.cpp 206, 249, 519; cpp_processor.cpp 1966–1970; core/munge.cpp 9–36.
- **Search:** `exhaust` found it after 7,148 timelines.
- **Theorems:** `munge_dash_underscore`, `munge_keeps_dot`.

**R39. A nested loop that rebinds a name breaks the outer `recur`.** Status: both.
```clojure
(loop [i 0] (let [z (loop [i 5] (if (< i 6) (recur (inc i)) i))] (if (< i 2) (recur (inc i)) i)))
; Clojure 2   jank C++ error "use of undeclared identifier"
```
- **Path:** ir/processor.cpp 270/541: `local_to_loop_shadow` is never restored; read at 422/439.

**R40. A nested fn that refers to an enclosing fn with a munged name crashes the compiler.** Status: both.
```clojure
((fn my-f [] (fn [] my-f)))   ; Clojure the fn   jank std::out_of_range in hoist_scoped_values
```
- **Path:** ir/processor.cpp 449.

**R41. Two `letfn`s in one fn emit invalid C++.** Status: both.
```clojure
(fn [] [(letfn [(f [] (g)) (g [] 1)] (f)) (letfn [(h [] 2)] (h))])   ; Clojure [1 2]   jank C++ error
```
- **Path:** cpp_processor.cpp 116, 897–904: `deferred_bindings` is never cleared.

**R42. Literal constants that are `=` and hash alike share one object.** Status: both.
```clojure
(let [a [[]] b ['()]] (list? (first b)))   ; Clojure true   jank false
```
- **Path:** cpp_processor.cpp 153–157; object.cpp 346.
- **Caveat:** medium.

**R43. `def` metadata is stored as code text.** Status: both.
```clojure
(defn f [x] x) (:arglists (meta #'f))                     ; Clojure ([x])   jank, AOT: (quote ([x]))
(let [y 5] (def ^{:k y} x 1)) (:k (meta #'x))             ; Clojure 5       jank, JIT: "Unable to resolve symbol: y"
```
- **Path:** ir/processor.cpp 91–95; cpp_processor.cpp 536–557; lazy_meta.cpp 30–46.

**R44. `case` on a long outside the i32 range.** Status: both.
```clojure
(case 2147483648 2147483648 :hit :miss)   ; Clojure :hit   jank :miss
```
A `-9223372036854775808` key fails to compile in jank.
- **Path:** c_api.cpp 991–1037; cpp_processor.cpp 1141–1170.
- **Theorem:** `case_integer_not_self`.

**R45. At -O3 (the template's release profile), var reads are merged across a redefinition.** Status: both.
```clojure
(def x 1) (defn f [] (let [a x] (def x 2) [a x])) (f)   ; Clojure [1 2]   jank [1 1]
```
- **Path:** ir/opt/hoist_var_derefs.cpp 55–153; cli.cpp 213–217.

**R46. At -O1/-O3, a deduplicated `case` value or loop binding crashes the compiler.** Status: both.
```clojure
(def mode 1) (defn f [] [mode (case mode 1 :one 2 :two :other)])   ; -O3: std::out_of_range
```
- **Path:** ir/rewrite.cpp 181–201; hoist_scoped_values.cpp 136.
- **Theorems:** `rewrite_keeps_case_value`, `rewrite_keeps_loop_values`.

**R47. A closure whose parameter has the fn's own name reads its context from the argument.** Status: both.
```clojure
(let [y 1] ((fn f [f] y) 5))   ; Clojure 1   jank UB
```
- **Path:** cpp_processor.cpp 1946–1957, 1984–1993.

**R48. At -O1/-O3, a constant used in two branches of a catch or finally body breaks the `try`.** Status: both.
```clojure
(try (f) (catch cpp/jank.runtime.object_ref e (if (g) :x :x)))   ; jank C++ "expected catch"
```
- **Path:** ir/opt/hoist_literals.cpp 98–124; cpp_processor.cpp 1065–1070, 1085–1086.

**R49. AOT: a NUL truncates string and character literals.** Status: both.
```clojure
(def s "a\u0000b") (count s)   ; Clojure 3   jank 1
```
- **Path:** cpp_processor.cpp 335–340, 360–373; codegen/api.cpp 62–65.
- **Theorem:** `cstring_drops_after_nul`.

**R50. AOT: ratio literals with a part outside i64 are wrong.** Status: both.
```clojure
1/9223372036854775808   ; jank -1/9223372036854775808
```
- **Path:** cpp_processor.cpp 317–323 → ratio.cpp 103–106.
- **Theorem:** `big_literal_negative`.

**R51. AOT: `#inst` literals cannot be compiled.** Status: both.
```clojure
(def t #inst "2020-01-01")   ; jank "Unimplemented constant codegen"
```
- **Path:** cpp_processor.cpp 481–485.

### Strings and characters (fork B, plus the strings agent)

Strings are UTF-8 bytes in jank (documented). Fork B judged results against Clojure's UTF-16 behavior. Judged by code points instead, R53 and R57 reduce to their inconsistency with jank's own byte-based `count`.

**R52. `count`, `nth`, `get`, `contains?` and `subs` work on bytes.** Status: both.
```clojure
(count "é")       ; Clojure 1     jank 2
(subs "é" 0 1)    ; Clojure "é"   jank "\xC3" (invalid UTF-8)
```
- **Path:** persistent_string.cpp 78/95/107/139/179; seq.cpp `sequence_length` 842, `nth` 648; core.cpp `subs` 398/411.
- **Theorem:** `count_eq_iff` (jank's count equals Clojure's iff the text is ASCII).

**R53. `seq` walks code points, so it disagrees with jank's own `count`.** Status: both.
```clojure
(count (seq "a😀"))   ; Clojure 3   jank 2, while (count "a😀") is 5 in jank
```
- **Path:** persistent_string_sequence.cpp 78/122/128.

**R54. The seq of a string whose last character is cut short reads past the end.** Status: both.
```clojure
(vec (seq (subs "aé" 0 2)))   ; jank: UB read
```
- **Path:** persistent_string_sequence.cpp 128–138.
- **Theorem:** `seq_walks_past_end`.

**R55. `=` with a string seq on the left is not reflexive.** Status: both.
```clojure
(let [x (seq "é")] (= x x))   ; Clojure true   jank false
```
- **Path:** persistent_string_sequence.cpp 34 → seq_ext.hpp 13 → core/equal.cpp 8.
- **Theorem:** `seq_not_reflexive`.

**R56. A string seq and an equal vector hash differently.** Status: both.
```clojure
(contains? (hash-set (seq "a")) [\a])   ; Clojure true   jank false
```
- **Path:** persistent_string_sequence.cpp 72.
- **Theorem:** `seq_hash_inconsistent`.

**R57. `compare`/`sort` on strings use UTF-8 byte order.** Status: both.
```clojure
(compare "Ａ" "😀")   ; Clojure positive   jank negative
```
- **Path:** immutable_string.hpp 576.
- **Theorem:** `compare_fullwidth_emoji`.

**R58. `index-of`/`last-index-of` return byte indices and mishandle negative or past-the-end starts.** Status: both.
```clojure
(clojure.string/index-of "a" "a" -1)   ; Clojure 0   jank nil
```
- **Path:** string.jank 227/240 → string_native.cpp 257/264.
- **Theorem:** `index_of_negative`.

**R59. `trim`/`blank?` use C `isspace` on bytes.** Status: both.
```clojure
(clojure.string/trim "\u2003a")   ; Clojure "a"   jank "\u2003a"
```
- **Path:** string_native.cpp 271, 304; immutable_string.hpp 635.

**R60. Case mapping is one code point at a time, through the locale.** Status: both.
```clojure
(clojure.string/upper-case "ß")   ; Clojure "SS"   jank "ß"
```
- **Path:** util/string.cpp 14/26.

**R61. `capitalize` lower-cases everything, then upper-cases only an ASCII first byte.** Status: both.
```clojure
(clojure.string/capitalize "Éa")   ; Clojure "Éa"   jank "éa"
```
- **Path:** util/string.cpp 54.

**R62. `replace` with an empty match splits UTF-8 sequences.** Status: both.
```clojure
(clojure.string/replace "é" "" "-")   ; Clojure "-é-"   jank "-\xC3-\xA9-"
```
- **Path:** string_native.cpp 171–181.

**R63. `escape` never matches non-ASCII keys.** Status: both.
```clojure
(clojure.string/escape "é" {\é "X"})   ; Clojure "X"   jank "é"
```
- **Path:** string.jank 207–225.

**R64. `char` and `int` depend on the locale and use other ranges.** Status: both.
```clojure
(char 233)     ; Clojure \é       jank, C locale: throws
(char 55296)   ; Clojure \uD800   jank throws
```
- **Path:** jtl/utf8.cpp `to_char` 170; character.cpp 104.

**R65. `(keyword ns name)` joins the two, then re-splits at the first `/`.** Status: both.
```clojure
(namespace (keyword "a/b" "c"))   ; Clojure "a/b"   jank "a"
```
- **Path:** core.cpp 521 → context.cpp 561/584/588 → symbol.cpp `separate` 8.

**R66. `char` wraps past its range check.** Status: both.
```clojure
(char -4294967231)   ; Clojure throws   jank \A
```
- **Path:** jtl/utf8.cpp 172 and 178 (`static_cast<wchar_t>`).

**R67. A nil namespace takes the splitting path.** Status: both.
```clojure
(namespace (symbol nil "b/c"))   ; Clojure nil   jank "b"
```
- **Path:** core.jank `symbol` 520–527 → core.cpp 97 → symbol.cpp 8.

### Printing

**R68. Doubles print through `to_chars`' shortest form.** Status: both.
```clojure
(str 100000.0)   ; Clojure "100000.0"   jank "1e+05"
(str 1.0E-4)     ; Clojure "1.0E-4"     jank "1e-04"
```
- **Path:** number.cpp 291/314 → string_builder.cpp 83–132.
- **Evidence:** 442 of 574 drawn doubles differ.

**R69. `str` of a collection prints strings and characters unquoted.** Status: both.
```clojure
(str ["a" \b])   ; Clojure "[\"a\" \\b]"   jank "[a b]"
```
- **Path:** persistent_vector.cpp 96; base_persistent_map.cpp 62.

**R70. `pr-str` escapes BEL and VT as `\a` and `\v`, which Clojure's reader rejects.** Status: both.
- **Path:** util/escape.cpp 179/183.

**R71. `pr-str` of a regex does not escape `"`.** Status: both.
```clojure
(pr-str (re-pattern "\""))   ; Clojure #"\""   jank #""" (unreadable)
```
- **Path:** re_pattern.cpp 23.

**R72. BigDecimals lose their scale and gain `.0`.** Status: both.
```clojure
(str 1M)   ; Clojure "1"   jank "1.0"
```
- **Path:** big_decimal.cpp 157/169.
- **Caveat:** depends on boost's `str()` (RB7).

**R73. `pr-str` takes exactly one argument.** Status: both.
```clojure
(pr-str 1 2)   ; Clojure "1 2"   jank arity error
```
- **Path:** core.jank 628–631.

**R74. The printer's dynamic vars do not work.** Status: both.
```clojure
(binding [*print-length* 2] (pr-str [1 2 3]))   ; jank: *print-length* cannot be resolved
```
- **Path:** core.jank 41 (`*print-readably*` is nil and never read).

**R75. `print-method` is never called.** Status: both.
- **Path:** core.cpp `pr` 192 prints with C++ `to_code_string`.

**R76. `print` of a string seq prints readable characters.** Status: both.
```clojure
(print-str (seq "ab"))   ; Clojure "(a b)"   jank "(\\a \\b)"
```
- **Path:** persistent_string_sequence.cpp 39–56.

**R77. `print`, `str` of collections and `print-str` write `Infinity`/`NaN`.** Status: both.
```clojure
(print-str ##Inf)   ; Clojure "##Inf"    jank "Infinity"
(str [##NaN])       ; Clojure "[##NaN]"  jank "[NaN]"
```
- **Path:** number.cpp 409/432; core.cpp 141/169.
- **Theorem:** `print_inf`.

### Regex (std::regex ECMAScript over bytes)

**R78. Regexes match bytes.** Status: both.
```clojure
(re-find #"." "é")   ; Clojure "é"   jank "\xC3"
```
- **Path:** re_pattern.cpp 9.

**R79. `$` does not match before a final newline.** Status: both.
```clojure
(re-find #"a$" "a\n")   ; Clojure "a"   jank nil
```

**R80. A group that did not participate is `""`.** Status: both.
```clojure
(re-find #"(a)?b" "b")   ; Clojure ["b" nil]   jank ["b" ""]
```
- **Path:** core.cpp 944.

**R81. `re-seq` re-searches the remainder as a new string.** Status: both.
```clojure
(re-seq #"^a" "aa")   ; Clojure ("a")     jank ("a" "a")
(re-seq #"a*" "b")    ; Clojure ("" "")   jank infinite
```
- **Path:** core.cpp `re_find` 972.

**R82. `re-matches` takes the first match from position 0, then checks it covers the input.** Status: both.
```clojure
(re-matches #"a|ab" "ab")   ; Clojure "ab"   jank nil
```
- **Path:** core.cpp 1002.

**R83. Regex input is cut at the first NUL.** Status: both.
```clojure
(re-find #"b" "a\u0000b")   ; Clojure "b"   jank nil
```
- **Path:** re_matcher.cpp 11; core.cpp 1006.

**R84. Replacements follow ECMAScript rules, and a function receives the match string.** Status: both.
```clojure
(clojure.string/replace "a1" #"(a)(\d)" (fn [[_ x y]] (str y x)))   ; Clojure "1a"   jank "1"
```
- **Path:** string_native.cpp 224/247.

**R85. `split`/`replace` retry a non-empty match after an empty one.** Status: both.
```clojure
(clojure.string/replace "aa" #"a*?" "-")   ; Clojure "-a-a-"   jank "-----"
```
- **Path:** string_native.cpp 224/233/403 (`std::regex_iterator`).
- **Evidence:** 176 of 4,920 ASCII questions differ.
- **Caveat:** libstdc++.

### C++ interop (analyze/cpp_util.cpp, processor.cpp, convert/builtin.hpp, cpp_processor.cpp)

**R86. A number object reaching a native `char` or `bool` parameter throws; the literal converts.** Status: changed.
```clojure
(cpp/raw "char f(char c) { return c; }") (defn h [x] (cpp/f x)) (h 65)   ; jank throws; (cpp/f 65) works
```
- **Path:** convert/builtin.hpp 162 (bool) and 181–183 (char).
- **What changed:** on f3d82d654, integer↔floating parameters threw too. 7135b7708 converts them through `to_integer`/`to_real` (238/288). Literal against parameter: 17 of 156 calls disagree (was 45).

**R87. A string literal passed to a `char const *` parameter is rejected.** Status: both.
```clojure
(cpp/raw "unsigned long len(char const *s) { return __builtin_strlen(s); }") (cpp/len "abc")
; C++ exact match   jank analyze/invalid-cpp-conversion
```
- **Path:** cpp_util.cpp 2069–2090; processor.cpp 571.
- **Caveat:** IA11 (CppInterOp on array pointee types).

**R88. `cpp/new` uses brace initialization.** Status: changed.
```clojure
(cpp/new (std.vector cpp/int) 3)   ; jank holds [3]; ((std.vector cpp/int) 3) holds 3 zeros
```
- **Path:** cpp_processor.cpp 1878–1889.
- **Correction:** the narrowing errors reported earlier do not happen; the JIT passes `-Wno-c++11-narrowing` (jit/processor_dynamic.cpp 250).

**R89. `if` on a native unscoped enum uses C++ truthiness.** Status: both.
```clojure
(cpp/raw "enum color { red, green };") (if cpp/red :t :f)   ; expected :t   jank :f
```
- **Path:** processor.cpp 2684–2702. jank's own comment there says non-bool built-ins are boxed.

**R90. `cpp/cast` accepts invalid casts and rejects valid ones.** Status: both.
- 14 valid `static_cast`s are rejected: base→derived pointers, to and from enums.
- 9 invalid ones are accepted, then fail in the JIT: casting away const, function↔`void*`.
- **Path:** cpp_util.cpp 962–967; processor.cpp 4305–4307.
- **Evidence:** 27 of 196 pairs.

**R91. Box type names lose cv-qualifiers and function-pointer-ness.** Status: both.
```clojure
(let [p (cpp/cast (:* (:const base)) cpp/nullptr) b (cpp/box p)] (cpp/unbox (:* base) b))
; succeeds; the book says unbox checks the type
```
- **Path:** cpp_util.cpp 413–420.
- **Evidence:** 20 of 64 box/unbox pairs.

**R92. Native values come back with loss.** Status: both.
- `cpp/UINT64_MAX` comes back as -1.
- `\é` passed to a `char` parameter becomes byte 0xC3.
- **Path:** builtin.hpp 181–183, 227–229, 277–279, 303–315.

**R93. A `char *` parameter accepts a string in analysis, then the C++ does not compile.** Status: both.
- **Path:** builtin.hpp 312.

**R94. The DSL accepts integer modifiers that name no type.** Status: both.
- Examples: `(:unsigned cpp/bool)`, `(:short (:long cpp/int))`.
- **Path:** processor.cpp 5131–5238.
- **Evidence:** 46 of 147 chains.

**R95. A jank char passed to an integer parameter is 0 under the C locale.** Status: both. From reading only.
- **Path:** builtin.hpp 238 → character.cpp 104.

### Core: compare, multimethods, namespaces, sorted collections, destructuring, defn

**R96. Booleans can't be compared with each other, but compare with numbers as 0/1.** Status: both.
```clojure
(compare true false)   ; Clojure 1   jank throws
(compare true 1)       ; Clojure CCE jank 0
```
- **Path:** number.cpp 56 → visit.hpp 463 (no boolean case); equal.cpp 24; sort is seq.cpp 1098.
- **Theorem:** `bool_bool_throws`.

**R97. A keyword compared with a non-keyword is undefined behavior.** Status: both.
```clojure
(try (compare :a 1) (catch Exception _ :caught))   ; Clojure :caught   jank UB (debug: abort)
```
- **Path:** keyword.cpp 50; rtti.hpp 50–58.
- **Theorem:** `keyword_vs_other_ub`.

**R98. `compare` has no identity shortcut.** Status: both.
```clojure
(let [x '(1)] (compare x x))   ; Clojure 0   jank throws
```
- **Path:** equal.cpp 24; object.cpp 228.

**R99. BigDecimal against double compares exactly.** Status: both.
```clojure
(compare 0.1M 0.1)   ; Clojure 0   jank -1
```
- **Path:** big_decimal.cpp 182; number.cpp 460.
- **Caveat:** RC2 (boost).

**R100. `prefer-method` declared on an ancestor is ignored.** Status: both.
```clojure
(derive ::c ::a) (derive ::c ::b) (derive ::b ::b0)
(defmethod f ::a [_] :a) (defmethod f ::b [_] :b) (prefer-method f ::a ::b0)
(f ::c)   ; Clojure :a   jank "neither is preferred"
```
- **Path:** multi_function.cpp 137 (caches the var, not its value), 186, 263.
- **Search:** `exhaust` found it after 28,889 timelines.
- **Theorem:** `no_prefs_same` (without prefers, dispatch agrees).

**R101. `get-method` throws when nothing applies.** Status: both.
```clojure
(get-method f ::b)   ; Clojure nil   jank throws
```
- **Path:** core.cpp 613 → multi_function.cpp 234.

**R102. `intern` rebinds a referred var.** Status: both.
```clojure
(intern 'user 'map 7) @#'clojure.core/map   ; Clojure fn   jank 7
```
- **Path:** ns.cpp 26–47; core.cpp 789; core.jank 4984.

**R103. `remove-ns` removes clojure.core.** Status: both.
- **Path:** core.cpp 840; context.cpp 420.

**R104. `=` between sorted collections with incomparable keys throws.** Status: both.
```clojure
(= (sorted-set 0) (sorted-set "a"))   ; Clojure false   jank throws
```
- **Path:** persistent_sorted_set.cpp 56; base_persistent_map.cpp 31.
- **Search:** `exhaust` found it after 942 timelines.

**R105. Sorted `find`/`select-keys` return the queried key.** Status: both.
```clojure
(find (sorted-map 1 :x) 1.0)   ; Clojure [1 :x]   jank [1.0 :x]
```
- **Path:** persistent_sorted_map.cpp 80; transient_sorted_map.cpp 62.
- **Theorem:** `find_returns_query_key`.

**R106. `reset-meta!` on `(sorted-map)` mutates the shared static empty.** Status: both.
- **Path:** meta.cpp 84; persistent_sorted_map.cpp 33.

**R107. Kwargs destructuring with a trailing seq of entries throws.** Status: both.
```clojure
((fn [& {:as m}] m) :a 1 (seq {:d 4}))   ; Clojure {:a 1 :d 4}   jank "invalid map entry"
```
- **Path:** core.jank 3427–3436; base_persistent_map.cpp 169.
- **Search:** `exhaust` found it after 299,132 timelines.

**R108. `defn` expands to a named fn, so recursion bypasses the var.** Status: both.
```clojure
(defn countdown [n] (if (pos? n) (countdown (dec n)) :done)) (def orig countdown)
(defn countdown [n] :redefined) (orig 3)   ; Clojure :redefined   jank :done
```
- **Path:** core.jank `defn` 727–779 (the emission is at 779); processor.cpp 1658–1673.

**R109. Re-evaluating `(ns x)` after shadowing a core name throws.** Status: both.
```clojure
(ns user) (def inc 1) (ns user)   ; Clojure nil   jank throws
```
- **Path:** core.jank 5581 → 4717 → ns.cpp 174.
- **Theorem:** `reload_after_shadowing_throws`.

**R110. `find-var` returns referred vars and accepts unqualified symbols.** Status: both.
```clojure
(find-var 'map)   ; Clojure throws   jank #'clojure.core/map
```
- **Path:** core.cpp 835; context.cpp 136; ns.cpp 117.

**R111. `ns-resolve` resolves aliases in `*ns*`, not in the namespace given.** Status: both.
```clojure
(ns a (:require [other :as s])) (ns b) (ns-resolve 'a 's/y)   ; Clojure #'other/y   jank nil
```
In the nREPL, `lookup ns=my.app sym=str/join` replies `no-info` (it replied `error` on f3d82d654).
- **Path:** core.cpp 865 → ns.cpp 117 → context.cpp 116, 444–454.
- **Theorem:** `alias_resolution`.
- (Core C25, nREPL N2.)

**R112. `in-ns` returns nil.** Status: both.
- **Path:** core.cpp 819.

**R113. Sorted-collection functions are unported (they throw).** Status: both.
- `sorted-set-by`, `sorted-map-by`, `rseq`, `subseq`, `rsubseq`.
- **Path:** core.jank 2438, 5032, 5081, 6510, 6527.

### Sequences

**R114. Integer `range` throws on long spans.** Status: both.
```clojure
(take 2 (range 9223372036854775807))   ; Clojure (0 1)   jank "integer_range overflow"
```
- **Path:** integer_range.cpp 186/197; `next` 113.
- **Theorem:** `count_throws_pos`.

**R115. Integer `range` loses elements when `end - start` wraps.** Status: both.
```clojure
(range -9223372036854775808 0 9223372036854775807)   ; Clojure (… -1)   jank (-9223372036854775808)
```
- **Path:** integer_range.cpp 194/203.
- **Theorem:** `quarter_steps_count`.

**R116. `range` with a real end never ends past 2^31.** Status: both.
```clojure
(count (range 2147483646 2147483649.0))   ; Clojure 3   jank never returns
```
- **Path:** range.cpp 147 (`add` wraps at i32, round 1 D1).
- **Theorem:** `wraps_past_i32`.

**R117. `doseq` mutates sequences the program still holds.** Status: both.
```clojure
(let [w (cons 0 [1 2 3])] (doseq [x w]) (count w))   ; Clojure 4         jank never returns
(let [r (range 1 4)] (doseq [x (cons 0 r)]) r)       ; Clojure (1 2 3)   jank (3)
```
- **Path:**
  - doseq steps with `fresh-seq` / `next-in-place` (core.jank 2742/2750).
  - seq.cpp `cons` stores `tail.seq()` (383).
  - `cons::next` returns that seq (cons.cpp 35), and `object::next_in_place` (object.cpp 303) is the default.
  - The seq is then mutated by persistent_vector_sequence.cpp 137, native_vector_sequence.cpp 126, integer_range.cpp 122 or repeat.cpp 80.
- **Theorem:** `vseq_past_end_never_ends`.

**R118. The `partition-by` transducer sends a partition twice after an early stop.** Status: both.
```clojure
(transduce (partition-by odd?) (completing (fn [acc p] (let [a (conj acc p)] (if (= 2 (count a)) (reduced a) a)))) [] [1 2 3])
; Clojure [[1] [2]]   jank [[1] [2] [2]]
```
- **Path:** core.jank 3320.
- **Theorem:** `partition_by_sends_twice`.

**R119. `chunk-cons` realizes its rest.** Status: both.
```clojure
(first (map inc (range 0.0 ##Inf)))   ; Clojure 1.0   jank stack overflow
```
- **Path:** seq.cpp 1066; core.jank 2061, 2910.
- **Theorem:** `first_of_map_maps_everything`.

**R120. `coll?`/`empty` are wrong for cons, repeat, sort results and array seqs.** Status: changed.
```clojure
(coll? (cons 0 [1]))   ; Clojure true   jank false
```
- **Path:** seq.cpp 77/787.
- **What changed:** lazy and string seqs were fixed in 7135b7708 (29 of 128 questions now deviate, was 33).

**R121. `get-in` on a value without lookup returns nil.** Status: both.
```clojure
(get-in 5 [])   ; Clojure 5   jank nil
```
- **Path:** seq.cpp 475/486/494/509.

**R122. Bytes are unsigned.** Status: both.
```clojure
(aget (byte-array [-1]) 0)   ; Clojure -1   jank 255
```
- **Path:** core/array.cpp 275; builtin.hpp 227.
- **Theorem:** `byte_roundtrip_agree_iff`.

**R123. Map `find` builds the entry from the key passed in.** Status: both.
```clojure
(key (find {[1] :v} '(1)))   ; Clojure [1]   jank (1)
```
- **Path:** persistent_array_map.cpp 60; persistent_hash_map.cpp 99.

**R124. Not ported (they throw or are undefined).** Status: both.
- `sequence` with an xform, `eduction`, `halt-when`, `iteration`, `aset-int`, `make-array`, `to-array-2d`.
- **Path:** core.jank 5533/5540, 7588, 7647, 6068, 6111, 6131.

### nREPL server (src/jank/jank/nrepl, nrepl/server.cpp, evaluate.cpp)

**R125. Output capture is process-global and races.** Status: both.
- Each eval redirects fd 1 with `dup2` to a temp file.
- Two clients: 9,222 of 12,870 interleavings give a wrong `:out`, and 390 leave fd 1 on a temp file for good.
- Shrunk tape: `thread.next` = 0,0,0,0,0,0,1,0,0. Story: t0 completes its capture up to its final flush; t1 runs `dup(1)` while fd 1 is still t0's temp file; t0 restores fd 1 and unlinks its file; t1 then restores fd 1 to t0's unlinked file.
- **Path:** capture.jank start 18, end 39, readback 52; core.jank 131.

**R126. An error while printing the value.** Status: changed.
```
eval (map (fn [_] (throw (ex-info "p" {}))) [1])
; nREPL: eval-error
; jank:  {status [error done], err "An exception was thrown from the nREPL handler…"}, and *e is not set
```
On f3d82d654 the connection died.
- **Path:** handler/eval.jank 59 (`(pr-str *1)`); core.jank 85–105.

**R127. Sessions keep no state.** Status: both.
```
s1: 1   s2: 2   s1: *1   ; nREPL 1   jank 2
```
`in-ns` is not kept between evals either.
- **Path:** evaluate.cpp 733/746–754; var.cpp 113.
- **Search:** `exhaust` found it after 37 timelines.

**R128. No `interrupt`, and one connection is handled strictly in order.** Status: both.
- **Path:** handler.jank 5–8; describe.jank 7–15.

**R129. A stack overflow or crash in an eval kills the whole server.** Status: both.
- **Path:** no signal or stack guard in `src/`.

**R130. Resources are never released.** Status: both.
- Per connection: the client, its 1 MiB buffer and its thread (server.cpp 61/127–129; core.jank 131).
- Per eval: the JIT-compiled code (evaluate.cpp 171 → jit/processor_dynamic.cpp 602).
- **Theorem:** `held_unbounded`.

**R131. `lookup` of a var whose arglists hold `nil` or `false`.** Status: changed.
```
lookup ns=clojure.core sym=iteration   ; expected: info   jank: {status [error done], err "…cannot write nil as bencode…"}
```
On f3d82d654 the connection died. A double in the arglists still writes an invalid frame (`i1.5e`).
- **Path:** lookup.jank 22–35; bencode.jank 119–122.
- **Theorem:** `write_entries_nil`.

**R132. An eval with no form.** Status: changed.
```
eval ";; nothing"   ; expected: no value   jank: value "0.0" (release), abort() (debug)
```
`""` itself is fixed (`no-code`).
- **Path:** handler/eval.jank 23–24; evaluate.cpp 743; context_dynamic.cpp 76–79.

**R133. Malformed bencode stalls a connection forever.** Status: both.
- Example: `d2:op8:describe2:id1:xe\n`, then a valid request: the second is never answered.
- **Path:** bencode.jank parse 78–91; core.jank 58–70.
- **Census:** of 402,234 buffers, 384,614 stall where the spec decoder rejects them, 177 are accepted though invalid, 0 decode to a different message.
- **Theorems:** `parse_newline_any`, `parse_space_any`.

**R134. Deep nesting overflows the stack from the client's bytes alone.** Status: both.
- 100,000 × `l` crashes the process.
- **Path:** bencode.jank 41, 53–54.
- **Caveat:** the depth that overflows depends on stack size.

**R135. Leaked sockets exhaust file descriptors.** Status: changed.
- The failing eval now gets an error reply, but fd 1 stays on a temp file and two backup fds leak.
- Then `accept` fails with EMFILE and the accept loop ends.
- **Path:** server.cpp 21–25, 127–129; capture.jank 12, 65–67.
- **Caveat:** about 250 connections under macOS's default limit.

**R136. Whitespace-only output is dropped.** Status: both.
```
(println)   ; nREPL :out "\n"   jank: no :out
```
- **Path:** handler/eval.jank 41–42, 57–58.

**R137. `inspect "true"` drops output and merges value and done.** Status: changed.
- On f3d82d654, a non-string `inspect` also killed the connection.
- **Path:** handler/eval.jank 51–53, 72.

**R138. `lookup`/`info` fail for every var outside the core-module list.** Status: 7135 only.
- The reply's `:ns` is `[:jank/source :module]`, which is nil for project namespaces, and nil cannot be written.
- **Path:** lookup.jank 23 → meta.cpp 177–181; bencode.jank 119–120.
- **Search:** found at the first timeline.

**R139. EINTR on a blocked `read_some` ends the connection, with its socket still open.** Status: 7135 only.
- **Path:** server.cpp 37–41.
- **Search:** found by `explore` at seed 0 (tape `net.read.eintr=1`); `exhaust` stopped at 20,000 timelines without reaching that decision.
- **Caveat:** low confidence; needs a signal without `SA_RESTART`.

**R140. A request without `op` gets a handler error instead of `unknown-op`.** Status: 7135 only.
- **Path:** handler.jank 7–8 (the default reply includes `:op nil`, which cannot be written).

### Round 1 (D1–D25) on 7135b7708

Every file round 1 cites is unchanged, except those for D11, D14, D15, D20 and D24, so its line numbers stand.

| D | Holds on 7135b7708 | Note |
|---|---|---|
| D1–D10 (numbers) | yes | math.hpp, math.cpp, oref.hpp, big_decimal.cpp unchanged. The book now says "Division by floating point `0.0` … will return `##Inf`"; D9's `(- ##Inf ##Inf)` still yields the x86-64 default NaN, which decodes as a null object. |
| D11 (`=` across non-sequential seqables) | **no (fixed)** | seq_ext.hpp 17 and seq.cpp 890 now require `is_sequential`. 0 sequential/non-sequential pairs disagree over 645². |
| D12 (equal values, different hashes) | yes | lazy_sequence.cpp 98–105; 1,100 equal pairs hash differently. |
| D13 (`hash-unordered-coll`) | yes | unchanged |
| D14 (array-map transient shares its source) | **no (fixed)** | transient_array_map.cpp 24–27 clones; `exhaust` complete over 33,849 timelines. |
| D15 (transient vector `nth` after `persistent!`) | **no (fixed)** | transient_vector.cpp 55 now asserts the transient is active. |
| D16–D19, D21–D23 | yes | atom.cpp, delay.cpp, context.cpp, var.cpp, core.cpp, core.jank unchanged; reruns found the same counterexamples (D22 after 57 timelines). |
| D20 (`deliver` returns the promise every time) | **no (fixed)** | promise.cpp 24–37; `exhaust` complete over 40 timelines. |
| D24 (try: catch throws and finally throws → `std::terminate`) | yes | cpp_processor.cpp 1054–1139; scope_exit.cpp 19–29 |
| D25 (`locking`) | yes | core.jank 5088/5095 |

## What was replicated (C++/jank → Lean; spec beside it)

The whole project builds with `lake build` (298 jobs; `Jank.lean` imports every module) and has no `sorry`. Each component has its own exe, declared in `lakefile.toml`.

| Component | jank replica | Clojure / C++ spec | Exe |
|---|---|---|---|
| Lexer and parser | `Jank/LexBytes.lean` (`mbrtowc`, `strtoll`, `strtod`, `stoi`, boost assign), `Lex.lean` (`next` and every case, `lexNumber`, loop steps), `Read.lean` (every `parse_*`, `read_string`, `unescape`, `parse_character`, map/set duplicate checks), `ReadSyntaxQuote.lean` (`syntax_quote`, `expand_segments`, `is_special`), `ReadRoundtrip.lean` (printers) | `ReadClj.lean` (LispReader: macros, `readToken`, `matchNumber`, `matchSymbol`, strings, chars, namespaced maps), `cljSQ` | `jank-reader` |
| Analyzer | `Jank/Analyzer/Processor.lean` (every non-interop `analyze_*`), `Expr.lean`/`Arena.lean` (all expression structs, `local_frame`), `Types.lean` (`literal_type`, `find_branch_common_type`, `mutable_type`), `Runtime.lean` (`macroexpand1`, `qualify_symbol`, `find_var`), `Eval.lean` (IR/codegen meaning) | `Spec.lean` (Compiler.java analysis and evaluation) | `jank-analyzer` |
| Code generator | `Jank/Codegen/Ir.lean` (builder), `Processor.lean` (every `gen`), `Opt.lean` (walk, rewrite, dominance, hoist passes), `Cpp.lean` (`cpp_processor`: constants, instructions), `Fmt.lean`, `Float.lean` (`to_chars`), `Exec.lean` (`_jank_*` API) | `Spec.lean` (Clojure evaluation), `CppAst.lean`/`Exec.lean` (C++ parsing, scoping and semantics of the emitted text) | `jank-codegen` |
| Interop | `Jank/Interop/CppInterop.lean` (about 120 wrappers), `CppUtil.lean` (all of cpp_util.cpp), `Analyze.lean`/`AnalyzeForms.lean` (`build_cpp_call`, `analyze_cpp_*`), `Convert.lean` (every `convert<T>`), `Codegen.lean` | `Cxx.lean`/`Facts.lean` (C++ type rules, overloads), `Spec.lean`, `Eval.lean` | `jank-interop` |
| Strings, printing, regex | `Jank/StrModel.lean`, `PrintModel.lean`, `RegexModel.lean` (backtracking ECMAScript engine with `regex_iterator`), `Strings/Bytes.lean` (utf8.cpp, immutable_string), `Strings/Object.lean` (string, char, string seq, core.cpp string fns), `Strings/Print.lean` (escape, unescape, `to_code_string`) | UTF-16 Java String/Character, Java regex, `Double.toString`, core_print (beside each) | `jank-strings` |
| Compare, multimethods, namespaces | `Jank/Compare.lean`, `Multi.lean`, `Ns.lean` | `Util.compare`, MultiFn.java, Namespace.java | `jank-core` |
| Sorted collections, destructuring, defn, printing extras | `Jank/Core/Sorted.lean`, `Destructure.lean`, `NsExtra.lean`, `PrintInf.lean` | PersistentTreeMap/Set, core.clj `destructure`, `defn` | `jank-core2` |
| Sequences | `Jank/Seq/IntRange.lean`, `Range.lean`, `Heap.lean` (identity and in-place mutation), `Chunked.lean`, `Transducers.lean`, `Core.lean` | LongRange/Range, core.clj transducers, RT | `jank-seq` |
| nREPL | `Jank/Nrepl/Bencode.lean` (byte by byte), `Server.lean` (accept/read/write, fd table, stdio, capture in `Threads`), `Runtime.lean`, `Search.lean`; fork C's `Jank/Nrepl.lean` (capture race, sessions) | spec decoder/encoder, `specEval`, per-session `*out*` | `jank-nrepl`, `jank-core nrepl` |
| Round 1 | `Jank/*.lean` (updated: `Equality.lean` `is_sequential`; `ArrayMap.lean` clone; `Vector.lean` assert-active; `Delay.lean` deliver) | unchanged | `jank-model` |

## What was left out, and why

- **Libraries with no source here:** boost (cpp_int, cpp_dec_float), immer, folly, std::regex internals, Clang/CppInterOp and bdwgc. Each is modeled by its documented behavior (see Assumptions).
- **Evaluation in the nREPL model:** abstracted to a program table. The reader, analyzer and JIT are not re-run there.
- **Codegen:**
  - optimize.cpp (LLVM passes);
  - ir/print.cpp (debug only);
  - `#line` and `GC_add_roots` lines;
  - BigDecimal constants (boost's printed form is unknown);
  - variadic fns with more than 10 arguments, and typed parameters.
- **Interop:**
  - the DSL's `:member*` forms;
  - templates other than `std::vector<int>`;
  - native exceptions;
  - the AArch64 `char` variant (parameterized, not searched).
- **Not ported in jank:** protocols, records and types (documented as missing), agents and refs/STM.
- **Covered by another component instead:**
  - The stopped strings agent's draft regex engine (never compiled) was deleted; `RegexModel.lean` covers regex.
  - My own lexer draft was removed after fork A's replica covered the reader.
- **Tests:** jank's test directories were never read.

## Assumptions

| ID | Area | Assumption |
|---|---|---|
| RA1 | reader | UTF-8 locale: strict UTF-8 `mbrtowc`; NUL has length 0. The C locale means glibc's ASCII one. |
| RA2 | reader | `isspace` is ASCII-only on bytes; `iswspace` is glibc's space class. |
| RA3 | reader | `wcrtomb` rejects surrogates. |
| RA4 | reader | `strtod` and `parseDouble` both round correctly. |
| RA5 | reader | boost `cpp_int` reads `0x` as hexadecimal and a leading `0` as octal, and throws on a bad digit. |
| RA6 | reader | `stol` accepts a sign and `0x`. |
| RA7 | reader | An empty BigDecimal literal is an error. |
| RA8 | reader | `std::regex` ECMAScript rejects Java-only groups. |
| RA9 | reader | Read context: `user` namespace, no aliases, no data readers. |
| RA10 | reader | Hangs are detected as loop fixed points; parser recursion deeper than input size + 8 is a stack overflow. |
| AN | analyzer | C++ types form a small universe. CppInterOp answers follow the standard: `GetCommonType` is `?:`'s type, and `=` on two `object_ref`s is not a builtin (only R36 depends on this). |
| AN | analyzer | `unordered_map` iterates in insertion order; code is loaded from a file. |
| G | codegen | Clang reads a decimal literal above `LLONG_MAX` as `unsigned long long`; no trigraphs; a narrowing case label is an error; `to_chars` gives the shortest form. |
| G | codegen | Constants are grouped by round 1's `=` and hash. |
| I | interop | LP64; `IsBuiltin` is false for enums; `GetScopeFromType` strips one pointer; overloads ranked per [over.match.best]. |
| I | interop | The JIT passes `-w -Wno-c++11-narrowing`. Signed overflow wraps (documented). |
| RB | strings | JDK ≥ 19 `Double.toString`; glibc C and UTF-8 locale rules; ECMA-262 `std::regex`; boost `cpp_dec_float::str()` prints no trailing zeros. |
| RC | core | Release builds (NDEBUG): debug asserts are off. `std::stable_sort` is insertion sort for n ≤ 7. `std::map`/`set` as documented. |
| RC | core | `refer`'s spec is Clojure 1.12's implementation (R109). |
| RC | core | folly `fbvector` has null storage when empty. |
| Q | seq | usize is 64 bits; out-of-bounds reads are reported as UB, not given a value. |
| N | nREPL | Boost.Asio `read_some` returns at least one byte or an error. POSIX: lowest free fd, EMFILE at the limit. |
| N | nREPL | nREPL protocol semantics come from jank's own sources and Clojure's eval/out semantics; nrepl.org was not read. |
| N | nREPL | A thread's `*ns*` is clojure.core or user. |

## Properties checked

1. Reading returns a form or an error for every byte string (no hang, no crash).
2. jank reads what Clojure reads, to the same value. Inputs jank accepts and Clojure rejects are counted, not reported.
3. Reading what `pr-str` printed gives the value back.
4. Syntax-quote expansions evaluate to Clojure's results.
5. `read-string` reads only its first form.
6. Analyzed programs give Clojure's result: special forms, `recur` targeting, shadowing, `&form`/`&env`, literal typing and boxing.
7. The emitted C++ compiles and runs to Clojure's result at -O0, -O1 and -O3 and in AOT. Every constant denotes itself.
8. `cpp/` forms behave as the book documents and as C++ rules give: casts, conversions, box/unbox, `if` truthiness, the DSL.
9. String, character, printing and regex functions match Clojure's docstrings and Java semantics.
10. `compare` is a total order consistent with `=`; `sort` is stable; sorted collections; multimethod dispatch; namespace operations.
11. Destructuring binds what Clojure binds; `defn` recursion goes through the var.
12. Sequence functions match their docstrings, are lazy where documented, and `doseq` leaves held values unchanged.
13. nREPL:
    - no deadlock and no hang;
    - every request gets replies with its id and session, ending in `done`;
    - eval output reaches its own client;
    - bencode round-trips, and arbitrary bytes give a message or an error;
    - `lookup` matches `ns-resolve`.

## Search runs (7135b7708; outputs in `results/`)

| World | Bounds | Result |
|---|---|---|
| Read is total, with NUL | `exhaust` over bytes ≤ 3; `explore` 3000 seeds, bytes ≤ 6 | found after 265 / 80 |
| Read is total, without NUL | `exhaust` bytes ≤ 4; `explore` 20,000 seeds, bytes ≤ 12 | complete, 1,222,981 timelines; nothing |
| Reader agreement tables | numbers ≤ 4 (111,151 strings), strings ≤ 4, characters ≤ 4, symbols ≤ 3, delimiters ≤ 3 | numbers: 831 wrong values, 27 rejected valid, 5,165 accepted invalid; strings: 2,864 hangs; characters without U+2003: complete, nothing |
| Analyzer | `exhaust` depth 1 (76,731 programs); tally of 20,000 at depth 4; tiny grammar at depth 2 | 8,488 / 4,219 differ, all explained; known classes excluded: nothing; depth 2 stopped at 1.5M, nothing |
| Codegen | 2,000 seeds × {-O0, -O1, -O3, AOT}; `exhaust` depth 1; constants table of 64 | 10–12 classes per mode; control complete over 3,464 timelines, nothing |
| Interop | worlds I–IX, full tables | I 157/2352, II 94/288, III 17/156, IV 3/13, V 27/196, VI 3/35, VII 20/64, VIII 46/147, IX 24/196 |
| Strings | texts ≤ 3 code points, both locales; doubles 574; regex 117,936 questions; split/replace iteration 66,300 | per-operation counts in `results/strings.txt` |
| Compare / sort / multimethods / namespaces | 24² pairs; sort length ≤ 3; multimethods 3/3/0 | 71/576 pairs; multimethods without prefers: complete, 2,048,000, nothing |
| Sorted collections | 2,191,770 map programs; 80,262 set programs | 70,480 / 3,168 differ; with R104/R105 set aside: complete, nothing |
| Destructuring | 435,132 programs | 15,840 differ; without a trailing seq: complete over 384,183, nothing |
| Sequences | integer range 5,219; real range 480; `doseq` 70; transducers 28,800; core 128 | 1,364 / 86 / 36 / 367 / 29 differ; each with its fix: complete, nothing |
| nREPL | capture 12,870 interleavings; bencode census 402,234; chunkings ≤ 4 reads (29,317), complete | as in the entries; controls stopped at 20,000 timelines, nothing |
| Round 1 | `jank-model` rerun | `results/run-7135b7708.txt` |

## Theorems (no `sorry`; `native_decide` unused; `bv_decide` relies on its LRAT checker)

- **Reader (12):** `mbrtowc_nul`, `nul_is_symbol_char`, `peek_nul`, `symbol_loop_stuck_on_nul`, `string_loop_stuck_on_nul`, `comment_loop_stuck_on_nul`, `comment_continues_past_cr`, `negated_digits_never_min` (bv_decide), `radix_258_is_2`, `radix_130`, `escape_keeps_nul`, `char_nul_printed_raw`.
- **Analyzer:**
  - `if` typing: `if_merges_distinct_natives`, `if_int_double`, `if_bool_int`, `if_object_branch`.
  - Literals and locals: `small_literal_is_int`, `loop_local_native`, `recur_conversions`, `int_local_wraps`.
  - Macros and frames: `macro_arguments`, `macro_form_is_not_the_form`, `outer_local_wins_over_fn_name`.
  - `case`: `case_last_branch_wins`, `case_order_matters`, `case_object_then_double`.
- **Codegen (11):** `munge_dash_underscore`, `munge_qmark_collision`, `munge_keeps_dot`, `rewrite_keeps_case_value`, `rewrite_keeps_loop_values`, `case_integer_not_self`, `cstring_drops_after_nul`, `big_literal_negative`, `decode_escape`, plus 2 helpers.
- **Interop (10):** `int_from_object_exact_iff`, `literal_add_exact_iff`, `literal_mul_exact_iff`, `makeBox_u32_never_small`, `makeBox_u64_never_small`, `u64_into_object_negative`, `u64_into_object_exact_iff`, `u32_roundtrip`, `literal_type_small_int`, `pointer_to_void_ignores_cv`, `pointer_to_void_accepts_function_pointers`.
- **Strings and printing (25):**
  - Lengths and counts: `count_eq_iff`, `count_ge`, `utf8_ge_utf16`.
  - `compare_len_sign_ok` (bv_decide), `compare_fullwidth_emoji`.
  - String seqs: `seq_walks_past_end`, `seq_not_reflexive`, `seq_hash_inconsistent`.
  - `nth_never_non_ascii`, `index_of_negative`.
  - Printing: `jank_100000`/`java_100000` and the other double pairs, the regex-quote theorems.
- **Core:**
  - Compare and multimethods: `long_compare_matches` (bv_decide), `bool_bool_throws`, `keyword_vs_other_ub`, `no_prefs_same`, `example_clojure`/`example_jank`.
  - Namespaces: `jank_intern_binds_found`, `clj_intern_replaces_referred`, `reload_after_shadowing_throws`.
  - Sorted and printing: `find_returns_query_key`, `clj_find_returns_stored_key`, `sort_empty_is_empty_list` (with `next_of_empty_sort_old` for f3d82d654), `print_inf`.
- **Sequences (13):** `count_throws_pos` and `count_ok_pos` (bv_decide), `quarter_steps_count`, `max_step_throws`, `range_max_throws`, `wraps_past_i32`, `vseq_past_end_never_ends`, `cons_range_after_doseq`, `partition_by_sends_twice`, `byte_roundtrip_agree_iff` (bv_decide), `byte_minus_one`, `cons_not_coll`, `first_of_map_maps_everything`.
  - Round-1 updates: `assoc_bang_keeps_source`, `dissoc_bang_keeps_source`, `transient_nth_after_persistent`. The old versions are kept as `*_f3d82d654`.
- **nREPL:**
  - Bencode writing: `write_str`, `write_nil`, `write_bool`, `write_entries_nil`, `iteration_arglists_unwritable`, `joinSorted_error_of_mem`.
  - Protocol: `describe_lists_handled_ops`, `alias_resolution`.
  - Parsing: `parse_newline_any`, `parse_space_any`.
  - Fork C's: `dead_stays_dead`, `held_unbounded`.

## Library gaps filled in the project (sdk/lean untouched)

- **`exhaust` stops at the first counterexample, and `shrink` can switch causes within one property.** Added census and tally walks (all timelines, violations counted per class), class-tagged property names, residual searches (the found trigger removed from the alphabet) and set-aside toggles. Each search ends with a complete run that finds nothing.
- **Consecutive small `mkStdGen` seeds give the same first draw.** Added `exploreMixed`, which runs each seed through a SplitMix64 finalizer.
- **Missing models, built in the project:**
  - an object heap with identity and in-place mutation (`Seq/Heap.lean`);
  - a C++ type/value model (`Interop/Cxx`, `Facts`, `Value`, `Eval`);
  - a C++ text parser and interpreter for emitted code (`Codegen/CppAst`, `Exec`);
  - an fd, socket and stdio table (`Nrepl/Server.lean`);
  - the locale as a world decision.
- **Threads:**
  - deadlock reports name what each thread waits for (`stuckDetail`);
  - a step bound, since blocked picks count against `maxSteps`;
  - stories through `Process.note`.
- **Kernel evaluation:**
  - `String` is opaque to `decide`, so models compare `List Char`/bytes;
  - fuel-indexed recursion is made structural so `decide` can run concrete programs;
  - `while` and derived `BEq` on nested inductives do not reduce, so they were rewritten.
- **Job limit:** `bin/job` holds one of 4 machine-wide slots and bounds each command with `perl alarm`; every build and search ran through it.

**Files:**
- Models: `Jank/` and `Run/`.
- Run outputs:
  - `results/reader.txt`, `analyzer.txt`, `codegen.txt`, `interop.txt`, `strings.txt`, `core.txt`, `core2.txt`, `seq.txt`, `nrepl.txt`;
  - `results/run-7135b7708.txt` (round 1 rerun);
  - `results/run.txt` (round 1 on f3d82d654).
- The forks' original reports: `results/fork-A-reader.txt`, `fork-B-strings-printing-regex.txt` (with a 7135b7708 update section appended), `fork-C-core-nrepl.txt`.
- The version diff: `results/upstream-f3d82d654-to-7135b7708.diff` and `results/upstream-f3d82d654-to-7135b7708-files.txt`.
- jank 7135b7708: `upstream-main/`. The old checkout `upstream/` is kept for the f3d82d654 column.

No commits were made.

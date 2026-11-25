# REPORT-3: jank 7135b7708 compared with Clojure 1.12, round 3: the libraries replicated, wider searches, proofs

**Version.** jank `7135b770857d625630ab6f9abe5861c618d67b82`, at `upstream-main/`. Every jank path below is under `upstream-main/compiler+runtime/` and uses 7135b7708 line numbers.

**Libraries.** Each library is shallow-cloned under `deps/` at exactly the commit jank pins; no history was read.
- Submodules: immer 282629d0, boost-multiprecision 2b3ab082, bdwgc 327ef1f8, CppInterOp 28b0830d, folly e54ca53d.
- From jank's `flake.lock` (nixpkgs 02f5696b):
  - GCC 15.3.0. Its libstdc++ regex sources are in `deps/libstdcxx-15.3.0/`.
  - LLVM 23.1.0 (`llvmPackages_23`). Only the Clang/LLVM files that CppInterOp and the pass pipeline reach are in `deps/llvm-23.1.0*/`.

**Status of each item.** Every item is a hypothesis. It comes from Lean replicas of the C++ and library code, re-read against the source. jank was never built or run.

**Who did what.** Nine agents worked in parallel, one per area: Boost, Immer, Regex, Runtime (folly and bdwgc), Interop (CppInterOp), Codegen, nREPL, Proofs, Search. I merged their results and renumbered them S1–S76.
- I re-read the source behind CX1, MP1, RT2, RT3, CG4, N1, W4, W5, IM1, IM2 and S61; each holds as stated.
- Each area's full report is in `results/r3-<area>-report.txt`, and its run output in `results/r3-<area>*.txt`.

**Build.** One `lake build` of all 20 targets (rounds 1–3, 601 jobs) succeeds.
- Round 3 adds 95 files and 30,511 lines under `Jank/R3/` and `Run/R3/`, with 9 new exes `jank3-<area>`.
- There is no `sorry`, no `native_decide` and no new axiom. Some proofs use `decide +kernel`; HashInv uses `bv_decide`.
- Rounds 1 and 2 still build. The Proofs agent edited `Lex.lean`, `Read.lean`, `Core/Destructure.lean` and `Core/Sorted.lean`, only to make definitions terminating. Afterwards `jank-reader` reproduces `results/reader.txt` exactly, and `jank-core2` reproduces `results/core2.txt` except for timings.

**Seeding defect.** `Source.seeded i` gives the same first draw for small `i`.
- Every round-3 random search uses SplitMix64-mixed seeds.
- Two of the Boost driver's explores were unmixed. I switched them to mixed seeds and reran them (`results/r3-boost-mixed.txt`): the same 12 classes plus division by zero, then nothing.
- Every "complete, nothing" verdict below comes from an exhaustive walk, so it does not depend on a first draw.
- Round 2's unmixed explores (analyzer rounds, R139 "seed 0") are now covered by complete runs: the Search agent's budget-2 worlds, and the nREPL agent's preemption-bounded T8.

## Deviations at a glance

| # | Area | jank (predicted) | Clojure / expected | Status |
|---|---|---|---|---|
| S1 | reader | `#'1`, `#'(f x)` are read errors | `(var 1)` | new (book documents the error) |
| S2 | BigDecimal | `(/ 6M 3M)` is `1.999…9M` (121 digits) | `2M` | new |
| S3 | BigDecimal | `(/ 1M 3)` is a 128-digit value; `(< 0M 1/3)` is true | throws (non-terminating) | new |
| S4 | BigDecimal | 128 significant digits: `(- 1M 1E-130M)` is `1.0M` | exact | new |
| S5 | BigDecimal | `(str 0.00001M)` is `"1e-05.0"`, which does not read back | `"0.00001"` | new |
| S6 | BigDecimal | `(+ 1M 0.5)` is `1.5M` | `1.5` (double) | new |
| S7 | BigDecimal | `(rem 1E130M 3)` is `99999997.0M` | `1M` | new |
| S8 | numbers | `(rem 1/2 0.1M)` throws; `(rem 1.75M 1/2)` is `0N` | `0.0M`, `0.25M` | new |
| S9 | numbers | `(bigdec 0.1)` is the binary value | `0.1M` | new |
| S10 | BigDecimal | `=` BigDecimals hash differently | equal hashes | extends D8 (with D12) |
| S11 | BigDecimal | `(double 1E-310M)` is `0.0` | `1.0E-310` | new |
| S12 | BigDecimal | `(long 1E130M)` saturates | throws | new, low |
| S13 | codegen/AOT | `(def x 0.00001M)`: the AOT module fails to load | loads | new |
| S14 | numbers | `(bigdec "inf")`, `"1e"`, `"."` accepted | throws | new, low |
| S15 | numbers | `(bigint "010")` is `8N`; `"+5"` throws; `"0x10"` is `16N` | `10N`, `5N`, throws | new |
| S16 | reader | `0010/3` is `8/3`; `1/0100000000000000000000` is wrong | `10/3` | extends R7 |
| S17 | reader | `1e4294967296M` is `1.0M`; `0x1e5M` is `100000.0M` | throws | new, low |
| S18 | numbers | `(bigint 100000000000000000000/3)` throws | `33333333333333333333N` | new |
| S19 | numbers | `(/ 7N 2)` is `3N` | `7/2` | extends D2 |
| S20 | numbers | `(* 0N 1/2)` is `0` | `0N` | new, low |
| S21 | numbers | `(double -7/3)` differs in the last digit | `-2.333333333333333` | new, low |
| S22 | regex | `#"é*"` repeats only é's last byte; `\u00e9` is the byte 0xE9 | repeats é | R78 changed |
| S23 | regex | `\u0141` is cut to its low byte (`A`) | Ł | new |
| S24 | regex | `#"[a-é]"` is a read error | valid | new |
| S25 | regex | possessive `a++a` compiles as nested greedy repeats | nil | R18 corrected |
| S26 | regex | `a{2}{3}` repeats; `#"{2}"` is a read error | `"aa"`; matches "" | new |
| S27 | regex | `#"^*a"`, `#"a$?"` are read errors | compile | new |
| S28 | regex | `#"\1"`, `#"(a\1)"` are read errors; `\10` is one backref | compile | new |
| S29 | regex | `[[:alpha:]]` is POSIX; `[a-z&&[^b]]` is not an intersection | Java classes | new |
| S30 | regex | `[]a]`: `]` first closes the class; `#"[^]"` matches any byte | Java | new |
| S31 | regex | `\cJ`, `\v`, `\A`, `\Q…\E`, `\e`, `\h`, `\01`, `\p{L}` mean other things | Java escapes | new |
| S32 | regex | `#"[\w-a]"` is a read error | valid | new |
| S33 | regex | a lookahead at the first position sees a new input (`a(?=\b)` matches "ab") | nil | new |
| S34 | regex | matching recurses per character: `(re-find #"a*" long-string)` segfaults | matches | new |
| S35 | regex | `#"a{99999}"` is a read error (NFA limit) | valid | new |
| S36 | analyzer | `(let [x 1] (if false (x) :ok))` does not compile | `:ok` | new (round 2 tagged it, unreported) |
| S37 | analyzer | `case` analyzes its default before its clauses | clauses first | new |
| S38 | analyzer | a macro expansion headed by a local's name is expanded again as a macro | the local wins | new |
| S39 | codegen | -O1+: a side-effect-free infinite loop is UB (likely deleted) | loops | new; changes R24 |
| S40 | codegen | float→int conversions unchecked: `(int 1e20)` UB, `(int 2147483648)` is 2147483648 | throws | new; extends R24 |
| S41 | codegen | `(let [a 1 b 1] {a :x b :y})` is `{1 :y}` | throws (duplicate key) | new |
| S42 | analyzer | fns with more than 10 params (a `& r` param counts) rejected | 20 + rest | new |
| S43 | codegen | `^cpp/long` param with fn-level `recur`: C++ compile error | 3 | new |
| S44 | codegen | `(eval (list 'quote v))` resets v's metadata | unchanged | new |
| S45 | interop | `(:long (:long int))` is `long`; the DSL cannot name `long long` | `long long` | new; changes R94 |
| S46 | interop | `(:signed char)` is `char` on x86-64; `(:unsigned char)` is `char` on AArch64 | distinct types | new |
| S47 | interop | `:member*` takes a member name, not a member type; the book's examples are rejected | book | new |
| S48 | interop | `:&member`/`:member*` skip access checks; overloaded static member "missing"; … | C++ | new, low |
| S49 | interop | explicit template args of a called function template are dropped | `(add<double> 1 2)` = 3.0 | new |
| S50 | interop | calls through function pointers reject reference-binding conversions | accepted | new |
| S51 | interop | pointer-to-member call on `Foo const *` rejected | accepted | new |
| S52 | interop | indirect calls accept explicit conversions and private bases | rejected | new, low |
| S53 | interop | built-in operators unavailable on class operands with conversions | `(cpp/+ meters 1.0)` = 2.5 | new |
| S54 | interop | an inherited static data member not found through an instance | found | new |
| S55 | interop | members of a private base accessible (then JIT error) | rejected | new, low |
| S56 | interop | `cpp/unsafe-cast` judges types: valid C casts rejected, invalid accepted | C cast rules | new |
| S57 | interop | `(if false 1 cpp/gd)` with `double gd = 2.5` is `2` | `2.5` | new; R23 variant (narrows) |
| S58 | interop | native catch handlers: by-value is by-reference, arrays never match | C++ handlers | new, low |
| S59 | collections | `=` key replaces the stored key: `(first (keys (assoc (hash-map '(1) :a) [1] :b)))` is `[1]` | `(1)` | new |
| S60 | collections | array-map transient readable after `persistent!` | throws | new (D15's map counterpart) |
| S61 | collections | `(conj {} ())`, `(merge {:a 1} ())`, kwargs ending in `()` throw | `{}`, `{:a 1}` | extends R107 |
| S62 | runtime | a validator calling `set-validator!` / reading its atom beside one: hang | 1 | new |
| S63 | runtime | `alter-var-root` re-entering its var: hang | 10 | new |
| S64 | runtime | `(def d (delay (realized? d))) @d`: hang | false | new |
| S65 | runtime | `future-cancel` while another thread derefs: three threads hang | true | new |
| S66 | runtime | `future-cancelled?` while another thread derefs: hang (Linux) | false | new |
| S67 | runtime | lazy var meta that reads the var's meta: hang | the map | new; lock side of R43 |
| S68 | runtime | AOT module top level waiting on a thread that `require`s: hang | loads | new |
| S69 | runtime/GC | an in-flight exception is not a GC root: `ex-info` freed before `catch` | `{:k [0 1 2]}` | new |
| S70 | runtime/GC | `var_unbound_root` is pointer-free: freed var read | `"Unbound: #'user/x"` | new |
| S71 | nREPL/eval | a top-level `(do …)` is analyzed whole: `(do (defmacro m [] 2) (m))` fails | 2 | new |
| S72 | nREPL | `lookup` in a missing ns answers for `user` | no-info | new |
| S73 | printing | `(pr-str *ns*)` is `"user"` | `#object[clojure.lang.Namespace …]` | new |
| S74 | nREPL | load-file switching ns replies with the file's ns | the session's ns | new, medium-low |
| S75 | nREPL | eval `1 2` gives one value; the first exception ends the input | value per form | new (rests on NA1) |
| S76 | nREPL | output printed while printing the value (lazy seq) is lost or reaches another client | `:out "1\n2\n"` | new |

## Corrections to rounds 1 and 2

**Retracted:**
- **R36.** CppInterOp's `GetBuiltinOperatorType(=, object_ref, object_ref)` is `object_ref`: Clang treats same-class assignment as built-in (SemaExpr.cpp 9693, 10226–10229). The analyzer then gives 5, which is Clojure's result.
- **R87.** `GetPointeeType` of an array is its element type (CppInterOp.cpp 3015), so the conversion action is `none`. Theorem `getPointeeType_array`.

**Weakened:**
- **R23** at the top level (Codegen, CG7). A top-level `if` at the REPL or in `jank run` is interpreted (evaluate.cpp 594–606, 651–654), so `(if true 1 2.5)` there is 1. R23 holds inside a fn, `let` or `loop`, and in AOT. It is also extended by S57.
- **R31** through the nREPL: it holds only when the request carries `file`.
- **D12, one example.** CHAMP compares only `Equal` at the first data slot on the query's hash path; it never compares hashes.
  - `(contains? #{0.0} -0.0)` is true (round 1 said false). `(count #{0.0 -0.0})` is 1, which retracts R13's second example (the literal is still accepted, so R13 stands).
  - It fails once another key pushes 0.0 below level 6: `(contains? #{0.0 2.0} -0.0)` is false and `(count (conj #{0.0 2.0} -0.0))` is 3.
  - 1/1N, R56 and round 1's other D12 examples are confirmed.
  - New consequences:
    - array→hash promotion: `(count (assoc (into {} (map vector (range 1 9) (repeat 0))) 1N :x))` is 9;
    - `(= (hash-map 1 0) (hash-map 1N 0))` is false;
    - `=` between array and hash maps is asymmetric: `(= {1 :a} (hash-map 1N :a))` is false while the reverse is true.

**Changed:**
- **R24.** At -O1 and above it is undefined behavior (S39, S40).
- **R78.** Changed by S22: on round 2's tables 1,891 jank answers change; 94 are retracted and 1,173 added.
- **R18.** Corrected by S25: possessive quantifiers compile. `(?i)`, lookbehind, named groups and atomic groups remain read errors.
- **R94.** Recount: 53 of 147 chains deviate on both platforms (round 2: 46).

**Confirmed with the libraries now replicated:**
- R7 and RA5: 0 differences over 813,616 strings and 16.6 M byte strings.
- R72, R99 (also extended to BigInt against double), R79–R85 (the "libstdc++" caveat on R85 is resolved), R89, R90, R123, R125–R127, R131–R132, R136, R138–R139, and D16 (with the folly replica).
- R25 holds at every -O level, because `-fwrapv` is passed (processor_dynamic.cpp; CMakeLists.txt 342).

**Model corrections (rounds 1/2 files left unchanged; the corrected function lives in round 3):**
- **Literal -2147483648.** The analyzer types it `int`, but the emitted text is a C++ `long`.
  - `(< (- -2147483648 1) 0)` is true.
  - `(let [u 0] (/ -2147483648 -1))` is -2147483648, not SIGFPE.
  - `(+ -2147483648 -2147483648)` is still 0 (an R25-class deviation).
- **Round 1's `jankBigdecOfLong`** saturated longs that round to 2^63. jank gives `9223372036854775808M`.
- **Round 2's `bigDecimalCreate`** accepted `"0-.M"`.
- **Round 2's Clojure-side `createAsIfByAssoc`** threw on a trailing set or string. Clojure walks them as entries.
- **Round 2's analyzer spec** rejected `(var other/private)`. Neither Clojure nor jank checks privacy there.
- **`Sorted.cvEq`** lacked a BigDecimal case.
- **"Empty fbvector has null storage"** holds only if it never allocated. After `clear`, `erase` or `pop_back` the block stays.
- **R138, refined.** `:module` is the ns current when the var's name was read.
- **R117, extended.** The hash-set seq does not decrement its `size` when walked in place.

## Deviations in full

### Reader and numbers (boost::multiprecision replicated)

jank's BigDecimal is `cpp_dec_float<100>`: 16 limbs of 8 decimal digits (128 digits) and an int32 exponent within ±2^26. Its BigInt is `cpp_int` with 64-bit limbs. boost paths are under `deps/boost-multiprecision/include/boost/multiprecision/`.

**S1. `#'` followed by anything but a symbol is a read error.** Status: new. Round 2 printed `#'1` once without reporting it.
```clojure
(read-string "#'1")   ; Clojure (var 1)         jank "A value after `#'` must be a symbol."
'[#'(f x)]            ; Clojure [(var (f x))]   jank: the file does not read
```
- **Path:** read/parse.cpp `parse_reader_macro_var_quote` 807 (check at 821–826). Clojure: LispReader VarReader 805–816.
- **Caveat:** the book documents the error (`reference/error/parse/invalid-reader-var.md`).

**S2. BigDecimal division multiplies by a truncated inverse.** Status: new.
```clojure
(/ 6M 3M)    ; Clojure 2M     jank 1.999…9M (121 digits)
(/ 3 6M)     ; Clojure 0.5M   jank 0.4999…98M
(/ 1.5M 3)   ; Clojure 0.5M   jank 0.4999…9M
```
- **Path:**
  - core/math.hpp `div` 299–340 → no_et_ops.hpp 139–166;
  - default_ops.hpp 569–574 (a long divisor is first converted to a decimal);
  - cpp_dec_float.hpp `operator/=` 1016–1045 → `calculate_inv` 1222–1286 (Newton iteration from a double estimate) → `operator*=` 951–1012, which keeps the top limbs and never rounds.
- **Reach:** BigDecimal/BigInt pairs (big_decimal.cpp 22–45), ratio/decimal pairs (ratio.cpp 12–16, 540–548), `(bigdec ratio)` (big_decimal.cpp 140–144). Any divisor with a prime factor other than 2 or 5.
- **Search:** 46 table questions. **Theorems:** `no_decimal_third`, `six_times_decimal_ne_two`. **Confidence:** high.

**S3. Non-terminating quotients return a value.** Status: new.
```clojure
(/ 1M 3)      ; Clojure throws "Non-terminating decimal expansion"   jank 0.333…M (128 digits)
(< 0M 1/3)    ; Clojure throws                                       jank true
```
- **Path:** as S2. `with-precision` is unported (core.jank 6487–6503).
- **Search:** 887 questions.

**S4. BigDecimals keep 128 significant digits.** Status: new.
```clojure
(- 1M 1E-130M)   ; Clojure exact   jank 1.0M
(+ 1 1E130M)     ; Clojure exact   jank 1E+130
```
- **Path:** cpp_dec_float.hpp `rd_string` 2296–2318 and `operator+=` 759–937. A literal with 133 digits is truncated when read.

**S5. BigDecimals below 1e-4 or from 1e128 print in boost's scientific form plus ".0".** Status: new. R72 still covers the lost scale.
```clojure
(str 0.00001M)                    ; Clojure "0.00001"   jank "1e-05.0"
(pr-str 1E130M)                   ; Clojure "1E+130M"   jank "1e+130.0M"
(read-string (pr-str 0.00001M))   ; Clojure 0.00001M    jank lexer error
```
- **Path:** big_decimal.cpp 157–175 → string_builder.cpp 240–249 (appends ".0") → cpp_dec_float.hpp `str` 1913–2081; number_base.hpp 1394 picks the notation.
- **Theorems:** `jank_str_fixed_iff`, `jank_sci_below_1e_4`, `jank_sci_from_1e128` (for every value).

**S6. A BigDecimal combined with a double gives a BigDecimal.** Status: new.
```clojure
(+ 1M 0.5)   ; Clojure 1.5                  jank 1.5M
(* 6M 0.1)   ; Clojure 0.6000000000000001   jank 0.600000000000000033306690738754696212708950042724609375M
```
- **Path:** math.hpp `add` 71–112 → boost `operator+(number, double)`, which converts the double exactly (cpp_dec_float.hpp 2461–2516) → make_box.hpp 36. Clojure uses `DOUBLE_OPS` (Numbers.java 976).
- **Search:** 722 questions.

**S7. `rem` of BigDecimals runs a 128-digit fmod.** Status: new.
```clojure
(rem 1E130M 3)   ; Clojure 1M   jank 99999997.0M
```
- **Path:** math.cpp 269–289 → default_ops.hpp 1260–1321.

**S8. `rem` of a ratio and a BigDecimal truncates the decimal first.** Status: new.
```clojure
(rem 1/2 0.1M)    ; Clojure 0.0M    jank throws "Division by zero is not permitted."
(rem 1.75M 1/2)   ; Clojure 0.25M   jank 0N
```
- **Path:** math.cpp 250–268 → generic_interconvert.hpp 533–563.
- **Search:** 94 questions.

**S9. `bigdec`/`bigint` of a double use the binary value instead of `Double.toString`.** Status: new.
```clojure
(bigdec 0.1)      ; Clojure 0.1M                        jank 0.1000000000000000055511151231257827021181583404541015625M
(bigint 1.0E23)   ; Clojure 100000000000000000000000N   jank 99999999999999991611392N
```
- **Path:** math.cpp 817 and 771–772 → `operator=(double)` 2461–2516.
- `(bigint 1.0E300)` is not even the double's exact value: 2^937 is computed by repeated squaring and truncated.

**S10. BigDecimals that jank calls `=` hash differently.** Status: extends D8 with D12's property.
```clojure
(count (hash-set 1M 1.0000000000000000001M))   ; jank 2, though jank's = says they are equal (D8)
```
- **Path:** big_decimal.cpp 177–180 → cpp_dec_float.hpp 259–266. The hashes are 3307139568 and 575929905.

**S11. `(double x)` of a BigDecimal rounds twice and flushes subnormals to 0.** Status: new.
```clojure
(double 9007199254740993.00000000000000000001M)   ; Clojure 9.007199254740994E15   jank …992E15
(double 1E-310M)                                  ; Clojure 1.0E-310               jank 0.0
```
- **Path:** big_decimal.cpp 197–200 → `extract_double` 1570–1610 (rounds to 19 digits, then `strtod`).

**S12. `(long x)` of a BigDecimal truncates exactly and saturates.** Status: new, low.
```clojure
(long 1E130M)   ; Clojure throws "Value out of range for long"   jank 9223372036854775807
```
- **Path:** big_decimal.cpp 192–195 → `extract_signed_long_long` 1664–1720.

**S13. AOT: a BigDecimal constant printed as `<d>e±XX.0` stops the module from loading.** Status: new; round 2 left BigDecimal constants out.
```clojure
(def x 0.00001M)   ; JIT works; AOT load throws "Unable to parse the string "1e-05.0""
```
- **Path:**
  - cpp_processor.cpp 311–316 emits `make_box<big_decimal>("{to_string()}")`, rebuilt at load at 2176–2180;
  - boost's `const char*` constructor is explicit, so `big_decimal(immutable_string)` is chosen;
  - `rd_string`'s exponent check (2104–2112) rejects the trailing ".0".
- **Search:** 845 of 3,311 literals fail. Every other literal rebuilds exactly, and 1,600 BigInt constants are exact. **Theorem:** `aot_sci_text_rejected` (every digit, sign and exponent).

**S14. `(bigdec s)` follows boost's grammar.** Status: new, low.
```clojure
(bigdec "inf")   ; Clojure throws   jank inf
(bigdec "1e")    ; Clojure throws   jank 1.0M
(bigdec ".")     ; Clojure throws   jank 0.0M
```
- **Path:** math.cpp 823 → `rd_string` 2133–2147, 2104–2112, 2200.
- **Search:** 1,030 of 66,430 strings, all of them accepted by jank and rejected by Clojure.

**S15. `(bigint s)` follows `cpp_int`'s grammar.** Status: new.
```clojure
(bigint "010")    ; Clojure 10N      jank 8N
(bigint "+5")     ; Clojure 5N       jank throws
(bigint "0x10")   ; Clojure throws   jank 16N
(bigint "-")      ; Clojure throws   jank 0N
```
- **Path:** math.cpp 765 → big_integer.cpp 33–58 (drops one trailing N) → cpp_int.hpp 1752–1922. A NUL ends the string.

**S16. Ratio parts that reach boost with a leading 0 are read as octal.** Status: extends R7 (new instances past round 2's tables).
```clojure
0010/3                    ; Clojure 10/3                     jank 8/3
00017/1                   ; Clojure 17                       jank 15
1/0100000000000000000000  ; Clojure 1/100000000000000000000  jank 1/1152921504606846976
008/3                     ; Clojure 8/3                      jank throws
```
- **Path:** lex.cpp 905–915 (a radix-8 numerator drops only its first 0) and 916–935 (a denominator past i64 goes whole to boost).
- **Theorems:** `octal_le_decimal`, `octal_lt_decimal` (∀; new for-every-input statement of R7's bounded finding).

**S17. BigDecimal literal exponents and hex-looking literals.** Status: new, low.
```clojure
1e4294967296M   ; Clojure throws "Exponent overflow"   jank 1.0M (atoll, then an int32 wrap)
0x1e5M          ; Clojure invalid number               jank 100000.0M
1e67108872M     ; jank inf, printed "inf.0M"
```
- **Path:** lex.cpp 1123–1132 → `rd_string` 2104–2112, 2351–2375.

**S18. `bigint` of a ratio goes through i64.** Status: new.
```clojure
(bigint 100000000000000000000/3)   ; Clojure 33333333333333333333N   jank throws "out of range for i64"
```
- **Path:** math.cpp 774–777 → ratio.cpp 113–116 → big_integer.cpp 200–208.

**S19. Integer `/` with a BigInt operand truncates.** Status: extends D2.
```clojure
(/ 7N 2)   ; Clojure 7/2   jank 3N
```
- **Path:** math.hpp `div` 299–340, using cpp_int's `/`.

**S20. Ratio arithmetic with a BigInt returns a long for an integral result.** Status: new, low.
```clojure
(* 0N 1/2)   ; Clojure 0N   jank 0
(/ 3N 1/2)   ; Clojure 6N   jank 6
```
- **Path:** ratio.cpp 87–101.

**S21. `(double -7/3)` divides two doubles.** Status: new, low. jank's value is the nearer one.
```clojure
(double -7/3)   ; Clojure -2.333333333333333   jank -2.3333333333333335
```
- **Path:** ratio.cpp 108–111.

Not reported: dividing a BigDecimal by zero gives `inf.0M`/`nan.0M`; the book documents this behavior (68 questions). Also noted: `numerator`, `denominator` and `biginteger` print as `1N`, and `rationalize` is unported.

### Regex (libstdc++ 15.3.0 replicated)

How jank reaches the library:
- `#"…"` → parse.cpp `parse_regex` 888 → re_pattern.cpp 9 `std::regex{ s.c_str(), ECMAScript }`.
- `re-*` → core.cpp 929–1012.
- `replace`/`split` → string_native.cpp 78–410.
- The executor is always the recursive DFS one (regex.tcc 48). Every regex table gives identical results in the C and UTF-8 locales.

libstdc++ paths are under `deps/libstdcxx-15.3.0/`.

**S22. A quantifier after a non-ASCII character repeats only its last byte, and `\u00e9` and `\xe9` are the byte 0xE9.** Status: R78 changed.
```clojure
(re-matches #"é*" "")    ; Clojure ""     jank nil
(re-find #"é+" "éé")     ; Clojure "éé"   jank "é"
(re-find #"\u00e9" "é")  ; Clojure "é"    jank nil
```
- **Path:** regex_scanner.tcc `_M_scan_normal` 96; regex_compiler.tcc `_M_quantifier` 179 (pops the last atom) and `_M_try_char` 563.
- **Theorem:** `e_acute_star_needs_lead_byte`.

**S23. `\uHHHH` above 0xFF is cut to its low byte.** Status: new.
```clojure
(re-find #"\u0141" "A")   ; Clojure nil (the pattern is Ł)   jank "A"
```
- **Path:** regex_scanner.tcc 353 → regex_compiler.tcc 563 (`assign(1, int)` narrows to `char`).
- **Theorem:** `u_escape_low_byte`.

**S24. A bracket range from ASCII to a non-ASCII byte is a read error.** Status: new.
```clojure
#"[a-é]"   ; Clojure valid   jank read error "Invalid range in bracket expression."
```
- **Path:** regex_compiler.h `_M_make_range` 500 compares signed `char`.
- **Theorem:** `makeRange_rejects_ascii_to_high` (∀ l < 128 ≤ r < 256).
- **Caveat:** x86-64 only. On AArch64, where `char` is unsigned, this goes away.

**S25. Possessive quantifiers compile, as nested greedy repeats.** Status: R18 corrected.
```clojure
(re-find #"a++a" "aaa")       ; Clojure nil    jank "aaa"
(re-matches #"\d*+\d" "12")   ; Clojure nil    jank "12"
```
- **Path:** regex_compiler.tcc `_M_term` 138 (`while (_M_quantifier())`).

**S26. A `{n}` after a quantifier repeats it; a `{n}` with nothing before it is a read error.** Status: new.
```clojure
(re-find #"a{2}{3}" "aaaaaa")   ; Clojure "aa"          jank "aaaaaa"
#"{2}"                          ; Clojure matches ""    jank read error
```
- **Path:** regex_compiler.tcc 138 and 80.
- **Caveat:** Java's side here is Pattern's behavior, not its javadoc (RXJ3).

**S27. A quantifier on an assertion is a read error.** Status: new.
```clojure
#"^*a"  #"\b+a"  #"(?=a)*a"  #"a$?"   ; Clojure compile   jank read error
```
- **Path:** regex_compiler.tcc `_M_term` 134 returns after `_M_assertion`.
- **Theorem:** `read_error_quantified_caret`.

**S28. Backreferences that Java accepts are read errors.** Status: new.
```clojure
#"\1"   #"\1(a)"   #"(a\1)"      ; Clojure compile               jank read errors
(re-find #"(a)\10" "aa0")        ; Clojure ["aa0" "a"] (\1 then "0")   jank read error (backref 10)
```
- **Path:** regex_scanner.tcc 372; regex_compiler.tcc 317 → regex_automaton.tcc 165/173.

**S29. POSIX bracket syntax and nested classes mean other things.** Status: new.
```clojure
(re-find #"[[:alpha:]]" "x")   ; Clojure nil   jank "x"
(re-find #"[[a]]" "a")         ; Clojure "a"   jank nil
(re-find #"[a-z&&[^b]]" "c")   ; Clojure "c"   jank nil
#"[[:foo:]]"                   ; Clojure valid   jank read error
```
- **Path:** regex_scanner.tcc 217–240; regex_compiler.tcc `_M_expression_term` 436; regex.tcc `lookup_classname` 279.

**S30. `]` first in a class closes it.** Status: new.
```clojure
(re-find #"[]a]" "a")   ; Clojure "a"      jank nil
#"[^]"                  ; Clojure error    jank matches any byte, newline included
```
- **Path:** regex_scanner.tcc 248.

**S31. Java escapes with another meaning.** Status: new.
```clojure
(re-find #"\cJ" "\n")      ; Clojure "\n"       jank nil (\cX is X)
(re-find #"\v" "\n")       ; Clojure "\n"       jank nil (VT only)
(re-find #"\Aa" "a")       ; Clojure "a"        jank nil (\A \z \Z \G are letters)
(re-find #"\Q.\E" ".")     ; Clojure "."        jank nil
(re-find #"\e" "e")        ; Clojure nil        jank "e"
(re-find #"\01" "\u0001")  ; Clojure "\u0001"   jank nil
#"\p{L}"  #"\x{41}"        ; Clojure valid      jank read errors
```
- **Path:** regex_scanner.tcc `_M_eat_escape_ecma` 310 (only `0 b f n r t v`; `\c` 344; `\x`/`\u` 353; any other letter is an identity escape).

**S32. A class escape before `-` in a bracket is a read error.** Status: new.
```clojure
#"[\w-a]"   ; Clojure \w, '-', 'a'   jank read error "Invalid start of '[x-x]' range"
```
- **Path:** regex_compiler.tcc 497.

**S33. A lookahead at a search's first position sees a new input.** Inside it `^` holds, and `\b`/`\B` ignore the character to the left. Status: new.
```clojure
(re-find #"a(?=\b)" "ab")            ; Clojure nil     jank "a"
(re-find #"foo(?=\bbar)" "foobar")   ; Clojure nil     jank "foo"
(re-seq #"b(?!^)" "b")               ; Clojure ("b")   jank nil
```
- **Path:** regex_executor.tcc `_M_lookahead` 151/157 builds the sub-executor with `_M_begin` at the current position. `_M_at_begin` (executor.h 167) and `_M_word_boundary` (552/560) look left only under `match_prev_avail`, which `_M_search` (42) sets only after the first start position.
- **Reach:** every first search of `re-find`, `re-matches`, `replace` and `split`.
- **Theorems:** `lookahead_caret_holds`, `lookahead_boundary_ignores_left` (for every state).

**S34. Matching recurses per character, so long inputs overflow the stack.** Status: new.
```clojure
(re-find #"a*" (apply str (repeat 3000000 \a)))   ; Clojure "aaa…"   jank SIGSEGV
```
- **Path:** regex_executor.tcc `_M_dfs` 510, `_M_rep_once_more` 178, `_M_handle_match` 321. Nearly every frame is a non-tail call.
- **Depth:** `a*` and `.*` take 2n+4 frames; `(a)*` 4n+4; `(a|b)*` 5n+5.
- **Bound:** with an 8 MiB stack and at least 16 bytes per frame (RXA4), n ≥ 262,143 overflows; at about 64 bytes per frame, n ≈ 65,000.
- Java runs single-character repeats in a loop.

**S35. Counted repeats past the NFA state limit are read errors.** Status: new.
```clojure
#"a{99999}"   #"\d{0,50000}"   ; Clojure valid   jank "Number of NFA states exceeds limit"
```
- **Path:** regex_compiler.tcc 243 → regex_automaton.h 33 (`_GLIBCXX_REGEX_STATE_LIMIT` 100000).

Round 2's regex entries on the replica:
- R79, R80, R82 are confirmed.
- R81 is confirmed, plus `(re-seq #"\b\w" "ab cd")` gives jank ("a" "b" "c" "d"). re-seq is also quadratic, because each find copies the remainder.
- R83 is confirmed per path. `replace` with no match returns the string cut at the NUL; `split` does not cut.
- R84 is confirmed with the exact ECMAScript rules: `"$12"` with one group gives ""; `"$2"` with one group gives "" (Clojure throws); a `replace-first` fn receives the groups vector. `re-quote-replacement` throws "TODO: port".
- R85 is confirmed on libstdc++'s own `regex_iterator` (regex.tcc 548/571/586).

### Analyzer

**S36. A local bound to a number, boolean or string literal cannot appear in call position, even where Clojure never makes the call.** Status: new. Round 2's run tagged it `native-callee` and set it aside without reporting it. It shares R23/R24's root, with a different symptom.
```clojure
(let [x 1] (if false (x) :ok))      ; Clojure :ok   jank analyze/invalid-cpp-call
(let [x true] (if false (x) :ok))   ; Clojure :ok   jank compile error
(loop [f 2147483647 k 0] (if (= k 1) (f 2147483647) (recur :k 1)))   ; Clojure nil   jank compile error
```
- **Path:** processor.cpp `analyze_let` 2377 (literal native type, cpp_util.cpp `literal_type` 603–720) → `analyze_call` 3607 → `analyze_cpp_call` 4055 → `build_indirect_cpp_call` 874/965 "There is no call operator for `int`".
- **Search:** 20 of 16,253,007 programs in a complete budget-2 world, and 50 more in samples.
- **Confidence:** medium-high (WA8).

**S37. `case` analyzes its default before its clauses.** Analysis has effects (a `def` interns its var), so the order changes what names mean. Status: new.
```clojure
(case 1 1 (def h 1) (h))                  ; Clojure #'user/h              jank unresolved symbol h
(case 2 1 (do (def inc 5) inc) (inc 1))   ; Clojure throws (unbound)      jank 2
(case 1 1 (var when) (do (def when 1) 2)) ; Clojure #'clojure.core/when   jank #'user/when
```
- **Path:** processor.cpp `analyze_case` 1386: default at 1466, clauses at 1500. Clojure: CaseExpr.Parser 9577 (clauses), then 9589 (default).

**S38. A macro expansion headed by a local's name is expanded again as a macro.** Status: new; distinct from R29.
```clojure
(let [when 0] (and 1 (when true 7)))                       ; Clojure throws (0 is not a fn)   jank 7
(let [comment (fn [x] (str "// " x))] (-> "hi" comment))   ; Clojure "// hi"                  jank nil
(defn f [time] (-> 5 time)) (f inc)                        ; Clojure 6                        jank prints "Elapsed time…", 5
```
- **Path:** processor.cpp `analyze_call` 3501–3533 → context.cpp `macroexpand` 639–661 recurses at 657 → `macroexpand1` 604–637, which never checks locals. Clojure: `analyzeSeq` 7616–7618 and `isMacro` 7427–7430.

### Code generator and optimizer

The configuration:
- `-O n` sets the codegen level (cli.cpp 324–341) and the runtime level for run/repl.
- The JIT and AOT clang arguments include `-fwrapv` (CMakeLists.txt 342), then `-O<level>` last.
- codegen/optimize.cpp is never called.
- The JIT runs clang's own `-O` pipeline on each incremental module (Clang 23.1.0 CodeGenAction.cpp 322, BackendUtil.cpp). LoopDeletion runs at O1 and above.

**S39. A side-effect-free loop (or fn-level `recur`) that never ends is undefined behavior at -O1 and above.** Status: new; changes R24.
```clojure
((fn [x] (loop [] (if x (recur) :done))) true)   ; Clojure never ends   jank -O0 never ends; -O1+ UB, likely returns :done
(loop [x 0] (if (< x 10) (recur (+ x 0.5)) x))   ; Clojure 10.0         jank -O0 never ends; -O1+ UB
```
- **Path:** cpp_processor.cpp gen(loop) 992–1022 (`while(true){` at 1011; recur's `continue;` at 934); ir/processor.cpp 261–317 and 522–591. C++ forward progress makes such loops `mustprogress` (CGStmt.cpp 1009–1048), and LoopDeletion removes them (LoopDeletion.cpp 105–115).
- **Search:** 83 of 2,000 programs in every optimized mode.
- **Theorems:** `jit_loops_must_progress`; `r24_never_exits` (∀ n > 0, c < n: new for-every-input version of R24's bounded result).
- **Confidence:** high that it is UB; medium on the outcome.

**S40. Float-to-integer conversions in emitted code have no range check.** Status: (a) extends R24; (b)–(d) new.
```clojure
(loop [x 0 n 0] (if (< n 1) (recur 1e10 (+ n 1)) x))   ; Clojure 1.0E10   jank -O0 -2147483648; -O1+ UB
(int 1e20)                                             ; Clojure throws   jank -O0 -9223372036854775808; -O1+ UB
(int 2147483648)                                       ; Clojure throws   jank 2147483648
((fn [^cpp/long p] p) 1e20)                            ; Clojure throws   jank UB inside libjank
```
- **Path:** (a) cpp_processor.cpp 1708–1716 (`static_cast<int>`); (b, c) math.hpp `to_int` 1410–1420; (d) `from_object` → `to_integer`; analyze_recur 2183–2214 → apply_implicit_conversion 1088–1118.

**S41. A map or set expression whose keys collide at run time does not throw.** Status: new. R13 covers only literal duplicates.
```clojure
(let [a 1 b 1] {a :x b :y})          ; Clojure throws "Duplicate key"   jank {1 :y}
(let [a 1 b 1] #{a b})               ; Clojure throws                   jank #{1}
{(identity 1) :x (identity 1) :y}    ; top level: Clojure throws        jank {1 :x, 1 :y}, count 2
```
- **Path:** codegen/api.cpp 213–449 (`assoc_in_place`, `conj_in_place`); evaluate.cpp eval(map) 447–491 (`in_place_unique` 463/469) and eval(set) 493–509. Clojure: `RT.map`/`RT.set` → `createWithCheck`.
- **Theorems:** `dup_pair`, `dup_set`, `no_dup_agree`.

**S42. More than 10 parameter symbols is rejected, and the `& rest` symbol counts as one.** Status: new.
```clojure
(fn [a b c d e f g h i j k] k)     ; Clojure ok   jank "too many parameters. The max is 10"
(fn [a b c d e f g h i j & r] r)   ; Clojure ok   jank the same error
```
- **Path:** processor.cpp 1866–1872; `max_params` is 10 (core/call.hpp 18).
- A fixed-arity fn called with N ≥ 11 arguments reports 11 in its arity error.
- **Caveat:** the error message states the limit; the book does not.
- **Search:** 1,949,679 calls, complete. Every other part of arity dispatch agrees; residual over 382,959 calls finds nothing.

**S43. A native-typed parameter with fn-level `recur` emits C++ that does not compile.** Status: new.
```clojure
((fn [^cpp/long n] (if (< n 3) (recur (+ n 1)) n)) 0)   ; Clojure (^long) 3   jank C++ "no matching constructor for … object_ref"
```
- **Path:** ir/processor.cpp 261–270 types every fn-recur shadow as `object_ref`; cpp_processor.cpp 1001 emits `object_ref s(n)`; oref.hpp 219–290 has no arithmetic constructor.
- **Search:** 84 of 2,000 programs.

**S44. Evaluating code that quotes an existing object rewrites that object's metadata in place.** Status: new.
```clojure
(def v (with-meta [1] {})) (eval (list 'quote v)) (meta v)   ; Clojure {}   jank nil
```
- **Path:** analyze/pass/strip_source_meta.cpp 13–42 calls `reset_meta` on the quoted object; core/meta.cpp 84–113, 229–239.
- **Theorem:** `strip_changes_iff` (∀).

### C++ interop (CppInterOp and the Clang answers it reaches replicated)

**S45. The DSL cannot name `long long`.** Status: new; changes R94.
```clojure
(cpp/cast (:long (:long int)) 1)                            ; C++ long long   jank long
#cpp (:member (std.numeric_limits (:long (:long int))) max)  ; the book's example says numeric_limits<long long>
```
- **Path:** processor.cpp `analyze_cpp_dsl_impl` 5205–5238 → CppInterOp.cpp `GetLongType` 3290: `LongLong` becomes `long`, and `Long` comes back unchanged (3301).
- **Theorems:** `dsl_never_long_long` (∀ chains, bases, platforms), `long_long_int_is_long`.

**S46. `(:signed char)` is plain `char` on x86-64, and `(:unsigned char)` is plain `char` on AArch64 Linux.** Status: new.
```clojure
(cpp/raw "int f(signed char *p) { return 1; }")
(cpp/f (cpp/cast (:* (:signed char)) cpp/nullptr))   ; C++ 1   jank x86-64: "No matching overload"
```
- On AArch64 the book's `(:array (:unsigned char) 1024)` becomes `char[1024]`.
- **Path:** CppInterOp.cpp `GetSignedType` 3131/3174 and `GetUnsignedType` 3188/3199.
- This is the only x86-64/AArch64 difference found. World III (R86, R92, R95) gives the same 10 of 312 on both platforms.

**S47. `(:member* T m)` takes a member name; the book defines it with a member type.** Status: new.
- `(:member* Foo (:fn int [(:& (:const std.string))]))` gives "Member names need to be symbols."
- `(:member* Foo int)` gives "There is no `int` member".
- `(:member* Foo x)` gives `int Foo::*`.
- **Path:** processor.cpp 5490–5540 (symbol check at 5502).
- **Search:** world X, 12 of 264.

**S48. Smaller member-form deviations.** Status: new, low.
- `:&member` and `:member*` skip `:member`'s private/protected check (JIT error later).
- All three forms look through pointers (CppInterOp.cpp `GetScopeFromType` 1111).
- An overloaded static member is reported missing (`GetNamed` 1181).
- `(:member Foo get)` of a non-static method is typed `int (*)()` (`GetTypeFromScope` 3537).

**S49. Explicit template arguments of a called function template are dropped.** jank deduces again from the call arguments. Status: new.
```clojure
(cpp/raw "template <typename T> T add(T a, T b) { return a + b; }")
(#cpp (add double) 1 2)   ; C++ 3.0   jank 3
(#cpp (add int) 1 2.5)    ; C++ 3     jank "No matching overload"
(#cpp (zero double))      ; C++ 0.0   jank "No matching overload"
```
- **Path:** processor.cpp 5601–5735; CppInterOp.cpp 6580; then processor.cpp 4111 → `build_cpp_call` 551–553 looks up the template by name → `find_best_overload` 1584 → `BestOverloadMatch` 2203 → `AddTemplateOverloadCandidate` 2114 with empty explicit arguments.
- **Search:** world XII, 69 of 75.

**S50. Calls through function pointers and pointers to members reject arguments that a reference parameter would bind after a conversion.** Status: new.
```clojure
(cpp/raw "long twice(long const &x) { return 2 * x; } long (*twice_ptr)(long const &) = twice;")
(cpp/twice_ptr 21)   ; C++ 42   jank "argument 0 is not convertible from `int` to `const long &`"
```
- **Path:** `build_indirect_cpp_call` 989 → cpp_util.cpp 927 → CppInterOp.cpp 639 (TryImplicitConversion to a reference type; SemaOverload.cpp 2663–2668).
- **Theorems:** `isImplicitlyConvertible_to_lref` / `_rref`. **Search:** world XI, 16 of 188.

**S51. A pointer-to-member call on a pointer to const is rejected.** Status: new.
```clojure
(#cpp (:&member Foo get) (cpp/cfoo))   ; C++ 3   jank "not convertible from `const Foo *` to `Foo *`"
```
- **Path:** processor.cpp 929 → `GetFunctionTypeFromPointerToMember`; `isConstQualified()` at 2900 tests the pointer, not the pointee.
- **Theorem:** `pm_const_pointee_dropped`.

**S52. Indirect calls accept invalid C++.** Status: new, low.
- Explicit constructors count as conversions (`AllowedExplicit::All`, CppInterOp.cpp 648).
- A privately derived object passes the pointer-to-member class check (processor.cpp 903).

**S53. Built-in operators are unavailable for class operands that convert to arithmetic types.** Status: new.
```clojure
(cpp/raw "struct meters { double v; operator double() const { return v; } }; meters mk() { return {1.5}; }")
(cpp/+ (cpp/mk) 1.0)   ; C++ 2.5   jank "operator `+` is not supported"
```
- **Path:** processor.cpp 367–511 → `GetOperator` 6977 returns only declared operators.
- **Search:** 12 of 42. **Confidence:** high (assumes CXA10).

**S54. An inherited static data member cannot be read through an instance.** Status: new.
```clojure
(let [b (cpp/Bar)] (cpp/.-count b))   ; count is static in base Foo; C++ 3   jank "There is no `count` member within `Bar`."
```
- **Path:** processor.cpp 4766 → `LookupDatamember` (2502) returns null for a static member; `get_static_datamembers` at 4803 lists only the class's own (1337).

**S55. A member of a privately inherited base passes analysis.** Status: new, low.
- **Path:** `IsPrivateVariable` 2797 checks only the member's own access. The JIT then fails.

**S56. `cpp/unsafe-cast` judges the type, not the value.** Status: new.
- It rejects valid C-style casts: `(cpp/unsafe-cast color 1.5)` and `(cpp/unsafe-cast long cpp/nullptr)` both give "Invalid unsafe-cast".
- It accepts integer, bool or pointer values cast to member pointers or `std::nullptr_t`.
- **Path:** processor.cpp 4447 → `IsCStyleConvertible` 653–686.
- **Theorems:** `isCStyleConvertible_floating`, `_nullptr`. **Search:** world XV, 19 of 144.

**S57. An `if` with a reference-typed native branch (a `cpp/` global or member access) takes the other branch's narrower type.** Status: new; an R23 variant (R23 widens, this narrows).
```clojure
(cpp/raw "double gd = 2.5; int gi = 7;")
(if false 1 cpp/gd)      ; Clojure 2.5   jank 2
(if false true cpp/gi)   ; Clojure 7     jank true
```
- **Path:** cpp_util.cpp `find_branch_common_type` 1909–1995. `GetCommonType` (578) is null for references, so the swap at 1979–1984 picks the convertible branch's type.
- **Theorem:** `getCommonType_ref_null`.

**S58. Native catch handlers differ from the C++ handler as written.** Status: new, low.
- jank turns a by-value catch into a reference (processor.cpp 3056–3079), so a modified rethrow differs.
- `(catch (:array int 3) e …)` never matches.
- `(catch (:&& int) e …)` compiles as `int &`.
- The book says "just like in C++". Not searched: the nREPL `handle-client` catches only `std::exception`, `object_ref` and `error_ref`, so another native type ends the connection.

### Collections (immer replicated)

**S59. A key or set element `=` to a stored one replaces the stored one in hash maps and hash sets.** Status: new.
```clojure
(first (keys (assoc (hash-map '(1) :a) [1] :b)))   ; Clojure (1)   jank [1]
(first (conj #{'(1)} [1]))                         ; Clojure (1)   jank [1]
(first (conj #{0.0} -0.0))                         ; Clojure 0.0   jank -0.0
(let [m (into {} [[0 0] [1 1] [2 2] [3 3] [4 4] [5 5] [6 6] ['(1) 0]])]
  (some vector? (keys (assoc m [1] 1))))           ; Clojure nil   jank true (8 entries promote)
```
- **Path:**
  - persistent_hash_map.cpp 110 → immer map.hpp 400 → champ.hpp 604–606 (`copy_inner_replace_value`, the whole pair) and 577–581 (collision nodes);
  - transient paths: champ.hpp 697–699, 654;
  - sets: persistent_hash_set.cpp 151 → set.hpp 220; transient_hash_set.cpp 46.
  - Below 8 entries the array map keeps the stored key (native_array_map.cpp 139–162).
- Clojure keeps the stored key: BitmapIndexedNode.assoc 704; PersistentHashSet.cons 98–101.
- **Theorems:** `doAdd_replaces` (∀), `im1_jank_key_replaced`.
- **Search:** class key-identity in six censuses. The residuals M1r2 (3,016,000), M2r2, M3r, S1r2 and S2r are complete with nothing.

**S60. An array-map transient can still be read after `persistent!`.** Status: new; the map counterpart of round 1's D15 (fixed for vectors).
```clojure
(let [t (transient {:a 1})] (persistent! t) (get t :a :nf))     ; Clojure throws   jank 1
(let [t (transient {:a 1})] (persistent! t) (contains? t :a))   ; Clojure throws   jank true
(let [t (transient {:a 1})] (persistent! t) (find t :a))        ; Clojure throws   jank [:a 1]
```
- **Path:** transient_array_map.cpp 47, 52, 62, 146 lack `assert_active()`; `to_persistent` 126–131 moves `data` with the defaulted move constructor (native_array_map.hpp 34), so the dead transient keeps the same array.
- **Theorem:** `im2_dead_array_reads` (∀ contents, key, default).

**S61. A map's `conj` rejects a seq of entries, including an empty list.** Status: extends R107. Round 2 had the code path, but only through a trailing `(seq m)` in kwargs destructuring.
```clojure
(conj {} ())                    ; Clojure {}        jank throws "invalid map entry"
(merge {:a 1} ())               ; Clojure {:a 1}    jank throws
(into {} [()])                  ; Clojure {}        jank throws
((fn [& {:as m}] m) :a 1 ())    ; Clojure {:a 1}    jank throws
```
- **Path:** obj/detail/base_persistent_map.cpp `conj` 169 (throws at 182–186: only nil, a map or a 2-vector); transient_array_map.cpp 98 (112–115); transient_hash_map.cpp 110 (124–129); core.jank destructure 3427–3436. Clojure: APersistentMap.cons 27–49 and ATransientMap.conj 25–47 walk any seqable.
- **Theorems:** `p1_jank_conj_throws`, `p1_clj_adds_nothing`, `odd_agrees`. `odd_agrees` fails on exactly two trailing elements: `(seq m)` and `()`.

### Runtime: locks (folly replicated) and GC (bdwgc replicated)

**S62. A validator that calls `set-validator!` on its own atom hangs, and so does one that reads or updates its atom beside a concurrent `set-validator!`.** Status: new; the validator counterpart of D16.
```clojure
(def a (atom 0))
(set-validator! a (fn [v] (when (= v 1) (set-validator! a (fn [_] true))) true))
(swap! a inc)   ; Clojure 1   jank hangs
```
- **Path:** atom.cpp `validate` 261–265 holds `validator.rlock()` (263) across the call; `set_validator` 236–241 takes `wlock()` (239). folly SharedMutex.h `lockExclusiveImpl` 1047–1110 sets kHasE, then waits for S (1086–1088).
- **Tape:** 11 × `thread.next` (coarse) / 21 steps on the fine replica. **Story:** thread 0's validator holds S and calls `get-validator`; thread 1's `set-validator!` sets kHasE; thread 0's nested rlock waits on kHasE while thread 1 waits on thread 0's S.

**S63. `alter-var-root` whose fn re-enters the var hangs.** Status: new.
```clojure
(def v 0)
(alter-var-root #'v (fn [x] (alter-var-root #'v inc) (+ x 10)))   ; Clojure 10   jank hangs
(alter-var-root #'v (fn [_] (def v 5) 6))                         ; Clojure 6    jank hangs
```
- **Path:** var.cpp `alter_root` 106–112 holds `write_mutex` (108) across `apply_to`; `bind_root` 101 takes it again. Clojure's methods are synchronized (reentrant).

**S64. A delay whose body asks `(realized? d)` or derefs `d` hangs.** Status: new. Round 1's D19 still holds and is unrelated.
```clojure
(def d (delay (realized? d))) @d                ; Clojure false                jank hangs
(def e (delay @(future (realized? e)))) @e      ; Clojure false                jank hangs
(def s (delay @s)) @s                           ; Clojure StackOverflowError   jank hangs
```
- **Path:** delay.cpp `deref` 19–46 holds a non-recursive `std::mutex` (21) across the body (34); `is_realized` 51 takes it again.

**S65. `future-cancel` of a future that another thread is dereferencing hangs all three threads.** Status: new.
```clojure
(def f (future (cpp/jank.runtime.sleep 100) 1)) (def g (future @f)) (cpp/jank.runtime.sleep 10)
(future-cancel f)   ; Clojure true (@g throws CancellationException)   jank: caller, g and f hang
```
- **Path:** future.cpp `deref` 17 holds the thread lock across `join()`. core.cpp `cancel_future` 1178 holds state S while taking the thread lock (1181). The future's completion needs state E (1132).
- **Tape:** 12 steps coarse / 23 fine.
- By reading: `cancel_future` returns void, so `(future-cancel f)` is nil. `future-done?` and `pmap` throw "TODO: port".

**S66. `future-cancelled?` on a running future that another thread is dereferencing hangs (Linux).** Status: new.
- **Path:** core.cpp `is_future_cancelled` 1192 holds the upgrade lock while taking the thread lock (1216); completion's E waits on kHasU (SharedMutex.h 905, 1050–1053).
- **Tape:** 11 coarse / 22 fine.

**S67. Reading pending lazy var metadata evaluates it under the var's exclusive lock, so a meta expression that reads the var's meta hangs.** Status: new; the lock side of R43.
```clojure
(defn mk [] (def ^{:doc "v" :m (meta #'v)} v 1)) (mk) (meta #'v)   ; Clojure the map   jank hangs
```
- **Path:** cpp_processor.cpp gen(def) 527–557 → var.cpp 296–302 → lazy_meta.cpp `get` 30–46 holds `state.wlock()` (32) across `_jank_eval_str`.
- Needs a def compiled through codegen; the top-level interpreter sets meta eagerly.

**S68. A module loaded through a managed load fn holds the loader's mutex while its top level runs.** If that top level waits on a thread that loads a module, both hang. Status: new.
```clojure
(ns app.core) (def x @(future (require 'app.other) 1))   ; AOT program: Clojure x = 1   jank hangs at startup
```
- **Path:** module/loader_dynamic.cpp `load` 724–737 holds `state.lock()` (recursive_mutex) across the load fn; another thread's require blocks at 727 or `find` 549–554.
- **Confidence:** medium.

**S69. A value in flight as a C++ exception is not a GC root.** Status: new.
```clojure
(defn boom [] (throw (ex-info "boom" {:k (vec (range 3))})))
(try (try (boom) (finally (dotimes [_ 100000] (vec (range 8)))))
     (catch cpp/jank.runtime.object_ref e (ex-data e)))   ; Clojure {:k [0 1 2]}   jank reads freed memory
```
- **Path:** cpp_processor.cpp gen(throw) 1024–1050 copies the pointer into `__cxa_allocate_exception` memory (malloc, never scanned); gen(try) 1053–1101 runs the finally while the value lives only there. bdwgc's docs/gcinterface.md 167–169 states this limit.
- **Search:** found after 2 timelines. Clojure is complete with nothing over 64–256; the control is complete over 512.
- **Confidence:** medium-high (RTA8).

**S70. `var_unbound_root` is allocated pointer-free yet holds its var.** Status: new.
```clojure
(def x) (def u @#'x) (ns-unmap *ns* 'x) (dotimes [_ 100000] (vec (range 8))) (str u)
; Clojure "Unbound: #'user/x"   jank reads a freed var
```
- **Path:** var.hpp 179–191 (`pointer_free{ true }`) → oref.hpp 3086–3088 (`GC_malloc_atomic`); var_unbound_root `to_string` 351–354.
- **Theorem:** `atomic_scans_nothing`. **Confidence:** medium.

Checked and clean: persistent_string's typed descriptor marks exactly the buffer word at every size (`ps_descriptor_scans_data`); future threads register (Linux); module roots are covered (RTA10).

Library-level, not reachable from jank (recorded only):
- folly `fbvector::emplace` with an aliasing argument.
- jtl `s = s.c_str()` frees before reading.
- `push_thread_bindings()` self-deadlocks, but its only caller is unused.

### nREPL (evaluation now wired to the reader, analyzer and evaluator replicas)

**S71. A top-level `(do …)` is analyzed as one form.** Its later forms do not see macros, ns switches or aliases made by earlier ones. Status: new.

| eval | Clojure | jank |
|---|---|---|
| `(do (defmacro m [] 2) (m))` | `2` | eval-error ("Wrong number of args (0)") |
| `(do (in-ns 'foo) (def c 1))` | `#'foo/c` | `#'user/c` |
| `(do (require '[clojure.string :as s]) (s/join [1 2]))` | `"12"` | eval-error: `s/join` unresolved |

- **Path:** context_dynamic.cpp `eval_string` 59–71 analyzes each read form whole; processor.cpp `analyze_def` 1303–1306 interns at analysis; `analyze_call` 3505; evaluate.cpp eval(do) 574. Clojure: Compiler.eval 7684–7691 evaluates each form of a top-level `do` in turn.
- **Reach:** the nREPL, load-file, module loading (loader_dynamic.cpp 833/843) and the terminal REPL.
- **Theorem:** `evalString_analyzes_whole_form`. **Search:** gTopDo complete over 37,412; 6,329 are this class.

**S72. `lookup`/`info` in a namespace that does not exist answers for `user`.** Status: new.
- **Exchange:** eval `(def b 1)`, then `lookup ns=foo sym=b`. jank replies `{:info {:ns "user" :name "b"}}`; the expected reply is no-info.
- **Path:** handler/lookup.jank 11 (`(or … default-ns)`; a TODO at 9).
- **Theorem:** `lookupTarget_unknown`.

**S73. `pr-str` of a namespace is its bare name.** Status: new.
```clojure
(pr-str *ns*)   ; Clojure "#object[clojure.lang.Namespace 0x… \"user\"]"   jank "user"
```
- **Path:** ns.cpp `to_code_string` 223.

**S74. load-file of a file that switches namespace replies `:ns` with the file's namespace.** Status: new, medium-low (NA2).
- **Exchange:** load-file of `(ns lf) (def c 3)` gives `:ns "lf"`; expected `"user"` (`Compiler.load` binds `*ns*`, 8146/8183).
- **Path:** handler/eval.jank 74–80 → 33–37 → 60.

**S75. One eval request is one input: one value, one `*1` shift, and the first exception ends it.** Status: new, medium (rests on NA1, nREPL = `clojure.main/repl` over the code).
- `1 2` gives only `:value "2"`.
- `(def a 1) (throw (ex-info "x" {})) (def b 2)` never defines `b`.
- **Path:** context_dynamic.cpp 59–79; evaluate.cpp `safe_eval` 743–748; handler/eval.jank 59.

**S76. What printing the value prints is lost to its client, or reaches another client.** Status: new; at R126's site, without an exception.
```
eval (map println [1 2])   ; nREPL :out "1\n2\n" then :value "(nil nil)"   jank :value only; "1\n2\n" goes to server stdout
```
- **Two connections:** client 1, evaluating `(print "b")`, receives `:out "b1\n2\n"`, even with captures serialized under a lock.
- **Path:** handler/eval.jank 31–36 (capture wraps only `safe-eval`) and 59 (`(pr-str *1)` realizes after the capture); capture.jank 18/39 swap fd 1 process-wide.
- **Tape:** `thread.preempt=3` at decision 57 and `=1` at 82, all other decisions 0. **Story:** conn 0's capture ends; conn 1's capture redirects fd 1; conn 0's `pr-str` prints into conn 1's file.
- **Search:** T10 at ≤2 preemptions, complete over 1,304,752: 864 timelines.

Round 2's nREPL entries on the wired model:
- R1 holds: the eval never answers, and that thread keeps fd 1 and 2 on its capture files.
- R125 needs two preemptions: complete over 1,197,488, 16,224 wrong `:out`.
- R126: `*1` keeps the unprintable value.
- R127, R132 and R136 are now proved for every input.
- R139 holds on a complete search (7,669 timelines, not seed 0).
- None is retracted.
- Noticed: the terminal REPL never sets `*e`.

## What was replicated

| Area | Lean files (`Jank/R3/<Area>/`) | Mirrors |
|---|---|---|
| Boost | `CppInt`, `DecFloat`, `Ieee`, `Num`, `Java`, `Reader`, `Codegen`, `Tables`, `Search`, `Checks`, `Assumptions`, `Theorems` | cpp_int `do_assign_string` (every branch and message), `do_get_string`, `eval_convert_to(double)`; 51 cpp_dec_float routines line by line (construction, compare, add/sub/mul/div, `calculate_inv`, `rd_string`, `str`, `extract_*`, `fmod`, `pow2`, hash, interconvert); jank's number objects and math paths per type pair; Java BigDecimal/BigInteger; `gen_constant` and the AOT load |
| Immer | `Rbts`, `Champ`, `Objects`, `HashInv`, `Maps`, `Vectors`, `Kit`, laws | rbts (B = BL = 5: positions, push_back/push_tail, update, take/slice_right, every `_mut` path, vector_transient, iterator); CHAMP (get, add/add_mut, sub/sub_mut, make_merged, every copy/move node op, collision nodes, iterator, transients); jank's vector, array map, hash map, hash set and transients over them, with the promotion at 8 |
| Regex | `Traits`, `Scanner`, `Compiler`, `Executor`, `Algo`, `JankFns`, `Java`, `Compare`, `Search`, `Round2`, `Theorems`, `Kernel` | `regex_traits<char>` with glibc ctype; the ECMAScript `_Scanner`; `_Compiler` with NFA insertion and the state limit; the DFS `_Executor` (every handler, lookahead sub-executor, recursion depth); `regex_iterator`, `format`, `regex_replace`; jank's `re-*`, `replace`, `split`; a java.util.regex spec |
| Runtime | `Folly`, `Locks`, `Gc`, `Containers`, `Common`, `Theorems` | folly SharedMutexImpl at the atomic level (state word, deferred readers, futex waits, upgrade); Synchronized as jank uses it; jank's lock sequences per operation (atom, var, lazy_meta, delay, future, promise, loader, thread bindings); bdwgc reachability (mask, interior pointers, kinds, `GC_make_descriptor`, roots); fbvector; jtl string ownership |
| Interop | `Clang`, `CppInterOp`, `JankPaths`, `Worlds`, `Census`, `Theorems` | about 45 CppInterOp functions line by line; the Clang Sema answers they call (conversions, reference binding, overload ranking, casts, built-in operators); the jank DSL, indirect calls, operators, member access, unsafe-cast and catch paths |
| Codegen | `Flags`, `Native`, `NativeSpec`, `NativeSearch`, `Variadic`, `Literals`, `Census`, `Theorems` | cli/CMake/JIT/AOT flags and clang's `-O`/mustprogress rules; analyzer typing plus emitted C++ types with a per-level LLVM/x86 UB model; arity dispatch and packing past 10 args; `_jank_amap`/`hset`, `eval(map)`/`eval(set)`, `strip_source_meta` |
| nREPL | `Rt`, `JankEval`, `Handler`, `World`, `CljEval`, `Threads`, `ThreadSearch`, `Search`, `Theorems` | `eval_string` as steps over round 2's reader, analyzer and evaluator replicas with effects (vars, binding frames, stdout through the fd table); `safe_eval`, do-eval, lookup, completions; a Clojure process (`clojure.main/repl`, Compiler.eval/load) as spec |
| Proofs | `Lin`, `Threads`, `Atom*`, `Multi`, `Vector`, `Delay`, `Destructure`, `Range`, `ArrayMap`, `Lex` | linearizability as a proposition; invariant proofs through `interleave`; terminating versions of the round-2 lexer (`next` structural), parser (well-founded), destructuring evaluator, `cvEq` |
| Search | `Common`, `Analyzer`, `Reader`, `Core`, `Core2`, `Seq`, `Strings` | budget-bounded analyzer grammar with 26 kinds; reader classifier by trigger; wider core/seq/strings worlds |

## What is still left out, and why

- **Boost:**
  - cpp_int arithmetic internals (modeled by their documented exact semantics, MPA1);
  - cpp_dec_float routines jank does not reach (sqrt, Karatsuba);
  - `with-precision` and `rationalize` (unported in jank).
- **Immer:**
  - rrb/flex vectors and champ `update`/`diff`/`operator==` (jank never calls them);
  - bytes and capacities;
  - GC reuse;
  - CHAMP laws other than get-after-add: other keys need an equivalence that agrees with the hash, and jank's does not (D12, R55);
  - nth after `conj!`/`pop!` (searched, not proved);
  - vectors past 2^35 elements.
- **Regex:**
  - BFS executor, POSIX grammars, icase/multiline (unreachable);
  - Java lookbehind and inline flags (parsed, not matched);
  - captures inside lookaheads;
  - backtracking performance;
  - glibc's UTF-8 ctype table (RXA1, not fetched).
- **Runtime:**
  - folly spin/yield phases (only delay);
  - Synchronized::copy/swap (unused);
  - the JIT and multimethod recursive mutexes (no callbacks under them);
  - bdwgc internals beyond reachability;
  - 143 of 37,488 two-thread programs past 20,000 states (undecided);
  - macOS futures (RTA9).
- **Interop:**
  - class templates (settled by reading: SemaTemplate 5639–5650);
  - GetOperator's real lookup and ADL (CXA10);
  - emitted C++ of the new worlds ("JIT error" claims come from C++ rules);
  - nREPL handling of native exceptions (read only).
- **Codegen:**
  - LLVM's exact output under UB (reported as "undefined", with the likely pass named);
  - class/pointer typed params;
  - native world at depth 2 (about 10^9 programs);
  - round 2's depth-2 control stopped at 186,717.
- **nREPL:**
  - `try`/`binding`/loops in code strings, `line`/`column`;
  - interrupt, stack overflow, fd exhaustion (round 2's results stand);
  - T3/T7/T9 stopped at their bounds (below).
- **Proofs:**
  - destructuring `pb`/`pvec`/`pmap` still `partial` (the kwargs conversion is proved, not whole expansions);
  - the eight lexer loops are not tied together;
  - parser totality;
  - sorted-collection agreement (termination only);
  - sdk `linearizable` is `partial`, so `Lin.Linearizable` stands in (PA1).
- **Search:**
  - round 2's tiny depth-2 analyzer world cannot be completed: it has exactly 44,589,295,635,161,858 programs (`r2_tiny_depth2`), and round 2's 1.5 M were all inside the `if` partition. It is replaced by complete budget-2 worlds;
  - analyzer budget ≥ 3, destructuring nested twice and syntax quote at depth 3 are sampled only;
  - the length-7 numbers table: 7 of 18 partitions;
  - the multimethod method-table order (WA6), which needs both hash-map orders.
- **Not ported in jank:** protocols, records, types, agents, refs/STM (documented).

## Assumptions

**Replaced:**

| Assumption | Replaced by | Verdict |
|---|---|---|
| RA5 (cpp_int prefix rule) | cpp_int replica | confirmed: 0 differ over 813,616 strings and 16.6 M byte strings; boost also stops at a NUL |
| RA7 (empty BigDecimal literal is an error) | cpp_dec_float replica | confirmed; round 2's model accepted `"0-.M"` |
| RB7 (cpp_dec_float `str()`: no trailing zeros) | replica | confirmed for digits; contradicted for notation (S5) |
| RC2 (BigDecimal vs double compares exactly) | replica | confirmed (12,100 pairs) |
| Round 1 A4 (64-bit limbs), A13 (precision) | replica | confirmed; A13 holds up to 128 digits (S4) |
| Round 1 A3 / round 2 "immer abstracted" | immer replica | vectors confirmed (theorems); set order is CHAMP's; lookup refined (D12); insert keeps the last element (S59) |
| RA8 (std::regex rejects Java-only groups) | libstdc++ replica | confirmed except possessive quantifiers (S25) |
| RB "ECMA-262 std::regex"; R85 caveat | libstdc++ replica | differs from ECMA-262 (`\cX`, `\u` narrowing, `[]`/`[^]`, POSIX classes, quantified assertions, empty-loop rule); R85 confirmed |
| Round 1 A7 (writer lock is two steps) | folly SharedMutex replica | deadlocks agree on all 108 S/E programs; folly adds upgrade and deferred readers |
| Round 1 "folly SharedMutex is non-reentrant, writer priority" | replica | confirmed |
| RC "empty fbvector has null storage" | fbvector replica | refined (after `clear`/`erase`/`pop_back` the block stays) |
| AN "GetCommonType is `?:`'s type" | CppInterOp | contradicted (usual arithmetic conversions; null for classes and references) |
| AN "`=` on object_refs is not built-in" | CppInterOp + Clang | contradicted: R36 retracted |
| IA11 (array pointee) | CppInterOp | contradicted: R87 retracted |
| I "IsBuiltin false for enums" | CppInterOp | confirmed (R89; `isBuiltin_enum`) |
| I "GetScopeFromType strips one pointer" | CppInterOp | confirmed; also strips array dimensions; null for references and function types |
| I "overloads per [over.match.best]" | Clang SemaOverload | confirmed, with value categories |
| IA3, IA5, IA8; IsImplicitlyConvertible as copy-init | CppInterOp | contradicted (S45, S46, S50; enums not integral; operands are lvalues) |
| G "signed overflow wraps (documented)" | flags | confirmed: `-fwrapv` in JIT and AOT (`jit_has_fwrapv`, `aot_has_fwrapv`) |
| G "JIT passes `-w -Wno-c++11-narrowing`" | flags | confirmed (AOT lacks the second; nothing narrows) |
| Top level evaluated with the compiled meaning | evaluate.cpp | contradicted for `if` (R23 weakened) |
| nREPL "evaluation is a program table" | wired replicas | replaced; reproduces R126, R132, R136 |

**Still standing or new** (full text in each area report):
- **Boost:**
  - MPA1: cpp_int `/` truncates, `%` takes the dividend's sign.
  - MPA2: `BOOST_HAS_INT128`.
  - MPA3: libstdc++ hashes; `>>` goes through `strtod`.
  - MPA4: atoll saturates; int32 casts wrap.
  - MPA5: Lean `Float` is binary64.
  - MPA6: JDK ≥ 19.
  - MPA7: overload resolution per type pair.
  - MPA8: division by zero is documented.
  - MPA9: big literals are boxed.
- **Immer:**
  - IMA1: owner tokens are never reused.
  - IMA2: mutation as same-identity replacement, checked by an aliasing invariant after every step.
  - IMA3: NDEBUG, untagged nodes.
  - IMA4: x86-64, signed `char`.
  - IMA5: round 1's `=` and hash.
  - IMA6: no identity shortcuts.
  - IMA7: users rebind transients.
- **Regex:**
  - RXA1: bytes 0x80–0xFF have no ctype class in either locale (UTF-8 table unverified).
  - RXA2: `transform_primary`.
  - RXA3: signed `char`.
  - RXA4: 8 MiB stack, ≥ 16 bytes per frame.
  - RXA5: Linux libstdc++.
  - RXJ1–4: Java details (ASCII `\b`, the loop rule, Pattern corners, lookahead captures).
- **Runtime:**
  - RTA1–3: spin phases, forced deferred-reader path, slot count 2/4.
  - RTA4: the coarse lock is justified by a refinement table of 1,360 programs, and every finding was rerun on the fine replica.
  - RTA5: callback depth budget.
  - RTA6: Clojure meta timing.
  - RTA7: cancellation at sleep.
  - RTA8: GC at any allocation; malloc and exception objects unscanned; no stale stack copies.
  - RTA9: Linux.
  - RTA10: lifted globals in declaration order.
  - RTA11: persistent_string layout.
- **Interop:**
  - CXA1: Clang predicates as read, other Sema answers per C++20.
  - CXA2: a non-fixed enum promotes to `int`.
  - CXA3–7: conversions, aggregates, assignment, casts, operator types per the standard.
  - CXA8: deferred deduction picks the same candidate.
  - CXA9: AArch64 `wchar_t` is unsigned.
  - CXA10: GetOperator finds no user operator.
  - CXA11: a cast-wrapped 0 is still a null pointer constant.
  - CXA12: array qualifiers sit on the elements.
  - CXA13: literal argument types.
- **Codegen:**
  - CGA1: the JIT runs clang's `-O` pipeline.
  - CGA2: x86 `idiv` traps; "integer indefinite".
  - CGA3: UB means any behavior.
  - CGA4: LoopDeletion's notion of side effects.
  - CGA5: globals in order.
  - CGA6: `^cpp/long` compared with `^long`.
  - CGA7: `va_arg`.
  - CGA8: binary64.
  - CGA9: x86-64 (on AArch64 only the -O0 column changes).
- **nREPL:**
  - NA1: eval = `clojure.main/repl` over the code (S75 only).
  - NA2: load-file = `Compiler.load` (S74 only).
  - NA3: `*ns*` = user per connection.
  - NA4: read, analyze and eval are one step each.
  - NA5: macros print nothing.
  - NA6: ns print with the hash elided.
  - NA7: core subset.
  - NA8: missing ns → no-info.
- **Proofs:**
  - PA1: Herlihy–Wing linearizability.
  - PA2: watches only record; distinct ids.
  - PA3: LL/SC CAS may fail spuriously.
  - PA4: deadlock = `interleave` report.
  - PA5: each delay thread derefs.
  - PA6: promise counted at the end.
  - PA7: the range fix is `countExact`.
  - PA8: P1 read, not run.
  - PA9: NUL-free file.
  - PA10: preference walk cut at 16 levels on both sides.
- **Search:**
  - WA1: reader classes by trigger.
  - WA2: 64-bit overflow is documented.
  - WA3: printed fn objects are implementation-defined.
  - WA4: byte strings are documented.
  - WA5: BigDecimal key sameness.
  - WA6: method-table order.
  - WA7: no `(var private)`.
  - WA8: GetScopeFromType of a builtin is null.
  - WA9: programs outside the replica count as agreeing.
- **Round 2's remaining assumptions stand:** RA1–RA4, RA6, RA9, RA10, the RB/RC locale and sort rules, Q and N.

## Properties checked

1. **Numbers:**
   - arithmetic, comparisons, `quot`/`rem` give Clojure's kind and value, or both throw;
   - `=` implies equal hashes;
   - `str`/`pr-str` match Clojure and read back;
   - conversions of every kind, and `bigdec`/`bigint` of strings;
   - AOT constants rebuild their literal.
2. **Collections:**
   - count, get, find, entries (keys told apart by identity) against Clojure's maps, sets and vectors after every step;
   - `=` symmetric, and `=` implies equal hash;
   - transient reads throw after `persistent!`;
   - CHAMP and rbtree invariants;
   - no aliasing between a live transient and other values.
3. **Regex:**
   - re-find, re-seq, re-matches, replace, replace-first, split give Clojure's results and throw exactly when Java does;
   - re-seq is finite;
   - matching stays within a stated stack bound.
4. **Runtime:**
   - the SharedMutex replica gives mutual exclusion and refines the coarse lock;
   - no deadlock that Clojure lacks;
   - nothing Clojure keeps alive is used after the collector freed it;
   - fbvector equals std::vector.
5. **Interop:**
   - DSL types match C++ specifiers; member forms match the book and C++;
   - indirect calls are accepted exactly when C++ accepts them;
   - explicit template arguments are honored; operators follow [over.match.oper];
   - member access, unsafe-cast and catch handlers follow C++;
   - `if` keeps each branch's value;
   - round 2's answers equal CppInterOp's.
6. **Codegen:**
   - jank equals Clojure per target and -O level;
   - -On equals -O0;
   - arity dispatch binds what Clojure binds;
   - run-time map/set keys behave as in Clojure;
   - eval leaves existing metadata unchanged.
7. **nREPL:**
   - no hang or deadlock;
   - replies carry id and session and end in one `done`, encode in bencode and decode with the spec decoder;
   - values and `:ns` match the spec;
   - each eval's `:out` is what it printed;
   - fd 1 is restored after every eval;
   - lookup matches `ns-resolve`; completions match `ns-map`;
   - per-session state.
8. **Widened round-2 properties:** analyzer, reader (agreement, totality, round trips, syntax quote), compare/sort, multimethods, namespaces, sorted collections, destructuring, ranges, transducers, chunked seqs, strings and printing.
9. **Proved for every input:** see Theorems.

## Search runs

"complete n" means every timeline within the bounds was run. "≤k" means every schedule within k preemptions of round robin.

| Area | World and bounds | Result |
|---|---|---|
| Boost | question table: 12,888 over 37 operands | 23 classes set aside in turn, then complete over 12,888, nothing |
| Boost | random literals: explore 20,000 mixed seeds per step | 12 classes + division by 0, then nothing (rerun mixed) |
| Boost | `(bigint s)`, `(bigdec s)`: 66,430 strings each | S15 528; S14 1,030 |
| Boost | codegen constants: 3,311 BigDecimal literals | S13 845; with S13 aside: complete, nothing |
| Boost | round 2's number table with the replica: 111,151 | 2 values change; strings ≤ 6 over `01789.eE-xMN/`: 5,229,043, nothing new |
| Immer | maps M1/M2/M3 (3–4 steps, identity keys) | complete 196,192 / 191,206 / 87,438; classes IM1, IM2, D12, R123 |
| Immer | map residuals M1r2 / M2r2 / M3r | complete 3,016,000 / 2,353,672 / 105,434, nothing |
| Immer | M1d (D12 on `=`/hash) | complete 16,953,976 |
| Immer | sets S1/S2 and residuals S1r2/S2r | complete; residuals 86,625 / 274,732, nothing |
| Immer | designed-hash M4 / M5 / S3 (depths 1, 6, collision nodes) | stopped at 10,750,000 / 4,750,000 / 24,500,000, nothing |
| Immer | vectors V1 / V1b at leaf, tail and depth boundaries | complete 33,316 / 684,330, nothing |
| Immer | V2–V4 (shift 15 and 20) and M6/S4 explores | nothing |
| Regex | round 2's tables (117,936 + 66,300), both locales | 1,891 answers change (S22) |
| Regex | syntax table 58,800; census ≤2 tokens 491,400 | classes as above |
| Regex | census ≤3 tokens: 12,794,600 per locale | 0 unexplained; residual with all toggles: complete, only R78/S25/S26 |
| Regex | census ≤4 tokens: 35,644,050 | 0 unexplained |
| Regex | exhaust ≤3 tokens, inputs ≤3, both locales | complete 3,655,600, nothing |
| Regex | exhaust ≤2 tokens, wide alphabet | complete 150,930, nothing |
| Regex | explore 20,000 mixed seeds | known classes only |
| Runtime | SharedMutex refinement: 1,360 programs, 2 and 4 slots | 807 = 807 deadlocks, 0 mismatches |
| Runtime | one-thread lock census | complete 62,391; residual complete, nothing |
| Runtime | two-thread lock census (12 partitions) | complete 37,488; 143 undecided |
| Runtime | GC worlds | found after 2; Clojure and controls complete |
| Runtime | fbvector (5 ops) / string (3 ops) | complete 2,570,054 / 32,520; residuals clean |
| Interop | census: 55 types, 3,025 pairs | — |
| Interop | worlds VIII' 3,432, X 264, XI 188, XII 75, XIII 42, XIV 30, XV 144, XVI 81, XVII 45 | each residual complete, nothing |
| Interop | round 2's V / VIII / III | 0/196 changed; 53/147; 10/312 on both platforms |
| Codegen | native world: 2,000 mixed seeds × JIT/AOT × -O0…-O3 | classes above |
| Codegen | native residual | depth 3: 20,000 seeds, nothing; depth 1: complete 421,986 per mode, nothing |
| Codegen | variadic | complete 1,949,679 |
| Codegen | map/set keys | complete 29,523 |
| Codegen | round 2 rerun | exact |
| Codegen | round 2 depth-2 control | stopped 186,717 |
| nREPL | World S: gEval / gNs / gTopDo / gKnown / gLoad / gFile / gLazyOut, 2 requests | complete 374,544 / 159,571 / 37,412 / 133,332 / 526 / 1,327 / 552 |
| nREPL | residual pairs / gResidual | complete 6,486 / 96,100, nothing |
| nREPL | 4 requests | 200,000 mixed seeds, nothing |
| nREPL | World T: T1 ≤2 / T2 ≤2 / T10 ≤2 | complete 1,197,488 / 1,344,960 / 1,304,752 |
| nREPL | World T: T4 ≤1 / T5 ≤1 / T6 ≤1 / T8 ≤2 | complete 2,016 / 34,496 / 48,384 / 7,669 |
| nREPL | World T: T3 / T7 / T9 | stopped at 400,000 / 1,489,000 / 853,000, nothing |
| nREPL | round 2's nine controls stopped at 20,000 | all complete (up to 1,313,952), nothing but R139 |
| Analyzer | budget 1 (383,161) and budget 2 (16,253,007 + 16,253,007 + 43,006,435) | complete, 0 unexplained after S36–S38 |
| Analyzer | samples at budgets 3–6 | 3.5 M, found S37, S38 |
| Reader | ≤6 over round 2's five alphabets and 7 new ones (5.2 M to 118.8 M each) | complete, 0 unexplained (S1) |
| Reader | totality without NUL, length 5 | complete 39,135,393 (round 2: ≤4, 1,222,981) |
| Reader | syntax quote, depth 2 | complete 63,397,308, nothing |
| Core | compare 50², sort ≤7 (39,089,245), comparator sorts | complete; R96–R99 only |
| Core | multimethods 3/3/1 | complete 32,768,000; R100 only |
| Core | namespaces, 6 ops | complete 7,529,536, nothing |
| Core2 | sorted sets | complete 42,797,040; R104 only |
| Core2 | sorted maps | complete 8,841,912 + 12,809,400; R104/R105 only |
| Core2 | destructuring nested twice | 2 M mixed seeds each; S61, then nothing |
| Seq | ranges 30,783; real ranges 3,696; transducers 3,947,580; chunked 804 | complete; known classes only |
| Strings | ≤5 code points, both locales: 17,567,638 | complete, 0 unexplained |
| Proofs | S61 table: 585 argument lists | 64 R107, 64 S61 |

## Theorems

No `sorry`, no `native_decide`, no new axiom. ★ marks a new for-every-input proof of a round-1/2 bounded result.

- **Atoms:**
  - ★ `linearizable_x86`: every interleaving of `swap!`/`@`/`compare-and-set!`/`reset!` is linearizable, for any number of threads and operations. Round 1: complete over 217,500; stopped at 500,000 with a deref.
  - ★ `linearizable_clojure`.
  - ★ `linearizable_llsc_weak`, `linearizable_llsc_no_cas`: LL/SC; round 1 stopped at 500,000.
  - ★ `llsc_cas_not_linearizable` (D17's tape).
  - ★ `no_deadlock`; `counter_linearizable`, `casRace_linearizable_x86`.
- **Multimethods:**
  - ★ `root_methods_same`, `agree_of_dominates_agree` (round 2: 2,048,000 programs without prefers).
  - `jank_prefers_direct` (R100's walk).
- **Destructuring:** ★ `even_agrees`, `odd_agrees` (round 2: 384,183); `p1_jank_conj_throws`, `p1_clj_adds_nothing`.
- **Vectors:**
  - ★ round 1's laws over its list model: `nth_iff`, `assoc_none_iff`, `assoc_set`, `pop_none_iff`, `subvec_none_iff`, `subvec_spec`, `transient_nth_agrees`.
  - ★ over immer's rbts itself: `iter_eq_get`, `get_assoc`, `get_assocMut`, `get_pushBack`, `get_take`, `get_pop_conj`, `pushBack_wfT`, `empty_wfT`, the size laws, `subvec_ok_iff`, `subvec_count`.
- **CHAMP:**
  - `get_add` (∀ well-formed champ, value, query; no assumption on the hash or the equality), with `map_get_assoc`, `set_get_conj`.
  - `doAdd_replaces` (S59 at its source).
  - `integer_longWithHash` (inverse of jank's long hash).
- **Round 1 fixes:** ★ `transient_keeps_source` (D14 fix; was complete over 33,849); ★ `delay_value_runs_once`, `delay_clojure_runs_once`, ★ `deliver_once` (D20 fix).
- **Sequences:** ★ `fixed_walk_agrees` with its 1- and 2-argument forms (round 2: 5,219 questions); `r24_never_exits`, `r24_clojure_exits`, `halfStep_*` (★ for R24).
- **Lexer:** ★ `lexSymbol_never_hangs` (round 2: 1,222,981 strings); loop-advance lemmas for every lexer loop.
- **Regex:**
  - ★ `dollar_only_at_end` (R79), ★ `smatch_groups_never_nil` (R80), ★ `reFind_stops_at_nul` and `reMatches_stops_at_nul` (R83), ★ `reSeq_infinite_of_stuck` (R81);
  - `format_two_digits_out_of_range` (R84), `makeRange_rejects_ascii_to_high` (S24), `lookahead_caret_holds`, `lookahead_boundary_ignores_left` (S33);
  - kernel-run examples.
- **Boost:**
  - `jank_str_fixed_iff`, `jank_sci_below_1e_4`, `jank_sci_from_1e128`, `aot_sci_text_rejected` (∀);
  - ★ `octal_le_decimal`, `octal_lt_decimal` (R7);
  - `no_decimal_third`.
- **Runtime:**
  - for every lock state: `exclusive_after_shared_never_drains`, `pending_writer_blocks_readers`, `writer_waits_for_reader`, `exclusive_reentry_blocked`, `upgrade_blocks_writer` (★ for D16's mechanism);
  - `ps_descriptor_scans_data`, `make_descriptor_exact` (all 64 six-word bitmaps), `atomic_scans_nothing`;
  - fbvector growth (`first_capacity`, `doubles_below_512`, `grows_by_half_between`).
- **Interop:**
  - ★ `dsl_never_long_long` (R94's class), `long_long_int_is_long`;
  - ★ `isBuiltin_enum` (R89), ★ `getPointeeType_array` (R87 retraction);
  - `isIntegral_enum`, `getScopeFromType_fnptr`;
  - `isImplicitlyConvertible_to_lref` / `_rref`, `isCStyleConvertible_floating` / `_nullptr`, `pm_const_pointee_dropped`, `getCommonType_ref_null`;
  - the platform split: `signed_char_is_char_x86`, `unsigned_char_is_char_aarch64`, and the others.
- **Codegen:**
  - `jit_has_fwrapv`, `aot_has_fwrapv`, `jit_level`, `aot_level`, `effectiveOpt_append_opt`, `jit_loops_must_progress`, `decimal_text_type_int_iff`, `int_min_literal_types`;
  - `only_variadic_agrees`, `ambiguous_agrees`, `eleven_to_twenty_fixed`, `ten_and_rest`, `strip_changes_iff`.
- **nREPL:**
  - `safeEval_success`, `safeEval_failure`;
  - ★ `safeEval_noForm_*` (R132), ★ `jankHandle_eval_session_indep` (R127), ★ `outReply_nil_iff` (R136);
  - `evalString_analyzes_whole_form` (S71), `lookupTarget_unknown`, `TB.deref_set_*`.
- **Search:** `r2_tiny_depth1`, `r2_tiny_depth2`, `r2_reduced_depth1` (exact world sizes); `w2_*`.

## Library gaps filled in the project (sdk/lean untouched)

- **Seeding:** `Source.seeded` with small seeds repeats its first draw. Every area uses SplitMix64-mixed seeds (`exploreMixed`, `mixSeed`).
- **Searches:**
  - `exhaust` stops at the first counterexample. Added censuses with classes and examples, residual chains of toggles, `exhaustUnder`/`censusUnder` (partitions by decision prefix), segmented censuses with resume paths, and Knuth's size `estimate`.
  - The sdk's `List.range` loops allocate the whole list; round-3 walks use `[0:n]`.
- **Threads:**
  - BFS state-space search with a visited set, shortest tapes and story replay;
  - preemption-bounded interleaving (`interleavePB`);
  - reentrant locks, condition variables, join and cancellation;
  - folly's SharedMutex (the library's `RwLock` agrees with it on deadlocks for S/E, but has no upgrade mode or deferred readers).
- **Linearizability:** a relational definition with the linearization-point method, because `History.linearizable` is `partial`.
- **Models:** a GC heap (kinds, descriptors, masking, roots, collection as a decision); object identity and in-place mutation with an aliasing check; keys with a chosen hash; a per-level LLVM/x86 UB model; Clang/CppInterOp semantics; a java.util.regex model; a Clojure process for the nREPL.
- **Kernel evaluation:** structural recursion and `decide +kernel` run replicas in the kernel; `Float` is opaque, so double examples are `#eval`'d.
- **Job limit:** `bin/job` (4 machine-wide slots, perl alarm) for every build and search; long censuses ran in segments of 18 minutes or less.

## Files

- Models: `Jank/R3/<Area>/`. Drivers: `Run/R3/<Area>.lean` (exes `jank3-boost`, `-immer`, `-regex`, `-runtime`, `-interop`, `-codegen`, `-nrepl`, `-proofs`, `-search`).
- Results: `results/r3-<area>-report.txt` (each area's full report) and `results/r3-<area>*.txt` (run outputs, including `r3-boost-mixed.txt`, `r3-runtime-census2-*.txt`, `r3-regex-grammar*.txt`, `r3-search-*.txt`).
- Pinned sources: `deps/` (immer, boost-multiprecision, bdwgc, cppinterop, folly, libstdcxx-15.3.0, llvm-23.1.0*, nixpkgs-pin).
- Scratch: `.r3-scratch/`.
- Changes outside round 3's own files:
  - `lakefile.toml`: 9 round-3 exe targets added.
  - `Run/R3/Boost.lean`: the coordinator's mixed-seed fix.
  - Round 1/2 files edited only to make definitions terminating: `Jank/Lex.lean`, `Jank/Read.lean`, `Jank/Core/Destructure.lean`, `Jank/Core/Sorted.lean`.
- No commits were made.

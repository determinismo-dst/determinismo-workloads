# REPORT-9: jank 94d32623 compared with Clojure 1.12, round 9

(The harness refused REPORT-9.md; this is REPORT-9.txt, in Markdown.)

**Version.** jank main 94d32623 (`upstream-r5/`). Its compiler+runtime is byte-identical to 7135b7708, the commit the real jank was tested at. Every jank path below is under `upstream-r5/compiler+runtime/`.

**Libraries.** Rounds 1–8's pinned sources (`fetch-sources.sh`). immer is jank-lang/immer 282629d0 (`deps/immer`, the submodule commit). Nothing new was fetched.

**Status.**
- Every item is a hypothesis from the Lean replicas, re-read against the source. jank was not built or run.
- Every Clojure result was run on Clojure 1.12.3 (JDK 23), the coordinator's version.
- The exceptions are nREPL 1.8.0's replies, read from its source. Its Java classes are not in the project, so the nREPL tests are jank only.

**Who did what.**
- Seven area agents worked in parallel, under `.r9-scratch/RULES.txt` (briefs in `.r9-scratch/briefs/`):
  - Q: the nREPL;
  - H: CHAMP;
  - W: strings as UTF-16;
  - E: errors as objects;
  - N: numbers;
  - T: sequences, laziness, transducers and ordering (new ground);
  - M: maps, sets, vectors, destructuring and the library namespaces (new ground).
- N and W each got one follow-up: N wrote V62b and R72f, W wrote W9r.
- I did:
  - the reconciliation of round 8's real run (section 1);
  - seven local fixes: V82, U80, U84, U88, U90, T9-2 and T9-9;
  - a Lean model of jank.shell's arguments (`Jank/R9/Coord/Shell.lean`);
  - the merge, its compile and warning checks over every .cpp file;
  - the test assembly and its Clojure check;
  - CHECK.md, an audit of the agents' tool calls, and this report.
- Area reports: `results/r9-<area>-report.txt` (nrepl, champ, str, err, num, seq, coll).

**Build.**
- `lake build` of the eight round-9 targets succeeds: 343 jobs. The targets are `jank9-nrepl`, `-champ`, `-str`, `-err`, `-num`, `-seq`, `-coll` and `-coord`.
- Round 9 adds 37 Lean files (9,186 lines) under `Jank/R9/` and `Run/R9/`.
- No `sorry`, no `native_decide`, no axiom declared.
- Every main theorem rests on `propext`, `Classical.choice` and `Quot.sound` at most (`results/r9-*-axioms.txt`). The exceptions are two of area N's, `fixNeg_boxable` and `fixNeg_nan`. They are proved by `bv_decide` (RULES allows it), which adds its own certificate axioms (`…_native.bv_decide.ax_*`): they trust the compiled proof checker, as `native_decide` would.
- The directory is about 1.7 GB (1.6 GB before the round), and nothing is left running.

## 1. Round 8 on the real jank, reconciled

### 1.1 CHECK.md's "should pass" against r8c-patched.tsv

- Every test round 8's CHECK.md named as passing with the patch passes, except g480, g481 and g482: `(nth "€€a" -1)` on its three paths. They err with "uncaught C++ exception: The index `-1` is out of bounds for this `persistent_string`."
- Every test CHECK.md named as still failing still fails, with the predicted value or error.
- Nothing passing with round 7's patch fails with round 8's (1,068 tests in common), and no stock verdict changed between the two runs.
- Round 8's 102 tests on stock: the 21 that pass are the 19 controls, y21 and y12g, as predicted.

**g480–g482: a wrong fix, from a model error in its path.**
- X20 made `persistent_string::nth` throw an object.
- A negative index never reaches it. `(nth s i)`, inlined or through the fn, is `cpp/jank.runtime.nth`, which is core/seq.cpp `nth` 648-660. That function rejects `index < 0` before it dispatches, with a std::runtime_error.
- Its text, "The index `{}` is out of bounds for this `{}`." with the type name, is word for word the one X20 changed, so the message could not tell the two throws apart.
- The same guard catches `(nth [1] -1)`. The walk over a sequential coll (684) and "not indexable" (690) throw std::runtime_errors too.
- Fixed by X20b (area E, section 4). RULES.txt now carries the lesson: follow the path to its throw.

### 1.2 The six fail/error changes

They are round 7's nine minus three: x27, s17 and a13 now pass, because V7r made read errors objects. Each of the six was predicted. Each is the test's own cause, made visible by a fix, or turned into another kind of error.

- **r34 (fail → error).**
  - R34 makes `(:k)` a call instead of an inlined `get`.
  - The call's arity error is `invalid_arity<0>` (object.cpp 82), a std::runtime_error ("Invalid call to `keyword` with `0` args provided."), which escapes `is`.
  - Fixed by A34.
- **r89 (error → fail).**
  - S71 evaluates a top-level `do` form by form, so the enum exists.
  - R89 then shows: an enum's zero is falsy (:f). No R89 fix.
- **b03 (error → fail).**
  - R54a ends the seq of a cut string at the last byte, so `(vec (seq (subs "aé" 0 2)))` is `[\a \�]`.
  - `subs` counts bytes (LG3). Fixed by W9u.
- **s49 (error → fail).** S71 again: the template is declared, and `(#cpp (s49_add double) 1 2)` gives 3, not 3.0 (S49).
- **u49 (fail → error).** U49a–d fix the first two assertions. The third, `ns-aliases`, throws "TODO: port ns-aliases" inside `is`.
- **v03 (fail → error).** V3 makes `load_dynamic_library` throw a C++ exception instead of nothing. Fixed by A34.

### 1.3 The 186 tests still failing, grouped

**The list.** Every test with its id, kind and cause: `results/r9-coord-186.txt`, made by `.r9-scratch/coord/classify.py` from `r8c-patched-failures.tsv`.

**The count.** The 186 are 132 replica tests and 54 generated ones. Each failure message was checked against the test's predicted value. The only mismatch is X20's path (1.1).

**By kind:**
- **Wrong fix, 3:** g480–g482 (X20).
- **Fix right, but its effect needs another cause fixed, 2:**
  - r34: R34, then the arity error;
  - v03: V3, then a C++ exception.
- **Partly fixed, 2:**
  - u49: `ns-aliases` is still unported;
  - u59: U59a, the run-time output target, is still unset.
- **Missing, 179.** Grouped:
  - **Round 8's four items with no fix, 12:**
    - H8-1: y22–y22e;
    - DEC8-1: y37–y38b;
    - Q1: y51, y51b;
    - Q2: y52.
  - **Strings as bytes, 66.**
    - Tests: b01, b02, b03, b07, lg3, v65–v68, v71, v75–v79, x19, x19b, x25b, and 48 generated.
    - The generated ones, by deviation: V66 18, R52 9, LG3 6, R58 6, V74+R58 6, V65 3.
  - **Numbers, 9:**
    - V55, V60, V61, V85: v55, v60, v61, v85;
    - V62/V63: v62, v63, g452–g454.
  - **Errors that are not objects, 8:**
    - V7 analysis and load: v07b, v07c;
    - V9: v09, v09b;
    - V18: v18;
    - V15: v15;
    - D15: d15;
    - U79: u79.
  - **CHAMP stored key, 2:** s59, u81.
  - **nREPL, 3:** V37: v37, v37b; U40: u40c.
  - **Regex engine (libstdc++'s std::regex), 21:** b24, b25, b27, b30, s22–s35, u35, v35, v36.
  - **C++ interop (CppInterOp), 25:** s49, s50, s53, u04, u05, u06, u20–u26, v25–v34 (11 tests), r89.
  - **Analyzer design, 6:** r28, r38, r108, r119, s36, s42.
  - **Printing, 4:** b16, b23 (one `to_string`), v46 (U39), b21 (`*print-length*`).
  - **Reader, 4:** a11, a17, a21 (design), a20 (local, not written).
  - **Runtime, 11:** u12, u18, u33, u40, u40b, u49, u59, u67, d21, d23, d25.
  - **Library, 9:**
    - u65 (format), u85 (nlohmann), u91, u92 (pprint), v47 (clojure.instant);
    - local, written this round: v82, u80, u84, u88, u90.

**Round 9 writes fixes for 109 of the 186** (CHECK.md section 2): every group above that names round 9, plus b27 (W9r also fixes R81).

**The 77 left:**
- regex 20;
- interop 25;
- analyzer 6;
- printing 4;
- reader 4;
- runtime 11;
- library 5 (u65, u85, u91, u92, v47);
- u40c and v15.

### 1.4 jank's suite

- 549 of 551 on stock and patched alike. The two failures are syntax-quote/pass-resolve-alias.jank and pass-unaffected.jank.
- The runner's trace shows each file read whole before it is evaluated (frames `user/let`, `reduce`), so `::c/bar` is read before `(alias 'c ...)` runs.
- With the patch, pass-unaffected's text is V7r's reader ex-info ("Unable to resolve namespace alias 'c'") instead of stock's "exit-0": the same failure, now an object.

## 2. Deviations at a glance

Clojure's result first, then jank's (stock unless noted). The tests are in `tests/jank_lean/deviations_r9_test.jank` (z1–z70, 181 deftests). Each comment gives the path, the stock value and the fix.

**Before choosing new ground, rounds 1–8 had covered:**
- **Reader, analyzer, codegen and interop:** reader, analyzer, codegen, C++ interop (rounds 1–5).
- **Numbers:** numbers and BigDecimal (1, 3, 6–8).
- **Hashing and equality:** hashing and `=` (1, 7).
- **Strings and regex:** strings, regex and printing (2, 3, 5, 6, 8).
- **Concurrency and errors:** transients, atoms, delays, bindings, futures and errors (1, 4, 5).
- **nREPL:** rounds 2–8.
- **CHAMP laws:** rounds 5–8.
- **Sequences:**
  - round 2's transducer catalogue (14 transducers over integers), R113–R124, chunking of real ranges only;
  - sort of at most 3 elements under a consistent compare;
  - round 4's cycle, nthrest, `counted?`, `reduce-kv`.
- **Collections:**
  - round 2's destructuring R107, multimethod prefers, sorted collections R104–R113;
  - round 4's collection objects U27–U34, clojure.data U61, clojure.walk U69, map entries U67, zipmap U81.

Never compared before:
- which sort algorithm runs, and what that does to comparisons that are not total preorders;
- the comparator's numeric result;
- which seqs are chunked (vectors, integer ranges);
- realization counts of iterate, apply and dedupe;
- `realized?` of cycle and of nested lazy seqs;
- sorted collections and NaN;
- index width and index kinds in `get`, `contains?` and `nth`;
- metadata through `select-keys` and `empty`;
- array-map promotion order;
- the order of keyword-argument maps;
- `assert`'s message;
- the walk demos;
- hash-set and hash-map iteration order against Clojure's own HAMT.

Both new areas were chosen there (sections 3.1–3.4).

**New (no earlier id):**
- **T9-1.** `(sort [3 ##NaN 1 2])`: `(3 ##NaN 1 2)` vs `(1 2 3 ##NaN)`. std::stable_sort vs TimSort. z39–z39c.
- **T9-2.** `(sort (fn [a b] (- a b)) [4294967296 0])`: `(4294967296 0)` vs `(0 4294967296)`. Clojure reads the comparator's result with `intValue`. z40, z40b. Fix: T9-2.
- **T9-3.** `(first (map f (range 100)))` calls f 32 vs 1 times. Vector seqs and `(range n)` are not chunked. z41–z41e.
- **T9-4.** `(doall (take 3 (iterate f 0)))` calls f 2 vs 3 times. z42–z42c.
- **T9-5.** `apply` realizes up to 12 arguments: `(first (mapcat f (list 1 … 15)))` calls f 4 vs 12 times. z43, z43b.
- **T9-6.** dedupe's first element realizes the whole 5-element list vs 2 elements. z44.
- **T9-7.** `(realized? (cycle [1 2]))`: true vs false. z45.
- **T9-8.** `(drop 3000000000 [1 2 3])`: throws "integer overflow" vs (). z46, z46b.
- **T9-9.** `(into [] (partition-all 2.0) [1 2 3 4 5])`: `[[1 2] [3 4] [5]]` vs `[[1 2 3 4 5]]`; a negative n throws vs not. z47, z47b. Fix: T9-9.
- **T9-10.** `(get (sorted-map 1 :a 2 :b 3 :c) ##NaN)`: :b vs :a; `dissoc`/`disj` of ##NaN empty the jank collection. z48–z48d.
- **T9-11.** `realized?` of an inner lazy seq unwrapped by an outer one: false vs true. z49, z49b.
- **T9-12.** A lazy-seq body that threw is forced again with its locals; Clojure's runs with them cleared: the counter reads 1 vs 2. z50.
- **T9-13.** `(str (map inc [1 2]))`: "clojure.lang.LazySeq@402" vs "(2 3)". Host-specific text, kept as stated. z54.
- **M9-1.** `(get [1 2 3] 4294967297)`: 2 vs nil. Clojure takes the key's `intValue`. z55–z55e.
- **M9-2.** `(get "abc" 1.5)`: `\b` vs nil; `contains?` and `nth` throw natively. z56–z56d.
- **M9-3.** `(contains? '(1 2) 0)`: throws vs false. z57–z57d.
- **M9-4.** `select-keys` drops the map's metadata. z59, z59b.
- **M9-5 = H9-3.** assoc of a present key to an 8-entry array map promotes it to a hash map, so the key order changes. z61–z61d, z31, z31b. Fix: H9-3.
- **M9-6.** The keyword-arguments map is a hash map: keys `[2 1]` vs `[1 2]`. Shares R107's code. z62, z62b.
- **M9-7.** `assert`: "Assert failed: (= 1 2)" and no data vs "assertion failed" with data. z63–z63d.
- **M9-8.** `prewalk-demo` / `postwalk-demo` print with `println`, not `prn`. z64, z64b.
- **M9-9.** `update-vals` of a sorted map stays sorted. z65, z65b.
- **M9-10.** `empty` of a seq keeps its metadata. z66, z66b.
- **M9-11.** Hash sets, and hash maps past 8 entries, iterate in another order than Clojure's HAMT: `(vec (hash-set 5 9 8))`. CHAMP stores a node's entries before its subnodes; Clojure interleaves them by position. z70–z70c.
- **H9-1.** A transient chain and its persistent twin end with different contents. Three BigDecimals share one hash; stock's `=` (D8) relates two pairs of them but not the third; the twins come out #{a} vs #{b} where Clojure gives #{a b}. z29, z29b. Fixed by the combined patch (R72's exact `=`) and by H8-1.
- **H9-2.** assoc of the held value, and conj of a member, return a new collection; Clojure returns the same object. z30–z30c. Fix: H8-1, H9-3.
- **Q9-1.** An nREPL eval of `""`: `#{"done"}` vs `#{"no-code" "done"}`. z33.
- **Q9-2.** An eval with no code lacks "error". z34.
- **Q9-3.** An eval in a missing ns lacks "error" and `:ns`. z35.
- **E9-1.** The runtime throws strings: `ex-message` of `(inc Long/MAX_VALUE)`'s error is nil (stock: a native error) vs "integer overflow". z6.
- **W9-1.** `(alength (char-array "é"))`: 1 vs 2. z15.

**New instances of known causes:**
- **DEC8-1:** `(-' 0.0)` and `(-' 1E+2M)`; `(- -2147483648)` (D1); `(-' Long/MIN_VALUE)` (V54). z8–z8d.
- **V55, V60, V61, V62/V63, V85:** z9–z14e.
- **The UTF-16 family:**
  - `(count "😀")` is 2;
  - half of a pair, its `index-of` and hash;
  - `reverse` of a reversed pair;
  - `replace` and `split` on an empty pattern;
  - `(char 65536)`;
  - `includes?` of half a pair;
  - `re-seq` past an empty match (R81).

  z16–z28.
- **A34's errors:** an arity error, an index error, analysis and load errors reaching `thrown?`; compiler data; a macro's ex-info as the cause. z1–z5.
- **S59/U81** through the hash-map constructor, the 8-entry promotion and set conj (z32–z32c). Also a kwargs map keeping the first equal key (z62c).
- **R121, R120, D10, U81, U67, D12:** z58–z58d, z60–z60d, z67, z68, z69, z69b, z51.

**Controls (named "control"):** 45. Each passes on stock and with the patch.

## 3. Deviations in full

Every deviation's program, Clojure's value, path, Lean proof and status is in its area report, section 1:
- `results/r9-seq-report.txt` (T9-*);
- `results/r9-coll-report.txt` (M9-*);
- `results/r9-champ-report.txt` (H9-*);
- `results/r9-nrepl-report.txt` (Q9-*);
- `results/r9-err-report.txt` (E9-1);
- `results/r9-str-report.txt` (W9-1).

The ones that change how a program behaves most are below.

### 3.1 M9-11: hash collections iterate in another order (area M)

- **The structure.** jank's CHAMP (immer) keeps, in each node, the entries stored directly before the subnodes. Clojure's BitmapIndexedNode keeps one array indexed by bit position.
- **When the orders agree.** For every key list and level, the two orders agree when no two keys share a position at that level (★ `HashOrder.champ_eq_clj_without_crowding`). They are always permutations of each other (★ `champ_perm_clj`).
- **Reach.**
  - Every hash set of a few keys whose 5-bit positions crowd, for example `(hash-set 5 9 8)`.
  - Every hash map past 8 entries.
  - 8,064 of the 16,384 subsets of 0–13 differ, and so does `(range n)` for every n ≥ 10.
- **What a program sees.** Printing, `seq`, `first`, `keys` and `vals`.
- **The model.** The order model matched round 3's CHAMP replica on all 16,384 subsets of 0–13, and Clojure's printed order on the probes.
- **No fix.** It is immer's node layout.

### 3.2 H9-1: twins with different contents (area H)

- **The three BigDecimals:**
  - a = 0.00000000000000000000000002084477M;
  - q = 0.00000000000000011000000000687110M;
  - b = 0.00000000000000023000000001916567M.
- **Why they collide.** All three hash to 3969516785 in jank. A boost search over 3 × 4,194,304 literals found them, and round 3's Lean replica gives the same hash.
- **Why `=` is not transitive here.** Stock `=` is within 2^-52 (D8): a = q and q = b, but not a = b.
- **The transient chain.** `(conj! a) (conj! b) (conj! a) (disj! q)` gives #{a}: the third `conj!` writes in place, then `disj!` removes b.
- **The persistent twin.** `(conj a) (conj b) (conj a) (disj q)` gives #{b}: `copy_collision_replace` moves a to the front (H8-1), then `disj` removes a.
- **Clojure:** #{a b} both ways.
- **Checked three ways:** immer's own code in C++, the Lean replica, and `decide +kernel` (`h91_stock_contents_differ`).
- **The theory behind it:**
  - With the fix, every mixed chain equals its all-persistent twin exactly, for every equality (★ `buildTF_agree_empty`).
  - Without the fix, they agree up to collision order when `=` is a partial equivalence (★ `buildT_agreeP_empty`).
  - H9-1 shows transitivity can't be dropped.

### 3.3 T9-1 and T9-2: sorting (area T)

- **Both sorts are stable.** For every list of fewer than 32 elements with integer keys, the replicas of std::stable_sort (libstdc++ 15: 7-element insertion chunks, buffered merges) and of TimSort (countRunAndMakeAscending, binarySort) return the same list for `sort`, `sort <`, `sort compare` and `sort >` (★ `replica_sort_agree*`).
- **The search.** Every total-preorder pattern up to length 8 (16,777,216 lists at length 8) plus 400,000 random lists of length 2–31 gave no difference.
- **T9-1 needs a comparison that is not a total preorder (NaN).** 35,698 of 87,380 lists up to length 8 with ##NaN differ.
- **T9-2: the comparator's result.**
  - A subtracting comparator agrees whenever every difference fits in an int (★ `minus_agree_in_int_range`).
  - 17,346 of 19,530 lists over {0, 1, 2^31, 3·10^9, 2^32} differ.
- **The fix, T9-2 (mine).** A long's or BigInt's low 32 bits; a double's (or ratio's) saturating cast is negative exactly when d ≤ −1.
- **Validation.** The std::stable_sort replica matched g++ 15's own sort on 15,888 cases. The TimSort replica matched Clojure 1.12.3 on the same 15,888.

### 3.4 T9-3 to T9-6: realization counts (area T)

- **Proved for every length (`Lazy.lean`):**
  - `first` of `map` over a range or vector: jank min(k, n) calls, Clojure min(n, 32);
  - `take k` of `iterate`: jank k calls, Clojure k − 1;
  - `apply`: jank min(len, 12), Clojure min(len, r + 2) for a variadic fn;
  - dedupe, for lists of 3 to 33 elements: jank 2, Clojure all of them.
- **Validation.** The counts matched Clojure on 209 cases.
- **No fixes.** Chunking, `iterator::next` and `apply_to`'s counting are design choices.

### 3.5 Q9-1 to Q9-3: eval's status sets (area Q)

- **The cause.** One: do-eval's own status sets (handler/eval.jank 23-29, 68).
- **Why no round saw them.** Round 3's judge never looked at these cases.

## 4. Fixes

Each applies alone to 94d32623. Each has a combined form in `fixes/combined/all.diff`: 114 files, made by `.r9-scratch/merge/r9.sh` from round 8's tree. The tests each fix should pass are in CHECK.md.

### Round 8's open items

**H8-1** (area H): `fixes/H8-1-immer.diff` in immer, plus `fixes/H8-1.diff` in jank.
- **The immer half.**
  - `copy_collision_replace` writes the new value in the replaced one's place.
  - A diff on jank's repository can't reach the submodule. The combined patch carries it as `fixes/combined/immer.diff`, applied in `third-party/immer`.
  - On immer itself, 2,249,685 random steps: transient/persistent order differences fell from 170,745 to 0.
- **The jank half (also S59 and U81).**
  - assoc, `hash-map`, the 8-entry promotion, `assoc!` and `conj!` keep the stored key, through immer's public `impl()`.
  - Round 6 had said no such API exists; that was a model error.
  - assoc of the identical value returns the map itself, and a set's conj of a member returns the set itself.
- **Proved:** with the fix, transient and persistent steps agree node by node (★ `addMutF_agree`), and a present key keeps its position (★ `addF_inPlace`, ★ `keys_kept`).

**DEC8-1** (area N): a runtime `negate`/`promoting_negate` called by `(- x)` and `(-' x)`.
- Long/MIN_VALUE throws, or becomes a BigInt with `-'`.
- -0.0 is kept.
- A NaN is returned as it is: a flipped NaN is the unboxable word D9 crashes on.
- A BigDecimal keeps R72's scale.
- **Round 8's suggestion was wrong** (`(mul -1 x)`): it wraps in C++ `int`, misses `-'`, and can make that NaN. Proved: ★ `fixNeg_eq_clj`, ★ `negDec_scale`, ★ `stockNegDec_eq_iff`.

**Q1, Q2, V37i** (area Q).
- **Q1:** a per-session input buffer and the stdin op. The tested behavior:
  - need-input with a wait: the connection's own thread handles the next requests, the stdin op among them;
  - Java's readLine rules, and nREPL's skip of one end of line after each eval;
  - `:stdin` in describe;
  - `read-line` calls a function bound to `*in*`.
- **Q2:** `(filterv some? …)` on the eval's replies. It applies after Q1 as `.r9-scratch/nrepl/Q2-on-Q1.diff`.
- **V37i:** interrupt is answered session-idle, or session-ephemeral without a session.
- **The fixed World T (World TQ), under every schedule:**
  - T9: 277,740 states and 42 final states, complete;
  - T3: 1,855,485 states and 245 final states, complete.
  - In both, round 3's judge holds, and no message lacks content (stock T9: 252 such messages).
- **Proved:** ★ `q2_messages`, ★ `responseFor_keeps_keys`, ★ `takeLine_split`, ★ `takeLine_addInput`.
- **Checked on the JVM:** the fix's code, copied verbatim, against `LineNumberingPushbackReader.readLine` over 400,000 random sequences: 0 differences.

**V62b** (area N, supersedes V62). `obj::single_real`, a heap number kind holding the float's value as an f64.
- Prints with Float.toString and hashes with Float.hashCode.
- Equals and compares with doubles by value.
- `float` and float-array reads return it; C++ floats stay small_real (suite file cpp/if/pass-typed-object.jank).
- The value-only V62 printed `(str (float 0.1))` with 17 digits. That regression is gone (z12e).
- Checked: its text and hash code, extracted verbatim, against Clojure on 30,803 floats, with 0 differences.
- **Still differs:**
  - `(double? (float 1))` (z12j: `double?` is `float?` in core.jank);
  - class names;
  - data.json writes a Float through its double;
  - interop floats stay doubles.

**The UTF-8 string family** (area W): W9u, W9h, W9c, W9r.
- **The design.** Strings stay UTF-8 bytes, and may hold a lone surrogate in its 3-byte form (WTF-8).
  - Every index a program sees is a UTF-16 unit; a char is one unit.
  - The string builder joins a high and a low surrogate back into 4 bytes, so `(str (subs s 0 1) (subs s 1))` and `(apply str (seq s))` give `s` back byte for byte, and `=` stays a byte comparison.
  - Each string caches its unit count, and ASCII keeps stock's O(1) paths.
  - The nREPL's bencode counts real bytes through two new natives.
- **W9h:** String.hashCode over units.
- **W9c:** `char` takes 0..0xFFFF.
- **W9r:** after an empty regex match, the search steps one unit. It is Java's Matcher.find over the bytes, which also fixes R81 (b27).
- **Proved for every string of units, lone surrogates included:**
  - `count`, `nth`, the hash, `index-of` and `last-index-of` equal Java's (★ `count_wtf8`, ★ `nth_wtf8`, ★ `hash_wtf8`, ★ `indexOf_wtf8`, ★ `lastIndexOf_wtf8`);
  - `subs` keeps the units (★ `subs_tail_units`), and `(subs s (index-of s x))` starts with x (★ `subs_indexOf_startsWith`).
  - For every byte string, `(subs s 0 (count s))` gives it back (★ `subs_whole`).
- **Searched:**
  - W9u's own C++ on 4,955 texts against Clojure: 1,148,414 results, 0 differences;
  - all 41,371 byte strings of up to 4 bytes under ASan and UBSan: 0 failures;
  - W9r on 302,255 results: 0 differences.
- **Still differs:** `char-array` (W9-1).

### REPORT-8's list for round 9

**V7's analysis and load parts, arity errors, and the other C++ exceptions: A34** (area E; it contains V7a).
- **The design: convert once, at the catch.** A `try` with an object handler gets an inner `try`:
  - handlers written before the object handler are rethrown unchanged (suite cpp/try/pass-catch-mixed.jank needs that);
  - objects pass through untouched;
  - an `error_ref` or a `std::exception` becomes an ex-info: its message, nil data, and for a jank error the error itself and its causes.
- **jank's own reporting stays as it was:**
  - `print_exception` prints the attached error's report;
  - `load_module` returns the attached error.
- **Proved for every handler list and thrown value:** the generated code is "an object handler is Clojure's catch of Throwable" (★ `fixed_eq_spec`). Nothing changes otherwise (★ `fixed_eq_stock_of_not_conv`, ★ `fixed_eq_stock_of_earlier`), and reporting is kept (★ `report_preserved`, ★ `load_module_unwrap`).
- **Searched:** 22,338 cases, all 67,014 checks agree.
- **V9 and V18:**
  - the thrown object is kept as the cause;
  - compile errors get the CompilerException shape (message, `:clojure.error/*` data, cause). Proved: ★ `v9_data_kept`, ★ `v18_star_e`.
- **X20b:** nth's checks throw ex-infos. For every collection and index, nth with X20 and X20b agrees with Clojure (★ `nth_fixed_eq_clj`), and X20's miss is proved (★ `x20_miss`).
- **Not written:**
  - V15 (a nil message: ex_info's signature, which needs a build);
  - E9-1 (each runtime string throw would become an ex-info).

**R72's speed** (area N).
- **What is measured.** Standalone C++ copies of stock's cpp_dec_float<100>, R72 and R72f, -O2, in ns per operation on the Mac. Treat the ratios as meaningful and the ns as indicative.
- **R72's cost on small values:**
  - add 46 against stock's 17.5;
  - compare 38 against 4.0;
  - hash 53, with one allocation, against 12;
  - but mul 18 against 160, div 123 against 1,063, and str 50 against 1,304.
- **R72 on medium and large values:**
  - compare reaches 120 ns and 604 ns (9 allocations);
  - hash reaches 156 ns and 640 ns (18 allocations).
  - The cause: counting digits through a decimal string.
- **What a fix changes: R72f** (combined only, written).
  - An i64 fast path, Java's intCompact, for `+ - *`, compare and hash.
  - Digit counts from the bit length, without a string.
  - A powers-of-ten table, and no rounding copy at precision 0.
  - It is bit for bit R72: 1,474,900 checks, and round 8's 229,699-case checker identical, 0 differences from the JVM.
  - ★ `fastAdd_eq`, ★ `fastSub_eq`, ★ `fastMul_eq` and ★ `fastCmp_eq` prove the fast path equals R72's path.
- **R72f's speed:**
  - small: add 9, compare 3.6, hash 2.4 with 0 allocations;
  - medium: compare 18, hash 14;
  - large: compare 41, hash 56.
  - Division and printing are unchanged.
- **Not measured:** X6's var deref per operation, which needs jank's var.

**The nREPL** (area Q).
- **T9u and T3u under every schedule: stopped, not complete.**
  - A flat state store reproduces T9 exactly (433,374 states).
  - T9u stopped at 66,000,266 states (60,955,648 expanded; round 8: 22,000,971).
  - T3u, its first run under every schedule, stopped at 65,293,143 states.
  - Both stopped at the 1,800-s job limit with nothing found, peak 3.6 GB.
  - Going on needs the store on disk (about 3.2 GB, past this round's disk share) or a reduction proved sound. Neither was done.
- **interleavePB as a decision tree (nREPLA6-1): half proved.**
  - Every run function that is causal and bounded, has at least 2 options per decision, and records path values modulo options, is exactly a finite decision tree. The sdk's `exhaust` over it ends complete with its leaf count (★ `tree_of_treelike`, ★ `exhaust_of_treelike`, ★ `exhaust_worldT`).
  - **Not proved:** that World T meets those conditions, or that a subtree is a function of the scheduler state.
  - **Checked on complete walks instead,** with 0 failures. The counts equal round 8's counters:
    - W1: 264,832;
    - W2 ≤0..≤3: 4, 84, 874, 5,974;
    - W3 ≤0..≤3: 4, 336, 11,938, 276,982;
    - T9 ≤0, ≤1: 64, 53,312;
    - T9u ≤0, ≤1: 64, 51,264;
    - T3 ≤0: 1,024.
    - T3 ≤1 stopped at 1,000,000 of 1,358,848.

**CHAMP's sequence theorem without a lawful equality** (area H).
- **With H8-1's fix, for every equality and every hash:** any chain of transient and persistent steps equals its all-persistent twin exactly, in contents, size and order (★ `buildTF_agree_empty`).
- **Stock, under a partial equivalence** (= symmetric and transitive; not reflexive, not agreeing with the hash):
  - a new invariant, each collision node pairwise unequal, holds at every reachable state (★ `cu_reach`);
  - the twins agree up to collision order (★ `buildT_agreeP_empty`).
- **Transitivity can't be dropped:** H9-1 is the program.
- **Searched:**
  - every sequence up to length 6 all-transient against all-persistent (3,257,437), and up to length 5 mixed (8,308,825);
  - under four equalities.
  - Results: 0 differences with the fix; on stock, contents differ only under the non-transitive one (9,336 and 2,624).
- **Not proved:** that jank's `=` is a partial equivalence apart from D8 and R55.

### Local fixes (coordinator and areas)

- **V82** (core.jank): `char-escape-string` and `char-name-string`, Clojure's maps. v82.
- **U80** (core.jank): `reduce-kv` reduces any other coll as a sequence of entries (Clojure's IKVReduce slow path). u80.
- **U84** (data/json_native.cpp): read-str takes nlohmann's SAX events, whose number_float carries the number's text.
  - With `:bigdec`, a decimal is the BigDecimal of its text; an integer past 64 bits is a BigInt of its text. u84.
  - Checked: syntax on both trees, jank's warnings (none), and nlohmann's SAX lexemes in a standalone run.
- **U88** (jank/shell.jank): `sh` gives boost an argument vector, the program found on the parent's PATH, instead of a quoted command line that boost splits again. u88.
  - Proved for every argument list: stock's split gives the arguments back when none contains `"` (★ `roundtrip_of_no_quote`, `Jank/R9/Coord/Shell.lean`).
  - The real test's argv is `[echo, a\, b"]` (`u88_echo`).
  - Searched: 599,844 lists of 1–3 arguments of 1–3 characters over {a, space, ", \}. 425,722 reach the child changed, all of them with a `"`.
  - The new C++, run standalone with deps/boost-process, gives echo `a" b` as one argument.
- **U90** (jank/shell.jank): `:env` names through `name`, values through `str`. u90.
- **T9-2** (core/seq.cpp): the comparator's result is read as Java's intValue. z40, z40b.
- **T9-9** (core.jank): partition-all's transducer casts n to a long and refuses a negative n. z47, z47b.
- **V55, V60, V61, V85** (area N):
  - V55: an object `-` checks a Long/MIN_VALUE subtrahend;
  - V60: `long` follows RT.longCast (2^63 saturates);
  - V61: a BigInteger flag prints without N;
  - V85: hash maps and sets test identity first, for heap objects.
- **H9-3** (area H): an 8-entry array map promotes only for an absent key, and assoc of the held value returns the map.

### The combined patch

- **What it is.** `fixes/combined/all.diff` (114 files) and `fixes/combined/immer.diff`. `.r9-scratch/merge/r9.sh` rebuilds them in this order:
  1. the coordinator's five;
  2. area E's merged A34+V9+V18+X20b;
  3. W9u, W9h, W9c, W9r;
  4. H8-1, H9-3;
  5. Q1, Q2-on-Q1, V37i;
  6. T9-2, T9-9;
  7. DEC8-1, V55, V60, V61, V62b, V85, R72f.

  Each step is a plain `git apply`, with no fuzz.
- **Compiled.** Every one of the tree's 207 .cpp files was checked syntax-only. 194 compile; the other 13 fail identically on round 8's tree (missing isocline, jankzip, cpptrace's real headers, build defines).
- **Warnings.** jank's warning flags on the 31 changed .cpp files gave one new warning, a `-Wcomment` from `/*` inside V18's comment. It was fixed in V18's diffs; none is left.
- **The .jank files.** fwdref.py: new 0 for every changed .jank file.
- **One predicted flip to failing:** fix-v03, which asserts jank's pre-A34 kind (`:native`). With A34 an object handler sees the error, which is Clojure's behavior; v03 itself passes.
- **Not in all.diff:**
  - V62 (V62b supersedes it);
  - V7a (inside A34);
  - Q2.diff (as Q2-on-Q1).

## 5. What is not exact

- Exceptions are compared by "throws" or by message, not by class (A34's ex-info stands for every Java exception class).
- V62b's Float has no class of its own for `double?`, `class` or `instance?`.
- W9u's non-ASCII `nth`/`get`/`subs` walk from the start (O(n)).
- W9r can't start a match inside a pair during an ordinary search, which a byte regex can't express.
- H8-1's jank side costs one extra lookup per hash-map assoc. Transient sets keep jank's one object per element: Clojure's transient set keeps the first element as the key and the last as the value, so no exact fix fits there.
- The nREPL's stdin from another connection is seen only when the waiting connection reads its next request (R128's one thread per connection).
- TimSort is replicated for fewer than 32 elements. std::stable_sort assumes its buffer is allocated.
- Benchmarks ran on arm64 macOS, not jank's x86-64 build.

## 6. Assumptions

**New:**
- **Coordinator:**
  - CoordA9-1: boost's `make_entry` on a lone `"` entry (undefined in C++) is modelled as empty; no tested argument reaches it.
  - CoordA9-2: Homebrew's boost_filesystem stands in for jank's in the U88 standalone run.
- **Areas:** listed in each report's section 6:
  - QA9-n, champA9-n (champA9-1: immer's half can't be a jank-repository diff), StrA9-n, ErrA9-n, NumA9-n, SeqA9-n, CollA9-n.
- **Replaced:**
  - round 6's "no public API returns the stored entry" (S59);
  - round 8's "for sets, returning the set would do" (true for persistent sets only);
  - round 1's A10 ("get truncating a long key with intValue is a quirk"): RULES section 5 doesn't allow it; it is now M9-1.

## 7. Properties

Rounds 1–8's 1–41 stand. New:

42. Every exception a program can catch in Clojure reaches jank's object catch as an object.
43. Sorting with a comparator reads its result as an int, and agrees with TimSort for total preorders.
44. A lazy expression realizes what Clojure's does (chunks of 32; iterate, apply and dedupe's counts).
45. Integer indices are read with intValue; a string takes any number index.
46. Hash collections iterate in Clojure's HAMT order.
47. assoc and conj of what a collection already holds return that collection.
48. A transient chain and its persistent twin have the same contents.
49. The nREPL's eval statuses are nREPL's (no-code, namespace-not-found with error).

## 8. Search runs

- **Coordinator:** U88's 599,844 argument lists.
- **Area E:** 22,338 catch cases (67,014 checks), and 64 nth cases.
- **Area N:**
  - 45,662 doubles and 2,008 longs against Clojure;
  - 30,803 floats;
  - 939,000 and 1,474,900 R72f checks;
  - round 8's 229,699 cases.
- **Area W:**
  - 4,955 texts (1,148,414 results);
  - 41,371 byte strings;
  - 302,255 regex results;
  - 383,832 replica checks.
- **Area H:**
  - 3,257,437 and 8,308,825 sequences under four equalities;
  - 2,249,685 immer steps;
  - 3 × 4,194,304 BigDecimal literals for the hash triple.
- **Area Q:**
  - World TQ T9 (277,740 states) and T3 (1,855,485), complete;
  - T9u stopped at 66,000,266, T3u stopped at 65,293,143;
  - 400,000 readLine sequences;
  - the walk checks of section 4.
- **Area T:**
  - 16,777,216 total-preorder lists (length 8) and 400,000 random lists;
  - 87,380 NaN lists, 19,530 subtracting-comparator lists;
  - 15,888 sort cases against g++ and the JVM;
  - 209 laziness cases;
  - partition-all over n ∈ {−1, 0, 1, 2, 3, 1.0, 2.0, 3.0}, lengths 0–12.
- **Area M:**
  - hash order over every subset of 0–11 (4,096) and 0–13 (16,384);
  - `(range n)` for n < 64;
  - vector `get` over 27 keys × sizes 0–4.

## 9. Theorems

★ marks a new for-every-input proof. Full lists with axioms: `results/r9-*-axioms.txt`.

- **Coordinator:** ★ `roundtrip_of_no_quote`, ★ `fold_join`, ★ `makeEntry_escape`, ★ `unescape_no_quote`; `u88_echo` and `quote_examples` (`decide +kernel`).
- **Area E:** ★ `fixed_eq_spec`, ★ `fixed_stock_eq`, ★ `fixed_eq_stock_of_not_conv`, ★ `fixed_eq_stock_of_earlier`, ★ `spec_eq_stock_of_none`, ★ `spec_eq_stock_of_not_conv`, ★ `a34_object_sees`, ★ `convErr_observed`, ★ `convStd_observed`, ★ `vb_outcome_a34`, ★ `thrown_a34`, ★ `report_preserved`, ★ `load_module_unwrap`, ★ `v18_star_e`, ★ `v9_data_kept`, ★ `nth_fixed_eq_clj`, ★ `x20_miss`, ★ `nth_stock_std`.
- **Area N:** ★ `fixNeg_boxable` and ★ `fixNeg_nan` (both `bv_decide`), ★ `fixNeg_eq_clj`, ★ `fixNegInteger_eq`, ★ `fixNegSmall_eq`, ★ `stockNegSmall_differs_iff`, ★ `stockNegInteger_differs_iff`, ★ `negDec_scale`, ★ `stockNegDec_scale`, ★ `stockNegDec_eq_iff`, ★ `stockNegDec_value`, ★ `fastAdd_eq`, ★ `fastSub_eq`, ★ `fastMul_eq`, ★ `fastCmp_eq`, ★ `withFast_add`, ★ `withFast_cmp`, ★ `rne_half`, ★ `rne_tie_even`, ★ `rne_nearest`.
- **Area W:** ★ `toUnits_wtf8`, ★ `count_wtf8`, ★ `nth_wtf8`, ★ `nthUnit_eq`, ★ `hash_wtf8`, ★ `hashUnits_eq`, ★ `indexOf_wtf8`, ★ `lastIndexOf_wtf8`, ★ `subs_whole`, ★ `drop_locate`, ★ `tailGen_units`, ★ `subs_tail_units`, ★ `subs_indexOf_startsWith`, ★ `unitsToCps_roundtrip`, ★ `piece_enc`, ★ `locate_end`.
- **Area H:** 37 starred, among them:
  - ★ `addMutF_agree`, ★ `add_congrF`, ★ `sub_congrE`, ★ `buildTF_agree_empty`;
  - ★ `addF_inPlace`, ★ `addMutF_inPlace`, ★ `keys_kept`;
  - ★ `cu_reach`, ★ `add_congrP`, ★ `sub_congrP`, ★ `buildT_agreeP_empty`;
  - plus `h91_stock_contents_differ` (`decide +kernel`).
- **Area Q:** ★ `responseFor_nil_keys`, ★ `responseFor_keeps_keys`, ★ `dropNils_no_nil`, ★ `q2_messages`, ★ `stock_blank_out`, ★ `takeLine_line_clean`, ★ `takeLine_none_iff`, ★ `takeLine_split`, ★ `takeLine_addInput`, ★ `agree_prefix`, ★ `build_wf`, ★ `build_run`, ★ `tree_of_treelike`, ★ `build_height`, ★ `exhaust_of_treelike`, ★ `exhaust_worldT`.
- **Area T:**
  - sorting: ★ `stableSort_ok`, ★ `timSortSmall_ok`, ★ `sorts_agree`, ★ `replica_sort_agree` (and `_lt`, `_compare`, `_gt`), ★ `minus_agree_in_int_range`;
  - laziness: ★ `Lazy.first_map_differs`, ★ `clj_iterate_take`, ★ `jank_iterate_take`;
  - partition-all: ★ `partition_all_agree`, ★ `jank_double_one_partition`;
  - sorted NaN: ★ `jank_lower_bound_nan`, ★ `clj_find_nan`;
  - and the helpers (51 declarations).
- **Area M:** ★ `clj_assoc_present_keeps_keys`, ★ `jank_assoc_at_8_promotes`, ★ `jank_assoc_below_8`, ★ `clj_kwargs_order`, ★ `champ_eq_clj_without_crowding`, ★ `champ_perm_clj`, ★ `vec_get_agree_int`, ★ `vec_get_agree_nonint`, ★ `vec_get_differs_iff`, ★ `str_get_agree_int`, ★ `str_frac_differs`, ★ `getIn_agree`, ★ `getIn_no_lookup`, ★ `contains_differs_iff`, ★ `selectKeys_differs`, ★ `assert_differs`, ★ `demo_differs`, ★ `updateVals_sorted_differs`.

## 10. Model errors corrected

- **Round 8's X20:** the path model skipped seq.cpp's guard (g480–g482).
- **Round 8's DEC8-1 suggestion** `(mul -1 x)`: it wraps in C++ `int`, misses `-'`, and makes D9's crashing NaN.
- **Round 8's V62 note** "the printing would still differ": V62b fixes it.
- **Round 6's** "no public API returns the stored key" (S59, U81): immer's `impl()` does.
- **Round 8's** "for sets, returning the set would do": true for persistent sets only. A transient set's `conj!` on a node it doesn't own still reorders.
- **Round 8's** "the sequence theorem without a lawful equality was not searched": proved with the fix; the stock counterexample is H9-1.
- **Round 3's S59 example (8-entry promotion)** drew only the key. The promotion itself reorders (H9-3 / M9-5).
- **Round 2's sorted-collection model** used one binary search for jank's std::map and Clojure's PersistentTreeMap. With a key that compares 0 with every key, the two land on different entries (T9-10).
- **Round 2's Chunked.lean** compared real ranges only; vectors and integer ranges were never compared (T9-3).
- **Round 1's A10** set aside `get`'s intValue truncation (M9-1).
- **Area Q's own first report** said Q1 and Q2 stack in any order. That was true under `patch`'s fuzz, not under `git apply`.

## 11. Tests

- **The file.** `tests/jank_lean/deviations_r9_test.jank` holds 181 deftests (z1–z70), one assertion each, each with its path and jank's predicted values, stock and with its fix. It was assembled by `.r9-scratch/coord/assemble.py` from the areas' tests; the map is in `.r9-scratch/coord/deviations_r9_test.jank.map`.
- **On Clojure 1.12.3:** 173 of 173 Clojure-runnable tests pass (`results/r9-coord-clj.txt`).
- **Jank only, 8:** z7c (C++ exception types), z26 (bencode) and z33–z38 (the nREPL handler in-process).
- **Controls:** 45, named "control".
- **With the round-9 patch:** what each test should do is in `fixes/combined/CHECK.md` section 5.

## 12. Audit of the area agents

Their tool calls were read from their transcripts for paths and commands outside RULES.txt:
- No web access, no `~/dev` or `~/.claude` reads, no jank history, no jankifier, and no process killed by pattern.
- `git log` was run only in round 8's merge tree (our own commits).
- **One departure.** Area W read Homebrew GCC 15.2's libstdc++ headers (`/opt/homebrew/Cellar/gcc/15.2.0/include/c++/15/bits/regex*`). It diffed them against the pinned 15.3.0 copy in `deps/`, to show its standalone regex harness, built with g++-15, runs the same search code as jank.
  - This is outside RULES' read list.
  - It is a toolchain library, not jank or any report of jank.
  - It is not used as a replica source.
- Areas T and H listed `/opt/homebrew/include` and `/opt/homebrew/bin`. Areas N and W compiled standalone programs with Homebrew's headers and compilers, which RULES allows.

## 13. Left for round 10

- **The build:** this patch per CHECK.md, with immer.diff.
- **No fix yet:**
  - T9-1, T9-3 to T9-8, T9-10 to T9-13;
  - M9-1 to M9-4, M9-6 to M9-11;
  - Q9-1 to Q9-3;
  - E9-1;
  - W9-1;
  - V15;
  - V62b's `double?`.
  - Among these, M9-11 is immer's node layout, and T9-1 and T9-3 are design choices.
- **The nREPL:**
  - T9u and T3u under every schedule need an on-disk store or a proved reduction;
  - the conditions of `tree_of_treelike` on World T.
- **CHAMP:** that jank's `=` is a partial equivalence outside D8 and R55.
- **R72f's** effect on jank itself, and X6's deref cost.

## 14. Files

- **Models:** `Jank/R9/{Nrepl,Champ,Str,Err,Num,Seq,Coll,Coord}/`.
- **Drivers:** `Run/R9/*.lean` (`jank9-<area>`).
- **Results:**
  - `results/r9-*`;
  - the 186 grouped: `results/r9-coord-186.txt`;
  - U88's search: `results/r9-coord-shell.txt`.
- **Tests:** `tests/jank_lean/deviations_r9_test.jank`.
- **Fixes:**
  - `fixes/`: 243 diffs. New: V82, U80, U84, U88, U90, A34, V7a, V9, V18, X20b, W9u, W9h, W9c, W9r, H8-1, H8-1-immer, H9-3, Q1, Q2, V37i, T9-2, T9-9, DEC8-1, V55, V60, V61, V62, V62b, V85.
  - `fixes/combined/`: `all.diff`, `immer.diff`, the group diffs, `README.txt`, `CHECK.md`.
- **Changed outside round 9's own files:** `lakefile.toml` (the jank9 targets), `README.md`, `NOTICE.md`.
- **Scratch: `.r9-scratch/`:**
  - `RULES.txt` and `briefs/`;
  - `coord/`: classify.py, assemble.py, the U84/U88 work, the Clojure run;
  - `merge/`: r9.sh, tree/, the syntax and warning logs, `orig-r8/` with round 8's all.diff, CHECK.md and README.txt;
  - each area's work.
- No commits.

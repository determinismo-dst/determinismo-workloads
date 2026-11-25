# Elle 4e359e5 in Lean 4: round 2

Round 2 extends round 1's replica (`REPORT.md`) to what round 1 left out, and to the HTTP service a test platform runs Elle through:
- rw-register's `:linearizable-keys?`, `:sequential-keys?` and `:transaction-order`, each alone and with `:wfr-keys?`;
- the cycle search's time limit and its fallback, as a decision that cuts the search anywhere;
- every jepsen.history and tesser fold Elle uses, over every chunking and combine order;
- `:not` and `:also-not` for every anomaly set;
- the service (`service/elle_service.clj`, a public platform's checkers/elle at b8f9cc9, Elle 0.2.8);
- three follow-ups to round 1's findings (D3, D10, D13), **prompted by the task**.

Versions and lines:
- Elle main 4e359e597c52938b0afebb8bc42273914d68a424, still main's latest; jepsen.history 0.1.9, jepsen.txn 0.1.3, tesser.core 1.0.10.
- Line numbers are from those sources.
- Lean v4.36.0, determinismo `sdk/lean` at b8f9cc9.

**The new replica was checked against the real programs before being trusted:**
- **rw-register with the options:** 4,900 real-Elle runs gave exactly the replica's verdict and anomaly types (`scratch/d2rr1.*`, `scratch/d2rr2.*`).
  - They cover each option alone, each with `:wfr-keys?`, and all four together.
  - 1,322 were invalid, 541 with `:cyclic-versions`.
- **The service:**
  - 920 runs of the service's own `check` gave exactly the Lean service's `valid`, `anomaly_types` and `not` (`scratch/r2/svc/sd1.*`). They cover all three models, `linearizable_keys`, strict-serializable-per-key, open invocations and duplicated reads.
  - On the 560 without open invocations, duplicates or the per-key model, the service's answer equals real Elle's on the same history.
- **closed-predicate, after round 2's explainer correction (see "not exact"):** 3,000 real-Elle runs equal the replica, 286 of them invalid (`scratch/r2/dcp.*`).

## Disagreements

Key `0` is x, key `1` is y. Unless written out, each operation is preceded by its invocation and transactions run one after another. "Every interpretation" is round 1's: each `:info` transaction committed or aborted, every version order, every value an indeterminate read could have returned.

### D14. `:transaction-order`: an `:info` write between two `:ok` writes hides their write-write edge

History, with transaction order `{3 0, 5 1, 1 2}` (the second write first, then the `:info` one, then the first):

    [{:process 0, :type :invoke, :f :txn, :value [[:w 0 2]]}
     {:process 0, :type :ok, :f :txn, :value [[:w 0 2]]}
     {:process 0, :type :invoke, :f :txn, :value [[:w 0 3]]}
     {:process 0, :type :ok, :f :txn, :value [[:w 0 3]]}
     {:process 1, :type :invoke, :f :txn, :value [[:w 0 1]]}
     {:process 1, :type :info, :f :txn, :value [[:w 0 1]]}]

- **Elle:** `:strict-serializable` valid.
- **Specification:**
  - Under the option's assumption, x's versions follow their writers' places, and every committed transaction has a place.
  - So 3 precedes 2, whether or not the `:info` write 1 committed between them: T1 -ww-> T0.
  - T0 finished before T1 began: G0-realtime in every interpretation.
- **A serializable form (id 3):** T0 (place 0) writes x 1 and reads y 3; an `:info` write of x 2 (place 1); T2 (place 2) writes x 3 and y 3. That is G1c in every interpretation; Elle `:serializable` valid.
- **Property and source:** completeness of a verdict with the option on. rw_register.clj:234-238 says "we assume that each key written in a transaction is assigned the version of its owning transaction", and 925-932 describes the map as "a numeric, total transaction order".
- **Code path:**
  - `key-writes-version-sorted` (rw_register.clj:210-232) keeps `:ok` and `:info` writes, so `transaction-order-graphs` (234-253) links 3 → 1 → 2.
  - `version-graphs->transaction-graph` (704-735) relates the writers of each direct version edge only.
  - `ext-index` (164-182) indexes `:ok` ops only ("TODO: we fail to index external writes of type :info").
  - Both edges touch 1, whose writer is not indexed, so no edge between T1 and T0 remains.
- **Controls (Elle catches each):** the `:info` op made `:ok` (id 1), `:fail` (id 5), or removed (id 2).
- **Also:** an op missing from the map sorts first (Clojure's `compare` puts `nil` before numbers). That is outside the documented "total" precondition.
- **Confirmed:** real Elle, `results/r2/d14.*`. Control id 4 there had a stale index in its map; it shows the missing-op behaviour. Lean: `Theorems2.transaction_order_info_breaks_chain`. Searches: E2-order, 360 of 1,643,624 timelines.

### D15. jepsen.history's pair index depends on chunking (a process invoking twice)

History: `[{:process 0 :type :invoke :value [[:append 0 1]]} {:process 0 :type :invoke :value [[:append 0 2]]} {:process 0 :type :ok :value [[:append 0 2]]}]`.

- **jepsen.history:**
  - In one chunk, it throws `:jepsen.history/double-invoke`.
  - Split between the two invocations, it raises no error. The first invocation is paired with nothing (`-1`, two chunks) or dropped from the index (three chunks).
- **Property and source:** a fold's result doesn't depend on its chunking. jepsen.history's fold.clj:115-150 runs each fold over 16,384-op chunks, combined left to right.
- **Code path:** `pair-index-fold`'s reducer asserts a double invoke only against its own chunk's tail (history.clj:430-440). The combiner merges tails `MERGE_LAST_WRITE_WINS` (history.clj:466-498), so an open invocation from an earlier chunk is overwritten.
- **Scope:** only histories where a process invokes twice (against Jepsen's convention). Every well-formed history gave the same result for every chunking; see Folds below.
- **Confirmed:** `scratch/r2/chunk-pair.clj` on real jepsen.history and Elle, with 16,387- and 16,389-op histories.
  - Inside chunk 0, both throw `double-invoke`.
  - With the two invocations at 16,383 and 16,384, no pair-index error: the first invocation has no completion.
  - Elle then fails differently, with D8's `AssertionError: No transaction wrote 0 = 1`.
- **Lean:** `Theorems2.pair_index_depends_on_chunking`.

### D16. Service: after deduplication, `not` omits what `duplicate-elements` rules out

History: T0 `[[:r 0 []]]`; T1 `[[:append 1 1] [:r 1 [1 1]]]`.
- **Service:**
  - `serializable`: `valid false`, `anomaly_types [duplicate-elements, empty-transaction-graph]`, `not []`.
  - `strict-serializable`: `[duplicate-elements]`, `not []`.
- **The lattice:** `duplicate-elements` is proscribed by PL-1 (consistency_model.clj:418-423), so its friendly boundary's `:not` is `[read-uncommitted]`.
- When the deduplicated history is itself invalid, `not` names only what Elle found, e.g. `[read-committed]` (D17's history), not the weaker read uncommitted.
- **Property and source:** `not` names the weakest models the reported anomalies rule out (consistency_model.clj:588-606).
- **Code path:** `check` (elle_service.clj:221-231) sets `:valid? false` and adds the type, but `:not` (line 234) is still the deduplicated history's boundary, `[]` when Elle found it valid.
- **Also:** the answer is forced invalid even for a model that doesn't prohibit `duplicate-elements` (e.g. PRAM). By reading only.
- **Confirmed:** the real service, `scratch/r2/svc/confirm.*` ids 0-2 and 10. Lean: `Theorems2.dedup_answer_not_empty`.

### D17. Service: deduplication hides G0-realtime

History:

    [{:process 2, :type :invoke, :f :txn, :value [[:append 1 1] [:r 1 nil]]}
     {:process 2, :type :ok, :f :txn, :value [[:append 1 1] [:r 1 [2 1]]]}
     {:process 1, :type :invoke, :f :txn, :value [[:append 0 1] [:append 0 2]]}
     {:process 0, :type :invoke, :f :txn, :value [[:append 1 2] [:r 1 nil]]}
     {:process 0, :type :ok, :f :txn, :value [[:append 1 2] [:r 1 [1 1 2]]]}
     {:process 1, :type :ok, :f :txn, :value [[:append 0 1] [:append 0 2]]}
     {:process 1, :type :invoke, :f :txn, :value [[:r 0 nil]]}
     {:process 1, :type :ok, :f :txn, :value [[:r 0 []]]}]

- **Service (`strict-serializable`):** `[G-single-item-realtime, duplicate-elements, incompatible-order]`, `not [read-committed]`.
- **Elle on the history without the duplicated read:** `[G-single-item-realtime, G0-realtime]`. Process 2 finished before process 0 began, yet read process 0's 2 before its own 1.
- **Property and source:** "deduplication hides nothing beyond the duplicate it reports" (the task).
- How I checked it: a type Elle reports without the duplicated reads must appear in the answer, or be implied by an answered type, or have a more severe answered type stand in for it (README, "something worse").
- **Code path:**
  - `deduplicated` (elle_service.clj:151-157) turns `[1 1 2]` into `[1 2]`, which now competes with `[2 1]` at equal length.
  - `sorted-values` sorts by length (list_append.clj:316), and the version order is the last value (`peek`, list_append.clj:410).
  - Among incompatible reads of equal length, hash order decides (round 1's D12). Here it picks `[1 2]`, and the realtime write cycle disappears.
  - A fix: drop a duplicate-holding read mop rather than deduplicate it.
- **Scope:** the verdict stays invalid (forced by the duplicate); the anomaly types lose G0-realtime. Found in 15 of 30,000 explored histories under that rule.
- **Confirmed:** real service and Elle, `scratch/r2/svc/confirm.*` ids 10-11. Lean: `Theorems2.dedup_hides_g0_realtime`.

### D18. Service: strict-serializable-per-key is stricter than "serializable and each key linearizable"

History (keys 0, 1, 2; a finishes before b begins; c spans both):

    [{:process 2, :type :invoke, :f :txn, :value [[:r 1 nil] [:w 2 1]]}
     {:process 0, :type :invoke, :f :txn, :value [[:r 0 nil] [:r 2 nil]]}
     {:process 0, :type :ok, :f :txn, :value [[:r 0 nil] [:r 2 1]]}
     {:process 1, :type :invoke, :f :txn, :value [[:r 0 nil] [:w 1 1]]}
     {:process 1, :type :ok, :f :txn, :value [[:r 0 nil] [:w 1 1]]}
     {:process 2, :type :ok, :f :txn, :value [[:r 1 1] [:w 2 1]]}]

- **Service:** strict-serializable-per-key `valid false` (G1c-realtime); `serializable` valid.
- **Specification:**
  - Serial order b, c, a explains every read.
  - Each key is linearizable on its own: key 0 is read only; on key 1, b's write precedes c's read; on key 2, c's write precedes a's read. c's linearization points differ per key, which per-key linearizability allows.
  - So reading (a), "serializable and each key linearizable", holds.
  - Reading (b), "real-time order only between operations touching a key in common", has the cycle a -rt(key 0)-> b -wr-> c -wr-> a.
- **Property and source:** the service's stated definition (elle_service.clj:17-20), whose "i.e." equates the two readings.
- **Code path:** `realtime-per-key-graph` (173-199) under `with-redefs` (201-208). Its closure equals real time between operations sharing a key, which is reading (b). The service matched (b) on 40,000 explored histories.
  - Why the readings part: each data edge on a linearizable key forbids the reverse real-time order. That rules out mixed cycles whose data paths between real-time edges have one step. Two-step paths, like b → c → a here, escape that.
- **Confirmed:** the real service, `scratch/r2/svc/confirm.*` ids 20-23, also with `linearizable_keys`. Lean: `Theorems2.per_key_readings_part`.

### D19. Service: per key, a predicate read has no keys

History: init `{0 0, 1 0}`; T1 `[[:w 0 1]]`; T2 `[[:rp [:= 0] {0 0, 1 0}]]` (a stale predicate read: key 0's match changed).

- **Service:**
  - `strict-serializable` (Elle): invalid, G-single-realtime.
  - `strict-serializable-per-key`: valid.
- **Property and source:** the stated definition. The predicate read reads key 0, so real time applies between T1 and T2.
- **Code path:**
  - `keys-of` (elle_service.clj:170-171) is `(into #{} (map second) (:value op))`. For `[:rp pred rows]` the second element is the predicate, so T2's only "key" is `[:= 0]`.
  - For an `:init` op (a map), the second element of each entry is its value, so init's "keys" are its values. By reading only.
- **Confirmed:** the real service, `scratch/r2/svc/confirm2.*` ids 40-41 and 45-46. Lean: `Theorems2.per_key_predicate_reads`.

### D20. closed-predicate: an item anti-dependency in a cycle with a predicate one is not G2-item

History (T1 and T2 concurrent):

    init {1 1, 2 0}
    T1 [[:r 2 0] [:w 1 3]]
    T2 [[:rp [:= 1] {1 1}] [:delete 2]]

- **Elle:** `:repeatable-read` valid. `:serializable` reports G2 with steps `[[:rwp 1 1 3] [:rw 2 0 :elle/dead]]`.
- **Specification:** T1 -rw-> T2 is an item anti-dependency: T1 read key 2 = 0, and T2 installed `:elle/dead`. With T2 -rwp-> T1, that is G2-item.
  - Adya's G2-item is a cycle with one or more item anti-dependency edges (thesis §3.2.4; ICDE 2000 §4.4), which PL-2.99 proscribes.
  - Elle's lattice has repeatable read prohibit G2-item (consistency_model.clj:479-481).
- **Code path:**
  - The cycle explainer names any cycle with a predicate edge G2 (txn.clj:496-521).
  - The G2-item search projects out `rwp` (txn.clj:543-608), so it can't find this cycle.
  - consistency_model.clj:122-127 notes the like problem for G-single.
- **Control (id 2):** `[:r 1 1]` in place of the predicate read: G2-item, repeatable read invalid.
- **Confirmed:** real Elle, `scratch/r2/cp-new.*` ids 0-2. Lean: `Theorems2.mixed_cycle_not_g2_item`. Searches: 543 of 30,000 closed-predicate histories, in every fix variant.

### D21. closed-predicate: a predicate read's rows are no item reads

History: init `{0 0, 1 0}`; T1 `[[:w 0 1]]`; T2 `[[:rp :true {0 0, 1 0}]]`.
- **Elle:** `:strict-serializable` valid.
- **Specification:** with the rows as item reads, T2 read key 0 = 0 after T1 installed 1, so T2 -rw-> T1 -rt-> T2: G-single-realtime.
- **Control (id 4):** add `[:r 0 0]` to T2: G-single-item-realtime.
- **Property and source:** the namespace docstring (closed_predicate.clj:6-9): the versions a predicate read covers "also appears as a non-predicate read or write in the history: these are *item* dependencies".
- **Code path:** `rw-graph` (closed_predicate.clj:486-542) gives a predicate read only `rwp` edges to versions that change its match (`xor`). Under `:true` no write changes it, and the rows yield no item edge.
- **Confirmed:** real Elle, `scratch/r2/cp-new.*` ids 3-4, and through the service (id 31). Lean: `Theorems2.predicate_rows_not_items`.

### D22. closed-predicate: an `:info` operation's unknown read is explained as a read

History:

    [{:process 0, :type :invoke, :f :init, :value {1 0, 2 0}}
     {:process 0, :type :ok, :f :init, :value {1 0, 2 0}}
     {:process 3, :type :invoke, :f :txn, :value [[:insert 0 2] [:w 1 3] [:r 2 nil]]}
     {:process 3, :type :info, :f :txn, :value [[:insert 0 2] [:w 1 3] [:r 2 nil]]}
     {:process 5, :type :invoke, :f :txn, :value [[:rp [:= 0] nil] [:r 0 nil] [:delete 2]]}
     {:process 5, :type :ok, :f :txn, :value [[:rp [:= 0] {}] [:r 0 nil] [:delete 2]]}]

- **Elle:** `:consistent-view` valid, as written and with D9's and D10's fixes. Without T3's `[:r 2 nil]`: G-single-item.
- **Specification (the checker's own reading):** T3 -wrp-> T5 (T5's version set holds T3's 3), and T5 -rw-> T3 (T5 read key 0 unborn; T3 installed 2): G-single.
- **Code path:**
  - The WR explainer's item path (closed_predicate.clj:545-562) reads `b`'s `:r` mops whatever `b`'s type. An `:info` op holds its invocation's `nil`, which `resolve-version` (300-318) turns into `:elle/dead`, the value T5 wrote.
  - So T5 → T3 is explained as `wr`, and the cycle classifies as G1c.
  - The G-single search drops it on type (txn.clj:790-795), and G1c's projection has no edge T5 → T3.
- **Confirmed:** real Elle, `scratch/r2/cp-info.*`. Lean: `Theorems2.info_read_explained_as_read`.

### Closing changes the anomaly types (no verdict change)

- An open invocation closed at the end gives different anomaly types from `:info` in place. Example: `[G-single-item, G-single-item-realtime, internal, strong-PL-2-cycle-exists]` against `[G-single-item, G1c-realtime, internal]`.
- Cause: the op's index moves, and round 1's C3 search-order effect follows.
- Found in 6 of 20,000 explored histories, never with a verdict change.
- Real service: `scratch/r2/svc/confirm3.*`.

## The three follow-ups (prompted)

Patches are on the classpath ahead of Elle's source: `scratch/r2/fix-d10/elle/closed_predicate.clj`, `scratch/r2/fix-d3/elle/{core,txn}.clj`, `scratch/r2/fix-d13/elle/rw_register.clj`. In the replica, the same fixes are switches (`fixedVersionLt`, `Opts.fixD3`, `Opts.fixD13`).

Elle's test suite ran from `scratch/r2/suite-*`:
- the default selector (project.clj:35, no `:perf`), on JDK 25, since jepsen.history.sim 0.1.5 needs it;
- `histories/` linked, as the tests expect.

As written: 103 tests, 102 pass. `checker-test` errors in this environment (it can't create `test-output/incompatible-order/:x.html`) in every run alike, so its later assertions run in none.

### D10: graph and explainer

- **Fix:**
  - `versions-after`'s paren (round 1);
  - `version<`: `:elle/unborn` precedes every version ("Every version follows :elle/unborn", 266), and the answer is false when `b` never follows `a`. This is also D11's fix.
- **Against the specification** (`CPSpec`: the DSG from Adya's definitions under the checker's own version order and version sets), 30,000 histories with predicate-read misses:
  - as written: misses consistent view 3,897, strict serializable 1,275, repeatable read 543, serializable 30;
  - paren only: Explainer exception on 4,944 histories;
  - complete fix: no exception, no false explanation, no false positive; remaining misses are D20 (543) and the D9 and D22 kind;
  - plus D9's `:w` fix: repeatable read 543 (D20) and consistent view 4 (D22).
- **Real Elle:**
  - Round 1's D10 history: G-single, explained `[:rwp 0 :elle/unborn 0] [:ww 1 0 :elle/dead] [:wr 1 :elle/dead nil]`.
  - The failure-to-observe history: G-single-realtime and predicate-read-miss, `[:rwp 5 :elle/unborn 3] [:realtime]`, no exception.
- **Suite:** all as baseline, except `failure-to-observe-test`, which now fails its equality. Its expected map encodes the missing edge: the read sees key 5 unborn after init completed, which `version-set`'s comment says "will manifest as explicable cycles" (393-403). The expected value needs G-single-realtime and its `:not`.
- **Lean:** `Theorems2.d10_fix_complete`.

### D3: the process order reaches `:info`, for models prohibiting G1a

- **Fix:**
  - `process-graph-with-info` links a process's last `:ok` op to its `:info` op, never out of it.
  - `realtime-graph-without-info` drops real-time edges into `:info` completions.
  - `additional-graphs` picks by whether the models prohibit G1a.
- **Why this is safe:**
  - In Elle, every edge out of an `:info` op comes from an `:ok` read that saw its write. In list-append that is wr, and ww from a read's order; in rw-register with D13's fix, wr, and ww only when observed.
  - In the interpretation where the `:info` op aborted, that read is an aborted read. So models prohibiting G1a are violated either way.
  - For the read-uncommitted family, such a cycle vanishes in that interpretation, so those edges are never needed and can only bring D5's false positives.
- **Against the specification, over every interpretation:**
  - list-append, 1 key, `:fail` and `:info` (round 1's E2 bounds): 700,000 exhaustive histories. No new false positive, no regression, no exception; 5,494 dropped false positives (round 1's D5 real-time instance).
  - 60,000 explored: the same, 336 dropped.
  - Strong session read committed's D3 misses: 170 to 0 in 20,000.
  - Remaining misses predate the fix (D4, D5 without process edges, D1).
- **Real Elle:**
  - D3's histories now G1c-process and G0-process.
  - The `[2 1]` history stays valid for strong session and strong read uncommitted; the latter was a false positive before.
- **Suite:** as baseline.
- **Lean:** `Theorems2.d3_fix`.

### D13: rw-register indexes `:info` writes

- **Fix:**
  - The write index holds `:ok` and `:info` ops: wr edges out of an `:info` op, ww and rw edges into it.
  - ww out of an `:info` writer only when an `:ok` read saw one of its writes and the models prohibit G1a. `ww+rw-graph` receives the options (rw_register.clj:903).
  - A version written only by `:info` ops is stepped over: its predecessors linked to its successors. This fixes D14 too.
- **Against the specification:**
  - 202,584 complete exhaustive histories (2 keys, `:fail` and `:info`).
  - 60,000 explored with a transaction order.
  - No new false positive, no regression, no exception. Remaining misses: the blind-write ordering limit, and an artifact of my assumption (an `:info` op absent from the order must have aborted, which Elle doesn't infer).
  - My first version (no ww out of any `:info` writer) missed a G0-realtime through an observed `:info` write; the refined version catches it.
- **Real Elle:**
  - D13's history: G1c-realtime.
  - D14's: G0-realtime and G1c.
  - An unread `:info` write between finished writes stays valid. A naive fix would report G0-realtime.
  - An observed one: strict serializable invalid, strong read uncommitted valid.
- **Suite:** as baseline; all three patches together, only `failure-to-observe-test` changes.
- **Lean:** `Theorems2.d13_fix`, `Theorems2.d13_fix_observed`.

## What was replicated, and what is not exact

Replicated, each function cited by line in the Lean source:
- rw-register's version sources and their order (`RwRegister.sources`, rw_register.clj:647-702). That covers `key-writes-version-sorted` with Clojure's `nil`-first stable sort, `ext-keys`, `ext-key-graph` as written (stack, shadowing, condensation), the version-graph fold, and `:cyclic-versions` with its sources.
- `util/timeout` around `cycle-cases-in-scc` (txn.clj:839-893):
  - a cut at every point, with types and cycles pushed;
  - the fallback (both branches take `g/fallback-cycle` of the whole SCC, round 1's C7);
  - explainer and classification exceptions as Elle throws them (round 1 skipped them silently).
- Each fold's reducer and combiner (`Folds`): pair index, failed and intermediate writes, process order, sorted values, tesser's ordered `into`, the version-graph fold.
- The boundary (`Boundary`).
- The service's `closed`, `duplicates`, `deduplicated`, `keys-of`, `realtime-per-key-graph`, `judged` and `check` (`Service`).
- The follow-up fixes (`Opts.fixD3`, `Opts.fixD13`, `fixedVersionLt`).
- `CPSpec`, a closed-predicate specification under the checker's reading.

Not exact:
- **Iteration orders:** `ext-key-graph`'s Bifurcan orders, and `g/fallback-cycle`'s successor order (Clojure's hash set of Op records), are the `Order` abstraction. Results don't depend on them, or any order yields a real cycle.
- **`util/timeout`'s race:** the worker running after `future-cancel`, and the two atoms read at different instants, are modelled only as cut points.
- **Folds:**
  - The data is abstract (sets as lists), so Bifurcan collision-order effects aren't modelled.
  - Chunkings are capped at 512 per history.
  - tesser.core's combine orders are sampled, 24 per chunking.
- **Service:** JSON parsing (checked end to end instead), HTTP, locks, the anomalies text and `window_ns` are not replicated.
- **closed-predicate:** round 1's replica gave version sets to `:info` ops' predicate reads. Elle's `version-sets` cache (413) holds `:ok` ones only. Corrected in round 2, after 3 false explanations surfaced against `CPSpec`; then 3,000 real-Elle runs agreed.

## Assumptions

- **Round 1's:** Jepsen conventions, interpretations, models as defined, cycle claims may be met by worse cycles.
- **The options' assumptions (`SpecOpts`):**
  - `:linearizable-keys?`: per key, the transactions touching it have a total order consistent with real time (an `:ok` op completed before the other was invoked), each read returning the latest write. With the version order fixed, that is acyclicity of the key's constraint graph. An unclean interpretation breaks it.
  - `:sequential-keys?`: the same with each process's order.
  - `:transaction-order`: every committed transaction has a place, and each key's installed versions follow their writers' places.
  - `:wfr-keys?`: an `:ok` transaction's external read of a key precedes its external write.
- **Verdicts with options:** "invalid" claims no interpretation satisfies the model and the assumption. Completeness is judged three ways: against every interpretation; against the assumption's interpretations; and where the option's order alone fixes each key's versions.
- **strict-serializable-per-key:** the two readings, (a) and (b), as written in D18.
- **Deduplication:** a type is hidden unless the answer reports it, or an implied type, or a more severe stand-in.
- **closed-predicate (`CPSpec`):**
  - Elle's version order, `:ok` and `:info` writes committed, version sets as `version-set` infers them;
  - Adya's item and predicate edges, unborn before every version;
  - repeatable read proscribes G2-item, while G-single and G2 count either kind of anti-dependency;
  - rows count as item reads only for D21's check.

## Properties with sources

42 kinds, 120 counting each model.

**Options (rw-register):**
- **Each source's inference is sound under its assumption** (5 sources): held. Never broke in any run. Sources: rw_register.clj:464-478, 234-238, 255-258, 925-951.
- **No false positive with an option on** (14 models): held.
- **Completeness:**
  - against every interpretation (14): broke only on round 1's documented register limits and D6/D13 (masked);
  - where the option's order fixes the versions (14): held;
  - under the assumption (14): broke on D14 and on what the options never infer.
- **`:cyclic-versions` claims the assumptions can't all hold** (rw_register.clj:937-940): held.
- **No exception on well-formed histories:** held.

What the options never infer:
- Under per-key atomicity, a transaction's read and write of a key are adjacent versions; under `:linearizable-keys?` or `:sequential-keys?` alone, its read precedes its write. Elle leaves that to `:wfr-keys?` (rw_register.clj:549-556).
- `:wfr-keys?` skips `nil` reads (268), so read-`nil`-then-write gives rw where ww holds (round 1's D1, register form).

**Time limit** (txn.clj:650-674, 725-893):
- never `:valid? true`: held, also proved (`timeout_never_valid`);
- a cut never turns a satisfiable verdict invalid: held;
- no exception appears or vanishes at a cut: held.
- Facts:
  - `elle.core/check` has no time limit (core.clj:519-603).
  - A cut turned `false` into `:unknown` in 14 of 18,780 cuts.

**Folds** (jepsen.history fold.clj:115-150; tesser core.clj:275-315):
- pair-index chunking: broke on malformed histories only (D15);
- failed-write-indices, intermediate-write-indices, process order, sorted values, the version-graph fold (any chunking and combine order), and `merge-with merge` associativity: held.

**`:not`/`:also-not`** (consistency_model.clj:568-606), four definitions on all 371 unions:
- impossible equals the models prohibiting an anomaly;
- `:not` is the minimal elements;
- `:also-not` is the rest, each implying a `:not` model;
- friendly names neither merge nor overlap.
- All held (`boundary_definitions`).
- Note: the boundary covers every anomaly found, reported or not (txn.clj:1028).

**Service** (elle_service.clj):
- equals Elle on what it was meant to send: held (560 runs);
- per-key reading (b): held;
- per-key reading (a): broke (D18);
- per-key never stricter than Elle's strict serializable: held;
- predicate reads per key: broke (D19);
- closing, verdict: held;
- closing, types: broke (no verdict change);
- dedup `not`: broke (D16);
- dedup hides: broke (D17).

**Follow-ups:** no new false positive, no regression, no exception: held for all three fixes.

**closed-predicate** (`CPSpec`; Adya; closed_predicate.clj docstrings):
- no exception: broke for the paren fix alone; held for the complete fix;
- explanations true: held for the complete fix (D11 fixed);
- soundness (14): held in every variant;
- completeness (14): broke (D10 and D9 as written, D20, D22).

## Search runs

Differential against the real programs:
- rw-register options: 4,900.
- Service: 920, and 560 against Elle.
- closed-predicate: 3,000.
- Suites: as written, each patch, all three together.
- Confirmation cases: `results/r2/d14.*`, `scratch/r2/followups.*`, `cp-new.*`, `cp-info.*`, `chunk-pair.clj`, `svc/confirm*.*`.

Exhaustive, complete (every timeline within the bounds; rw-register 3 transactions, 1 micro-op, 2 keys, 2 threads, any reads, `:fail` and `:info`):
- E2-lin: 202,584; nothing broke.
- E2-seq: 202,584; only the blind-write limit.
- E2-order: 1,643,624; only D14 (360).
- F-d13-rr and G-d13-rr: 202,584 each; no fix property broke.

Exhaustive, partial (depth-first prefixes):
- E-lin, E-lin-wfr, E-seq, E-seq-wfr, E-order, E-order-wfr, E-order-noinfo: 1,000,000 each, with 2 micro-ops.
- F-d3-la: 476,000; F-d3-la-split: 700,000 (of 1,152,552).
- G-d13-order-e: 518,500 of 1,643,624 at its time limit, past timeline 170,503 where Elle as written first missed D14; the only property broken is the assumption artifact (`completeness-assumed:read-committed`, 39,848 timelines: an `:info` op absent from the order is taken as aborted, which Elle doesn't infer); no `fix:` property broke.

Explored:
- Options: 3,000 unmasked, then 20,000 each with D6/D13 masked.
- Time limit: 3,000 and 3,000, plus statistics: 1,810 and 1,320 SCC searches; 18,780 and 14,946 cuts.
- Folds: 2,000, 2,000 malformed, 3,000, 3,000.
- Service properties: 3,000; 20,000 and 20,000 per key; 30,000 deduplication.
- D3: 20,000 ×2 and 60,000 ×2.
- D13 with an order: 60,000 ×3.
- closed-predicate: 40,000 ×4, and 30,000 ×4 with misses.

Each run's shrunk counterexamples, with tapes and EDN, are in `results/r2/NAME.txt` and `.cases.edn`; the explorations' are in `scratch/r2/`.

## Theorems

All in `Elle/Theorems2.lean`; it builds, and so do round 1's theorems on the changed code.

Proved by hand:
- `mem_foldl_dedup`, `mem_dedup`;
- `timeout_reportable` (`:cycle-search-timeout` is reportable for any options);
- `timeout_never_valid`: any options, any anomaly map holding a timeout case, any boundary flag, `result-map` is not `:valid? true`.

By `native_decide`:
- `timeout_not_cycle_exists`;
- `boundary_definitions`: 371 unions, none failing;
- one per disagreement: `transaction_order_info_breaks_chain` (D14, and its fix), `pair_index_depends_on_chunking` (D15), `dedup_answer_not_empty` (D16), `dedup_hides_g0_realtime` (D17), `per_key_readings_part` (D18), `per_key_predicate_reads` (D19), `mixed_cycle_not_g2_item` (D20), `predicate_rows_not_items` (D21), `info_read_explained_as_read` (D22);
- the follow-ups: `d10_fix_complete`, `d3_fix`, `d13_fix`, `d13_fix_observed`.

Not proved: soundness of the inferences, or the folds' chunking independence, in general.

## Library gaps

Built here because determinismo's `sdk/lean` (b8f9cc9) lacks them, beyond round 1's list:
- **Property reporting:** a timeline reports only its first broken property. A fix's regression could hide under an earlier `completeness:` name, so I needed skip lists and reruns. Informational counts (dropped false positives) have to pass as violations.
- **Decisions and enumeration:** no decision for chunkings or for cut points; no permutation or composition enumeration.
- **Parsing and output:** no JSON; no EDN reader.
- **Search control:** exhaustive search has no prefix sizing or progress estimate; a depth-first prefix of a large space is a narrow corner of it.
- **Lake:** two executables can't share a root module. Rebuilding one while a batch runs it needed a second root (`Main2`, `Main3`).

## Reproducing

    lake build Elle elle-r3
    .lake/build/bin/elle-r3 diff2 rr seeds=40 txns=4 mops=3 keys=2 threads=3 read=cuts out=scratch/d2rr1 && runner/elle.sh scratch/d2rr1.cases.edn scratch/d2rr1.elle.edn && python3 runner/compare.py scratch/d2rr1.replica.edn scratch/d2rr1.elle.edn
    .lake/build/bin/elle-r3 exhaust2 rr order=1 txns=3 mops=1 keys=2 threads=2 read=any runs=1000000000 noinforeads=1 out=results/r2/E2-order
    .lake/build/bin/elle-r3 svcdiff x seeds=40 out=scratch/r2/svc/sd1 && (cd scratch/r2/svc && clojure -M svcrun.clj sd1.cases.edn sd1.out.edn) && python3 runner/svccompare.py scratch/r2/svc/sd1.out.edn scratch/r2/svc/sd1.replica.edn
    .lake/build/bin/elle-r3 cpfix x va=1 vlt=1 w=1 misses=1 seeds=30000
    scratch/r2/elle-cp.sh scratch/r2/followups.cases.edn OUT.edn fix-d10 fix-d3 fix-d13
    scratch/r2/suite.sh all fix-d10 fix-d3 fix-d13

# Elle 4e359e5 in Lean 4: round 1

Elle (jepsen-io/elle, commit 4e359e597c52938b0afebb8bc42273914d68a424, "Version 0.2.9-SNAPSHOT", one commit after v0.2.8) is replicated in Lean 4 function by function:
- the history handling and the process and real-time orders;
- list-append, rw-register (initial-state and `:wfr-keys?` version graphs), closed-predicate, and `elle.core`'s monotonic-key checker;
- the graph machinery: Bifurcan's Tarjan as written, the BFS cycle search, the explainers;
- the anomaly classification and the consistency-model lattice.

An independent specification, written from Adya's and the Elle paper's definitions, enumerates every interpretation of small histories. Searches over histories built from determinismo decisions (`explore`, `exhaust`, `shrink`) compare the two.

**The replica was checked against real Elle before being trusted.** 18,790 real-Elle runs on random histories, with every model, gave exactly the replica's verdict and anomaly types:
- list-append: 3,400 runs with orderly reads, and 2,550 with any reads, garbage included;
- rw-register: 2,550 runs, and 2,040 with `:wfr-keys?`;
- closed-predicate: 2,250 runs;
- monotonic-key: 6,000 runs.

That agreement needed Elle's hash-iteration orders, which the replica computes and which were checked against Clojure itself: Clojure's `Murmur3/hashLong` and `hashOrdered`, Bifurcan's CHAMP order of ops, and Clojure's HAMT order of read vectors.

Every disagreement was then run through real Elle:
- `results/cases.elle.edn` has 31 runs; ids are cited below.
- `results/cases.txt` puts each case's replica, specification and real-Elle verdicts side by side.
- `results/closed-predicate*.edn` has the closed-predicate runs, as written and patched.

## Disagreements

Verdicts are for `check` with `{:consistency-models [M]}`. "Every interpretation" means every Adya history compatible with the observation (paper §4.2.2): each `:info` transaction committed or aborted, every version order, every value an indeterminate read could have returned. Key `0` is x and key `1` is y. Unless written out, each op below is preceded by its invocation, the transactions run one after another, and the full EDN is in `results/cases.cases.edn` under the cited id.

### D1. An unread append becomes an anti-dependency: G-single is reported as G2-item

History (concurrent):

    [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil] [:append 1 1]]}
     {:process 1, :type :invoke, :f :txn, :value [[:r 1 nil] [:append 1 2] [:append 0 1]]}
     {:process 0, :type :ok, :f :txn, :value [[:r 0 []] [:append 1 1]]}
     {:process 1, :type :ok, :f :txn, :value [[:r 1 []] [:append 1 2] [:append 0 1]]}]

- **Elle (ids 0-2):** `:snapshot-isolation` valid; `:consistent-view` valid; `:repeatable-read` invalid with G2-item, cycle `[3 2 3]`, steps `[:rw :rw]`.
- **Specification:** both orders of y's appends are clean interpretations.
  - With T0 << T1: T0 -ww-> T1 and T1 -rw-> T0.
  - With T1 << T0: T1 -ww-> T0 and T0 -rw-> T1 (T0 read x's initial version; T1 installed x's first).
  - Both have a cycle with exactly one anti-dependency (G-single), so PL-2+ and PL-SI are violated in every interpretation.
  - Elle's G2-item cycle exists only in the first order.
- **Property and source:** completeness of the consistent-view and snapshot-isolation verdicts. Adya's PL-2+ proscribes G1 and G-single. Cerone and Gotsman 2016, Theorem 10, define SI as acyclicity of `(WR ∪ WW) ; RW?`. Elle's own lattice says consistent view and SI prohibit G-single (consistency_model.clj:422, 449-467).
- **Code path:**
  - `values-from-single-appends` (list_append.clj:247-269) gives y no order, because it has two appends.
  - `previously-appended-element` (list_append.clj:517-535) places an append of unknown position after the last read element; here that is `::init`.
  - `rw-mop-deps` (list_append.clj:550-561) then gives every reader of `[]` an rw edge to both appends.
  - `ww-mop-dep` (list_append.clj:537-548) gives no edge between them.
  - The edge T1 -rw-> T0 stands for T1 -ww-> T0 when T1's own append installed y's first version.
  - The explainer (txn.clj:477-536) sees adjacent `[:rw :rw]` and says G2-item. PL-SI's cycle-exists check (txn.clj:319-321) has no ww or wr edges to extend.
- **Scope:** the docs (list_append.clj:789-791, paper §3) say unread appends can't be ordered, and the paper's inferred graph (§4.3.2) uses only the read prefix. Here Elle goes past that prefix, reports a cycle, and labels it with a weaker class than every interpretation has.
- **Also:**
  - Strong session SI misses through the same mechanism (`results/la-det.txt`).
  - rw-register's form uses the "`nil` before every value" rule (rw_register.clj:184-208, 704-735): case `register-initial-state-g-single`, ids 22-23. SI and consistent view are valid there; the specification says violated.
- **Confirmed by running Elle:** yes. Lean: `Theorems.unobserved_appends` and `Theorems.register_initial_state_g_single`.

### D2. Two models together drop the process order

History (one process appends, then doesn't see its own write):

    [{:process 0, :type :invoke, :f :txn, :value [[:append 0 1]]}
     {:process 0, :type :ok, :f :txn, :value [[:append 0 1]]}
     {:process 0, :type :invoke, :f :txn, :value [[:r 0 nil]]}
     {:process 0, :type :ok, :f :txn, :value [[:r 0 []]]}]

- **Elle (ids 6-9):** `[:strong-session-snapshot-isolation]` invalid with G-single-item-process; `[:strong-session-snapshot-isolation :strong-read-uncommitted]` valid. Same for `:strong-session-serializable` alone (invalid) and with `:strong-read-uncommitted` (valid).
- **Specification:** strong session SI and strong session serializable are violated (T1 -rw-> T0 and the session edge T0 -> T1).
- **Property:** monotonicity in the models asked for. Source: txn.clj:656-668 makes the prohibited anomalies a union over the models.
- **Code path:**
  - `additional-graphs` (txn.clj:676-698) adds only `realtime-graph` once any realtime anomaly is reportable ("No need to bother with process, cuz we'll find those too").
  - The cycle becomes G-single-item-realtime, which strong session SI doesn't prohibit.
  - The `strong-session-*-cycle-exists` subgraphs (txn.clj:330-337) need process edges that are now absent.
- **Confirmed by running Elle:** yes. Lean: `Theorems.realtime_model_hides_process_anomaly` and `Theorems.realtime_replaces_process`. Every explore run broke this property.

### D3. The process order skips `:info` transactions

History, two transactions (from the exhaustive search):

    [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil]]}
     {:process 0, :type :ok, :f :txn, :value [[:r 0 [1]]]}
     {:process 0, :type :invoke, :f :txn, :value [[:append 0 1]]}
     {:process 0, :type :info, :f :txn, :value [[:append 0 1]]}]

- **Elle:**
  - id 27: `:strong-session-read-committed` valid.
  - id 28: `:strong-read-committed` invalid with G1c-realtime.
  - Case `process-order-skips-info`, id 4: `:strong-session-serializable` valid on a G0-process.
- **Specification:** if T1 committed, T1 -wr-> T0 and the session edge T0 -> T1 make G1c-process. If it aborted, T0's read is G1a. Violated in every interpretation.
- **Property and source:** completeness of the strong session verdicts. Daudjee and Salem define session order; the paper's §5.1 says "if process P1 performs T1 then T2, we can infer T1 <p T2".
- **Code path:** `process-graph` links only `:ok` ops (core.clj:301). `realtime-graph` does link `:info` completions (core.clj:412-415).
- **Confirmed by running Elle:** yes. Lean: `Theorems.process_skips_info_2txn` and `Theorems.process_order_skips_info`.

### D4. A failed append inside a read hides the write-write edge: read uncommitted passes a G0

History (id 10):
- W (ok): `[[:append 0 1] [:append 1 2]]`
- F (fail): `[[:append 0 2]]`
- U (ok): `[[:append 0 3] [:append 1 1]]`
- Reads (ok): `[[:r 0 [1 2 3]]]` and `[[:r 1 [1 2]]]`

Facts:
- **Elle:** `:read-uncommitted` valid. It reports G1a and a dirty update, both of which read uncommitted allows.
- **Specification:** installed versions form a prefix chain (paper §4.1.3). W's `[1]` comes before U's `[1 2 3]`, which is built on F's aborted version (a dirty update), so W -ww-> U. Key y gives U -ww-> W. G0 in every interpretation.
- **Property and source:** completeness of read uncommitted, strong session read uncommitted and strong read uncommitted (also `results/la-fail.txt` and the exhaustive E2 runs). Adya's PL-1 proscribes G0, and Elle's lattice allows G1a and dirty updates under read uncommitted (consistency_model.clj:434-443).
- **Code path:** the write index is built over `h/possible` (list_append.clj:603-611), which has no failed ops. `ww-mop-dep` (list_append.clj:537-548) asks who wrote the element just before U's, gets F's (absent from the index), and adds no edge, instead of reaching the last committed writer.
- **Scope:** the paper's soundness argument covers clean interpretations only. This verdict is about the model that allows exactly the unclean ones.
- **Confirmed by running Elle:** yes. Lean: `Theorems.failed_append_hides_ww`.

### D5. A writer that may have aborted: Elle rejects read uncommitted (a false positive)

History, two transactions (from the exhaustive search):

    [{:process 0, :type :invoke, :f :txn, :value [[:append 0 1] [:r 0 nil]]}
     {:process 0, :type :ok, :f :txn, :value [[:append 0 1] [:r 0 [2 1]]]}
     {:process 0, :type :invoke, :f :txn, :value [[:append 0 2] [:append 0 3]]}
     {:process 0, :type :info, :f :txn, :value [[:append 0 2] [:append 0 3]]}]

- **Elle:**
  - id 26: `:read-uncommitted` invalid with G0, cycle `[1 3 1]`, steps `[:ww :ww]`: T1 -ww-> T0 because 2 comes before 1, and T0 -ww-> T1 because T1's unread 3 comes after 1.
  - Case `info-write-may-have-aborted`, id 11: the same false positive with four transactions.
  - id 5: `:strong-read-uncommitted` on D3's four-op history.
- **Specification:** T1 can't have committed, because its version `[2 3]` and T0's `[2 1]` don't lie on one trace. With T1 aborted, T0 built on T1's aborted version (a dirty update) and there is no G0. Read uncommitted is satisfiable.
- **Property and source:** soundness of the read-uncommitted verdict. Adya's PL-1 allows G1a; the paper (§4.2.2) says an indeterminate transaction "may either commit or abort"; Elle's lattice has dirty update imply only G1a (consistency_model.clj:154).
- **Code path:** list-append builds ww/wr/rw edges over `h/possible` (list_append.clj:603), treating `:info` writes as committed. The paper's Theorem 1 claims cycles only for clean interpretations, but `result-map` (txn.clj:1003-1028) still turns the G0 into "not read uncommitted".
- **Confirmed by running Elle:** yes. Lean: `Theorems.info_may_have_aborted_2txn` and `Theorems.info_write_may_have_aborted`.

### D6. rw-register: a fuzzy read passes repeatable read; a G1c through a second read passes read committed

Fuzzy read (ids 13-15): writes x=1 and x=2, then T = `[[:r 0 1] [:r 0 2]]`.
- **Elle:** `:repeatable-read` and `:consistent-view` valid; `:snapshot-isolation` invalid only through `:internal`.
- **Specification:** both version orders give G-single, so PL-2.99 and PL-2+ are violated in every interpretation. This is the canonical non-repeatable read (Berenson et al.'s P2).
- **Code path:**
  - The anomaly is reported only as `:internal` (rw_register.clj:77-101), and repeatable read doesn't prohibit `:internal` (consistency_model.clj:479-481).
  - The graph uses `ext-reads` (rw_register.clj:718, 839), which keeps only each key's first read.

Second read (id 16):

    [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil] [:w 1 1]]}
     {:process 1, :type :invoke, :f :txn, :value [[:r 1 nil] [:r 1 nil] [:w 0 2]]}
     {:process 0, :type :ok, :f :txn, :value [[:r 0 2] [:w 1 1]]}
     {:process 1, :type :ok, :f :txn, :value [[:r 1 nil] [:r 1 1] [:w 0 2]]}]

- **Elle:** `:read-committed` valid.
- **Specification:** read-dependencies both ways (unique writes), so G1c in every interpretation.
- **Code path:** `wr-graph` (rw_register.clj:833-877) indexes `txn/ext-reads` (jepsen.txn 0.1.3, txn.clj:51-64). The namespace docstring's first rule (rw_register.clj:14) covers every read.
- **Scope check:** with each key read at most once per transaction (8,000 explored histories), read committed never broke again. The remaining register misses need an order between two written values, which rw-register documents it can't infer.
- **Confirmed by running Elle:** yes. Lean: `Theorems.register_fuzzy_read` and `Theorems.register_second_read_g1c`.

### D7. rw-register misses a transaction reading its own later write

History: `[[:r 0 1] [:w 0 1]]`, one ok transaction (ids 18-19).
- **Elle:** strict serializable and serializable valid.
- **Specification:** no interpretation; the paper's event order forbids reading from the future (§4.1.3). list-append reports this as `:future-read`, which implies G1c (consistency_model.clj:142-147: "a trivial cycle in which T1 -wr-> T1").
- **Code path:** `wr-graph` adds a self-loop (rw_register.clj:859), and `strongly-connected-components` drops singleton components (graph.clj:376).
- **Confirmed by running Elle:** yes. Lean: `Theorems.register_future_read`.

### D8. list-append crashes on a garbage read

History: one ok transaction `[[:r 0 [7]]]` (id 30).
- **Elle:** throws `AssertionError: Assert failed: No transaction wrote 0 = 7`. It threw the same in 1,581 of 2,550 random real-Elle runs with garbage reads.
- **Specification:** no interpretation. The README and the paper (§6.1) list garbage reads as an anomaly Elle reports.
- **Code path:** `dirty-update-cases` asserts that every element was written (list_append.clj:450-451).
- **Confirmed by running Elle:** yes. Lean: `Theorems.garbage_read_throws`.

### D9. closed-predicate: `[:w k v]` writes get no write-write edges

History:

    [{:process 0 :type :invoke :f :init :value {0 0, 1 0}}
     {:process 0 :type :ok :f :init :value {0 0, 1 0}}
     {:process 1 :type :invoke :f :txn :value [[:w 1 1]]}
     {:process 1 :type :ok :f :txn :value [[:w 1 1]]}
     {:process 2 :type :invoke :f :txn :value [[:r 1 nil] [:r 0 nil]]}
     {:process 2 :type :ok :f :txn :value [[:r 1 1] [:r 0 nil]]}]

- **Elle:** `:serializable` and `:snapshot-isolation` valid (`results/closed-predicate.elle.edn`). With the keyword fixed in a scratch copy: invalid, G-single-item, `[5 1 3 5]`, steps `[:rw :ww :wr]`. With `[:delete 1]` instead of the write, the unmodified code catches it.
- **Specification:** under the checker's own version order, init -ww-> T1 -wr-> T2 -rw-> init: a G-single (read skew).
- **Code path:** `(case f (:insert :write :delete)` at closed_predicate.clj:663. Every other function spells it `:w` (closed_predicate.clj:128, 178, 210, 805).
- **Confirmed by running Elle:** yes, as written and patched. Lean: `Theorems.CP.write_keyword`.

### D10. closed-predicate: the unborn branch of `versions-after` is discarded

History: init `{0 0, 1 0}`; T1 `[[:delete 1]]`; T2 `[[:rp [:= 0] {}] [:r 1 nil]]`.
- **Elle:** `:snapshot-isolation` valid. With the parenthesis fixed: G-single, steps `[:rwp :ww :wr]` (`results/closed-predicate-2.*.edn`).
- **Specification:** Elle's own fallback reading (closed_predicate.clj:392-403: "the most charitable interpretation is that we somehow chose the unborn version"; and 266: "Every version follows :elle/unborn") gives T2 -rwp-> init -ww-> T1 -wr-> T2.
- **Code path:** the `if` at closed_predicate.clj:271-274 closes before the `loop` at 276, so its value is thrown away. The loop returns `nil` for unborn on keys that init created, so `rw-graph` (519-539) adds no rwp edge.
- **Scope:** such a read is also a predicate-read-miss, which only serializable and stronger prohibit.
- **Confirmed by running Elle:** yes, as written and patched. Lean: `Theorems.CP.versions_after_unborn`.

### D11. closed-predicate: `version<` is true whenever its first version exists

- **What happens:** on D10's patched run, Elle explains the step T2 -> init as `{:type :rwp, :key 1, :value :elle/dead, :value' 0}`. That is false: key 1's versions are `[0 :elle/dead]`, so 0 comes first. The edge itself is real (it comes from key 0); the explanation is not.
- **Property:** explanations, i.e. each reported cycle is a real cycle of the stated edges.
- **Code path:** `version<` (closed_predicate.clj:285-299) is a `loopr`; when the versions run out it returns its accumulator `found-a?`. `RWExplainer` (449-471) relies on it.
- **Confirmed by running Elle:** yes (`scratch/cpdebug.clj`). Lean: `Theorems.CP.version_lt_ignores_b`.

### D12. The verdict depends on the hashes of values

Cases `value-hash-order-a` and `-b` (ids 20-21) are the same history with x's elements 1 and 2 swapped. Two committed appends to x are read as `[1]` and `[2]`, and y is read as `[3 4]`.
- **Elle:** `:read-uncommitted` is invalid (G0) for one and valid for the other.
- **Specification:** no interpretation exists, and renaming values can't change that.
- **Property:** determinism and order independence.
- **Code path:**
  - Each key's set of read values becomes a Clojure hash set (`datafy`, bifurcan-clj core.clj:96-101).
  - It is sorted by length, stably (list_append.clj:316).
  - `append-index` takes the last value (`peek`, list_append.clj:410) as the version order. Among incompatible reads of equal length, Clojure's hash order decides which one that is.
- **Confirmed by running Elle:** yes. Lean: `Theorems.value_hash_order`.

### D13 (a TODO in the code). rw-register ignores `:info` writes

History: T0 `[[:r 0 1]]` ok, then the same process invokes T1 `[[:w 0 1]]`, which ends `:info` (id 29).
- **Elle:** `:strict-serializable` valid.
- **Specification:** if T1 committed, G1c-realtime; if it aborted, G1a. Violated in every interpretation. list-append catches the equivalent history (id 28).
- **Code path:** `ext-index` indexes only `:ok` ops; its docstring says "TODO: we fail to index external writes of type :info. That's bad." (rw_register.clj:170-173).
- **Confirmed by running Elle:** yes.

## Classification, explanations and the lattice (no verdict change found)

- **C1.** Elle reports G-single-item where some clean interpretation has only a worse G0 or G1c (the reverse of D1). The README allows "something worse", and every claim held once a worse cycle may stand in.
- **C2.** G1a is reported for a dirty update. `g1a-cases` flags any element that a failed op appended (list_append.clj:83-112); the paper (§4.3.1) calls that a dirty update unless the element is the read's last.
- **C3.** A search can record its cycle under another type. `cycle-cases-in-scc` marks the implications of the spec's name as done, not those of the cycle's type (txn.clj:883-887). Case `search-type-recorded-as-other` (ids 24-25): a G1c-realtime cycle exists, but Elle names only `strong-PL-2-cycle-exists` (and the same G-single-item-realtime cycle twice). The order of the search follows Bifurcan's hash order of op indices.
- **C4.** Spelling mismatch in the lattice: implications use `:GSIb`/`:GSI` (consistency_model.clj:94, 134-135), models prohibit `:G-SIb`/`:G-SI` (423, 450). Other entries mask it. Lean: `Theorems.gsi_spellings_disconnected`.
- **C5.** Lost update implies G2-item (consistency_model.clj:159), but H_lu has one anti-dependency, i.e. it is G-single. Cursor stability covers it. Lean: `Theorems.lost_update_not_g_single`.
- **C6.** Explanation steps for unread appends and for `nil` registers are not direct Adya edges. Transitively, every step held in every clean interpretation.
- **C7.** `cycle-cases-in-scc-fallback` finds a smaller SCC and then searches `g` instead (txn.clj:751). It is only reached after a timeout.
- **C8.** The README demo, which has no invocations, throws `:jepsen.history/not-running` with jepsen.history 0.1.9.

## What held

- **In scope, nothing broke.** For list-append histories with no `:fail` or `:info` and every append read, verdicts for all 14 models matched the specification:
  - 220,312 exhaustive one-key histories (classification included);
  - 98,914 exhaustive two-key histories;
  - 6,250 explored six-transaction histories.
- **Exhaustive determinate runs.** The determinate exhaustive runs E1 (337,264) and E3 (226,596) produced no verdict disagreement.
- **Claims.** Every Elle claim held in every clean interpretation once a more severe cycle may stand in. G1a, G1b, dirty-update and internal claims held in every interpretation.
- **Graph machinery.**
  - Bifurcan's Tarjan matched mutual reachability on every graph Elle built.
  - `realtime-graph`'s closure matched real-time precedence.
  - Every explanation step was an edge of its stated kind.
  - No verdict changed under another iteration order of the ops.
- **Monotonic-key.** It matched its specification on 6,000 histories (1,137 of them invalid) and matched real Elle on all of them.
- **Lattice.** A stronger model always prohibits everything a weaker one does. Lean: `Theorems.prohibited_monotone`.

## What was replicated, and what is not exact

Replicated, with each function cited by line in the Lean source:
- jepsen.history 0.1.9: ops, pairing by process, `possible`, `oks`, `completion`, `invocation`. jepsen.txn 0.1.3: `ext-reads`, `ext-writes`. (`Elle/Basic.lean`)
- `elle.rels`, BitRels.java, and `elle.graph`: links, union, projection, select, self-edge removal, sequential composition and extension, and Bifurcan's Tarjan as written. (`Elle/Graph.lean`)
- Hash orders. (`Elle/Hash.lean`)
- `elle.core`. (`Elle/Core.lean`, `Elle/Monotonic.lean`)
- `elle.bfs` and BFSPath.java. (`Elle/Bfs.lean`)
- `elle.txn`, everything `check` calls. (`Elle/Txn.lean`)
- `elle.consistency-model`. (`Elle/Model.lean`; its memo tables are proved equal to the definitions by `Theorems.tables_agree`)
- list-append. (`Elle/ListAppend.lean`)
- rw-register with initial-state and `:wfr-keys?`. (`Elle/RwRegister.lean`)
- closed-predicate, with D9 and D10's fixes available as switches. (`Elle/ClosedPredicate.lean`)

Not replicated, or not exact:
- Rendering, files, `elle.viz`, generators, and mop indices in explanations.
- rw-register's `:sequential-keys?`, `:linearizable-keys?` and `:transaction-order`.
- The cycle-search timeout and its fallback.
- Exceptions are an outcome value, without the exact class.
- `:not`/`:also-not` are computed only on request.
- Folds run sequentially.

## Assumptions

- **Jepsen conventions:**
  - Every op has an integer process.
  - `:fail` and `:info` completions carry the invocation's value.
  - A process is replaced after `:info`.
  - Values are unique per key, no register write is `nil`, and keys are integers.
- **List-append interpretations:**
  - A transaction's appends to a key are contiguous.
  - A key's installed versions form a prefix chain; only aborted transactions' writes sit between them (dirty updates).
  - Reads after the transaction's own writes must return its own version and are not dependencies.
  - Indeterminate reads return some installed version.
- **Order edges:**
  - Session edges run from an acknowledged transaction to a later committed one of the same process.
  - Real-time edges likewise, without the process condition.
  - Neither starts from an indeterminate transaction.
- **Models as defined:**
  - read uncommitted: G0;
  - read committed: adds G1a, G1b, G1c and dirty updates;
  - repeatable read: adds item anti-dependency cycles;
  - consistent view: adds G-single;
  - snapshot isolation: Cerone and Gotsman's `(WR ∪ WW) ; RW?` cycles, plus INT;
  - serializable: any anti-dependency cycle, plus INT;
  - session and strong variants add their edges.
- **`:unknown`** is no claim either way. Elle answers `:empty-transaction-graph` for histories without dependencies, as documented.
- **Cycle claims** may be satisfied by a more severe cycle (README).

## Properties with sources

- **Soundness.** Paper §4.3; README "Soundness"; Adya's definitions.
- **Completeness within scope.** Paper §4.3.1-4.3.2; README "Completeness" and "a complete prefix of the Adya version order".
- **Claims.** Paper Theorem 1.
- **Classification.** Adya's G-single and G1a; paper §4.3.1.
- **Explanations.** Paper §4.3.2; README.
- **Order independence.** Task statement.
- **Model-set monotonicity.** txn.clj:656-668.
- **Lattice.** consistency_model.clj:251-254.
- **Tarjan.** graph.clj:373.
- **Real-time reduction.** core.clj:372-378.
- **Monotonic key.** core.clj:14-22.
- **No throw.** README.

## Search runs

**Exploration** (reads at cuts of a decided execution order; up to 5-6 transactions, 2 keys, 3 threads):

- `la-det` (no fail/info), 5,000 timelines. Broke: model-pair monotonicity (D2), G-single classification, consistent-view completeness (6) and strong session SI completeness (2).
- `la-det-obs` (every append read), 5,000 timelines. Broke: monotonicity only.
- `la-fail`, 5,000 timelines. Broke: completeness of strong session and strong read uncommitted (D4), and the others above.
- `la-info`, 5,000 timelines. Broke: strong session read committed completeness (94, D3), soundness of read uncommitted (2) and strong read uncommitted (33) (D5).
- `rr-cuts` and `rr-det`, 5,000 each. Broke: register completeness (D6 and the documented version-order limit).
- `rr-det-single`, 8,000 timelines. Read committed no longer broke.
- `la-det-obs-big`, 20,000 timelines, 6,250 in scope. Nothing broke.
- Two early list-append runs of 3,000 each, plus the differential tests (18,790 real-Elle runs).

**Exhaustive** (every timeline within the bounds; up to 3 transactions, up to 2 micro-ops, reads are any list of up to 2 distinct appended elements; model-pair check off):

- E1, list-append, determinate, 1 key: 337,264 histories, complete. Broke: classification only.
- E1 restricted to every append read: 220,312 in scope. Nothing broke.
- E2, list-append, 1 key, with fail and info: 1,152,552 histories, complete, split by decision prefix into 40 + 3,680 + 399,792 + 399,792 + 174,624 + 174,624. Broke: D3, D4, D5, classification.
- E3, list-append, determinate, 2 keys, 1 thread: 226,596 histories. Broke: classification only.
- E3 restricted to every append read: 98,914 in scope. Nothing broke.
- E4, list-append, interleaved, fail and info, 1 micro-op: 36,204. Broke: D3, D5, G1a classification.
- E5, rw-register, determinate: 41,008. Broke: register completeness (D6, documented limit).
- E6, rw-register, 1 key, fail and info: 225,288. Broke: completeness only (D6, D13, documented limit); no soundness failures.
- E7, rw-register, interleaved: 31,236. Broke: D13 only.
- Total: 2,050,148 histories. Every run's shrunk counterexamples, with tapes, are in `results/NAME.txt` and `results/NAME.cases.edn`.

## Theorems

All in `Elle/Theorems.lean`.

Proved by hand:
- `isPrefix_iff`.
- `neighbours_prefix_pairwise` and `incompatibleOrders_nil_iff`: `incompatible-orders` reports nothing for a key exactly when its sorted values are pairwise prefixes.
- `stepRel_none_mode_no_rw`, `stepRel_single_then_none`, `stepRel_no_adjacent_rw`, `taken_not_valid`: the BFS path machine takes exactly one anti-dependency in single mode, never two in a row in non-adjacent mode, and doesn't accept a path that ends on one.

Proved by `native_decide` (the compiled replica and specification evaluate them):
- Lattice and tables: `tables_agree`, `prohibited_monotone`, `gsi_spellings_disconnected`, `lost_update_not_g_single`, `internal_not_prohibited_by_rr`, `realtime_replaces_process`.
- One theorem per disagreement: `unobserved_appends`, `process_order_skips_info`, `process_skips_info_2txn`, `realtime_model_hides_process_anomaly`, `failed_append_hides_ww`, `info_write_may_have_aborted`, `info_may_have_aborted_2txn`, `register_fuzzy_read`, `register_second_read_g1c`, `register_initial_state_g_single`, `register_future_read`, `value_hash_order`, `garbage_read_throws`, `CP.write_keyword`, `CP.versions_after_unborn`, `CP.version_lt_ignores_b`.

Not proved: Tarjan in general, and soundness of the inference rules in general.

## Library gaps

Built here because determinismo's `sdk/lean` (b8f9cc9) lacks them:
- `exhaust` stops at the first counterexample. I needed every property's first counterexample, counts, a time budget, progress output, dry-run sizing and splitting by decision prefix (in `Main.lean`).
- The searches return only decisions. Replaying them to get the history back is `Props.runOnce`.
- No graph algorithms, no permutation or subset enumeration, no EDN writer, no runner for the real program.
- `History.linearizable` is single-object, so it doesn't apply to isolation levels.

## Reproducing

    lake build Elle elle-search
    .lake/build/bin/elle-search cases la out=results/cases
    runner/elle.sh results/cases.cases.edn results/cases.elle.edn
    .lake/build/bin/elle-search exhaust la read=any txns=3 mops=2 keys=1 threads=2 maxread=2 interleave=0 fail=0 info=0 pairs=0 out=results/ex-E1
    .lake/build/bin/elle-search diff la read=cuts seeds=200 out=scratch/diff-la2 && runner/elle.sh scratch/diff-la2.cases.edn scratch/diff-la2.elle.edn && python3 runner/compare.py scratch/diff-la2.replica.edn scratch/diff-la2.elle.edn

`runner/elle.sh` runs real Elle from `upstream/` with dependencies in a project-local Maven repository (`deps/m2`) through the job slots.

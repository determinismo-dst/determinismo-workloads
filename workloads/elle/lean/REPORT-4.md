# Elle 4e359e5 in Lean 4: round 4, the proof round

Round 4 replicates the service as it will be deployed next (`service-9a914f9/`), proves for every history (no bound on its size) what rounds 1 to 3 had checked by search, checks D12's refined fix, and says what is left. Rounds 1 to 3 are in `REPORT.md`, `REPORT-2.md`, `REPORT-3.md`.

Versions:
- Elle main is still 4e359e5 (`git ls-remote`, 2026-11-25).
- Lean v4.36.0, `sdk/lean` b8f9cc9, jepsen.history 0.1.9, jepsen.txn 0.1.3.
- `lake build Elle elle-search elle-r2 elle-r3 elle-r4 elle-r5` builds rounds 1 to 4.
- The proofs are in `Elle/R4/` (4,914 lines, 233 theorems). The round's runner is `elle-r5` (`Main5.lean`). Results are in `results/r4/` and `scratch/r4/`.

## The service as deployed next

### What it is

- `service-9a914f9/src/elle/` holds six namespaces. Each equals round 3's `scratch/r3/fix-safe/elle/` byte for byte (`diff -q`).
- `service-9a914f9/src/elle_service.clj` equals the deployed one (`service-5fc908e`).
- Only the README and `test/elle_service_test.clj` differ besides. The tests add D23, D1, D7 and D8 cases.

So the switch set for "deployed next" is the deployed one (D3, D9 to D11, D13, and the service's D16, D17, D19) plus round 3's safe set: D1, D4 with D5, D6, D7, D8, D20, D21, D22.

### Where each fix sits (`service-9a914f9/src/elle/`)

- `list_append.clj`:
  - D8: `dirty-update-cases` passes over an element nobody appended (464-470). `garbage-read-cases` is at 505-515, and is reported at 1119-1120 and 1158-1159.
  - D4: `element-before` and `committed-previous-element` (566-586), used by `ww-mop-dep` (595-599) for every model.
  - D5: `preprocess`'s `g1a?` arity (641-649); the version order from reads without `:info` elements (664-683); the write index of `:ok` ops only (688).
  - D1: the `RWExplainer` and `rw-graph` without unread pairs (781-846); `unread-pairs`, `UnreadExplainer` and `unread-cycles` (899-970); merged into the cycles (1146-1148).
- `rw_register.clj`: D1's register form (header, 11), D6 (16-19, then from 154), D7 (`op-future-read-case`, `future-read-cases`, 133-151).
- `closed_predicate.clj`: D21 (from 451), D22 (470, 592).
- `txn.clj`: D20 (529, 602, 618, 842).
- `consistency_model.clj`: `:fuzzy-read` (426-428, 491-492) and `:garbage-read` (449-451).

### Replicated

- `Round4.deployedNextOpts` (`Elle/Round4.lean`): `Service.deployedOpts` with `fixD1`, `fixD4`, `fixD5`, `fixD6`, `fixD7`, `fixD8`, `fixD20`, `fixD21`, `fixD22`.
- `Round4.checkNext`: the service's `check` with those switches.
- Every fix stays a switch, off by default, beside Elle as written.

### Checked against the real service

The real `service-9a914f9` `check` (Clojure, `scratch/r4/svc/svcrun.clj`) against the replica:

- **46 minimal cases:** rounds 1 to 3's fix and service cases, D12's regression, D23. All equal (`scratch/r4/svc/cases4.*`).
- **29,282 random cases**, all equal:
  - list-append at cuts and with any reads;
  - rw-register at cuts and with any reads, with and without `linearizable_keys`;
  - closed predicate, with and without predicate-read misses;
  - every model of the service, per key, open invocations, duplicated reads.
  - 5,782 of the 28,058 large-batch cases are invalid (`scratch/r4/svc/batch.cmp.txt`).

The minimal cases through the service as deployed next (`elle-r5 svccases4`):
- **Invalid, as the specification says:** D1, D4, D6, D7 (strict serializable), D8, D9, D10, D13, D20, D21, D22, D23.
- **Valid:** D5's two histories under read uncommitted (an interpretation satisfies it).
- **Misses left, as round 3 listed:**
  - D7 under read uncommitted: no interpretation exists, but `:future-read` is a G1c, which read uncommitted allows.
  - D12's hash-order pair: D12 isn't deployed.

The service as deployed next against the deployed one and the specification (`elle-r5 next`, 40,000 histories each):
- **list-append, any reads:**
  - no new false positive, no regression, no exception;
  - caught 12; caught where no interpretation exists 61; false positives dropped 27;
  - left: one snapshot isolation miss.
- **list-append, cuts:**
  - caught 167; no interpretation 21; dropped 41;
  - left: one miss each for strong session snapshot isolation, strong session read uncommitted and strong read uncommitted, all missed by the deployed service too.
- **rw-register:** caught 2,294; no interpretation 17,290. Misses left are the blind-write limit, missed by the deployed service too.
- **closed predicate without read misses:** caught 3,698, no false positive. Left: repeatable read 29, D20's remainder.
- **closed predicate with read misses:** 2,006 serializable reports are predicate-read misses (`:predicate-read-miss`, proscribed by PL-3), which this property's specification doesn't model. Round 3 counted them separately. They are not new.

## The model the proofs quantify over

### Well-formed histories (`LA.WF`, `Elle/R4/Interp.lean`)

A list-append history as the service hands it to Elle:
- operations at their index;
- only reads and appends (of integers);
- a read of an operation that didn't end `:ok` holds `nil` (unknown);
- an `:ok` read holds no element twice (the service drops such reads, D17);
- each element of a key is appended by one completion, once.

Register histories (`RR.WF`, `Elle/R4/Fixes.lean`): operations at their index, written values are integers, each value written once per key.

### Interpretations

**Clean** (`Interp.Clean`; Elle §4, Theorem 1's clean interpretations):
- Which transactions committed: every `:ok`, any `:info`, nothing else.
- Per key, the version order: exactly its committed appenders, no repeats.
- Version `i` is the first `i` writers' appends.
- A read before its transaction's own append of the key returns some version that doesn't hold the transaction's own writes.
- A read after own appends returns the version just before the transaction's own, then its own appends so far.

**Every interpretation, dirty ones included** (`GInterp.Valid`, `Elle/R4/GInterp.lean`), for the models that allow G1a. Commitment and version order are as above, plus each writer's *base*: what its appends went on, i.e. the version before it, then aborted elements.
- `chain`: an earlier writer's base and appends are a prefix of a later writer's base.
- `own`: a writer's elements aren't in its base.
- `pins`: a read holding a writer's `n`-th element holds that writer's base and its first `n + 1` appends. This is the specification's decomposition of a read into writer segments.
- `appended`: every element read was appended by someone.

**The DSG** (`Interp.dsg`, `Elle/R4/Dsg.lean`):
- ww between successive writers;
- wr from the writer of the version an external read returned;
- rw from that reader to the next writer;
- `so` and `rt` from an `:ok` transaction to a committed one invoked after it completed (`so`: same process), with the invocation from the pair index, as round 1's specification draws them.

The phenomena are as round 1's `Spec.cyclePhen` computes them: G0, G1c, G-single, G2, G-nonadjacent, each with its process and realtime variants.

### The model against round 1's specification

`Elle/R4/Validate.lean` decides each clause on concrete interpretations (`elle-r5 validate`):
- Every clean interpretation that `Spec.interpsListAppend` enumerates satisfies `Interp.Clean`.
- Every edge of `Interp.dsg` is an edge of the specification's DSG with the same relationship. It may have fewer: committed `:info` transactions' reads are left out, so a cycle in it is also one in the specification's.
- Every interpretation, clean or not, satisfies `GInterp.Valid`, with the base the specification pins.

Runs:
- 40,000 histories at cuts;
- 40,000 with any reads;
- the whole space of 3 transactions, 2 micro-ops, 1 key, 2 threads, reads up to 2 elements, with fails and infos: 13,224,488 timelines, complete. Of these, 2,441,362 have interpretations, 1,606,320 have dirty ones, and 1,203,318 have clean ones.

No clause failed and no extra edge appeared, in any interpretation. So the theorems below, stated over the declarative model, cover every interpretation of round 1's specification on every history searched. The model is written from the definitions, so the theorems themselves hold for every history.

## Theorems proved (every history)

Each has the axioms `propext`, `Classical.choice`, `Quot.sound` only (`#print axioms` in `Elle/R4/Theorems4.lean`). None uses `sorry` or `native_decide`.

### The cycle lifting (`Elle/R4/Cycle.lean`, `Elle/R4/Lift.lean`)

- **`lift_cycle`**: a closed walk of explained steps, each lifting into a DSG as `StepLift` says, shows in that DSG what `classify`'s branch claims (`Claim`), or a G-single through one of D1's unread steps.
- **`StepLift`**, what each step is in the DSG:
  - a `ww` step: a path of write dependencies (D1's unread step: that, or the DSG has a G-single);
  - `wr`: a read dependency;
  - `rw`: an anti-dependency followed by write dependencies; or, where the reader's own unread append came next, write dependencies only;
  - `process`: a session-order edge;
  - `realtime`: a real-time edge.
- **`Claim`**, by the number of anti-dependency steps, each with the cycle's variant:
  - none: G1c (G0 without a `wr` step);
  - one: G-single or G1c;
  - more, adjacent: G2 or G1c;
  - more, non-adjacent: G-nonadjacent, and G2 or G1c.
- `cyc_G0`, `cyc_G1c`, `cyc_GSingle`, `cyc_G2`, `cyc_GNonadj` (`Cycle.lean`): the phenomena of a periodic closed walk of segments, by where its anti-dependency segments are.
- `Dsg.lean`: the implications G0 ⇒ G1c ⇒ G-nonadjacent; G-single ⇒ G2 and G-nonadjacent; each phenomenon ⇒ its process and realtime variants.

### List-append's edges hold in every clean interpretation (`Elle/R4/LASound.lean`)

For well-formed histories, `preprocess` for models that prohibit G1a (D5's fix leaves `:info` appends indexed), with D4's step-over on (as deployed next):

- **`ww_lift`**: a `ww` explanation `a -> b` (`ww-mop-dep`). In every clean interpretation where `b` committed, `a` committed too and precedes `b` in the key's version order.
- **`wr_lift`**: a `wr` explanation is a read dependency, both ends committed.
- **`rw_lift`**: an `rw` explanation the `ww` explainer didn't take is one of:
  - an anti-dependency from `a` to the next writer, which precedes or is `b`;
  - or `a`'s own append came next and precedes `b` (the D1 situation).
  - A read after the reader's own appends never yields an `rw` explanation: the `ww` explainer takes it first.
- **`unread_lift`** (D1): an unread step `a -> b`. Either `a` precedes `b`, or the interpretation has a G-single through `a`.

These are the paper's recoverability (unique appends name each element's writer) and traceability (each read is a prefix of one chain) arguments. `LAChain.lean` holds the chain lemmas. `LAIndex.lean` holds what the indices hold: `write-index`, `read-index`, `sorted-values`, `append-index`, `prevElem`, `committed-previous-element`.

### Process and real-time steps (`Elle/R4/Orders.lean`)

- **`pairIndex_ok`**: the pair index pairs a completion with an invocation of its process before it, with no operation of that process between.
- **`lt_invIdx_of_proc`**, **`lt_invIdx_of_realtime`**: a process explanation out of a completion, and a real-time explanation, both come before the target's invocation.
- `processGraph_src_ok`, `realtimeGraph_src_ok`: those graphs link only out of `:ok` ops (with or without D3's `:info` edges).

### Theorem 1 for list-append, the service as deployed next (`Elle/R4/LACycle.lean`)

- **`la_cycle_clean`**: for a well-formed history, models that prohibit G1a, the main search's graph or D1's second one, and the process or real-time graph (with or without D3's `:info` edges). Every closed walk of the analysis's edges that its explainers explain shows, in every clean interpretation, `Claim` for its steps, or a G-single through an unread step.
- `src_com`: every edge leaves a committed transaction.
- `graph_explain_complete`: every edge of `graph` is explained.
- `step_lift`: each explained step lifts.

**From classes to models** (`Elle/R4/Lattice.lean`, `elle-r5 lattice`):
- For each of the 14 models, every cycle class Elle's lattice prohibits (8 bases × 3 variants) is ruled out by `Claim` for that model in the specification: every alternative holds a phenomenon the model proscribes. D1's unread G-single is included.
- Elle's lattice is a `while` loop over strings, which the kernel can't reduce. So this table is checked by evaluation, not proof. **No class is left uncovered.**
- The check first flagged G-nonadjacent for repeatable read and the serializable models. `Claim`'s non-adjacent branch was too weak. It now adds "G2 or G1c", proved in `lift_cycle`.
- Every non-clean interpretation shows G1a, G1b or a dirty update, which every model that prohibits G1a proscribes. So a cycle Elle reports for such a model rules the model out in every interpretation.

### D4 with D5: read uncommitted in every interpretation (`Elle/R4/GInterp.lean`)

Under D5's fix (models allowing G1a), only `:ok` appends are indexed, the version order comes from a read without `:info` elements, and D4 steps over failed elements.

- **`ww_lift_d5`**: a `ww` explanation into an `:ok` op holds in every interpretation, dirty ones included: the writer it names precedes the target.
- **`la_g0_cycle_d5`**: every G0 cycle Elle reports under D5's fix holds as a G0 of the same variant in every interpretation. A G0 cycle has steps `ww`, `process` or `realtime` (classes G0, G0-process, G0-realtime), the only classes read uncommitted and its variants prohibit. So read uncommitted, strong session read uncommitted and strong read uncommitted get no false positive.
- `src_ok_d5`: under D5's fix every edge leaves an `:ok` op, so `:info` ops, which may have aborted, are never on a cycle.

### D23 (`Elle/R4/GInterp.lean`)

- **`d23_ww`**: under D5's fix, suppose the element before an append `e` of `t0` in the version order (the last observed element, when `e` is unread) is an element of another `:ok` op `t1`. Then `ww-mop-dep` names `t1`: the step `t1 -ww-> t0` is explained.
- `ai_no_info`: under D5's fix the version order holds no `:info` op's element.

The class of histories D23 belongs to: an `:ok` transaction `t0`, one of whose appends is preceded in the `:info`-free version order by an element of an `:ok` transaction `t1` that `t0` precedes in real time (or in its process).
- D5 explains `t1 -ww-> t0`, and the real-time (process) graph explains `t0 -> t1`.
- The cycle is G0-realtime (G0-process), and `la_g0_cycle_d5` shows it in every interpretation.
- With D3's fix alone, the version order could be a read of `:info` elements (D23: `[3 4]`). Then `t0`'s predecessor was the `:info` transaction, and the only cycle ran through the real-time edge into it that D3 removed.
- That D5's search finds the cycle is the search's completeness, which isn't proved (below). Round 3's E2 segment caught all 48 of D23's histories there with D5, and all 105 of the whole E2 space.

### D8 and D7: no interpretation (`Elle/R4/Fixes.lean`)

- **`garbage_no_interp`** (D8): a `:garbage-read` case, an `:ok` read holding an element no op appended, has no interpretation.
- **`RR.future_read_no_interp`** (D7): a `:future-read` case, an `:ok` transaction reading the value it writes later itself, has no interpretation. Values are unique, so its only writer is the reader. An external read returns another committed transaction's write or `nil`, and an internal one returns the transaction's last own write, so neither can return it. These are round 1's specification's `nonAdya` branches.

### D12's refinement renames with the values (`Elle/R4/Rename.lean`)

- **`sortedValues_d12b_ren`**: for any injective renaming `ρ` of elements (appends and reads alike), `sorted-values` with the refinement on the renamed history is the renamed `sorted-values`.
- **`appendIndex_d12b_ren`**: so is `append-index`, the version order.

The order of reads of equal length depends on their count of elements no failed op appended (`failedAppends` renames with them) and on where each was first read. Elle 0.2.8's `Hash.vectorsOrder` depends on the values' hashes.

## What is still partial, and exactly what is left

- **The search returns cycles of its graph.**
  - `bfsSearch` (bfs.clj) is a `partial def` in the replica, so its result can't be reasoned about; its loop trimming may not terminate in general.
  - The theorems take any closed walk of the analysis's edges that the explainers explain. A reported cycle case is one if the search returns cycles of the graph it searched (round 1's `explanations` property, searched).
  - Tarjan's SCCs (`cycle-exists` cases) aren't proved either.
- **rw-register's edges and D6.**
  - Not proved: `wr`, `rw` from the version graphs, D1's register form, and D6's fuzzy reads (a G-single in every clean interpretation).
  - Round 3's searches stand. For D6: 40,000 histories, the claims held; one key with fail and info, 225,288 timelines, complete.
  - D7 is proved.
  - `:linearizable-keys?` needs its own assumption (each key linearizable) and isn't covered.
- **Closed predicate** (cpFixed's D9 to D11, D20, D21, D22): not proved. Under the checker's own reading (`CPSpec`), round 3's searches and differential runs stand.
- **Per-key real time** (strict-serializable-per-key's graph) and D2's two graphs together aren't covered by `ExtraOK`.
- **Non-cycle anomalies** other than D7 and D8 are not proved: G1a, G1b, dirty update, internal, incompatible order, lost update, duplicates.
- **No exception.**
  - Proved: every edge of `graph` is explained (`graph_explain_complete`).
  - Not proved: that `preprocess`'s two verification loops pass on well-formed histories; that `dirty-update-cases` returns with D8's fix; that `classify` never returns `none` on a cycle (it does only when every step is `process` or `realtime`, which go forward in time); the search's termination.
  - Round 3's searches found no exception on well-formed histories: 240,000 histories and the finished runs.
- **D23's "caught".** The edge is proved. That the search finds the cycle is the completeness above.
- **D12's refinement, the rest of the pipeline.** The version order is proved to rename. That the write and read indices, `ww-mop-dep`, `rw-mop-deps` and the graph rename too is not proved. Each compares elements only for equality.
- **The model link** uses Elle's lattice by evaluation (above).
- **The declarative model** is checked against round 1's executable specification by search (above), not proved equal to it.

## D12's refinement

**Fix** (`Opts.fixD12b`, `ListAppend.sortedValues … (failed := some fs)`; the Clojure patch is `scratch/r4/fix-d12b/elle/list_append.clj`, on service-9a914f9's namespace):
- Among reads of equal length, the version order ranks a read by its count of elements no failed operation appended, then by where it was first read (operation, then micro-op).
- The failed set comes from the whole history: in `preprocess`, in D1's `unread-cycles`, and in `check`'s two `sorted-values` calls.

**Checks** (40,000 histories each, round 3's bounds and seeds):
- **On the deployed service** (round 3's base, comparable with D12's run):
  - no regression (D12 had 1), no new false positive;
  - caught where no interpretation exists: 229, as D12;
  - the false positives left are D5's kind, already in the deployed base (9, 10, 8).
- **On the service as deployed next, any reads:** caught 229, no regression, no false positive, no exception. Left: one snapshot isolation miss.
- **On the service as deployed next, cuts** (5 transactions, 3 micro-ops): caught 254, no regression, no false positive. Left: strong session snapshot isolation 2, snapshot isolation 1.
- **Renaming every value** (`1000 - e`): the refinement flips **no** verdict. The base flips 250 (deployed, any reads), 255 (next, any reads) and 505 (next, cuts).
- **D12's regression** (strong read uncommitted, where the chosen read held only a failed append): caught again (G0-realtime), and also when renamed.
- **D12's hash-order pair:** valid for both orders.
- **Real Elle** (service-9a914f9's namespaces with the patch ahead): the 6 D12 cases and 12,600 random cases equal the replica (`scratch/r4/fd/`).
- **Proof:** the version order renames with the values (above).

**Verdict: safe to deploy.**
- It is deterministic: proved for the version order, and no verdict flipped in 120,000 renamed histories.
- It loses no verdict in the searches.
- It fixes D12's one regression.
- It agrees with real Elle.

## New disagreements

None. Every statement I attempted either holds for every history or is left open as stated above, and no counterexample came up. Two observations, neither a wrong verdict:

- Under D5's fix, a `ww` edge into an `:info` op can be false. That happens in an interpretation where the op committed before the writer the edge names: its elements, read before the writer's, are filtered out of the version order. Such an op has no edge out of it (`src_ok_d5`), so it is on no cycle and no verdict depends on the edge.
- A first-search `rw` step from a reader that also appended an unread element is a write dependency in the interpretations where that append came next (`rw_lift`'s second case). The cycle's class is then lower (G-single becomes G1c), and every model that prohibits the reported class also prohibits the lower one (the lattice check). This is D1, fixed by the second search.

## Assumptions

- Histories are well-formed as above: what the service hands Elle, closed and deduplicated.
- Models that prohibit G1a are judged on clean interpretations. Every other interpretation shows G1a, G1b or a dirty update, which those models proscribe.
- Models that allow G1a are judged on every interpretation.
- The search (`bfsSearch`) returns cycles of the graph it searched.
- `flip` and the iteration `Order` are arbitrary in every theorem (the hash orders are decisions).
- The specification's DSG has every edge the declarative one has (checked by search).

## Properties with sources

- Theorem 1 (Kingsbury and Alvaro, "Elle", VLDB 2020, §4): cycle anomalies hold in every clean interpretation. Recoverability and traceability: §4.1.
- Adya's DSG and phenomena (thesis §3.2-3.4; Adya, Liskov, O'Neil, ICDE 2000), as round 1's `Spec.cyclePhen` computes them.
- Read uncommitted and its variants allow G1a (Adya's PL-1; consistency_model.clj).
- No false positive and no exception (the task); D12's renaming invariance (determinism, round 1's D12 property).

## Library gaps (what sdk/lean lacked)

`sdk/lean` (Determinismo) is for searching: decisions, tapes, shrinking. It has no proof support. For these proofs:
- **Relation closures.** `TransGen`/`ReflTransGen` aren't in core either. `Plus`/`Star` are written in `Dsg.lean`.
- **Association lists.** There is no library; the `amPut`/`amUpdate`/`lookup` lemmas are in `R4/Prelude.lean` and `R4/Rename.lean`.
- **Loops.** There are no lemmas for `for` loops in `Id` (invariants, with an index, with early `return`) or for `while` loops. They are written on core's `List.forIn_cons` and `Lean.Loop.forIn_eq_of_monadTail` (`R4/Prelude.lean`, `R4/Orders.lean`).
- **`partial def`s** hide what they compute. Clojure's and Bifurcan's hash orders (`Hash.hamtOrder`, `champOrder`) are now total, with the same equations, terminating on the shift. The cycle search can't be made total.
- **Kernel evaluation.** Elle's lattice and `String.endsWith` don't reduce in the kernel, so `decide` can't check model tables.
- **Validation harness.** There was none to check a declarative model against an executable one: `R4/Validate.lean`.
- **Tactics.** Mathlib's tactics (`by_contra`, `tauto`, `set`, `Nat.le_induction`, `swap`) aren't available.

## Replica changes this round

- `Opts.fixD12b`, `Fx.d12b`, `ListAppend.failedAppends`, and `sortedValues`' `failed` argument: the refinement, off by default.
- `Hash.champOrder`, `Hash.hamtOrder`: `partial def` changed to a total `def` by the shift, with the same equations. Rounds 1 to 3's `native_decide` theorems still hold.
- `Elle/Round4.lean`: the deployed-next switches, D12's regression history.
- `Main5.lean` (`elle-r5`): `svcdiff4`, `svccases4`, `fix4`, `rename4`, `fixdiff4`, `d12cases`, `next`, `validate`, `lattice`.

## Search runs this round

- Service as deployed next: 46 minimal and 29,282 random cases on the real service, all equal.
- D12's refinement: 6 runs of 40,000 (fix and renaming, two bases, two read modes); 12,606 cases on real Elle, all equal.
- The declarative models against the specification:
  - 80,000 random histories;
  - 13,224,488 exhaustive timelines (complete), for the clean model;
  - the same again for the general model.
- The service as deployed next against the deployed one and the specification: 5 runs of 40,000 (list-append any and cuts, rw-register, closed predicate with and without read misses).

## Reproducing

    lake build Elle elle-r5
    .lake/build/bin/elle-r5 svccases4 la
    (cd scratch/r4/svc && . ../../r3/env.sh && clojure -M svcrun.clj cases4.cases.edn cases4.out.edn)
    python3 -I scratch/r4/svc/cmp.py scratch/r4/svc/cases4
    scratch/r4/svc/batch.sh
    scratch/r4/d12b.sh; scratch/r4/fd/run.sh
    scratch/r4/validate.sh; scratch/r4/validate2.sh
    .lake/build/bin/elle-r5 lattice la
    scratch/r4/next.sh

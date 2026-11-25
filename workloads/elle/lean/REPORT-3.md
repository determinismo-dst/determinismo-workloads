# Elle 4e359e5 in Lean 4: round 3

Round 3 checks the deployed HTTP service (`service-5fc908e/`). It also finishes round 2's partial searches and writes and checks a fix for every disagreement still open. Rounds 1 and 2 are in `REPORT.md` and `REPORT-2.md`.

Versions:
- Elle main is still 4e359e5 (`git ls-remote`, 2026-11-25).
- The Elle 0.2.8 jar the service loads has the same `.clj` sources as `upstream/src`.
- `svc:N` below means `service-5fc908e/src/elle_service.clj` line N. Patched namespaces are cited by file and line.
- jepsen.history 0.1.9, jepsen.txn 0.1.3, Lean v4.36.0, `sdk/lean` b8f9cc9.
- `lake build Elle` builds the theorems of rounds 1, 2 and 3.

## The deployed service's check

### Replicated

Each change is a switch beside round 2's replica, off by default.

- **`Opts.cpFixed`** (closed_predicate.clj):
  - `ww-graph` matches `:w` (684);
  - `versions-after` keeps its unborn branch (283-297);
  - `version<` puts `:elle/unborn` first and is false when b never follows a (299-320).
- **`Opts.fixD3`** (core.clj, txn.clj):
  - `process-graph-with-info` (core.clj:360-384) and `realtime-graph-without-info` (core.clj:477-488);
  - `additional-graphs` picks between them by whether the model prohibits G1a (txn.clj:694-707).
- **`Opts.fixD13`** (rw_register.clj):
  - `ext-write-index` (194), `observed-info-indices` (207), `step-over-info` (215-245);
  - the `g1a?` arity of `version-graphs->transaction-graph` (780-808), `ww+rw-graph` (875-882), `wr-graph` (915-916).
- **The service itself** (`Service.check … (deployed := true)`):
  - `deduplicated` (svc:164-190) drops each read holding a value twice, from its completion and its invocation;
  - `not` after duplicates is the boundary of the answer's types (svc:262-265);
  - `keys-of` (svc:194-202) gives an init its map's keys and a predicate read every key;
  - per-key sources (svc:213-218).

Checked against the real deployed service (`scratch/r3/svc/svcrun.clj`, the service's `check` in a JVM):
- 15 minimal cases and 9,549 random cases gave equal `valid`, `anomaly_types` and `not`.
- The random cases cover list-append, rw-register and closed predicate; 1,991 are invalid, 720 use `linearizable_keys`, 930 are per key, and the rest are open invocations and duplicated reads.
- One replica error surfaced first and is fixed. `realtime-graph-without-info` unlinks edges after the fact, so Bifurcan keeps their vertices. The replica never added them, so 8 graphs looked empty and read `:unknown` where the service said `true`. Round 2's D3 replica had the same error.

### Each target case (replica and real service equal)

- **D3:**
  - `process-skips-info-2txn` under strong session read committed: G1c-process (round 2's service: valid).
  - `process-order-skips-info` under strong session serializable: G0-process.
  - The same history under strong read uncommitted: valid (Elle 0.2.8: G0-realtime). Its aborted interpretation satisfies the model.
- **D9:** the read skew through `[:w 1 1]` is G-single-item under serializable and snapshot isolation. With the init's value read instead: valid.
- **D10:**
  - init `{0 0, 1 0}`, then `[[:delete 1]]`, then `[[:rp [:= 0] {}] [:r 1 nil]]`: snapshot isolation invalid, G-single.
  - Elle's own failure-to-observe history: G-single-realtime beside predicate-read-miss.
- **D11:** the explanation step is now `{:type :rwp, :key 0, :value :elle/unborn, :value' 0}`. Round 1's was `{:key 1, :value :elle/dead}`, which was false. Checked on the real service's text (`svc/explain.clj`) and in the replica.
- **D13:** `register-info-write-read-early` under strict serializable: G1c-realtime.
- **D14:** the service has no `:transaction-order` parameter, so it can't receive D14. The deployed rw-register on round 2's cases gives G0-realtime (id 0) and G1c (id 3); the controls are unchanged.
- **D16:** the answer has `not [read-uncommitted]`.
- **D17:** the answer holds G0-realtime and duplicate-elements.
- **D19:** the stale predicate read is invalid per key (G-single-realtime).

The service's own tests (`clojure -M:test`, from a copy in `scratch/r3/svc-copy`): 9 tests, 12 assertions, 0 failures.

Elle's suite with `src/elle` ahead: 103 tests, same as written except two.
- `failure-to-observe-test` now also reports its G-single-realtime, as the service README says.
- `checker-test` errors in this environment, as it does on every run (it can't create its output file).

### Over every interpretation (`Round3.deployedProps`, `deployedServiceProps`, `perKeyProps`)

240,000 explored histories, 40,000 each:
- list-append with reads at cuts, and with any reads;
- rw-register at cuts (4 transactions) and with any reads;
- closed predicate, and closed predicate with predicate-read misses.

Results:
- **Deployed false positive Elle 0.2.8 doesn't report:** none.
- **Exceptions:** none.
- **False claims:** none (each newly reported type holds in every clean interpretation).
- **Closing and deduplication:** both held.
- **Caught, where Elle 0.2.8 passed and every interpretation fails:**
  - list-append: 1,382 and 626;
  - rw-register: 2,904 and 1,850;
  - closed predicate with misses: 22,672.
- **Elle 0.2.8 false positives dropped (D5's real-time instance):** 519 and 126.
- **Remaining false positives:** 9 or 10 per read-uncommitted-family model, the same as Elle 0.2.8 (the D5 kind).
- **Regression:** 1 (D23).
- **Remaining misses:** the known kinds.
  - list-append: D1 (consistent view 56, snapshot isolation 59), D4.
  - rw-register: the blind-write limit, D6, D7.
  - closed predicate: D20 and D21 (repeatable read 335 and 1,034), D22 (consistent view 3).
- **Predicate-read misses:** Elle's `:predicate-read-miss` is counted as a violation of the models that proscribe it (PL-3, consistency_model.clj:426-431). Otherwise 1,899 such reports would show as false positives, as they do in Elle 0.2.8.
- **A run that lost its counts:** at 5 transactions, rw-register was killed by the job limit after 30,000 histories, inside one history's interpretations. Its log shows no false positive and no exception in those 30,000.

## The finished runs

**D3's fix over round 1's whole E2 space:**
- 1,152,552 timelines, complete, in 6 prefix segments, models with order edges.
- No new false positive and no exception.
- Caught 9,692; dropped 10,645 false positives.
- **105 regressions (D23).**
- Remaining, from before: strong session read uncommitted and strong read uncommitted false positives (6,314 and 6,112); completeness misses (372 and 752).

**D13's fix with a transaction order, the whole space:**
- 1,643,624 timelines, complete, in 9 segments.
- No new false positive, regression, exception, soundness failure, or miss against every interpretation.
- Caught 65,688.
- The only other property broken is `completeness-assumed`: 57,976 to 91,744 per model. This is round 2's artifact: the specification takes an `:info` op missing from the order as aborted, which Elle doesn't infer.

**The four searches round 2 left:**
- `:info` never in the order, exhaustive: 621,824 complete, nothing broken.
- `:linearizable-keys?` with `:wfr-keys?` at 2 micro-ops, exhaustive: 74,608 complete, nothing broken.
- The order without `:info`, at larger bounds: 60,000 explored, nothing broken.
- `:linearizable-keys?` with `:wfr-keys?` and any reads, at larger bounds: 60,000 explored, nothing broken.

**Round 2's other larger-bound runs:**
- `:linearizable-keys?` at 60,000, and `:sequential-keys?` with `:wfr-keys?` at 60,000: only `completeness-assumed`. These are the per-key orders the options never infer.
- The order without `:info`, completeness checked: 20,000, nothing broken.

New runner: `elle-r4 exhaust3/explore3` (`Props3.checkAll2`) counts every property a timeline breaks, and `dry=1` sizes a prefix without checking it.

## Fixes

Every fix is a patch on top of the deployed namespaces, in `scratch/r3/fix-dN/`, generated by `scratch/r3/patches/{la,rr,txn,cp,cm}.py`, with `fix-all` holding all of them together.

How each was checked:
- **Real Elle:** each fix's minimal histories, 31 cases × 13 runs (`scratch/r3/cmp-cases3.py`): equal to the replica, and each fix catches its case.
- **Differential:** 94,876 random cases, the patch against the replica.
  - The first `all` batches had 24 differences. They came from two patch errors, both fixed: D12's tie between two values first read in one op, and D6's version graph missing second reads' values (a NullPointerException).
  - Every batch after the fixes agreed.
- **Properties:** `Round3.fixProps`, the deployed Elle plus the fix against the deployed Elle, over every interpretation.
- **Elle's suite:** with the patch ahead. Changes beyond the deployed baseline are listed per fix.

### D7: rw-register's future read

- **Fix:** an `:ok` read of a value the same transaction writes later is reported as `:future-read` (lattice: G1c).
- **Checks:**
  - 40,000 histories: 17,066 newly invalid where no interpretation exists, 3 caught;
  - nothing bad; 2,100 differential cases equal;
  - suite: no change.
- **Safe to deploy.**

### D1: appends nobody read, after a read of the same key (list-append and rw-register)

- **Fix:**
  - A reader of a key's last version that also appends or writes the key, with nothing ever reading or ordering its own write, gets a `ww` step, not `rw`, to another such writer. This runs as a second cycle search.
  - A G0 or G1c through such a step is reported as G-single-item; any other class stands. Either the reader's write came first, or a G-single runs through the reader.
- **Checks:**
  - caught: list-append 153 and 1; rw-register 212 and 3;
  - exhaustive two keys: 160,200 of 226,596 timelines (time limit);
  - no false positive, regression, exception or false claim;
  - 11,200 differential cases equal.
  - Suite: `lost-update-test`'s expected map now gains G-single-item.
- **Safe.** It costs the second search and changes some anomaly names.
- Remaining: snapshot isolation misses appends nobody read when no reader also appends.

### D21: predicate-read rows as item reads

- **Fix:** item `wr` and `rw` edges from an `:ok` predicate read's rows, as the namespace docstring assumes.
- **Checks:**
  - 40,000 histories: caught 5,111; repeatable read misses go from 335 to 235;
  - 2,100 differential cases equal.
  - Suite: `g1c-multi-key-delete-test` now gets G-single-item and repeatable read in `not`.
- **Safe**, if rows are item reads.

### D8: garbage reads

- **Fix:** `dirty-update-cases` skips elements nobody appended. `:garbage-read` is proscribed by PL-1, like `duplicate-elements`.
- **Checks:**
  - 40,000 histories with garbage reads: 314,216 model checks no longer throw; 1,296 now invalid where no interpretation exists;
  - 2,100 differential cases equal.
  - Suite: the lattice tests list the new name.
- **Safe.**

### D6: rw-register's every external read and fuzzy reads

- **Fix:**
  - `wr`, `rw` and the initial-state graph use every read of a key the transaction hasn't written;
  - two values read for one key are reported as `:fuzzy-read`, proscribed by repeatable read and consistent view.
- **Checks:**
  - 40,000 histories: caught 4,167; read committed misses go from 36 to 0;
  - exhaustive one key with fail and info: 225,288 complete, caught 50,304;
  - 8,400 differential cases equal.
  - Suite: `all-anomalies-test`, and rw-register `checker-test`'s `not`.
- **Safe.**

### D22: closed predicate's `:info` read explained as a read

- **Fix:** the explainers read only an `:ok` op's reads.
- **Checks:** caught 3 (consistent view misses go to 0); 2,100 differential cases equal; suite: no change.
- **Safe.**

### D20: closed predicate's mixed cycles

- **Fix:**
  - a cycle with two or more anti-dependencies, one an item one, is G2-item or G-nonadjacent-item;
  - those searches take predicate anti-dependencies beside an item one;
  - the absence of a PL-2.99 cycle no longer rules them out.
- **Checks:**
  - caught 945; repeatable read misses go from 1,034 to 89;
  - 4,200 differential cases equal; suite: no change.
- **Safe.** It runs extra searches.

### D5 (with D4's step-over, extended after D23): an `:info` writer may have aborted

- **Fix, for models that allow G1a:** `:info` appends are not indexed as writes, and the version order comes from reads with their elements removed.
- **Checks:**
  - false positives dropped: 27 and 30; caught: 11 and 26; no false positive left;
  - E2 segment 2.0.0, 359,200 timelines, checked against Elle 0.2.8: no regression (D23's 48 there are caught);
  - 8,400 differential cases equal; suite: no change.
- **Safe** (read-uncommitted family only).

### D4 alone: a failed append inside a read

- **Fix:** `ww-mop-dep` steps over elements no indexed op appended.
- **Checks:** caught 11, but **3 new false positives in 40,000 histories**. Each one is an `:info` writer still indexed, so ship D4 only with D5.
- **Not safe alone.**

### D12: hash order

- **Fix:** among reads of equal length, the version order uses where each was first read (op, then micro-op), not Clojure's hash order.
- **Checks:**
  - renaming values: Elle 0.2.8 flips 250 verdicts in 40,000 histories, the fix flips none;
  - **1 regression**: strong read uncommitted, where the chosen read held only a failed append;
  - 4,200 differential cases equal.
  - Suite: `sim-prefix-test`'s expected incompatible pair changes.
- **Deterministic, but not strictly safe.**
- Proposed refinement (not run): rank reads by their count of non-failed elements first.

### D2: two models drop the process order

- **Fix:** when the models prohibit a process anomaly whose real-time variant they allow, the process graph is added, explained first.
- **Checks:**
  - caught 8,148 and 9,937; 6,000 differential cases equal; suite: no change.
  - The pair misses left are violations of the two models only together, which Elle can't split into cases.
- **Safe.** Unreachable through the service.

### D15: the pair index across chunks

- **Fix (`history.clj`):** the combiner throws `::double-invoke` for a process still running whose first op in the chunk is an invocation.
- **Checks:**
  - malformed histories: as written depends on chunking in 1,138 of 4,000; fixed never;
  - well-formed: unchanged;
  - real jepsen.history: across the boundary it now throws, and straddling pairs are unchanged.
- **Safe in an ahead-of-time build** (the service compiles from source). As a source overlay it breaks code compiled against the original `Op` class: Elle's `sim-*` tests hit a ClassCastException.

### All together

- 150,000 explored histories: no new false positive, regression, exception or false claim.
- Caught: list-append 146, rw-register 3,207 and 1,743, closed predicate 3,385.
- Suite: 7 failures, all of them listed above.

## New disagreements

### D23: the deployed D3 fix loses strong read uncommitted violations

History (process 0, one transaction after another):

    [[:r 0 [2]] [:append 0 1]]       :ok
    [[:r 0 [3 4]] [:append 0 2]]     :ok
    [[:append 0 3] [:append 0 4]]    :info

- **Elle 0.2.8:** strong read uncommitted invalid, G0-realtime, through the `:info` transaction.
- **The deployed service and Elle:** valid.
- **Specification:** violated in every interpretation.
  - The `:info` transaction can't have committed: its [3 4] and T0's [2] don't lie on one trace.
  - So 2 is installed before T0's 1: T1 -ww-> T0. With real time T0 → T1, that is G0-realtime.
- **Property and source:** no lost verdict against Elle 0.2.8. Round 2 claimed the edges into `:info` ops "can only bring D5's false positives".
- **Code path:**
  - `realtime-graph-without-info` (core.clj:477-488) is picked by txn.clj:697-701.
  - Elle's version order is the longest read, `[3 4]` (`append-index`, list_append.clj:392).
  - T0's 1 is placed after 4 (`previously-appended-element`, 517), so the only cycle Elle ever saw ran through the `:info` op.
- **Counts:** 105 of 1,152,552 E2 timelines; 1 of 40,000 explored.
- **Confirmed:** Elle 0.2.8 and the deployed namespaces (`scratch/r3/d23/*.edn`), and the real service (valid).
- **Fixed by D5's extension:** G0-realtime, and also G0-process for strong session read uncommitted. Lean: `Theorems3.d23`.

## strict-serializable-per-key

- **Closure:** the deployed graph's closure equals the closure of real time between operations sharing a key, on all 240,000 histories and on D18's and D19's cases.
  - An init's keys are its map's keys.
  - A predicate read precedes every later op.
  - An op touching a key precedes every later predicate read.
- **A wrinkle:** a predicate read is also linked to a later op that touches no key (an empty transaction). That op has no other edge, so this changes no verdict.
- **Never invalid where reading (b) holds.**
- **Misses:**
  - closed predicate and list-append: none;
  - rw-register: 292 and 135, which are Elle's own strict-serializable misses.
- **Round 2's reading (b) was wrong in my specification:** it kept process edges between transactions with no key in common. As stated, real time and so process order apply only between operations sharing a key, and the service implements that. The two readings differ on 4 to 13 histories in 40,000.
- **D18's history is still invalid per key**, so the service implements reading (b), as its definition now says. Lean: `deployed_per_key_reading_b`.

## What was replicated, and what is not exact

**New Lean code:**
- `Opts` switches `cpFixed`, `perKeyFixed`, and `fixD1` … `fixD22`.
- `Service.deduplicatedFixed`, `Core.svcKeysOfFixed`, the deployed `realtimePerKeyGraph`.
- In `ListAppend`: `Fx`, D1's second search, `committedFrom`, `garbageReadCases`, the D5 version order.
- In `RwRegister`: `allExtReads`, `fuzzyReadCases`, `futureReadCases`, `unreadPairsRR`.
- `ClosedPredicate.itemReads` and `analyzeOpts`.
- `Folds.pairIndexFoldFx`.
- The lattice gains `fuzzy-read` and `garbage-read`. Elle as written never reports them, so its verdicts don't change.

**Not exact:**
- JSON, HTTP, locks and `window_ns` (checked end to end instead).
- D1's step maps: the replica checks types only.
- The BFS's `required-rels` set order for D20's new specs: no difference seen.

## Assumptions

- Rounds 1 and 2's, plus:
  - fixes are judged on top of the deployed Elle;
  - a model set holds if some interpretation satisfies every model in it;
  - D1's claims are "class X, or a G-single";
  - `future-read` and `garbage-read` claim that no interpretation exists;
  - closed predicate uses `CPSpec`, with rows as item reads for D21, and predicate-read-miss counted for the models that proscribe it.
- I take the deployed per-key definition as reading (b) as stated, with no process edges between operations on different keys.

## Properties with sources

- **Deployed service:**
  - no new false positive, no lost verdict, no exception (README; the task);
  - claims (paper, Theorem 1);
  - `not` (consistency_model.clj:588-606);
  - deduplication;
  - per-key closure and reading (b) (svc:17-24).
- **Fixes:** no new false positive, no regression, no exception, claims; D12 renaming invariance; D15 chunking independence (fold.clj:115-150).
- **Finished runs:** round 2's properties.

## Search runs

- Part 1: 240,000 explored, plus 30,000 partial; 9,549 differential cases against the real service and 15 minimal cases.
- Part 2: 2,796,176 exhaustive (complete), 696,432 exhaustive in the four searches (complete), 260,000 explored.
- Part 3:
  - 21 explored runs of 30,000 to 40,000;
  - exhaustive: 225,288 (complete), 160,200 (partial) and 359,200 (partial);
  - 94,876 differential cases;
  - suites for the deployed Elle and each fix.
- Results are in `results/r3/*` and `scratch/r3/*`.

## Theorems

`Elle/Theorems3.lean`, by `native_decide`:
- `deployed_d3`, `deployed_d9_d10`, `deployed_d11`, `deployed_d13_d14`, `deployed_d16_d17_d19`, `deployed_per_key_reading_b`;
- `fix_d1`, `fix_d1_register`, `fix_d2`, `fix_d4_d5`, `fix_d6_d7`, `fix_d8_d12`, `fix_d20_d21_d22`, `fix_d15`, `d23`.

## Library gaps

- No per-history time budget: one heavy history killed a job and lost its counts. Searches now write `.partial.txt` every 5,000 histories.
- Interpretation enumeration has no time bound.
- One property per timeline, which I replaced with `checkAll2`.
- No dry-run sizing of a space.
- Exes can't share a root module, so I copied each binary per run to rebuild safely.

## Reproducing

    ~/dev/.lean-jobs/job 1790 lake build Elle elle-r4
    .lake/build/bin/elle-r4 deployed la seeds=40000 txns=5 mops=3 keys=2 threads=3 read=cuts
    .lake/build/bin/elle-r4 fix la fix=d1 seeds=40000 txns=4 mops=2 keys=2 threads=3 read=any maxread=3
    .lake/build/bin/elle-r4 exhaust3 la fixd3=1 txns=3 mops=2 keys=1 threads=2 read=any maxread=2 interleave=0 fail=1 info=1 prefix=2.0.0
    scratch/r3/elle-patched.sh scratch/r3/cases3.cases.edn OUT.edn fix-all deployed
    scratch/r3/suite.sh all fix-all deployed
    (cd scratch/r3/svc && . ../env.sh && clojure -M svcrun.clj cases.cases.edn cases.out.edn)

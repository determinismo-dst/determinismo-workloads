# Elle findings not reported upstream

From the Lean replica of Elle (jepsen-io/elle main 4e359e5, one commit after v0.2.8; rounds 1 and
2, blind; REPORT.md and REPORT-2.md have each history, verdict and code path). Every one was
reproduced by running the real Elle on its minimal history (results/). jepsen-io/elle's issues
were searched on 2026-11-25: none matches.

Each block runs in a REPL with Elle 0.2.8 on the classpath, after:

```clojure
(require '[elle.list-append :as la] '[elle.rw-register :as rr]
         '[elle.closed-predicate :as cp] '[jepsen.history :as h])
```

"Expected" is the verdict over every interpretation of the history (every version order, every
outcome of an indeterminate operation), from the definitions rather than Elle's code.

## Wrong verdicts: Elle passes a history that violates the model

- [ ] **D1: an unread append becomes an anti-dependency, so a G-single is reported as G2-item.**

```clojure
(def h1 (h/history
          [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil] [:append 1 1]]}
           {:process 1, :type :invoke, :f :txn, :value [[:r 1 nil] [:append 1 2] [:append 0 1]]}
           {:process 0, :type :ok, :f :txn, :value [[:r 0 []] [:append 1 1]]}
           {:process 1, :type :ok, :f :txn, :value [[:r 1 []] [:append 1 2] [:append 0 1]]}]))
(la/check {:consistency-models [:snapshot-isolation]} h1)   ; Elle: valid              expected: invalid, G-single in every interpretation
(la/check {:consistency-models [:consistent-view]} h1)      ; Elle: valid              expected: invalid
(la/check {:consistency-models [:repeatable-read]} h1)      ; Elle: invalid, G2-item   expected: invalid, G-single
```

`values-from-single-appends` (list_append.clj:247-269) gives y no order, because it has two
appends. `previously-appended-element` (517-535) places an append of unknown position after the
last read element, here `::init`, so `rw-mop-deps` (550-561) gives every reader of `[]` an rw edge
to both appends, and `ww-mop-dep` (537-548) none between them. The explainer (txn.clj:477-536)
names the adjacent `[:rw :rw]` G2-item. rw-register misses the same through its "`nil` before every
value" rule (rw_register.clj:184-208, 704-735).

- [ ] **D2: asking for two models at once drops the process order.**

```clojure
(def h2 (h/history
          [{:process 0, :type :invoke, :f :txn, :value [[:append 0 1]]}
           {:process 0, :type :ok, :f :txn, :value [[:append 0 1]]}
           {:process 0, :type :invoke, :f :txn, :value [[:r 0 nil]]}
           {:process 0, :type :ok, :f :txn, :value [[:r 0 []]]}]))
(la/check {:consistency-models [:strong-session-snapshot-isolation]} h2)
;; Elle: invalid, G-single-item-process
(la/check {:consistency-models [:strong-session-snapshot-isolation :strong-read-uncommitted]} h2)
;; Elle: valid   expected: invalid
```

`additional-graphs` (txn.clj:676-698) adds only `realtime-graph` once any realtime anomaly is
reportable. The cycle becomes G-single-item-realtime, which strong session SI doesn't prohibit,
and the `strong-session-*-cycle-exists` subgraphs (txn.clj:330-337) need the process edges now
absent. The same for `:strong-session-serializable`.

- [ ] **D3: the process order skips `:info` transactions.**

```clojure
(def h3 (h/history
          [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil]]}
           {:process 0, :type :ok, :f :txn, :value [[:r 0 [1]]]}
           {:process 0, :type :invoke, :f :txn, :value [[:append 0 1]]}
           {:process 0, :type :info, :f :txn, :value [[:append 0 1]]}]))
(la/check {:consistency-models [:strong-session-read-committed]} h3)
;; Elle: valid   expected: invalid (G1c-process if the :info append committed, G1a if not)
(la/check {:consistency-models [:strong-read-committed]} h3)
;; Elle: invalid, G1c-realtime (the realtime order does reach :info)
```

`process-graph` links only `:ok` ops (core.clj:301); `realtime-graph` links `:info` completions
(core.clj:412-415). With a third transaction, strong session serializable passes a G0-process
(results/cases.txt, `process-order-skips-info`).

- [ ] **D4: a failed append inside a read hides the write-write edge.**

```clojure
(la/check {:consistency-models [:read-uncommitted]}
          (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:append 0 1] [:append 1 2]]}
             {:process 0, :type :ok, :f :txn, :value [[:append 0 1] [:append 1 2]]}
             {:process 1, :type :invoke, :f :txn, :value [[:append 0 2]]}
             {:process 1, :type :fail, :f :txn, :value [[:append 0 2]]}
             {:process 2, :type :invoke, :f :txn, :value [[:append 0 3] [:append 1 1]]}
             {:process 2, :type :ok, :f :txn, :value [[:append 0 3] [:append 1 1]]}
             {:process 3, :type :invoke, :f :txn, :value [[:r 0 nil]]}
             {:process 3, :type :ok, :f :txn, :value [[:r 0 [1 2 3]]]}
             {:process 4, :type :invoke, :f :txn, :value [[:r 1 nil]]}
             {:process 4, :type :ok, :f :txn, :value [[:r 1 [1 2]]]}]))
;; Elle: valid (it reports G1a and a dirty update, which read uncommitted allows)
;; expected: invalid, G0 in every interpretation (W -ww-> U on x, U -ww-> W on y)
```

The write index is built over `h/possible` (list_append.clj:603-611), which has no failed ops.
`ww-mop-dep` (537-548) asks who wrote the element just before U's, gets the failed transaction's,
which isn't in the index, and adds no edge.

- [ ] **D6: rw-register's dependencies use only each transaction's first read of a key.**

```clojure
;; a fuzzy read
(def h6a (h/history
           [{:process 0, :type :invoke, :f :txn, :value [[:w 0 1]]}
            {:process 0, :type :ok, :f :txn, :value [[:w 0 1]]}
            {:process 1, :type :invoke, :f :txn, :value [[:w 0 2]]}
            {:process 1, :type :ok, :f :txn, :value [[:w 0 2]]}
            {:process 2, :type :invoke, :f :txn, :value [[:r 0 nil] [:r 0 nil]]}
            {:process 2, :type :ok, :f :txn, :value [[:r 0 1] [:r 0 2]]}]))
(rr/check {:consistency-models [:repeatable-read]} h6a)      ; Elle: valid                   expected: invalid, G-single in every interpretation
(rr/check {:consistency-models [:consistent-view]} h6a)      ; Elle: valid                   expected: invalid
(rr/check {:consistency-models [:snapshot-isolation]} h6a)   ; Elle: invalid, :internal only

;; a G1c through a second read
(rr/check {:consistency-models [:read-committed]}
          (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil] [:w 1 1]]}
             {:process 1, :type :invoke, :f :txn, :value [[:r 1 nil] [:r 1 nil] [:w 0 2]]}
             {:process 0, :type :ok, :f :txn, :value [[:r 0 2] [:w 1 1]]}
             {:process 1, :type :ok, :f :txn, :value [[:r 1 nil] [:r 1 1] [:w 0 2]]}]))
;; Elle: valid   expected: invalid, G1c in every interpretation
```

The fuzzy read is reported only as `:internal` (rw_register.clj:77-101), which repeatable read
doesn't prohibit (consistency_model.clj:479-481). `wr-graph` (rw_register.clj:833-877) indexes
`txn/ext-reads` (jepsen.txn txn.clj:51-64), each key's first read only; the namespace docstring's
first rule (rw_register.clj:14) covers every read.

- [ ] **D7: rw-register drops the self-edge of a transaction reading its own later write.**

```clojure
(rr/check {:consistency-models [:strict-serializable]}
          (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil] [:w 0 1]]}
             {:process 0, :type :ok, :f :txn, :value [[:r 0 1] [:w 0 1]]}]))
;; Elle: valid   expected: invalid, no interpretation (list-append reports it as :future-read)
```

`wr-graph` adds the self-loop (rw_register.clj:859), and `strongly-connected-components` drops
singleton components (graph.clj:376).

- [ ] **D9: closed-predicate's `ww-graph` matches `:write` where everything else uses `:w`.**

```clojure
(def h9 (h/history
          [{:process 0 :type :invoke :f :init :value {0 0, 1 0}}
           {:process 0 :type :ok :f :init :value {0 0, 1 0}}
           {:process 1 :type :invoke :f :txn :value [[:w 1 1]]}
           {:process 1 :type :ok :f :txn :value [[:w 1 1]]}
           {:process 2 :type :invoke :f :txn :value [[:r 1 nil] [:r 0 nil]]}
           {:process 2 :type :ok :f :txn :value [[:r 1 1] [:r 0 nil]]}]))
(cp/check {:consistency-models [:serializable]} h9)         ; Elle: valid   expected: invalid, G-single (a read skew)
(cp/check {:consistency-models [:snapshot-isolation]} h9)   ; Elle: valid   expected: invalid
```

`(case f (:insert :write :delete)` at closed_predicate.clj:663; every other function spells it
`:w` (128, 178, 210, 805), so writes get no write-write edges. With the one-word fix Elle reports
G-single-item, and its 15 closed-predicate tests still pass. Our SDK writes `["w", k, v]`, so every
closed-predicate run of ours was judged without those edges until our service's fix.

- [ ] **D10: closed-predicate's `versions-after` discards its unborn branch (a misplaced paren).**

```clojure
(cp/check {:consistency-models [:snapshot-isolation]}
          (h/history
            [{:process 0 :type :invoke :f :init :value {0 0, 1 0}}
             {:process 0 :type :ok :f :init :value {0 0, 1 0}}
             {:process 1 :type :invoke :f :txn :value [[:delete 1]]}
             {:process 1 :type :ok :f :txn :value [[:delete 1]]}
             {:process 2 :type :invoke :f :txn :value [[:rp [:= 0] nil] [:r 1 nil]]}
             {:process 2 :type :ok :f :txn :value [[:rp [:= 0] {}] [:r 1 nil]]}]))
;; Elle: valid   expected: invalid, G-single (T2 -rwp-> init -ww-> T1 -wr-> T2)
```

The `if` at closed_predicate.clj:271-274 closes before the `loop` at 276, so its value is thrown
away; the loop returns `nil` for unborn on keys that init created, and `rw-graph` (519-539) adds no
rwp edge. The paren fix alone makes Elle's own `failure-to-observe-test` throw "Explainer": the
whole fix needs D11's too.

- [ ] **D12: list-append's version order among incompatible reads follows Clojure's hash-set
  order.** Two histories that differ only in x's values 1 and 2 swapped:

```clojure
(def h12a (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:append 0 1] [:append 1 4]]}
             {:process 0, :type :ok, :f :txn, :value [[:append 0 1] [:append 1 4]]}
             {:process 1, :type :invoke, :f :txn, :value [[:append 0 2] [:append 1 3]]}
             {:process 1, :type :ok, :f :txn, :value [[:append 0 2] [:append 1 3]]}
             {:process 2, :type :invoke, :f :txn, :value [[:r 0 nil]]}
             {:process 2, :type :ok, :f :txn, :value [[:r 0 [1]]]}
             {:process 3, :type :invoke, :f :txn, :value [[:r 0 nil]]}
             {:process 3, :type :ok, :f :txn, :value [[:r 0 [2]]]}
             {:process 4, :type :invoke, :f :txn, :value [[:r 1 nil]]}
             {:process 4, :type :ok, :f :txn, :value [[:r 1 [3 4]]]}]))
(def h12b (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:append 0 2] [:append 1 4]]}
             {:process 0, :type :ok, :f :txn, :value [[:append 0 2] [:append 1 4]]}
             {:process 1, :type :invoke, :f :txn, :value [[:append 0 1] [:append 1 3]]}
             {:process 1, :type :ok, :f :txn, :value [[:append 0 1] [:append 1 3]]}
             {:process 2, :type :invoke, :f :txn, :value [[:r 0 nil]]}
             {:process 2, :type :ok, :f :txn, :value [[:r 0 [2]]]}
             {:process 3, :type :invoke, :f :txn, :value [[:r 0 nil]]}
             {:process 3, :type :ok, :f :txn, :value [[:r 0 [1]]]}
             {:process 4, :type :invoke, :f :txn, :value [[:r 1 nil]]}
             {:process 4, :type :ok, :f :txn, :value [[:r 1 [3 4]]]}]))
(la/check {:consistency-models [:read-uncommitted]} h12a)   ; Elle: invalid, G0   expected: invalid, no interpretation
(la/check {:consistency-models [:read-uncommitted]} h12b)   ; Elle: valid         expected: invalid, no interpretation
```

Each key's set of read values becomes a Clojure hash set (`datafy`, bifurcan-clj core.clj:96-101),
sorted by length, stably (list_append.clj:316); `append-index` takes the last one (`peek`, 410) as
the version order. Among incompatible reads of equal length, the hash order picks it.

- [ ] **D13 (a TODO in the code): rw-register ignores `:info` writes.**

```clojure
(rr/check {:consistency-models [:strict-serializable]}
          (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil]]}
             {:process 0, :type :ok, :f :txn, :value [[:r 0 1]]}
             {:process 0, :type :invoke, :f :txn, :value [[:w 0 1]]}
             {:process 0, :type :info, :f :txn, :value [[:w 0 1]]}]))
;; Elle: valid   expected: invalid (G1c-realtime if the :info write committed, G1a if not)
```

`ext-index` indexes only `:ok` ops; its docstring says "TODO: we fail to index external writes of
type :info. That's bad." (rw_register.clj:170-173). list-append catches the same history (D3's
`h3`, `:strong-read-committed`).

- [ ] **D14: rw-register's `:transaction-order`: an `:info` write placed between two `:ok` writes
  hides their write-write edge.**

```clojure
(rr/check {:consistency-models [:strict-serializable] :transaction-order {3 0, 5 1, 1 2}}
          (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:w 0 2]]}
             {:process 0, :type :ok, :f :txn, :value [[:w 0 2]]}
             {:process 0, :type :invoke, :f :txn, :value [[:w 0 3]]}
             {:process 0, :type :ok, :f :txn, :value [[:w 0 3]]}
             {:process 1, :type :invoke, :f :txn, :value [[:w 0 1]]}
             {:process 1, :type :info, :f :txn, :value [[:w 0 1]]}]))
;; Elle: valid   expected: invalid, G0-realtime in every interpretation (3 precedes 2: T1 -ww-> T0)
;; controls: the :info op made :ok, made :fail, or removed: Elle reports it
```

`key-writes-version-sorted` (rw_register.clj:210-232) keeps `:ok` and `:info` writes, so
`transaction-order-graphs` (234-253) links 3 → 1 → 2, and `version-graphs->transaction-graph`
(704-735) relates the writers of each direct version edge only. `ext-index` (164-182) doesn't index
the `:info` writer of 1, so no edge between the two `:ok` transactions remains.

- [ ] **D20: closed-predicate names a cycle with one item and one predicate anti-dependency G2,
  not G2-item, so repeatable read passes it.**

```clojure
(def h20 (h/history
           [{:process 0 :type :invoke :f :init :value {1 1, 2 0}}
            {:process 0 :type :ok :f :init :value {1 1, 2 0}}
            {:process 1 :type :invoke :f :txn :value [[:r 2 nil] [:w 1 3]]}
            {:process 2 :type :invoke :f :txn :value [[:rp [:= 1] nil] [:delete 2]]}
            {:process 1 :type :ok :f :txn :value [[:r 2 0] [:w 1 3]]}
            {:process 2 :type :ok :f :txn :value [[:rp [:= 1] {1 1}] [:delete 2]]}]))
(cp/check {:consistency-models [:repeatable-read]} h20)   ; Elle: valid   expected: invalid, G2-item
(cp/check {:consistency-models [:serializable]} h20)
;; Elle: invalid, G2, steps [[:rwp 1 1 3] [:rw 2 0 :elle/dead]]
;; control: [:r 1 nil]/[:r 1 1] in place of the predicate read: G2-item, repeatable read invalid
```

The cycle explainer names any cycle with a predicate edge G2 (txn.clj:496-521), and the G2-item
search projects out `rwp` (543-608), so it can't find this cycle. Adya's G2-item is a cycle with
one or more item anti-dependency edges (thesis §3.2.4), which Elle's repeatable read prohibits
(consistency_model.clj:479-481).

- [ ] **D21: closed-predicate: a predicate read's rows give no item anti-dependency.**

```clojure
(cp/check {:consistency-models [:strict-serializable]}
          (h/history
            [{:process 0 :type :invoke :f :init :value {0 0, 1 0}}
             {:process 0 :type :ok :f :init :value {0 0, 1 0}}
             {:process 1 :type :invoke :f :txn :value [[:w 0 1]]}
             {:process 1 :type :ok :f :txn :value [[:w 0 1]]}
             {:process 2 :type :invoke :f :txn :value [[:rp :true nil]]}
             {:process 2 :type :ok :f :txn :value [[:rp :true {0 0, 1 0}]]}]))
;; Elle: valid   expected: invalid, G-single-realtime (T2 read key 0 = 0 after T1 installed 1)
;; control: [:r 0 0] added to T2: G-single-item-realtime
```

The namespace docstring (closed_predicate.clj:6-9) says the versions a predicate read covers
"also appears as a non-predicate read or write in the history: these are *item* dependencies".
`rw-graph` (486-542) gives a predicate read only `rwp` edges to versions that change its match;
under `:true` no write changes it, and the rows yield no item edge.

- [ ] **D22: closed-predicate explains an `:info` operation's unknown read as a read of
  `:elle/dead`.**

```clojure
(cp/check {:consistency-models [:consistent-view]}
          (h/history
            [{:process 0, :type :invoke, :f :init, :value {1 0, 2 0}}
             {:process 0, :type :ok, :f :init, :value {1 0, 2 0}}
             {:process 3, :type :invoke, :f :txn, :value [[:insert 0 2] [:w 1 3] [:r 2 nil]]}
             {:process 3, :type :info, :f :txn, :value [[:insert 0 2] [:w 1 3] [:r 2 nil]]}
             {:process 5, :type :invoke, :f :txn, :value [[:rp [:= 0] nil] [:r 0 nil] [:delete 2]]}
             {:process 5, :type :ok, :f :txn, :value [[:rp [:= 0] {}] [:r 0 nil] [:delete 2]]}]))
;; Elle: valid   expected: invalid, G-single (T3 -wrp-> T5 -rw-> T3)
;; without T3's [:r 2 nil]: Elle reports G-single-item
```

The WR explainer's item path (closed_predicate.clj:545-562) reads `b`'s `:r` mops whatever `b`'s
type. An `:info` op holds its invocation's `nil`, which `resolve-version` (300-318) turns into
`:elle/dead`, the value T5 wrote. So T5 → T3 is explained as `wr`, the cycle classifies as G1c, the
G-single search drops it on type (txn.clj:790-795), and G1c's projection has no edge T5 → T3.

## A false positive

- [ ] **D5: list-append treats an observed `:info` write as committed.**

```clojure
(la/check {:consistency-models [:read-uncommitted]}
          (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:append 0 1] [:r 0 nil]]}
             {:process 0, :type :ok, :f :txn, :value [[:append 0 1] [:r 0 [2 1]]]}
             {:process 0, :type :invoke, :f :txn, :value [[:append 0 2] [:append 0 3]]}
             {:process 0, :type :info, :f :txn, :value [[:append 0 2] [:append 0 3]]}]))
;; Elle: invalid, G0, cycle [1 3 1], steps [:ww :ww]
;; expected: valid (the :info transaction can't have committed: [2 3] and [2 1] aren't on one
;; trace; aborted, it leaves only G1a and a dirty update, which read uncommitted allows)
```

list-append builds its edges over `h/possible` (list_append.clj:603), treating `:info` writes as
committed. The paper's Theorem 1 claims cycles only for clean interpretations, but `result-map`
(txn.clj:1003-1028) still reports the G0.

## Exceptions

- [ ] **D8: list-append throws on a garbage read**, which the README lists as an anomaly to report.

```clojure
(la/check {:consistency-models [:strict-serializable]}
          (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil]]}
             {:process 0, :type :ok, :f :txn, :value [[:r 0 [7]]]}]))
;; Elle: throws AssertionError "Assert failed: No transaction wrote 0 = 7"
;; expected: invalid, a garbage read (no interpretation)
```

`dirty-update-cases` asserts that every element was written (list_append.clj:450-451). Real Elle
threw it on 1,581 of 2,550 random runs with garbage reads.

- [ ] **D15: jepsen.history's pair index depends on chunking**: a process invoking twice throws
  `double-invoke` within one 16,384-op chunk and goes unnoticed across chunks (malformed histories
  only).

```clojure
(def ops [{:process 0 :type :invoke :f :txn :value [[:append 0 1]]}
          {:process 0 :type :invoke :f :txn :value [[:append 0 2]]}
          {:process 0 :type :ok :f :txn :value [[:append 0 2]]}])
(la/check {:consistency-models [:serializable]} (h/history ops))
;; throws :jepsen.history/double-invoke, as documented
;; the same two invocations at indices 16,383 and 16,384 of a longer history (one chunk each):
;; no double-invoke; the first invocation pairs with nothing, and Elle throws D8's AssertionError
```

`pair-index-fold`'s reducer checks a double invoke only against its own chunk's tail
(history.clj:430-440); the combiner merges tails last-write-wins (466-498), overwriting an open
invocation from an earlier chunk. Folds run over 16,384-op chunks (fold.clj:115-150).

## A false explanation

- [ ] **D11: closed-predicate's `version<` is true whenever its first version exists.** On D10's
  history with the paren fix, the reported cycle is real, but its explanation names a false
  version order.

```clojure
;; D10's history, closed_predicate.clj with D10's paren fix alone:
(cp/check {:consistency-models [:snapshot-isolation]} h10)
;; Elle: invalid, G-single; the step T2 -> init explained as
;;   {:type :rwp, :key 1, :value :elle/dead, :value' 0}
;; expected: key 1's versions are [0 :elle/dead]: 0 comes first
```

`version<` (closed_predicate.clj:285-299) is a `loopr`; when the versions run out it returns its
accumulator `found-a?`. `RWExplainer` (449-471) relies on it.

## No verdict change

G1a reported for a dirty update; a cycle recorded under another anomaly type (G1c-realtime never
named); the `:GSIb`/`:G-SIb` spelling mismatch in the lattice; lost update implying G2-item rather
than G-single-item; the timeout fallback searching the wrong graph; the README demo rejected by
jepsen.history 0.1.9.

## Fixes written and checked (round 3, REPORT-3.md)

Each a patch on the deployed namespaces, checked over every interpretation of 40,000 histories
(no new false positive, no lost verdict, no exception), on real Elle's minimal histories, against
the Lean replica on random cases, and with Elle's suite:
- **Safe:** D7 (a read of the transaction's own later write: `:future-read`), D1 (G-singles
  through appends nobody read: a second cycle search, some anomaly names change), D21 (predicate
  rows as item reads), D8 (garbage reads: `:garbage-read`, no crash), D6 (every external read;
  `:fuzzy-read`), D22, D20 (mixed item and predicate cycles), D5 with D4 (an `:info` writer may
  have aborted, for models allowing G1a), D2 (the process order beside a real-time model).
- **Not safe alone:** D4 (3 new false positives in 40,000 without D5).
- **Not strictly safe:** D12 (deterministic now, but 1 lost verdict in 40,000; a refinement is
  proposed).
- **Safe only compiled ahead of time:** D15 (jepsen.history's pair index across chunks).

## Fixed in our service (checkers/elle, platform next 3810980)

Elle's own code, as patched namespaces loaded ahead of its jar, each checked over every
interpretation of the replica's histories (no new false positive), on Elle and with its suite:
D3 (process order through `:info`, and no real time into `:info` completions for models allowing
G1a, which removes D5's false positives), D9, D10 with D11, D13 with D14. Our service's own: D16
(`not` after deduplication), D17 (deduplication hid an anomaly), D19 (per-key predicate reads).
D18 (our strict-serializable-per-key is stricter than its stated "serializable, each key
linearizable", as YDB's own suite is): the user kept the stricter reading; its description now
says so, and a failure under it is reported with that note.

Found in round 3 in our own fix, **D23**: the deployed D3 fix (no real time into `:info`
completions for models allowing G1a) loses some strong read uncommitted verdicts Elle 0.2.8
reached through an `:info` transaction (105 of 1,152,552 timelines of round 1's E2 space):

```clojure
(la/check {:consistency-models [:strong-read-uncommitted]}
          (h/history
            [{:process 0, :type :invoke, :f :txn, :value [[:r 0 nil] [:append 0 1]]}
             {:process 0, :type :ok, :f :txn, :value [[:r 0 [2]] [:append 0 1]]}
             {:process 0, :type :invoke, :f :txn, :value [[:r 0 nil] [:append 0 2]]}
             {:process 0, :type :ok, :f :txn, :value [[:r 0 [3 4]] [:append 0 2]]}
             {:process 0, :type :invoke, :f :txn, :value [[:append 0 3] [:append 0 4]]}
             {:process 0, :type :info, :f :txn, :value [[:append 0 3] [:append 0 4]]}]))
;; Elle 0.2.8: invalid, G0-realtime   our service: valid   expected: invalid in every interpretation
```

The `:info` transaction can't have committed (its `[3 4]` and the first's `[2]` aren't on one
trace), so 2 precedes 1: T1 -ww-> T0, with real time T0 → T1. D5's extended fix restores it.

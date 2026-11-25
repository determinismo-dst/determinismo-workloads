# Elle findings not reported upstream

From the Lean replica of Elle (jepsen-io/elle main 4e359e5, one commit after v0.2.8; rounds 1 and 2,
blind; REPORT.md and REPORT-2.md have each history, verdict and code path). Every one was reproduced by running the real
Elle on the minimal history (results/cases.elle.edn). jepsen-io/elle's issues were searched on
2026-11-25: none matches.

## Wrong verdicts: Elle passes a history that violates the model

- [ ] **D1: an unread append becomes an anti-dependency, so a G-single is reported as G2-item.**
  Snapshot isolation and consistent view pass a history with a G-single in every interpretation
  (list-append; rw-register the same through its "nil first" rule).
- [ ] **D2: asking for two models at once drops the process order.** Strong session SI fails a
  history alone and passes it with strong read uncommitted beside it.
- [ ] **D3: the process order skips `:info` transactions.** Strong session read committed and
  serializable miss session violations through an indeterminate write that was read
  (core.clj:301).
- [ ] **D4: a failed append inside a read hides the write-write edge.** Read uncommitted passes a G0.
- [ ] **D6: rw-register's dependencies use only each transaction's first read of a key.** A fuzzy
  read passes repeatable read; a G1c through a second read passes read committed.
- [ ] **D7: rw-register drops the self-edge of a transaction reading its own later write.** Every
  model accepts it (list-append reports it as a future read).
- [ ] **D9: closed-predicate's `ww-graph` matches `:write` where everything else uses `:w`**
  (closed_predicate.clj:663, checked). Writes get no write-write edges; serializable passes a read
  skew. The one-word fix catches it, and Elle's 15 closed-predicate tests still pass. Our SDK
  writes `["w", k, v]`, so every closed-predicate run of ours was judged without those edges.
- [ ] **D10: closed-predicate's `versions-after` discards its unborn branch (a misplaced paren,
  closed_predicate.clj:271-276, checked).** A predicate anti-dependency is missed; SI passes. The
  paren fix catches it, but alone it breaks Elle's own `failure-to-observe-test`: the edge it
  adds from a predicate read of an unborn key to the init transaction, in a realtime cycle,
  makes the RW explainer throw "Explainer" (its predicate path's `version<` cannot order
  `:elle/unborn`, which is never in a key's versions). A whole fix needs the explainer too.
- [ ] **D12: list-append's version order among incompatible reads follows Clojure's hash-set
  order.** Renaming two values flips the read-uncommitted verdict.
- [ ] **D13 (a TODO in the code): rw-register ignores `:info` writes** (rw_register.clj:170-173).
  Strict serializable passes a read of a later indeterminate write.

## A false positive

- [ ] **D5: list-append treats an observed `:info` write as committed.** It rejects read
  uncommitted where the interpretation with that transaction aborted is allowed.

## A crash and a false explanation

- [ ] **D8: list-append throws `AssertionError: No transaction wrote …` on a garbage read**
  (list_append.clj:450, checked), which the README lists as an anomaly to report. Real Elle threw
  it on 1,581 of 2,550 random runs with garbage reads.
- [ ] **D11: closed-predicate's `version<` is true whenever its first version exists.** An
  explanation names a false version order (the edge itself is real).

## No verdict change

G1a reported for a dirty update; a cycle recorded under another anomaly type (G1c-realtime never
named); the `:GSIb`/`:G-SIb` spelling mismatch in the lattice; lost update implying G2-item rather
than G-single-item; the timeout fallback searching the wrong graph; the README demo rejected by
jepsen.history 0.1.9.

## Round 2

- [ ] **D14: rw-register's `:transaction-order`: an `:info` write placed between two `:ok`
  writes hides their write-write edge.** Strict serializable passes a G0-realtime.
- [ ] **D15: jepsen.history's pair-index fold depends on chunking**: a process invoking twice
  throws `double-invoke` within one 16,384-op chunk and goes unnoticed across chunks (malformed
  histories only).
- [ ] **D20: closed-predicate names a cycle with one item and one predicate anti-dependency G2,
  not G2-item**, so repeatable read passes it.
- [ ] **D21: closed-predicate: a predicate read's rows give no item anti-dependency**: a stale
  `:true` read passes strict serializable.
- [ ] **D22: closed-predicate explains an `:info` operation's unknown read as a read of
  `:elle/dead`**: a G-single is misclassified and consistent view passes it.

## Fixed in our service (checkers/elle, platform next 3810980)

Elle's own code, as patched namespaces loaded ahead of its jar, each checked over every
interpretation of the replica's histories (no new false positive), on Elle and with its suite:
D3 (process order through `:info`, and no real time into `:info` completions for models allowing
G1a, which removes D5's false positives), D9, D10 with D11, D13 with D14. Our service's own: D16
(`not` after deduplication), D17 (deduplication hid an anomaly), D19 (per-key predicate reads).
D18 (our strict-serializable-per-key is stricter than its stated "serializable, each key
linearizable", as YDB's own suite is): the user kept the stricter reading; its description now
says so, and a failure under it is reported with that note.

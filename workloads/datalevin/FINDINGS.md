# Datalevin findings

Bugs found on Datalevin 1.2.10 that still hold in 1.2.11, the newest release. 1.2.11 was checked
by reading its source, not by running it.

## A leader's power loss loses writes it acknowledged

- What: after a power loss, the leader comes back without its last acknowledged writes and leads
  again. The promotion floor sees no lag, so nothing blocks it.
- Why: LMDB runs `:writemap :nosync`, and the WAL's applied LSN is committed inside LMDB. A power
  loss can keep the LSN's page but not the data it covers, so recovery skips WAL records that
  were never applied (`txlog-recovery-context`).
- 1.2.11: same code.

## The server that joins last can take the database for a key-value one

- What: every Datalog request to that server then fails (`No implementation of method:
  :init-max-eid ... KVLMDB`). If the cluster depends on it, no read is answered.
- Why: HA peers open the database on a joining server with `open-kv`, and the type of the first
  open is recorded for good (`effective-db-type`).
- 1.2.11: same code.

## A graceful stop (SIGTERM) of a busy server crashes it

- What: SIGSEGV or a glibc mutex assertion in LMDB's native code, within about two seconds of the
  stop.
- Why: the shutdown hook closes the LMDB environment while request threads still have
  transactions open.
- 1.2.11: probably still there. The shutdown hook and `close-store-resources!` are unchanged;
  `close-kv`'s own changes were not read.

## A power loss can leave the VERSION file empty

- What: the database never opens again ("Database requires migration").
- Why: `VERSION` is written with a plain `spit`; neither the file nor its directory is synced.
  The window is a database's first half minute, or an upgrade.
- 1.2.11: `write-version-file` is still a plain `spit`.

## A power loss can leave the control plane's snapshot unreadable

- What: that server's HA control plane never starts again. Each failed start leaves SOFAJRaft
  threads behind, until the server runs out of memory. Two such servers take the whole cluster
  down.
- Why: `save-fsm-snapshot!` writes the snapshot without syncing it before JRaft publishes it.
- 1.2.11: `save-fsm-snapshot!` still syncs nothing.

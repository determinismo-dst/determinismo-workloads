# Datalevin findings

Bugs found on 1.2.10 that still hold in 1.2.11, the newest release (2026-11-20). 1.2.11 was
checked by reading its source (master c992272 has the same `src/`), not by a hunt. The details
and the evidence are in [README.md](README.md#found).

## A leader's power loss loses writes it acknowledged

- What: after a power loss, the leader comes back without its last acknowledged writes and leads
  again; the promotion floor sees no lag.
- Why: LMDB runs `:writemap :nosync`, and the WAL's applied LSN is committed inside LMDB. A power
  loss can keep the LSN's page but not the data, so recovery skips WAL records it never applied
  (`txlog-recovery-context`).
- Seen: trial run 1137 timeline 1; hunt run 1145, 15 of 59 timelines; aws-hunt run 18.
- 1.2.11: same code.

## The server that joins last can take the database for a key-value one

- What: every Datalog request to that server then fails (`No implementation of method:
  :init-max-eid ... KVLMDB`).
- Why: HA peers open the database on a joining server with `open-kv`, and the first open's type
  is recorded for good (`effective-db-type`).
- Seen: hunt run 1145, all 59 timelines; timeline 35, no read answered for 50 minutes.
- 1.2.11: same code.

## A graceful stop (SIGTERM) of a busy server crashes it

- What: SIGSEGV or a glibc mutex assertion in LMDB's native code, 0.06 to 1.7 s after the stop.
- Why: the shutdown hook closes the LMDB environment while request threads still have
  transactions open.
- Seen: hunt run 1145 timelines 11 and 45; trial run 1137 timeline 0.
- 1.2.11: probably still there; the shutdown hook and `close-store-resources!` are unchanged
  (`close-kv`'s own changes not read).

## A power loss can leave the VERSION file empty

- What: the database never opens again ("Database requires migration").
- Why: `VERSION` is written with a plain `spit`, neither the file nor its directory synced.
- Seen: trial run 1108, all three servers. The window is a database's first half minute, or an
  upgrade.
- 1.2.11: `write-version-file` is still a plain `spit`.

## A power loss can leave the control plane's snapshot unreadable

- What: that server's HA control plane never starts again. Each failed start leaves SOFAJRaft
  threads behind until the server runs out of memory. Two such servers take the whole cluster
  down.
- Why: `save-fsm-snapshot!` writes the snapshot without syncing it before JRaft publishes it.
- Seen: hunt run 1145 timeline 6; aws-hunt run 18 timeline 49 (two servers, no read answered
  for 600 s after the faults).
- 1.2.11: `save-fsm-snapshot!` still syncs nothing.

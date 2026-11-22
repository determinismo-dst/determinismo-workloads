# Datalevin

[Datalevin](https://github.com/datalevin/datalevin) (1.2.10, 2026-10-28, EPL-2.0): a Datalog
database on LMDB, in Clojure, with its own WAL and, since 1.0, a consensus-lease
high-availability mode (`doc/ha.md`): one write leader per database, chosen through a lease in a
SOFAJRaft control plane, followers replaying the leader's WAL. Jepsen never analyzed it; it has
a Jepsen suite of its own (`jepsen/`), run in one JVM or against remote nodes, with kills,
pauses, partitions, clock skew, I/O stalls and full disks.

What determinismo adds: power losses (what was not synced is lost; partial persistence keeps
part of it), its WAL's and LMDB's and SOFAJRaft's files under them, thread pausing inside its
JVMs (the coverage agent on the code HA's safety runs through: `datalevin.ha`, `.server`,
`.tx_group`, `.txlog`, `.kv`, `.storage`, `.lmdb`, `.remote`, `.client`, `.protocol`, and
`com.alipay.sofa.jraft`; not the query engine, which doubled a server's start), and exploration
that returns to the moments where faults mattered.

## What it promises (doc/ha.md, doc/wal.md, 2026-11-05)

- One write leader per database at a time, admitting writes only under a lease it proved fresh
  (a stalled renewal stops writes within about two renew intervals).
- A write is acknowledged once the leader applied it under its lease and confirmed its LSN with
  the authority. With the default `:ha-max-promotion-lag-lsn 0`, "losing the only copy of an
  acknowledged write blocks automatic promotion instead of permitting a leader behind that
  floor": a failover never loses an acknowledged write.
- WAL `:strict` (HA's default): a transaction waits for the WAL segment's fsync.
- Clock skew past the budget pauses automatic failover rather than guessing.
- Explicit transactions find the leader across the known endpoints (`open-transact`); followers
  serve reads, possibly behind.

## Properties

| Kind | Message | Where | Threat |
|---|---|---|---|
| always | Elle finds no anomaly in the history (list-append, strict serializable) | host check | two leaders under overlapping leases, a promoted node behind an acknowledged write, a stale read through a deposed leader |
| always | every acknowledged append is in the final read | eventually (explicit transaction on the leader) | power losses (the WAL's fsync, LMDB's data file), a promotion behind the floor |
| sometimes | a transaction commits; the final reads reach the leader once faults stop | drivers, eventually | (the workload works under faults) |
| unreachable | the cluster answers once faults stop | eventually | a cluster that never elects again |

A transaction's failure is unknown (Elle's `:info`) unless Datalevin says it was refused before
it applied; none is counted definite yet.

## The system

| Node | What it runs |
|---|---|
| `dl1`, `dl2`, `dl3` | `datalevin.server` on 8898, the database `det` in HA mode (`node/datalevin_node.clj`), a SOFAJRaft voter on 7801, every one promotable. |
| `client` | the test program's commands, with Datalevin's remote client (resolved in the guest only). |

The HA options are Datalevin's own Jepsen suite's (`jepsen/src/datalevin/jepsen/remote.clj`,
`base-ha-opts`): a 1 s lease renewal, a 3 s lease, a 1 s clock-skew budget, promotion only fully
caught up, and a fencing hook that does nothing (`exit 0`), as the suite's: safety then rests on
the lease alone, which is the claim under test. The servers' clock skew stays under the budget
(800 ms at most): past it Datalevin pauses failover by design.

Faults: the servers' power losses (with partial persistence), kills, graceful stops, pauses,
partitions, clock skew. The client has none of its own.

## Found

- **Datalevin 1.2.10 HA: a leader's power loss loses writes it acknowledged, and it leads again
  without them** (trial run 1137, timeline 1, found blind; Elle: G2-item-realtime,
  incompatible-order). dl1 led from 440 s; at 464.13 s it lost power (partial persistence: 50 of
  its unsynced pages kept, the journal committed), came back at 464.48 s, reopened `det` at
  479.8 s and led again from 480 s. dl2 and dl3 refused writes meanwhile, as promised. But dl1
  now served the state of about 452 s: of key 48's 80 acknowledged appends, its read at 490.1 s
  had 34, the 46 acknowledged from 452.0 to 461.7 s gone (key 49: 7, to 463.0 s); every key of
  that window lost appends in the final reads. Not the WAL's durability: replayed to 463.4 s,
  dl1's WAL segment read the same through the page cache and with O_DIRECT (on the disk), and
  replayed to 470 s, after the power loss, it still held the lost appends' values. So recovery
  did not replay them. How, as far as we can tell from the code (the same on master,
  2026-11-05): with the WAL on, LMDB is opened `:writemap :nosync` (binding/cpp.clj); every
  LMDB commit writes the WAL commit marker, its applied LSN, into LMDB's own `kv-info`
  (binding/cpp/write.clj, `transact-commit-metadata*`); and recovery replays the WAL only from
  that marker (kv/txlog.clj, `txlog-recovery-context`). LMDB's dirty pages reach the disk in
  any order, so a power loss can keep the marker's page and not the data it covers: the WAL's
  records below the marker are skipped, the node's applied LSN claims them, and the promotion
  floor (`:ha-max-promotion-lag-lsn 0`, "losing the only copy of an acknowledged write blocks
  automatic promotion") sees no lag. Datalevin's Jepsen suite kills processes, which keeps the
  page cache, and has no power loss. Not in the tracker (searched power loss, crash recovery,
  commit marker, nosync, writemap, WAL replay; #228, LMDB corruption under `:nosync` before the
  WAL, is its background). Not reported. Found again by the first hunt (run 1145, 2 h): in 15 of
  its 59 timelines (timeline 2: dl1's power loss at 402.05 s, 1.2 to 3 s after the appends it
  lost were acknowledged).
  Reproduce: by search, `infra/hunts/datalevin-append.json` (seed 1, 600 s timelines) at build
  8f5695769484, once every 105 CPU-minutes; exactly, run 1145 timeline 2 (or trial run 1137
  timeline 1, build b239fc963d71): `determinismo bundle <run directory> 2 <out>`, then
  `cd <out> && determinismo explore --run . --branch 2` on a host of srv4's CPU model.
- **Datalevin 1.2.10 HA: the server that joins last can take the database for a key-value one
  for good, and then fails every Datalog request** (hunt run 1145, found blind). A server creates
  a database at its first open and records its type then (server.clj `open-server-store`,
  `transact-new-db`), and every later open takes the recorded type over the one asked
  (`effective-db-type`). The HA peers open their databases on a joining server as key-value
  (`{:type :open-kv, :db-name "det", :opts {:wal? true}}`). dl3, up last at 22.15 s, got dl1's
  such open first (23.34 s: "open det that exist? false"), so its system database records `det`
  as `:key-value`, dl1's and dl2's as `:datalog` (read from each node's system database at 700
  s of timeline 35); the node's own Datalog HA open at 23.44 s ("exist? true") was answered as
  opened. From then on dl3 holds `det` as a `KVLMDB`, and Datalog requests to it fail:
  `No implementation of method: :init-max-eid of protocol: #'datalevin.interface/IStore found
  for class: datalevin.kv.KVLMDB` (`db-info`, handlers.clj:1864), in all 59 timelines (the
  setup is theirs), and in timeline 35, where the cluster depended on dl3 once faults stopped,
  for the 50 minutes to the cap: no read answered. Not in the tracker (searched init-max-eid,
  KVLMDB, open-kv, database type). Not reported.
  Reproduce: the setup of `infra/hunts/datalevin-append.json` (any timeline shows the error on
  dl3); timeline 35 for the outage: `determinismo bundle <run directory> 35 <out>`.
- **Datalevin 1.2.10: a graceful stop (SIGTERM) of a busy server crashes it in LMDB's native
  code** (hunt run 1145 and trial run 1137, found blind): all three native crashes came 0.06 to
  1.7 s after a `stop` fault of that server, a SIGTERM as systemd or Kubernetes sends. Timeline
  11: dl1, restarted after a power loss, was opening `det` (the HA `:open`) when stopped at
  414.87 s; frozen at 414.90 s its JVM was shutting down (its `SIGTERM handler` threads, the
  shutdown hook's thread `Thread-3` loading its classes) while the opener's thread ran on; from
  414.95 s the hook (binding/cpp/lifecycle.clj `run-shutdown-close!`, the close storage.clj
  `create-new-store!` registers) closed the store (`close-store-resources!`, the KVLMDB, the
  txlog state: their coverage lines), and the opener's `mdb_txn_begin` met the closed
  environment: `Fatal glibc error: pthread_mutex_lock.c:130 (___pthread_mutex_lock): assertion
  failed: mutex->__data.__owner == 0` (its core: JNI `mdb_txn_begin` -> `mdb_txn_renew0` ->
  `pthread_mutex_lock`, no file of `det` mapped any more), then SIGSEGV and a core dump.
  Timeline 45: dl3 stopped at 403.04 s, SIGSEGV in `libdtlv.so` `mdb_page_search_root` 1.7 s
  later (a reader, `pool-6-thread-4`, and another thread faulting); trial run 1137 timeline 0:
  dl3 stopped at 408.44 s, SIGSEGV in "VM Periodic Task" 1.0 s later. LMDB requires every
  transaction closed before `mdb_env_close`; the hook waits for none, and nothing stops the
  server's threads first. Known in part: Datalevin #347 (2025-11, "the DB had been closed while
  the sampler was still trying to read the DB", fixed for the sampler in b4bbaf4), not the
  shutdown hook's close under requests. Not reported.
  Reproduce: by search, the hunt below, once every 786 CPU-minutes; exactly, run 1145 timeline
  11 (`determinismo bundle`).
- **Datalevin 1.2.10: a power loss can leave a database's VERSION file empty, and the database
  never opens again: "Database requires migration"** (trial run 1108, all three servers, found
  blind). `datalevin.binding.cpp/open-kv` writes `VERSION` with a plain `spit`, the file and
  its directory never synced, when it creates a database (after LMDB's `data.mdb`) or opens
  one another version wrote. LMDB syncs `data.mdb`, and that commit carries the new file's
  creation through ext4's journal while its data waits for writeback. A power loss in between
  keeps an empty (or no) `VERSION` beside a whole `data.mdb`, and every open after takes it for
  a database from before versioning: "Database requires migration", the server exiting at
  start. In a replay of
  run 1108's timeline after its power losses, each server's `system/VERSION` and `646574/VERSION`
  (the database `det`) were 0 bytes, their `data.mdb` whole. A machine's flusher writes the file
  back within about 30 s of its creation, so the window is a fresh database's first half minute
  (or an upgrade's). Same code on master (2026-11-05). Not in the tracker (searched
  "requires migration", "VERSION file", fsync). Not reported. The servers model a 30 s flusher
  since (`:writeback-s`), and the exit is counted as known.
  Reproduce: exactly, trial run 1108 timeline 0 (build bfbc74dae2d7; its program and image kept
  with the run): `determinismo bundle <run directory> 0 <out>`, then `cd <out> && determinismo
  explore --run . --branch 0`. The hunt's faults rarely reach a database's first half minute
  (none of run 1145's 59 timelines).

- **Datalevin 1.2.10 HA: a follower bootstrapping from a snapshot holds the leader's whole
  database file in its heap, and runs out of memory once the file outgrows it** (hunt run 1145,
  timeline 17; found blind). dl2's `OutOfMemoryError: Java heap space` at 677.8 to 683.1 s
  (`-Xmx1100m`). At 660.000 s its heap (infra/host/heap.sh with HeapRefs.java, dumped with its
  unreachable objects) held 973 MB in 15,575 byte arrays of 65,536 bytes (`c/+buffer-size+`),
  zeroed (the data file's unused pages), all in one Clojure transient vector; and its threads at
  that moment (`det:threads dl2`) had the HA follower sync loop inside `datalevin.client/copy-out`
  (client.clj:849), called from `remote KVStore.copy` (remote.clj:1287), from
  `fetch-ha-endpoint-snapshot-copy!` (ha/replication.clj:2039), from
  `bootstrap-ha-follower-from-snapshot`. The path, in the source: the leader streams its data
  file in 64 KB chunks (`copy-file-out`, server/copy.clj, one buffer reused); the follower's
  `copy` writes the file only after `cl/request` returns, and the request's `copy-out` collects
  every chunk into one transient vector until `:copy-done`, so a follower needs a heap larger
  than the leader's whole data file. Here the copy ran out of its time budget at 660 s
  (`check-budget!` throwing in `receive`), its gigabyte dropped (the full GC every dump after it
  met), and the follower's next attempt filled the heap again. Still so on master (2026-11-06).
  Not in the tracker (searched copy OutOfMemoryError, snapshot copy memory, copy-out,
  binary-chunks). Not reported.
  Reproduce: `determinismo bundle <run 1145's directory> 17 <out>`, then in it `determinismo
  explore --run . --branch 17`; its threads at the moment: `infra/host/moment.sh 1145 17 660000
  'det:threads dl2'`.

- **Datalevin 1.2.10 HA: a power loss soon after its control plane snapshots leaves the snapshot
  unreadable, and the server's control plane never starts again; each attempt leaves a SOFAJRaft
  node's threads behind, until the server runs out of memory** (hunt run 1145, timeline 6;
  found blind). dl1 lost power at 256.18 and 257.50 s; from 273 s to the end (3,189 s) its HA
  control plane failed to start, 1,500 "Fail to init" lines, each after "HA control JRaft FSM
  snapshot load failed" (`snapshot_866`): `Thaw failed. Possible decryption/decompression error,
  unfrozen/damaged data` (`load-fsm-snapshot!`, ha/control.clj:895). The snapshot is written
  unsynced (`save-fsm-snapshot!`: `u/dump-bytes`, a plain `Files/write` to a temporary file, then
  an atomic move into JRaft's snapshot directory, which JRaft publishes), so after a power loss
  the published snapshot's file can hold what was never synced. The server stays out of the HA
  group for good. And at 1,630 s its JVM had 433 each of `JRaft-NodeImpl`, `JRaft-LogManager`
  and `JRaft-FSMCaller` threads (`det:threads dl1`; the JVM, its heap full, gave no stacks to
  SIGQUIT), its `OutOfMemoryError`s from 1,640 s on: a node's threads per failed start, left
  running (inferred from their count against the failed starts, not read in SOFAJRaft's source:
  a node whose init fails inside `createAndInitRaftNode` never reaches the service Datalevin
  shuts down). Still so on master (2026-11-06, `save-fsm-snapshot!` and `dump-bytes`). Not in
  the tracker (searched snapshot load failed, Thaw failed, Fail to init node, thread leak,
  control snapshot, fsync snapshot). Not reported. Two such losses take the whole cluster:
  in [aws-hunt run 18](https://determinismo-dst.github.io/determinismo-workloads/runs/18-aws/)
  (2026-11-22, c5.metal), timeline 49, dl2's and dl3's power losses at 677 to 681 s each cut its
  published `fsm-state.nippy` from 385 bytes to 0 (`snapshot_1342`, `snapshot_1425`: the power
  loss's own record of the files it changed, that file the only one), both control planes failed
  every start from 776 s on (816 times), and with two of three voters gone no read answered for
  the 600 s after the faults ("the cluster answers once faults stop"). Still written unsynced in
  1.2.11 and on master c992272 (2026-11-21).
  Reproduce: `determinismo bundle <run 1145's directory> 6 <out>`, then in it `determinismo
  explore --run . --branch 6`; its threads: `infra/host/moment.sh 1145 6 1630000 'det:threads dl1'`.

## Status

Open, from hunt run 1145 (59 timelines), each to explain before it is a finding or ours:

- Three timelines (6, 35, 46) ran to the 3,600 s cap without their scenario finishing: our final
  reads, retrying each key 30 times with no deadline over them, outlasted a cluster that never
  answered (ours, bounded since: 600 s); timeline 35's is the key-value finding above, 6's the
  control plane's snapshot above. The other `OutOfMemoryError`s (timelines 3, 13, 28) are the
  snapshot copy above: "HA follower sync loop crashed" inside `fetch-ha-endpoint-snapshot-copy!`.

Trials 1095 to 1116 (one timeline each) made it run under its faults, each fix ours:
- the servers' heap holds two argon2id logins at once (each 128 MiB, twice reserved in half the
  heap: at 512 MB none, at 640 MB one, its peers' logins refused as busy), and the servers keep
  C2: Bouncy Castle's argon2id takes 2.5 s a login under C1 only, 0.65 s with C2, and logins
  starved (a restarted server's own open of its HA database among them, its SOFAJRaft voter
  never started again: no leader);
- the servers' HA traffic logs in with their account (`:ha-client-credentials`, doc/ha.md: it
  defaults to the built-in password, and every peer's login failed);
- the setup waits for the cluster to take a write (the servers are ready once they listen,
  before their HA database opens): every timeline starts from a cluster with a leader;
- Datalevin compiled ahead of time, as a jar (the guest's image has its files at time 0, and
  Clojure took the classes of a directory for older than their sources: compiled at every
  start), and the coverage agent on the HA path only;
- the JDK's AOT cache for the drivers' JVMs, trained with the jars at time 0 (refused for their
  times otherwise): Datalevin's client loads in 6 s, 107 s before;
- drivers keep their slot through a server's restart (15 s of failed connections), connect
  without the schema (connecting transacted it), and the faults' quiet stretches last up to
  60 s (three servers restarted at once listened 27 s later).

- logins at one argon2id pass over 8 MiB in the test (our node rebinds Datalevin's defaults, four
  over 128 MiB, not configurable, before its server creates the account): three servers share
  the VM's one CPU where each has its own cores in production, a login took 0.65 s of it, and
  after the faults the servers' HA traffic to each other, logging in again as its requests timed
  out, kept two of them hashing (about 200 s of CPU in 230 s, every final read timed out): an
  overload sustaining itself, of the test's machine more than of Datalevin;
- each server's own open of its HA database every second on one client (a quorum forms while
  the voters' attempts overlap; spread out, no restarted voter ever rejoined), and faults in
  bursts of up to 5 s with up to 120 s quiet (a restarted server takes 30 to 40 s to listen,
  log in, rejoin, elect and lease).

Trial run 1116: the first transactions committed under faults (52 by 502 s); trial run 1137:
1,701 and 3,447 in its two timelines, both judged (the finding above in timeline 1; in timeline 0
dl3's JVM died of SIGSEGV in its VM Periodic Task thread, a core dump kept: next).

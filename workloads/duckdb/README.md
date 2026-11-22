# DuckDB under determinismo

DuckDB 2.0.1 (MIT), embedded as Jepsen's DuckDB test embeds it (jepsen-io/duckdb, an early
prototype of Kyle Kingsbury's): a local node (`local_node.py`, Python with DuckDB's package)
holds one database file on its node's own disk and serves transactions to the drivers, a DuckDB
connection each; and through 2.0's Quack client-server protocol (the `quack` profiles).

```
zig build duckdb-test
determinismo explore --kernel ~/guest/vmlinuz --initrd ~/guest/base.cpio --memory-mib 2048 \
  --program zig-out/bin/duckdb-test --scenario append --seed 1 --branches 64
```

Coverage: DuckDB is built from its release's source (PyPI's sdist, checksummed) by clang with
trace-pc-guard and the C SDK's callbacks, with Quack and httpfs built into the module at the
commits the release pins; their edges report themselves as source lines (the module unstripped
in /symbols) and are thread pausing's points. The nodes' Python and DuckDB's Python package: the
Python SDK's `coverage_start`. The profiles' coverage set holds both (`duckdb_test.zig`).

Assertions in DuckDB's own source (`assertions.patch`, applied before the build: assertions
only, DuckDB's behavior unchanged), each a property of every run:

- WAL replay's recovery paths, `sometimes`: a torn tail ignored; a checkpoint under way at the
  crash, and its outcomes (it had finished: its checkpoint WAL replayed; it had not: both WALs
  merged; a failed checkpoint's marker truncated); a WAL with no committed transaction
  truncated; committed transactions replayed.
- `unreachable`: a committed transaction failing WAL replay's second pass. That pass reads only
  up to the last commit boundary the first pass read whole, and a serialization error there is
  ignored: the transactions after it would be skipped without a word.
- `always`: commit ids only grow; the last commit id read before any commit is the bootstrap
  timestamp. DuckDB 2.0.0's `last_commit` had no initializer until its first commit, and a
  checkpoint before it read whatever the memory held (the assertion "the last commit id is read
  only after a commit set it" failed there); fixed by duckdb/duckdb PR #28066 ("Initialize
  last_commit at the bootstrap timestamp": a forced shutdown checkpoint on a reopened database
  left tables out), in 2.0.1.
- `sometimes`: a commit runs an automatic checkpoint, one beside other transactions, and a
  checkpoint finishing with commits in its checkpoint WAL (moved over the main WAL).

Elle checks each timeline at strong snapshot isolation, what Jepsen's test checks (DuckDB's
optimistic concurrency: each transaction reads its snapshot, and a conflict found at the commit
rolls it back; Jepsen saw it allow G2-item, so no more than snapshot isolation is asked):

| Scenario | Workload |
|---|---|
| `append` | Jepsen's list-append: tables append0..2 (a key's table k mod 3), a key's list a text (even keys) or a BIGINT[] (odd ones; Jepsen's INTEGER[] widened for our unique values), each append an `INSERT ... ON CONFLICT` or a `MERGE INTO`, each read by the primary key or the unindexed secondary one; once faults stop, every committed append in its key's list |
| `fkey_register` | Jepsen's fkey-register: a register behind a foreign key (`logical` maps a key to its `physical` row), each write updating the physical row in place or pointing the key at a fresh one; Elle's rw-register |
| `trigger` | DuckDB 2.0's triggers: statement triggers over transition tables (`REFERENCING NEW TABLE`, `OLD TABLE`) copy `ev`'s inserts into `ev_mirror` and its deletes out of it, a row trigger (`FOR EACH ROW`, `NEW.id`) copies `rows` into `rows_mirror` (2.0.0 refuses the two kinds on one table); every snapshot's mirrors hold their tables' rows, and once faults stop every committed insert is there with its copy and every committed delete gone from both |
| `variant` | DuckDB 2.0's `VARIANT`: a register (`variants`) whose values are variants of four shapes (an integer, a text, a list, a struct), drawn per write; Elle's rw-register on the values, and every read the shape its value was written with (`variant_typeof`) |

Profiles:

| Profile | Nodes |
|---|---|
| `default` | the embedded database, as Jepsen's test |
| `quack` | DuckDB 2.0's client-server protocol (Quack): the database file in a Quack server (`db`, `quack_server.py`: `quack_serve` over plain HTTP, one token), the drivers' connections Quack sessions from two client nodes (`c1`, `c2`, `local_node.py --quack db`: each connection its own DuckDB that `ATTACH`es the server and `CONNECT`s to it, Quack's recommended way). Faults on the server (power losses too), the clients and the links between |
| `quack-reconnects` | `quack` with Quack's reconnect support on (`quack_enable_reconnects`, server and clients) |

Each transaction draws how its values go: bound as a prepared statement's parameters (what
applications write) or written into its SQL as literals; and each Quack connection draws its
session: CONNECT-ed (the whole session routed to the server, Quack's recommended way) or the
server attached as the client's default catalog (`ATTACH ... AS qk; USE qk`: plans run in the
client, tables on the server). "A statement's bound parameters reach the database" judges every
reply where the session supports them, embedded and attached. A CONNECT-ed session refuses them
by design: DuckDB's fix for #27628 (merged 2026-10-22, after 2.0.0) kept "Parameterized prepared
statements cannot be executed while CONNECT-ed", where 2.0.0 says "Values were not provided for
the following parameters"; the node marks that refusal (`fail unsupported-while-connected`, an
event `duckdb_bound_refused_connected`), and Elle still judges that it applied nothing (2.0.0's
prepare could run a statement on the server: the same PR).

Checkpoints (the WAL folded into the database file) run under the faults in every scenario:
DuckDB checkpoints on its own once its WAL passes 16 MB, which a timeline never writes, so each
node start draws its `checkpoint_threshold` (16 MB, 1 MB, 64 KB or 8 KB, from
`$DETERMINISMO_DRAW`; its first output line says which), and a `checkpoint` driver beside the
workload asks for `CHECKPOINT`, now and then `FORCE CHECKPOINT` (which aborts the transactions
under way). The scenario's own properties judge what survives.

Every choice (keys, statements, columns, modes) is the driver's, drawn from the SDK. Outcomes:
`ok` with the reads; `fail` when nothing was applied (an error before the commit, a conflict at
it); `info` when the commit got no answer or another error. Faults: restarts, graceful stops and
power losses (DuckDB writes and syncs its WAL at each commit: a committed transaction must
survive the node's crash and the WAL's replay), and the default ones.

## Found

**Through an attached Quack catalog, a statement with bound parameters is refused** (the property
"a statement's bound parameters reach the database" fails: hunt run 1651, 107 timelines), "Values
were not provided for the following parameters: 1, 2", in 2.0.0 and in the 2.0.1 pre-release
(2.0.1.dev2610291258), checked outside determinismo against a Quack server on the Mac
(`INSERT INTO qk.t VALUES (?, ?)`, `SELECT * FROM qk.t WHERE id = ?`, in and out of a
transaction). Quack's documentation makes an attached server a full catalog, writes and
transactions forwarded, and names no limit on parameters; no issue tracks it (searched the
error text, "quack parameters", "ATTACH quack"; #27269, open, is CONNECT's prepare). Trial run
1211 (`quack`, append, 4 timelines, each connection's session drawn): the property failed in all
four, through attached sessions. Hunt run 1219 (`quack`, append, its first pass, 156 timelines):
in 138. Hunt run 1239 (`quack`, `trigger`, its first pass, 162 timelines): in 150. Not reported.
Run 1239 also met the WAL refusal below in 40 timelines, and in exactly those "the trigger tables
answer once faults stop" was reached (the server never opened the database again).

**A process crash loses a commit other transactions already read** (Elle, list-append under
strong snapshot isolation: G-single-item-realtime; hunt run 1950, `duckdb-append`'s first pass,
timeline 241 of 279). A transaction of two appends to key 29 (the workload's
`INSERT ... ON CONFLICT DO UPDATE SET val_list = list_append(...)`) was committing when another
connection's transaction read key 29, saw both values and committed; 10 ms later the node's
process was killed (a restart, not a power loss: the page cache keeps every write), and after
it the values were gone for good. Replays of the timeline: neither the WAL (1,348 bytes,
unchanged from 138.204 s through the kill) nor the database file ever held them; the files
copied at 138.208 s, after the read and before the kill, opened by DuckDB 2.0.0 on the Mac,
lack them. The cause, in 2.0.0's `DuckTransactionManager::CommitTransaction`: a commit whose
estimated size reaches `auto_checkpoint_skip_wal_threshold` (100,000 by default; this
two-value upsert reached it, its node's `checkpoint_threshold` drawn 8KB) skips the WAL and
relies on the automatic checkpoint that follows it, but publishes its rows (commit id set,
transaction lock released) before that checkpoint runs; a crash inside the checkpoint loses a
commit others have read. DuckDB's own `debug_checkpoint_abort` on the timeline's files shows
it: aborted before the header write or after the free-list write, the reopened database lacks
the values. `repro-visible-before-durable.py` reproduces it outside determinismo (2.0.0 on the
Mac: 22 of 50 kills right after a committed read saw the values lost them; 195 of 200 from the
timeline's own files). In the timeline the checkpoint was stretched by fsync stalls, and the
four restarts after the kill hung opening (no output, no error) until 182 s. main has since
gated new snapshots on durability (`GetDurableSnapshot`, WAL group commit 9f13f05370), but keyed
on `wal_sync_offset`, which a commit that skipped the WAL leaves at 0, counted as durable: **main
has it too.** The repro on main's pre-release build 2.1.0.dev2610310630 (71f47d410f, 2026-10-31,
the gate included) lost the values in 11 of 50 kills; main of 2026-11-13 (e6626e3a2a) changes
that file in 12 lines, none of them this rule or the skip-WAL path (only an exception for
buffered index replays and the error handling of a failed commit). No issue tracks it (searched the setting, "skip WAL", "visible before
durable", lost commits after a crash). Not reported.

**Ours: lost updates in `fkey_register` were write skew our writes allowed** (hunt run 1983, 37
timelines of Elle's lost-update at strong snapshot isolation). Of Jepsen's two writes, an update
of the physical row in place and a repoint of the logical key at a fresh row write disjoint rows:
DuckDB 2.0.0 commits both (checked natively, two connections interleaved: in place against in
place, "Conflict on update!"; repoint against repoint, "Conflict on tuple deletion!"; mixed, both
committed), as snapshot isolation allows, and on the key that is a lost update. The in-place write
now updates its logical row too (`SET physical_id = physical_id`), so any two writes of a key
conflict (all four mixes refused natively). jepsen-io/duckdb's workload has the same writes (its
README: "not polished yet").

## Observed

**A database that never opens again: "the WAL checkpoint iteration does not match the database
file" (trial run 1200, `quack-reconnects`, `trigger`, seed 2, timeline 3; probably duckdb#27465,
fixed after 2.0.0).** The Quack server (`checkpoint_threshold` drawn, the checkpoint driver
running, `FORCE CHECKPOINT` among its requests) lost power at 59.9 s, was restarted at 60.9 s
and 61.8 s, and from its start at 63.9 s every open failed: `IO Error: Failure while replaying
WAL file "/data/jepsen.duckdb.wal": This WAL was created for this database file, but the WAL
checkpoint iteration does not match the database file. ... File checkpoint iteration: 111, WAL
checkpoint iteration: 109`. The server stayed down to the end (its clients' connections a SYN
retried), so whatever the WAL held after the last checkpoint is out of reach. duckdb#27465
(closed 2026-11-05, PR #28274 on main: "Always rotate WAL at checkpoint start, even when
empty") is the same refusal from a forced checkpoint that starts with an empty WAL while a
transaction commits: the header advances, the WAL keeps the old iteration (there N+1 against N;
here two apart). 2.0.1 (2026-11-20) carries the fix (its backport 8845ee0bd), and the workload runs 2.0.1 since
2026-11-22: the srv4 campaign's first stretch on 2.0.0 met the refusal again after process
crashes alone, no power loss (run 4, timeline 7: file iteration 635, WAL 628). Since, the checkpoint driver
records each request (`duckdb_checkpoint`, forced or not). Hunt run 1203 (`quack`, `trigger`,
its first pass, about 150 timelines) met it in five incidents (timelines 4, 46, 52, 70 and 97,
and 144 forked from 52 at 291.8 s), each after forced checkpoints (2 to 47 completed). Timeline
144 replayed to 291.82 s, before its power loss, read the files from the guest's side: the
database's current header at iteration 31, the live WAL's version entry at 29 (field 103,
0x1d). The process was already writing into a WAL two checkpoints behind its header, so any
restart refuses it, power loss or not: #27465's mechanism (a checkpoint advancing the header
without rotating the WAL). Not reported.

## Credits

What this example tests, and how, comes from others' work:

- Jepsen (Kyle Kingsbury, jepsen.io): jepsen-io/duckdb's local node, its append and fkey-register
  workloads and their checks. Our code is written anew; none of Jepsen's is copied.
- Elle (Kyle Kingsbury and Peter Alvaro), which checks the histories.

# A commit that skips the WAL is visible before it is durable: a crash loses data other transactions already read

### What happens?

A transaction whose estimated size reaches `auto_checkpoint_skip_wal_threshold` skips the WAL and
relies on the automatic checkpoint that follows its commit. But `DuckTransactionManager::CommitTransaction`
publishes the commit (commit id set, commit lock released) before that checkpoint makes it durable.
Another connection can read the new rows and commit; if the process then dies during the
checkpoint (a plain process crash, SIGKILL, not a power loss), the reopened database does not
have them. A committed transaction that another transaction already read is lost.

On 2.0.0 the repro below loses the data in 22 of 50 kills; on main's pre-release
2.1.0.dev2610310630 (71f47d410f) in 11 of 50. Main's durable-snapshot gate (WAL group commit,
9f13f05370) does not cover this path: `GetDurableSnapshot` skips transactions whose
`wal_sync_offset` is 0, which is exactly what a commit that skipped the WAL has, so it counts as
durable. Today's main (e6626e3a2a) is unchanged there.

With default settings this takes a commit estimated at 100,000 or more (a bulk load) plus a crash
during the checkpoint after it. A small `checkpoint_threshold` makes any commit take the path; the
repro uses 8KB to hit it with a two-row upsert.

DuckDB's own `debug_checkpoint_abort` shows the same: with the checkpoint aborted before the
header write (or after the free-list write), the reopened database lacks the committed rows.

### To Reproduce

`pip install duckdb`, then `python3 repro.py <empty directory> [iterations]`. Each iteration
loads a table, forks a process that commits a two-row upsert while a reader thread in the same
process polls the row in its own transactions, and kills the process (SIGKILL) the moment a
reader transaction commits having seen the new values. The parent then reopens the database and
checks whether the values survived.

```python
import os
import shutil
import signal
import sys
import threading

import duckdb

work = sys.argv[1]
iterations = int(sys.argv[2]) if len(sys.argv) > 2 else 50
UPSERT = ("INSERT INTO append2 AS t (id, sk, val_list) VALUES (?, ?, [?]::BIGINT[]) ON CONFLICT (id) "
          "DO UPDATE SET val_list = list_append(t.val_list, ?) WHERE t.id = ?")
PAIR = (3096514530377888, 3096514530377889)
lost = kept = 0
for iteration in range(iterations):
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    path = os.path.join(work, "test.duckdb")
    seen = os.path.join(work, "seen")
    setup = duckdb.connect(path, config={"checkpoint_threshold": "8KB"})
    setup.execute("CREATE TABLE append2 (id INT NOT NULL PRIMARY KEY, sk INT NOT NULL, val_text TEXT, val_list BIGINT[])")
    for value in range(117):
        setup.execute(UPSERT, [29, 29, value, value, 29])
    setup.close()
    pid = os.fork()
    if pid == 0:
        db = duckdb.connect(path, config={"checkpoint_threshold": "8KB"})
        reader, writer = db.cursor(), db.cursor()

        def poll():
            while True:
                reader.execute("BEGIN TRANSACTION")
                values = reader.execute("SELECT val_list FROM append2 WHERE id = 29").fetchone()[0]
                reader.execute("COMMIT")
                if PAIR[0] in values:
                    # A committed transaction saw the new values: crash now.
                    open(seen, "w").close()
                    os.kill(os.getpid(), signal.SIGKILL)

        threading.Thread(target=poll, daemon=True).start()
        writer.execute("BEGIN TRANSACTION")
        for value in PAIR:
            writer.execute(UPSERT, [29, 29, value, value, 29])
        writer.execute("COMMIT")
        threading.Event().wait(5)
        os._exit(0)
    os.waitpid(pid, 0)
    if not os.path.exists(seen):
        continue
    values = duckdb.connect(path).execute("SELECT val_list FROM append2 WHERE id = 29").fetchone()[0]
    if PAIR[0] in values:
        kept += 1
    else:
        lost += 1
print(f"duckdb {duckdb.__version__}: {lost + kept} kills right after a committed read saw the new values; "
      f"after reopening, lost {lost}, kept {kept}")
```

Output:

```
duckdb 2.0.0: 50 kills right after a committed read saw the new values; after reopening, lost 22, kept 28
duckdb 2.1.0.dev2610310630: 50 kills right after a committed read saw the new values; after reopening, lost 11, kept 39
```

Expected: `lost 0`. Once a transaction that read the values has committed, a crash must not
remove them.

Where it happens: `DuckTransactionManager::CommitTransaction`
(src/transaction/duck_transaction_manager.cpp), the `skip_wal_write_due_to_checkpoint` path,
which publishes the commit before the checkpoint that makes it durable; and
`GetDurableSnapshot` in the same file, which treats `wal_sync_offset == 0` as durable. The
skip-WAL commit path came with #20918, which handled concurrent commits during that checkpoint
but not concurrent reads of the skip-WAL commit.

### OS:

macOS 15.1, arm64 (also seen on Linux x86_64)

### DuckDB Version:

2.0.0; main pre-release 2.1.0.dev2610310630 (71f47d410f)

### DuckDB Client:

Python

### Hardware:

Apple M3 Max

### Full Name:

<your name>

### Affiliation:

<your affiliation>

### What is the latest build you tested with? If possible, we recommend testing with the latest nightly build.

I have tested with a nightly build (2.1.0.dev2610310630, main as of 2026-10-31; main's code on
this path is unchanged since)

### Did you include all relevant data sets for reproducing the issue?

Yes

### Did you include all code required to reproduce the issue?

- [x] Yes, I have

### Did you include all relevant configuration (e.g., CPU architecture, Python version) to reproduce the issue?

- [x] Yes, I have

# SPDX-License-Identifier: MIT
# DuckDB 2.0.0: a commit that skips the WAL for an automatic checkpoint publishes its rows before
# that checkpoint makes them durable. Another connection's transaction reads them and commits; the
# process is then killed (SIGKILL: a process crash, the page cache keeps every write) and the
# reopened database has none of them. Hunt run 1950, duckdb-append, timeline 241 (README, Found).
#   python3 repro-visible-before-durable.py <empty dir> [iterations]
# The workload's table and statement (local_node.py): key 29's list, then a transaction of two
# INSERT ... ON CONFLICT DO UPDATE list_append upserts, the checkpoint_threshold 8KB the killed
# node had drawn. A reader thread polls key 29 in its own transactions and kills the process the
# moment one of them commits having seen the new values.
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
    path = os.path.join(work, "jepsen.duckdb")
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

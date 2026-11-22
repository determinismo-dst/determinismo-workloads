# SPDX-License-Identifier: MIT
# DuckDB 2.0's Quack server: the database file /data/jepsen.duckdb on this node's disk, served to
# the client nodes (local_node.py --quack) over the guest's network. Plain HTTP: Quack's docs
# leave TLS to a terminating proxy, and its default for a non-local address (HTTPS with a
# certificate of its own) is refused by clients that cannot verify it. One token.
# QUACK_RECONNECTS=1 turns its reconnect support on (clients acknowledge results; the server
# keeps the last until acknowledged), the clients' too.
import os
import sys
import time

import duckdb

import determinismo as det

PATH = "/data/jepsen.duckdb"
TOKEN = "determinismo-token"
EXTENSIONS = {"extension_directory": "/opt/duckdb/extensions"}  # Quack and httpfs are built in (Dockerfile); none installed.
# The checkpoint threshold drawn for this start, as local_node.py draws it (its THRESHOLDS).
THRESHOLDS = ("16MB", "1MB", "64KB", "8KB")
THRESHOLD = THRESHOLDS[(int(os.environ.get("DETERMINISMO_DRAW", "0")) >> 8) % len(THRESHOLDS)]


def main():
    # The platform's coverage (the Python SDK, sys.monitoring): this node's code and DuckDB's
    # Python package, each line a "coverage" event the first time it runs. DuckDB's engine is
    # C++, not covered (serve's gate: a run without coverage is stopped, "coverage always").
    det.coverage_start([os.path.dirname(os.path.abspath(__file__)), os.path.dirname(duckdb.__file__)])
    # The WAL replayed before serving.
    database = duckdb.connect(PATH, config=dict(EXTENSIONS, checkpoint_threshold=THRESHOLD))
    database.execute("LOAD quack")
    if os.environ.get("QUACK_RECONNECTS") == "1":
        database.execute("SET quack_enable_reconnects = true")
    served = database.execute(
        "CALL quack_serve('quack:0.0.0.0', token = '%s', allow_other_hostname = true, "
        "disable_ssl = true)" % TOKEN).fetchall()
    print("quack server:", served, "reconnects:", os.environ.get("QUACK_RECONNECTS") == "1",
          "checkpoint_threshold:", THRESHOLD, flush=True)
    while True:
        time.sleep(3600)


if __name__ == "__main__":
    sys.exit(main())

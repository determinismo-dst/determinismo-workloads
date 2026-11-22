# SPDX-License-Identifier: MIT
# DuckDB 2.0.0 (MIT) embedded in Jepsen's local node, as jepsen-io/duckdb runs it: a Python
# process (local_node.py) holding one database file, serving the drivers. Dependencies fetched
# at build time: the guest has no network.
FROM docker.io/library/python:3.12.16-slim-bookworm
# Python's standard library compiled here: the image ships it without bytecode, so a first start
# writes it, unsynced, and a power loss persisting part of that tears a .pyc (its header kept, its
# body cut): Python then fails to start (EOFError from _compile_bytecode, CPython #72194; local-fs
# hunt run 1019, 161 timelines). Nothing written at run time either.
RUN python3 -m compileall -q -j 0 "$(python3 -c 'import sysconfig; print(sysconfig.get_paths()["stdlib"])')"
ENV PYTHONDONTWRITEBYTECODE=1
RUN pip install --no-cache-dir duckdb==2.0.0
# DuckDB 2.0's Quack extension (its client-server protocol), installed here: the guest has no
# network to fetch it at its first LOAD; and httpfs, whose crypto module quack_serve needs
# (autoloaded: "read-only crypto module loaded" without it). In a directory of their own: a node
# starts without HOME, where DuckDB looks by default (~/.duckdb).
RUN python3 -c "import duckdb; c = duckdb.connect(config={'extension_directory': '/opt/duckdb/extensions'}); c.execute('INSTALL quack'); c.execute('INSTALL httpfs')"
COPY workloads/duckdb/local_node.py /opt/duckdb/local_node.py
COPY workloads/duckdb/quack_server.py /opt/duckdb/quack_server.py
RUN mkdir -p /data
ENTRYPOINT ["python3", "-u", "/opt/duckdb/local_node.py", "7000"]

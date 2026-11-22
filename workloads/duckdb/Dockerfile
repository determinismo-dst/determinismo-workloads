# SPDX-License-Identifier: MIT
# DuckDB 2.0.1 (MIT) embedded in Jepsen's local node, as jepsen-io/duckdb runs it: a Python
# process (local_node.py) holding one database file, serving the drivers. DuckDB built from its
# release's source (PyPI's sdist, checksummed) by clang with trace-pc-guard coverage and the C
# SDK's callbacks (sdk/c/coverage.c), Quack (its client-server protocol) and httpfs (whose crypto
# module quack_serve needs) built into the module the same way, at the commits the release pins
# (.github/config/extensions): the engine's, Quack's and httpfs's edges report themselves once a
# timeline, as source lines (the module, unstripped, in /symbols), and thread pausing pauses its
# threads there. The nodes' Python and DuckDB's Python package: the Python SDK's coverage. Every
# dependency fetched at build time: the guest has no network.
FROM docker.io/library/python:3.12.16-slim-bookworm AS duckdb
ARG DUCKDB_SHA256=5b3f493140e35b75298ee0fc606d98e3065e8601e64fe81b09326de7a6fd68e0
RUN apt-get update -q \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends \
      clang git libssl-dev libcurl4-openssl-dev ca-certificates curl \
 && rm -rf /var/lib/apt/lists/*
RUN curl -fsSL -o /tmp/duckdb.tar.gz \
      https://files.pythonhosted.org/packages/49/d8/ebb8ff07c617d1a8c25e7f7718a6955d2d5f7e539ec5219be1da478c0a42/duckdb-2.0.1.tar.gz \
 && echo "${DUCKDB_SHA256}  /tmp/duckdb.tar.gz" | sha256sum -c - \
 && mkdir -p /opt/duckdb/src && tar -xzf /tmp/duckdb.tar.gz -C /opt/duckdb/src --strip-components=1 && rm /tmp/duckdb.tar.gz
COPY --from=determinismo-sdk c/determinismo.h c/coverage.c c/coverage-flags.sh /sdk/
RUN cd /sdk && clang -O2 -fPIC -c coverage.c -o coverage.o && ar rcs libdeterminismo-coverage.a coverage.o
# The SDK's assertions inside DuckDB (assertions.patch: WAL replay's recovery paths, commit ids,
# automatic and concurrent checkpoints; assertions only, DuckDB's behavior unchanged), the SDK's
# header on the include path, its implementation the callbacks' archive's.
COPY workloads/duckdb/assertions.patch /sdk/assertions.patch
RUN cd /opt/duckdb/src && git apply /sdk/assertions.patch
# What is instrumented: the source files the node's coverage set holds (a build argument from the
# test program's profile: DuckDB's sources and its build directory's unity files, all under
# /opt/duckdb). The callbacks are the SDK's, linked whole into the module and the executables
# (CMake's compiler checks), not a sanitizer runtime of clang's. Line tables only: source lines
# for coverage, at a fraction of full debug information's size. One compile job per 4 GB of free
# memory, at most one a CPU: DuckDB's unity files take gigabytes each, and a free runner's 16 GB
# with ninja's default 6 jobs left it silent for 40 minutes (campaign run 44980447823). Unstripped: nanobind links a
# Release module with -Wl,-s unless given NOSTRIP (added to the module's nanobind_add_module, the
# build file's only change), and scikit-build-core strips on install unless install.strip=false.
ARG DETERMINISMO_COVERAGE
RUN cd /opt/duckdb/src && sed -i 's/^  NB_STATIC$/  NB_STATIC\n  NOSTRIP/' CMakeLists.txt \
 && grep -q '^  NOSTRIP$' CMakeLists.txt \
 && flags="$(sh /sdk/coverage-flags.sh /sdk/lists) -fno-sanitize-link-runtime -gline-tables-only -I/sdk" \
 && jobs=$(awk '/MemAvailable/ {j = int($2 / 4194304); print j < 1 ? 1 : j}' /proc/meminfo) \
 && if [ "$jobs" -gt "$(nproc)" ]; then jobs=$(nproc); fi \
 && echo "DuckDB built with $jobs jobs" \
 && CMAKE_BUILD_PARALLEL_LEVEL=$jobs CC=clang CXX=clang++ CFLAGS="$flags" CXXFLAGS="$flags" \
    LDFLAGS="-Wl,--build-id -Wl,--whole-archive /sdk/libdeterminismo-coverage.a -Wl,--no-whole-archive" \
    pip wheel -v --no-cache-dir --no-deps -w /wheels . \
      --config-settings=cmake.build-type=Release --config-settings=install.strip=false \
      "--config-settings=cmake.define.BUILD_EXTENSIONS=core_functions;json;parquet;icu;quack;httpfs"

FROM docker.io/library/python:3.12.16-slim-bookworm
# httpfs's libcurl (OpenSSL's libssl is the image's already).
RUN apt-get update -q \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y -q --no-install-recommends libcurl4 \
 && rm -rf /var/lib/apt/lists/*
# Python's standard library compiled here: the image ships it without bytecode, so a first start
# writes it, unsynced, and a power loss persisting part of that tears a .pyc (its header kept, its
# body cut): Python then fails to start (EOFError from _compile_bytecode, CPython #72194; local-fs
# hunt run 1019, 161 timelines). Nothing written at run time either.
RUN python3 -m compileall -q -j 0 "$(python3 -c 'import sysconfig; print(sysconfig.get_paths()["stdlib"])')"
ENV PYTHONDONTWRITEBYTECODE=1
COPY --from=duckdb /wheels /wheels
RUN pip install --no-cache-dir /wheels/duckdb-*.whl && rm -rf /wheels \
 && mkdir /symbols && find /usr/local/lib/python3.12/site-packages -maxdepth 2 -name '_duckdb*.so' -exec cp {} /symbols/ \; \
 && ls /symbols/_duckdb*.so
# The platform's Python SDK (determinismo.py: events, assertions, coverage), as the build's
# context determinismo-sdk gives it.
COPY --from=determinismo-sdk python/determinismo.py /opt/duckdb/determinismo.py
COPY workloads/duckdb/local_node.py /opt/duckdb/local_node.py
COPY workloads/duckdb/quack_server.py /opt/duckdb/quack_server.py
RUN mkdir -p /data
ENTRYPOINT ["python3", "-u", "/opt/duckdb/local_node.py", "7000"]

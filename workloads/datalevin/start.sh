#!/bin/sh
# SPDX-License-Identifier: MIT
# start.sh server <node> | client | <the test program's arguments>: a Datalevin HA server, or the
# client node (the program prepared, then its REPL), or one of the program's commands (as
# /opt/workload/run: the composer runs the program's commands through it).
set -eu
classpath="$(cat /opt/datalevin/classpath)"
opens="--add-opens=java.base/java.nio=ALL-UNNAMED --add-opens=java.base/sun.nio.ch=ALL-UNNAMED --enable-native-access=ALL-UNNAMED"
case "${1:-}" in
  server)
    mkdir -p /data/datalevin
    # 1.1 GB: Datalevin hashes each login's password with argon2id at 128 MiB, reserving twice
    # that within half the heap's maximum (auth.clj): at -Xmx512m every server exited at start,
    # at 640m one hash at a time refused the others' logins as busy, retried every 0.2 s by its
    # peers' HA clients (trial run 1110: no driver ever connected). Two at a time here.
    # The JVM SDK's coverage on the code HA's safety runs through (its leases, replication,
    # transaction log, storage, the server and its protocol, SOFAJRaft), not the query engine,
    # instrumented ahead of time (the image's server-classpath): no agent transforming at load,
    # and the servers' own AOT cache holds (16.5 s to load on one of srv4's cores with the agent,
    # 4.7 s so; restarted servers took 46 to 55 s to serve in trial run 1121, down most of the
    # timeline). C2 kept: a login's argon2id (Bouncy Castle's, in Java) takes 2.5 s under C1 only
    # against 0.65 s, and logins starved (trial run 1114).
    exec java $opens -Xmx1100m -XX:+UseSerialGC -XX:AOTCache=/opt/datalevin/server.aot \
      -cp "$(cat /opt/datalevin/server-classpath):/opt/datalevin/node" clojure.main -m datalevin-node "$2"
    ;;
  client)
    /opt/start.sh prepare
    # Ready (its REPL listening) once the cluster took a write: a leader elected, every timeline
    # starting from it.
    /opt/start.sh await
    exec /opt/start.sh nrepl 7888 0.0.0.0
    ;;
esac
# A command runs in the client node's JVM (its REPL's, up since the setup: serve-commands), its
# client this script's thin one: no JVM started and no Datalevin client loaded again a start (a
# median 4.4 s of each driver's start in hunt run 1145).
if [ "${1:-}" = run ]; then
  exec /opt/workload/src/warm-run "$@"
fi
# The test program: compiled once (prepare, during setup) into /opt/workload/classes, so every
# command of every timeline starts compiled, after the jars: the JDK's AOT cache of Datalevin's
# client (the image's) holds for a classpath it is a prefix of. The REPL's JVM runs every command
# at once (up to four drivers, each its connections): a heap for all of them.
program="$classpath:/opt/workload/classes:/opt/workload/src"
heap=256m
[ "$1" = nrepl ] && heap=1024m
java="java $opens -XX:+UseSerialGC -XX:TieredStopAtLevel=1 -Xmx$heap -XX:AOTCache=/opt/datalevin/client.aot"
if [ "$1" = prepare ]; then
  mkdir -p /opt/workload/classes
  exec $java -cp "$program" clojure.main -m datalevin-workload compile datalevin-workload
fi
exec $java -cp "$program" clojure.main -m datalevin-workload "$@"

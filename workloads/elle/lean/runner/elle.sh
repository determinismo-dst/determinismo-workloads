#!/bin/sh
# Runs real Elle (upstream/, from ./fetch-sources.sh) on IN.edn's cases, writing OUT.edn:
#   runner/elle.sh IN.edn OUT.edn [seconds]
# With LEAN_JOB set, through it ($LEAN_JOB <seconds> <command>: a machine's job slots).
here=$(cd "$(dirname "$0")/.." && pwd)
cp="$(cat "$here/deps/classpath.txt"):$here/upstream/target/classes:$here/upstream/src"
if [ -n "${LEAN_JOB:-}" ]; then
  exec "$LEAN_JOB" "${3:-1200}" java -Xmx2g -cp "$cp" clojure.main "$here/runner/run.clj" "$1" "$2"
fi
exec java -Xmx2g -cp "$cp" clojure.main "$here/runner/run.clj" "$1" "$2"

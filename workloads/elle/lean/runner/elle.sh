#!/bin/sh
# Runs real Elle on IN.edn, writing OUT.edn. Through the machine's job slots.
here=$(cd "$(dirname "$0")/.." && pwd)
cp="$(cat "$here/deps/classpath.txt"):$here/upstream/target/classes:$here/upstream/src"
exec ~/dev/.lean-jobs/job "${3:-1200}" java -Xmx2g -cp "$cp" clojure.main "$here/runner/run.clj" "$1" "$2"

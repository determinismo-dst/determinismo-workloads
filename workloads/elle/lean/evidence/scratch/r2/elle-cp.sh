#!/bin/sh
# elle-cp.sh IN OUT [PATCH-DIR ...]: real Elle (with patch dirs ahead of its source) on IN's cases.
here=$(cd "$(dirname "$0")/../../.." && pwd)  # the replica's directory
in=$1; out=$2; shift; shift
pre=""
for d in "$@"; do pre="$pre$here/evidence/scratch/r2/$d:"; done
cp="$pre$(cat $here/deps/classpath.txt):$here/upstream/target/classes:$here/upstream/src"
exec ${LEAN_JOB:+"$LEAN_JOB" 1200} java -Xmx2g -cp "$cp" clojure.main $here/evidence/scratch/r2/run-detail.clj "$in" "$out"

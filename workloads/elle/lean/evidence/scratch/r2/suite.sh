#!/bin/sh
# suite.sh NAME [PATCH-DIR ...]: Elle's test suite with the patch dirs ahead of Elle's source, run in
# evidence/scratch/r2/suite-NAME (test-output/ lands there; histories/ linked, images/ made, as the tests
# expect from Elle's root). JDK 25 ($JAVA): jepsen.history.sim 0.1.5 is compiled for it.
here=$(cd "$(dirname "$0")/../../.." && pwd)  # the replica's directory
name=$1; shift
pre=""
for d in "$@"; do pre="$pre$here/evidence/scratch/r2/$d:"; done
cp="$pre$(cat $here/deps/classpath.txt):$here/upstream/target/classes:$here/upstream/src"
mkdir -p $here/evidence/scratch/r2/suite-$name/images && cd $here/evidence/scratch/r2/suite-$name
[ -e histories ] || ln -s $here/upstream/histories histories
${LEAN_JOB:+"$LEAN_JOB" 1790} "${JAVA:-java}" -Xmx3g -cp "$cp" clojure.main $here/evidence/scratch/r2/run-tests.clj > $here/evidence/scratch/r2/suite-$name.txt 2>&1

#!/bin/bash
# usage: run-suite.sh <suite> <builddir with flecs.o>  -- links the suite against the object and runs it (-j 4)
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
S=$1; B=$2; O=$R/build/suites/$S/obj
mkdir -p "$B/suites"
perl -e 'alarm shift; exec @ARGV' 300 cc "$O"/*.o "$B/flecs.o" "$R/build/harness/bake_test.o" -lm -lpthread -o "$B/suites/$S" || { echo LINK-FAILED; exit 2; }
cd "$B/suites" && "$R/bin/slot.sh" "./$S" -j 2 > "$S.log" 2>&1; rc=$?
rm -f "$B/suites/$S"; echo "$S rc=$rc"; grep -E 'FAIL|PASS:' "$S.log" | sed 's/\x1b\[[0-9;]*m//g' | tail -30

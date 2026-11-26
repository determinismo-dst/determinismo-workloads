#!/bin/bash
# usage: run-cpp-suite.sh <builddir with flecs.o>  -- links the cpp suite against the object and runs it (-j 2)
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
B=$1; O=$R/build/suites/cpp/obj
mkdir -p "$B/suites"
perl -e 'alarm shift; exec @ARGV' 300 c++ "$O"/*.o "$B/flecs.o" "$R/build/harness/bake_test.o" -lm -lpthread -o "$B/suites/cpp" || { echo LINK-FAILED; exit 2; }
cd "$B/suites" && "$R/bin/slot.sh" ./cpp -j 2 > cpp.log 2>&1; rc=$?
rm -f ./cpp; sed 's/\x1b\[[0-9;]*m//g' cpp.log | grep -E '\(cpp\.all\)'
sed 's/\x1b\[[0-9;]*m//g' cpp.log | grep -E '^\./cpp ' | sort > cpp.log.fails
sed 's/\x1b\[[0-9;]*m//g' "$R/build/orig/suites/cpp.log" 2>/dev/null | grep -E '^\./cpp ' | sort > cpp.log.basefails
comm -23 cpp.log.fails cpp.log.basefails | sed 's/^/  NEW FAIL: /'

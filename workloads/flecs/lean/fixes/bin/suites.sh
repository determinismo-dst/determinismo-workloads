#!/bin/bash
# usage: suites.sh F<n> <suite>...  -- runs the suites against build/F<n>/flecs.o and lists failures not in the v4.2.0 baseline
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
F=$1; shift
for s in "$@"; do
  "$R/bin/run-suite.sh" "$s" "$R/build/$F" > /dev/null 2>&1
  L=$R/build/$F/suites/$s.log
  sed 's/\x1b\[[0-9;]*m//g' "$L" | grep -E "\($s\.all\)"
  sed 's/\x1b\[[0-9;]*m//g' "$L" | grep -E '^\./'"$s"' ' | sort > "$L.fails"
  sed 's/\x1b\[[0-9;]*m//g' "$R/build/orig/suites/$s.log" | grep -E '^\./'"$s"' ' | sort > "$L.basefails"
  comm -23 "$L.fails" "$L.basefails" | sed 's/^/  NEW FAIL: /'
done

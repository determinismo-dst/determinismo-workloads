#!/bin/bash
# usage: verify-combo.sh <combined.diff> <name> F<n>...  -- one build with several patches applied together:
# runs every test in tests/ and the suites; writes build/verify/<name>/summary.txt
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
D=$1; N=$2; shift 2
B=$R/build/verify/$N; rm -rf "$B"; mkdir -p "$B/distr"
S=$B/summary.txt
{
echo "== $N: $*"
"$R/bin/check-apply.sh" "$D"
python3 -I "$R/bin/apply2distr.py" "$D" "$R/orig/flecs-4.2.0" "$B/distr" > "$B/apply2distr.log" || echo "APPLY2DISTR FAILED"
[ -f "$B/distr/flecs.h" ] || cp "$R/orig/flecs-4.2.0/distr/flecs.h" "$B/distr/"
perl -e 'alarm shift; exec @ARGV' 900 cc -std=gnu99 -O1 -g -c -I "$B/distr" "$B/distr/flecs.c" -o "$B/flecs.o" 2> "$B/cc.log" || echo "COMPILE FAILED"
echo "warnings: $(grep -c 'warning:' "$B/cc.log")"
covered=" "; for f in "$@"; do covered="$covered$("$R/bin/tests-for.sh" $f) "; done
echo "-- every test (covered = a patch in this build targets it)"
for t in "$R"/tests/*.c; do n=$(basename $t)
  case "$covered" in *" $n "*) tag=covered;; *) tag=other;; esac
  echo "$tag $("$R/bin/runtests.sh" "$B" "$B/distr" "$t" 2>&1 | grep -v 'line 5:')"
done
echo "-- suites"
for s in core query addons collections; do
  "$R/bin/run-suite.sh" "$s" "$B" > /dev/null 2>&1
  L=$B/suites/$s.log
  sed 's/\x1b\[[0-9;]*m//g' "$L" | grep -E "\($s\.all\)"
  sed 's/\x1b\[[0-9;]*m//g' "$L" | grep -E '^\./'"$s"' ' | sort > "$L.fails"
  sed 's/\x1b\[[0-9;]*m//g' "$R/build/orig/suites/$s.log" | grep -E '^\./'"$s"' ' | sort > "$L.basefails"
  comm -23 "$L.fails" "$L.basefails" | sed 's/^/  NEW FAIL: /'
done
"$R/bin/run-cpp-suite.sh" "$B"
rm -f "$B/suites/cpp"
} > "$S" 2>&1
cat "$S"

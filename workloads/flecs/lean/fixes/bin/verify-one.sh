#!/bin/bash
# usage: verify-one.sh F<n>  -- from fixes/F<n>.diff alone: apply check, amalgamation, tests patched
# (object and the task's one-step cc command), suites; writes build/verify/F<n>/summary.txt
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
F=$1; B=$R/build/verify/$F; rm -rf "$B"; mkdir -p "$B/distr"
S=$B/summary.txt
{
echo "== $F"
"$R/bin/check-apply.sh" "$R/fixes/$F.diff"
python3 -I "$R/bin/apply2distr.py" "$R/fixes/$F.diff" "$R/orig/flecs-4.2.0" "$B/distr" > "$B/apply2distr.log" || echo "APPLY2DISTR FAILED"
[ -f "$B/distr/flecs.h" ] || cp "$R/orig/flecs-4.2.0/distr/flecs.h" "$B/distr/"
[ -f "$B/distr/flecs.c" ] || cp "$R/orig/flecs-4.2.0/distr/flecs.c" "$B/distr/"
"$R/bin/slot.sh" perl -e 'alarm shift; exec @ARGV' 900 cc -std=gnu99 -O1 -g -c -I "$B/distr" "$B/distr/flecs.c" -o "$B/flecs.o" 2> "$B/cc.log" || echo "COMPILE FAILED"
echo "warnings: $(grep -c 'warning:' "$B/cc.log")"
tests=(); for t in $("$R/bin/tests-for.sh" $F); do tests+=("$R/tests/$t"); done
echo "-- tests, patched object"
"$R/bin/runtests.sh" "$B" "$B/distr" "${tests[@]}" 2>&1 | grep -v 'line 5:'
echo "-- tests, one-step: cc -std=gnu99 -O1 -g -I distr <test>.c distr/flecs.c -lm -lpthread"
mkdir -p "$B/one"
for t in "${tests[@]}"; do n=$(basename $t .c)
  "$R/bin/slot.sh" perl -e 'alarm shift; exec @ARGV' 900 cc -std=gnu99 -O1 -g -I "$B/distr" "$t" "$B/distr/flecs.c" -lm -lpthread -o "$B/one/$n" 2>/dev/null || { echo "$n: COMPILE-ERROR"; continue; }
  (cd "$B/one" && perl -e 'alarm shift; exec @ARGV' 60 "./$n" > "$n.out" 2>&1); echo "$n: rc=$?"; rm -rf "$B/one/$n" "$B/one/$n.dSYM"
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

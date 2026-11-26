#!/bin/bash
# usage: tsan-run.sh <tsan build dir> <distr dir> <test.c> [runs]  -- links a test with the TSan flecs.o, runs it, lists the functions of the race reports
B=$1; D=$2; T=$3; N=${4:-1}; n=$(basename "$T" .c)
mkdir -p "$B/t"
perl -e 'alarm shift; exec @ARGV' 120 cc -std=gnu99 -O1 -g -DNDEBUG -fsanitize=thread -I "$D" "$T" "$B/flecs.o" -lm -lpthread -o "$B/t/$n" || { echo "$n: COMPILE-ERROR"; exit 2; }
for r in $(seq 1 $N); do
  (cd "$B/t" && TSAN_OPTIONS="halt_on_error=0" perl -e 'alarm shift; exec @ARGV' 120 "./$n" > "$n.$r.out" 2>&1); rc=$?
  races=$(grep -c 'WARNING: ThreadSanitizer: data race' "$B/t/$n.$r.out")
  echo "$n run $r on $B: rc=$rc races=$races $(grep -E 'FAIL|system runs' "$B/t/$n.$r.out" | head -2 | tr '\n' ' ' | cut -c1-200)"
  # first frame of each access in each report
  grep -A2 -E '^  (Write|Read|Previous write|Previous read|Atomic)' "$B/t/$n.$r.out" | grep -oE '#0 [a-z_A-Z0-9]+' | sort | uniq -c | sort -rn | head -12
done
rm -rf "$B/t/$n" "$B/t/$n.dSYM"

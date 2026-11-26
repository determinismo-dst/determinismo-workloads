#!/bin/bash
# usage: run-check.sh <patch F<n>> <fixes/checks/file.c>  -- runs a check program on v4.2.0 and on build/verify/F<n>
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
P=$1; C=$2; n=$(basename "$C" .c)
for b in orig "verify/$P"; do
  B=$R/build/$b; D=$B/distr; [ "$b" = orig ] && D=$R/orig/flecs-4.2.0/distr
  mkdir -p "$B/chk"
  perl -e 'alarm shift; exec @ARGV' 120 cc -std=gnu99 -O1 -g -I "$D" "$R/$C" "$B/flecs.o" -lm -lpthread -o "$B/chk/$n" 2>/dev/null || { echo "$b: COMPILE-ERROR"; continue; }
  (cd "$B/chk" && perl -e 'alarm shift; exec @ARGV' 60 "./$n" > "$n.out" 2>&1); rc=$?
  rm -rf "$B/chk/$n" "$B/chk/$n.dSYM"
  echo "$n on $b: rc=$rc $(sed 's/\x1b\[[0-9;]*m//g' "$B/chk/$n.out" | grep -E 'FAIL|fatal|OK|PASS' | head -3 | tr '\n' ' ' | cut -c1-220)"
done

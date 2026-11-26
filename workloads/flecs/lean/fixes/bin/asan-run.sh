#!/bin/bash
# usage: asan-run.sh <asan build dir> <distr dir> <test.c>  -- links a test with the ASan flecs.o and runs it
B=$1; D=$2; T=$3; n=$(basename "$T" .c)
mkdir -p "$B/t"
perl -e 'alarm shift; exec @ARGV' 120 cc -std=gnu99 -O1 -g -fsanitize=address -fno-omit-frame-pointer -DFLECS_USE_OS_ALLOC -I "$D" "$T" "$B/flecs.o" -lm -lpthread -o "$B/t/$n" || { echo "$n: COMPILE-ERROR"; exit 2; }
(cd "$B/t" && ASAN_OPTIONS=halt_on_error=1 perl -e 'alarm shift; exec @ARGV' 120 "./$n" > "$n.out" 2>&1); rc=$?
rm -rf "$B/t/$n" "$B/t/$n.dSYM"
echo "$n on $B: rc=$rc $(grep -E 'ERROR: AddressSanitizer|FAIL|^OK|SUMMARY' "$B/t/$n.out" | head -3 | tr '\n' ' ' | cut -c1-250)"

#!/bin/bash
# usage: CFLAGS_EXTRA="-DX ..." runtests-mode.sh <builddir with flecs.o> <distr include dir> <test.c>...
# as runtests.sh, with extra flags for the test's compile (the object must be built with the same ones)
B=$1; shift; INC=$1; shift
for t in "$@"; do
  n=$(basename "$t" .c)
  mkdir -p "$B/t"
  if ! perl -e 'alarm shift; exec @ARGV' 120 cc -std=gnu99 -O1 -g $CFLAGS_EXTRA -I "$INC" "$t" "$B/flecs.o" -lm -lpthread -o "$B/t/$n" 2>"$B/t/$n.cc.log"; then
    echo "$n: COMPILE-ERROR"; head -5 "$B/t/$n.cc.log"; continue
  fi
  (cd "$B/t" && perl -e 'alarm shift; exec @ARGV' 60 "./$n" >"$n.out" 2>&1); rc=$?
  rm -rf "$B/t/$n" "$B/t/$n.dSYM"
  echo "$n: rc=$rc $(sed 's/\x1b\[[0-9;]*m//g' "$B/t/$n.out" | grep -E 'FAIL|fatal|INCONCL|Leak' | head -2 | tr '\n' ' ' | cut -c1-200)"
done

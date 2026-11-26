#!/bin/bash
# usage: runtests.sh <builddir with flecs.o> <distr include dir> <test.c>...
# compiles each test against the object and runs it with a 60 s alarm
B=$1; shift; INC=$1; shift
for t in "$@"; do
  n=$(basename "$t" .c)
  mkdir -p "$B/t"
  if ! perl -e 'alarm shift; exec @ARGV' 120 cc -std=gnu99 -O1 -g -I "$INC" "$t" "$B/flecs.o" -lm -lpthread -o "$B/t/$n" 2>"$B/t/$n.cc.log"; then
    echo "$n: COMPILE-ERROR"; head -5 "$B/t/$n.cc.log"; continue
  fi
  (cd "$B/t" && perl -e 'alarm shift; exec @ARGV' 60 "./$n" >"$n.out" 2>&1); rc=$?
  rm -rf "$B/t/$n" "$B/t/$n.dSYM"
  echo "$n: rc=$rc $(grep -E 'FAIL|fatal|INCONCL' "$B/t/$n.out" | head -2 | tr '\n' ' ' | cut -c1-200)"
done

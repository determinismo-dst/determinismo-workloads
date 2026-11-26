#!/bin/bash
# usage: chk.sh <builddir with flecs.o and distr/> <check.c>  -- compiles a check program against a build and runs it
B=$1; C=$2; n=$(basename "$C" .c)
D=$B/distr; [ -d "$D" ] || D=$FLECS_FIXES_ROOT/orig/flecs-4.2.0/distr
mkdir -p "$B/chk"
perl -e 'alarm shift; exec @ARGV' 120 cc -std=gnu99 -O1 -g -I "$D" "$C" "$B/flecs.o" -lm -lpthread -o "$B/chk/$n" || { echo "COMPILE-ERROR"; exit 2; }
(cd "$B/chk" && perl -e 'alarm shift; exec @ARGV' 60 "./$n"); rc=$?
rm -rf "$B/chk/$n" "$B/chk/$n.dSYM"
echo "$n on $B: rc=$rc"

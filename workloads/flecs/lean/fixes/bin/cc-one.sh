#!/bin/bash
# usage: cc-one.sh <suite> <file.c>  -- compiles one suite source to an object
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
S=$1; f=$2; T=$R/orig/flecs-4.2.0/test/$S; O=$R/build/suites/$S/obj
n=$(basename "$f" .c)
[ -f "$O/$n.o" ] && exit 0
perl -e 'alarm shift; exec @ARGV' 900 cc -std=gnu99 -O0 -g -w -c -I "$R/build/harness" -I "$R/orig/flecs-4.2.0/distr" -I "$T/include" -I "$R/orig/flecs-4.2.0/include" "$f" -o "$O/$n.o.tmp" && mv "$O/$n.o.tmp" "$O/$n.o" || echo "FAILED $f"

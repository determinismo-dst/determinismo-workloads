#!/bin/bash
# usage: tsan-build.sh <distr dir> <out dir>  -- release flecs.o (NDEBUG) with ThreadSanitizer
D=$1; O=$2; mkdir -p "$O"
$FLECS_FIXES_ROOT/bin/slot.sh perl -e 'alarm shift; exec @ARGV' 1500 cc -std=gnu99 -O1 -g -DNDEBUG -fsanitize=thread -c -I "$D" "$D/flecs.c" -o "$O/flecs.o" 2> "$O/cc.log" && echo "built $O" || { echo "FAILED $O"; tail -3 "$O/cc.log"; }

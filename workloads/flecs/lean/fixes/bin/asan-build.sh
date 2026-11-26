#!/bin/bash
# usage: asan-build.sh <distr dir> <out dir>  -- flecs.o with AddressSanitizer and FLECS_USE_OS_ALLOC (every block a malloc)
D=$1; O=$2; mkdir -p "$O"
perl -e 'alarm shift; exec @ARGV' 1500 cc -std=gnu99 -O1 -g -fsanitize=address -fno-omit-frame-pointer -DFLECS_USE_OS_ALLOC -c -I "$D" "$D/flecs.c" -o "$O/flecs.o" 2> "$O/cc.log" && echo "built $O" || { echo "FAILED $O"; tail -3 "$O/cc.log"; }

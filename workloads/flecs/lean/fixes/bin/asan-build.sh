#!/bin/bash
# usage: asan-build.sh <distr dir> <out dir>  -- flecs.o with AddressSanitizer and FLECS_USE_OS_ALLOC (every block a malloc)
# ASAN_MODE overrides the allocator flag (default -DFLECS_USE_OS_ALLOC; ASAN_MODE= for the default allocator)
D=$1; O=$2; mkdir -p "$O"
$FLECS_FIXES_ROOT/bin/slot.sh perl -e 'alarm shift; exec @ARGV' 1500 cc -std=gnu99 -O1 -g -fsanitize=address -fno-omit-frame-pointer ${ASAN_MODE--DFLECS_USE_OS_ALLOC} -c -I "$D" "$D/flecs.c" -o "$O/flecs.o" 2> "$O/cc.log" && echo "built $O" || { echo "FAILED $O"; tail -3 "$O/cc.log"; }

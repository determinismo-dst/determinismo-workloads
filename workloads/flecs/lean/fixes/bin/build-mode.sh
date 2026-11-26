#!/bin/bash
# usage: build-mode.sh <distr dir> <out dir> <cc flags...>  -- flecs.o from an already patched distr with extra flags
D=$1; O=$2; shift 2; mkdir -p "$O"
$FLECS_FIXES_ROOT/bin/slot.sh cc -std=gnu99 -O1 -g "$@" -c -I "$D" "$D/flecs.c" -o "$O/flecs.o" 2> "$O/cc.log" && echo "built $O" || { echo "FAILED $O"; tail -3 "$O/cc.log"; }

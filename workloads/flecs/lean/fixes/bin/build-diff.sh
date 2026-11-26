#!/bin/bash
# usage: build-diff.sh <patch> <builddir> [extra cc flags...]  -- patched amalgamation in <builddir>/distr
# and <builddir>/flecs.o (one job slot)
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
P=$1; B=$2; shift 2
rm -rf "$B/distr"; mkdir -p "$B/distr"
python3 -I "$R/bin/apply2distr.py" "$P" "$R/orig/flecs-4.2.0" "$B/distr" > "$B/apply2distr.log" || { echo "APPLY2DISTR FAILED"; tail -3 "$B/apply2distr.log"; exit 1; }
[ -f "$B/distr/flecs.h" ] || cp "$R/orig/flecs-4.2.0/distr/flecs.h" "$B/distr/"
[ -f "$B/distr/flecs.c" ] || cp "$R/orig/flecs-4.2.0/distr/flecs.c" "$B/distr/"
"$R/bin/slot.sh" cc -std=gnu99 -O1 -g "$@" -c -I "$B/distr" "$B/distr/flecs.c" -o "$B/flecs.o" 2> "$B/cc.log" || { echo "COMPILE FAILED"; grep -m5 error "$B/cc.log"; exit 1; }
echo "built $B (warnings: $(grep -c 'warning:' "$B/cc.log"))"

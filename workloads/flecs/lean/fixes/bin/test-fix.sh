#!/bin/bash
# usage: test-fix.sh F<n> <test.c>...  -- writes fixes/F<n>.diff from work/F<n>, applies it to the
# amalgamation, compiles it (one compile slot), runs the tests patched and unpatched
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
F=$1; shift
cd "$R/work/$F" || exit 1
git diff --no-color -- src include > "$R/fixes/$F.diff"
[ -s "$R/fixes/$F.diff" ] || { echo "empty diff"; exit 1; }
B=$R/build/$F; rm -rf "$B/distr"; mkdir -p "$B/distr"
python3 -I "$R/bin/apply2distr.py" "$R/fixes/$F.diff" "$R/orig/flecs-4.2.0" "$B/distr" || exit 1
[ -f "$B/distr/flecs.h" ] || cp "$R/orig/flecs-4.2.0/distr/flecs.h" "$B/distr/"
[ -f "$B/distr/flecs.c" ] || cp "$R/orig/flecs-4.2.0/distr/flecs.c" "$B/distr/"
"$R/bin/slot.sh" perl -e 'alarm shift; exec @ARGV' 900 cc -std=gnu99 -O1 -g -c -I "$B/distr" "$B/distr/flecs.c" -o "$B/flecs.o" 2> "$B/cc.log" || { echo "COMPILE FAILED"; grep -m5 error "$B/cc.log"; exit 1; }
grep -m3 warning "$B/cc.log"
tests=(); for t in "$@"; do tests+=("$R/tests/$t"); done
echo "-- patched"; "$R/bin/runtests.sh" "$B" "$B/distr" "${tests[@]}" 2>&1 | grep -v 'line 5:'
echo "-- v4.2.0"; "$R/bin/runtests.sh" "$R/build/orig" "$R/orig/flecs-4.2.0/distr" "${tests[@]}" 2>&1 | grep -v 'line 5:'

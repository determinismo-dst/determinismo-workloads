#!/bin/bash
# usage: verify-modes.sh <name> <distr dir>  -- the build modes the round-8 tests need, on one patched
# amalgamation (or v4.2.0's): release (-DNDEBUG) for F53, F55 and F58's tests; -DFLECS_USE_OS_ALLOC and
# -DFLECS_SANITIZE for F55's leak test. Writes build/modes/<name>/summary.txt
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
N=$1; D=$2; B=$R/build/modes/$N; rm -rf "$B"; mkdir -p "$B"
S=$B/summary.txt
{
echo "== $N ($D)"
for m in ndebug:-DNDEBUG osalloc:-DFLECS_USE_OS_ALLOC sanitize:-DFLECS_SANITIZE; do
  n=${m%%:*}; f=${m#*:}
  "$R/bin/build-mode.sh" "$D" "$B/$n" $f > /dev/null
done
echo "-- release (-DNDEBUG)"
CFLAGS_EXTRA=-DNDEBUG "$R/bin/runtests-mode.sh" "$B/ndebug" "$D" \
  "$R/tests/iter_changed_multi_threaded_system.c" "$R/tests/iter_skip_multi_threaded_system.c" \
  "$R/tests/query_order_by_skip_corrupts_monitor_allocator.c" \
  "$R/tests/query_order_by_stale_slice_next_iterator.c" \
  "$R/tests/prefab_parent_instantiate_depth_keeps_tables.c"
echo "-- -DFLECS_USE_OS_ALLOC"
CFLAGS_EXTRA=-DFLECS_USE_OS_ALLOC "$R/bin/runtests-mode.sh" "$B/osalloc" "$D" \
  "$R/tests/query_order_by_skip_leaks_dirty_state.c"
echo "-- -DFLECS_SANITIZE"
CFLAGS_EXTRA=-DFLECS_SANITIZE "$R/bin/runtests-mode.sh" "$B/sanitize" "$D" \
  "$R/tests/query_order_by_skip_leaks_dirty_state.c"
for n in ndebug osalloc sanitize; do rm -f "$B/$n/flecs.o"; done
} > "$S" 2>&1
cat "$S"

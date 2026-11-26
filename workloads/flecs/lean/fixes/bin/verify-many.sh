#!/bin/bash
# usage: verify-many.sh F<n>...  -- verify-one.sh for each patch, in sequence
for f in "$@"; do
  $FLECS_FIXES_ROOT/bin/verify-one.sh "$f" > /dev/null 2>&1
  echo "done $f"
done

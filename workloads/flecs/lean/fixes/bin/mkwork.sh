#!/bin/bash
# usage: mkwork.sh F<n>  -- a writable copy of v4.2.0's src/ and include/ in work/F<n>, staged in a local index (never committed)
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
W=$R/work/$1
[ -d "$W" ] && { echo "exists: $W"; exit 0; }
mkdir -p "$W" && cp -R "$R/orig/flecs-4.2.0/src" "$R/orig/flecs-4.2.0/include" "$W/" && chmod -R u+w "$W"
cd "$W" && git init -q && git add -A && echo "$W"

#!/bin/bash
# usage: build-suite-objs.sh <suite>  -- compiles test/<suite>/src/*.c once (against the untouched headers), 2 at a time
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
S=$1; T=$R/orig/flecs-4.2.0/test/$S; O=$R/build/suites/$S/obj
mkdir -p "$O"
ls "$T"/src/*.c | xargs -P 2 -n 1 "$R/bin/cc-one.sh" "$S"
ls "$O"/*.o | wc -l

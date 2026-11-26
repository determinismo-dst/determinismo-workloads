#!/bin/bash
# usage: cxx-one.sh <file.cpp>  -- compiles one cpp suite source to an object
R="${FLECS_FIXES_ROOT:?set FLECS_FIXES_ROOT to a directory holding orig/flecs-4.2.0 and work/}"
f=$1; T=$R/orig/flecs-4.2.0/test/cpp; O=$R/build/suites/cpp/obj
n=$(basename "$f" .cpp)
[ -f "$O/$n.o" ] && exit 0
perl -e 'alarm shift; exec @ARGV' 1200 c++ -std=c++17 -O0 -g -w -c -I "$R/build/harness" -I "$R/orig/flecs-4.2.0/distr" -I "$T/include" -I "$R/orig/flecs-4.2.0/include" "$f" -o "$O/$n.o.tmp" && mv "$O/$n.o.tmp" "$O/$n.o" || echo "FAILED $f"

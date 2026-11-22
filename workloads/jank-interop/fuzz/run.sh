#!/bin/sh
# SPDX-License-Identifier: MIT
# Native fuzzing of every construct, no determinismo (on the Mac or a host): cycles the constructs,
# each run CASES of Hegel's cases (src/jank_interop/fuzz.jank) at the lowest priority, JOBS at once,
# each at most 1800 s; a line per run in $LOG (PASS, FAIL with origins and a minimal case, HANG with
# its case, or the exit status of a crash). Failures replay first next time (.hegel/ in the cwd).
#   workloads/jank-interop/fuzz/run.sh [cases, default 200] [jobs, default 3]
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
cases=${1:-200}
jobs=${2:-3}
log=${LOG:-$HOME/jank-fuzz/log.txt}
mkdir -p "$(dirname "$log")" && cd "$(dirname "$log")"
os=$(uname -s | tr A-Z a-z); arch=$(uname -m); [ "$arch" = x86_64 ] && arch=amd64
lib=$repo/libs/hegel-jank/hegel-sys/lib/$os-$arch
# The constructs: their entries have an :area (the scalar types' have a :name too).
names=$(grep -o '{:name "[^"]*" :area' "$repo/workloads/jank-interop/src/jank_interop/cases.jank" | sed 's/{:name "//; s/" :area$//')
# At most $1 seconds (macOS has no timeout(1)). The killer's output goes nowhere and its sleep is
# killed with it: a sleep holding the capture's pipe made every $(...) wait the whole limit.
limited() {
  limit=$1; shift
  "$@" & pid=$!
  ( sleep "$limit"; kill -9 "$pid" 2>/dev/null ) > /dev/null 2>&1 & killer=$!
  wait "$pid"; status=$?
  pkill -P "$killer" sleep 2>/dev/null; kill "$killer" 2>/dev/null
  return $status
}
run_one() {
  out=$(limited 1800 nice -n 19 jank -I "$repo/libs/hegel-jank/hegel-sys/include" -L "$lib" -lhegel \
    --module-path "$repo/libs/hegel-jank/hegel/src:$repo/workloads/jank-interop/src" \
    run-main jank-interop.fuzz -- "$1" "$cases" 2>&1)
  status=$?
  line=$(printf '%s\n' "$out" | grep -E '^(PASS|FAIL|HANG) ' | tail -1)
  [ -z "$line" ] && line="EXIT $status $1: $(printf '%s' "$out" | grep -v '^#[0-9]' | tail -3 | tr '\n' ' ' | cut -c1-400)"
  echo "$(date -u +%FT%TZ) $line" >> "$log"
}
while true; do
  printf '%s\n' "$names" | while IFS= read -r name; do
    while [ "$(jobs -p | wc -l)" -ge "$jobs" ]; do sleep 5; done
    run_one "$name" &
  done
  wait
done

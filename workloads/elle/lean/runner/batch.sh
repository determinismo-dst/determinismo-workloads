#!/bin/bash
# Search batches: each line of $1 is "NAME MODE WORKLOAD ARGS...", run in turn; output in
# results/NAME.{txt,cases.edn} and .jobs/NAME.log. With LEAN_JOB set, each search runs through it
# ($LEAN_JOB <seconds> <command>: a machine's job slots).
cd "$(dirname "$0")/.."
mkdir -p .jobs
while read -r name mode wl args; do
  [ -z "$name" ] && continue
  case "$name" in \#*) continue;; esac
  echo "== $name $mode $wl $args"
  ${LEAN_JOB:+"$LEAN_JOB" 1790} .lake/build/bin/elle-search "$mode" "$wl" $args out=results/"$name" > .jobs/"$name".log 2>&1
  grep -v '^\[' .jobs/"$name".log
done < "$1"

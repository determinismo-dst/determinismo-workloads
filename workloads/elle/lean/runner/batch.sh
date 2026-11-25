#!/bin/bash
# Search batches: each line of $1 is "NAME MODE WORKLOAD ARGS...", run in turn through the job
# slots; output in results/NAME.{txt,cases.edn} and .jobs/NAME.log.
cd "$(dirname "$0")/.."
while read -r name mode wl args; do
  [ -z "$name" ] && continue
  case "$name" in \#*) continue;; esac
  echo "== $name $mode $wl $args"
  ~/dev/.lean-jobs/job 1790 .lake/build/bin/elle-search "$mode" "$wl" $args out=results/"$name" > .jobs/"$name".log 2>&1
  grep -v '^\[' .jobs/"$name".log
done < "$1"

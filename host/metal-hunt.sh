#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# metal-hunt.sh <minutes> [seed] [workload] [scenario] [memory-mib] [timeline]: a workload's hunt
# (DuckDB's append by default: its 2 GiB VMs and 180 s timelines) on a machine the platform's
# infra/host/setup.sh has just set up (serve on 127.0.0.1:7878, its tree ~/determinismo), with
# this repository copied to ~/determinismo-workloads (.github/workflows/aws-hunt.yml does both).
#
# The program is built here against the very platform this machine was set up with (zig's
# --fork: serve's tree, whatever ref the workflow asked; its SDK then always matches the explorer
# that runs it) and put where serve's tree keeps programs, the workloads beside it (a workload
# names its Dockerfiles from the tree's root, as in an assembled tree); then one tree run of the
# asked length, its counts every ten minutes and at its end. Counts only: the workflow's log is a public repository's. Exit 0 when the run ended
# (failing properties are findings, not errors), 1 when it could not start or did not end.
set -euo pipefail
minutes=${1:?usage: metal-hunt.sh <minutes> [seed] [workload] [scenario] [memory-mib] [timeline]}
seed=${2:-1}
workload=${3:-duckdb}
scenario=${4:-append}
memory_mib=${5:-2048}
timeline=${6:-180s}
serve=http://127.0.0.1:7878
tree=$HOME/determinismo
here=$HOME/determinismo-workloads

cd "$here"
~/opt/zig/zig build -Drelease --fork="$tree" "$workload-test"
install -m 755 "zig-out/bin/$workload-test" "$tree/zig-out/bin/$workload-test"
mkdir -p "$tree/workloads"
rsync -a --delete "$here/workloads/" "$tree/workloads/"

body=$(python3 -c "
import json, sys
minutes, seed, workload, scenario, memory_mib, timeline = sys.argv[1:7]
print(json.dumps({'program': f'zig-out/bin/{workload}-test', 'scenario': scenario, 'seed': int(seed),
                  'time_budget': minutes + 'm', 'timeline': timeline, 'memory_mib': int(memory_mib),
                  'branching': 'tree'}))" "$minutes" "$seed" "$workload" "$scenario" "$memory_mib" "$timeline")
curl -s -m 900 -X POST -d "$body" "$serve/runs" > started.json
run=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1])).get('id',''))" started.json 2>/dev/null || true)
[ -n "$run" ] || { echo "the run was refused: $(head -c 300 started.json)"; exit 1; }
echo "run $run started: $workload $scenario, seed $seed, ${minutes} minutes"
echo "$run" > "$here/run-id" # The workflow's report reads it.

status() {
  curl -s -m 60 "$serve/runs/$run" | python3 -c "
import json, sys
r = json.load(sys.stdin)
s = r.get('stats') or {}
wall = s.get('wall_ns', 0) / 3.6e12
virtual = s.get('vtime_ns', 0) / 3.6e12
print(r.get('state', ''), f\"{s.get('timelines', 0)} timelines, {s.get('failing_timelines', 0)} failing,\",
      f\"{s.get('behaviors', 0)} behaviors, {virtual:.1f} virtual h\")" 2>/dev/null || echo "unread"
}
properties() {
  curl -s -m 60 "$serve/runs/$run/properties" | python3 -c "
import json, sys
p = json.load(sys.stdin)
failing = sum(1 for x in p if x.get('status') == 'failing')
print(f'{len(p)} properties, {failing} failing')" 2>/dev/null || echo "properties unread"
}

# Bounded: the budget, then the run's own wind-down (its last timelines end) and some room.
deadline=$(( $(date +%s) + minutes * 60 + 1800 ))
while :; do
  line=$(status)
  state=${line%% *}
  echo "$(date -u +%H:%M) ${line#* }"
  # Serve's runs are done once no longer running (its own `done`); a read that failed is no news.
  case $state in running|unread) ;; *) break ;; esac
  [ "$(date +%s)" -lt "$deadline" ] || { echo "the run did not end within its budget and 30 minutes"; exit 1; }
  sleep 600
done
echo "run $run $state: $(properties)"

# The run's report in Markdown (summary.md), for the workflow's run page (its job summary).
python3 "$here/host/run-summary.py" "$serve" "$run" "seed $seed" "$minutes minutes" "$workload" "$scenario" > "$here/summary.md"

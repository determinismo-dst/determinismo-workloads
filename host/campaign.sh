#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# campaign.sh <state> <minutes> <workload> [scenario] [memory-mib] [timeline]: one stretch of a
# workload's campaign, its one long tree run: started the first time (with a budget it never
# reaches), resumed by every later stretch (serve's resume: the same run, the timelines its
# record has skipped, its tree continued from their summaries), and stopped after <minutes> so
# that the next stretch continues it. Serve's data and the run's pinned system live in <state>
# (the workflow carries it from one job to the next), the run's id in <state>/run-id, the
# stretches so far in <state>/stretches. Counts every ten minutes, summary.md at the end.
# Exit 0 when the stretch ran and the run stopped to be continued (failing properties are
# findings, not errors), 1 otherwise.
set -euo pipefail
state=${1:?usage: campaign.sh <state> <minutes> <workload> [scenario] [memory-mib] [timeline]}
minutes=${2:?usage: campaign.sh <state> <minutes> <workload> [scenario] [memory-mib] [timeline]}
workload=${3:?usage: campaign.sh <state> <minutes> <workload> [scenario] [memory-mib] [timeline]}
scenario=${4:-append}
memory_mib=${5:-2048}
timeline=${6:-180s}
serve=http://127.0.0.1:7878
tree=$HOME/determinismo
here=$HOME/determinismo-workloads
cd "$here"

if [ -s "$state/run-id" ]; then
  run=$(cat "$state/run-id")
  answer=$(curl -s -m 300 -X POST "$serve/runs/$run/resume")
  echo "run $run resumed: $answer"
  grep -q '"state":"running"' <<< "$answer" || { echo "the run did not resume"; exit 1; }
else
  # The program, built against the platform serve runs (as host/metal-hunt.sh does).
  ~/opt/zig/zig build -Drelease --fork="$tree" "$workload-test"
  install -m 755 "zig-out/bin/$workload-test" "$tree/zig-out/bin/$workload-test"
  mkdir -p "$tree/workloads"
  rsync -a --delete "$here/workloads/" "$tree/workloads/"
  # A budget no campaign reaches: each stretch stops it, the next resumes it.
  body=$(python3 -c "
import json, sys
workload, scenario, memory_mib, timeline = sys.argv[1:5]
print(json.dumps({'program': f'zig-out/bin/{workload}-test', 'scenario': scenario, 'seed': 1,
                  'time_budget': '100000h', 'timeline': timeline, 'memory_mib': int(memory_mib),
                  'branching': 'tree'}))" "$workload" "$scenario" "$memory_mib" "$timeline")
  curl -s -m 900 -X POST -d "$body" "$serve/runs" > started.json
  run=$(python3 -c "import json,sys; print(json.load(open(sys.argv[1])).get('id',''))" started.json 2>/dev/null || true)
  [ -n "$run" ] || { echo "the run was refused: $(head -c 300 started.json)"; exit 1; }
  echo "$run" > "$state/run-id"
  echo "run $run started: the $workload campaign, $scenario"
fi
echo "$run" > "$here/run-id" # The workflow's report reads it.
stretch=$(( $(cat "$state/stretches" 2>/dev/null || echo 0) + 1 ))
echo "$stretch" > "$state/stretches"

status() {
  curl -s -m 60 "$serve/runs/$run" | python3 -c "
import json, sys
r = json.load(sys.stdin)
s = r.get('stats') or {}
print(r.get('state', ''), f\"{s.get('timelines', 0)} timelines, {s.get('failing_timelines', 0)} failing,\",
      f\"{s.get('behaviors', 0)} behaviors, {s.get('vtime_ns', 0) / 3.6e12:.1f} virtual h\")" 2>/dev/null || echo "unread"
}

# The stretch: counts every ten minutes, the run stopped at its end (or ended on its own).
end=$(( $(date +%s) + minutes * 60 ))
while :; do
  line=$(status)
  state_now=${line%% *}
  echo "$(date -u +%H:%M) ${line#* }"
  # Where it is (building an image, booting, a timeline's end): the explorer's latest line.
  latest=$(curl -s -m 30 "$serve/runs/$run/output?lines=1&explorer=1" | tail -1 | cut -c1-160 || true)
  [ -z "$latest" ] || echo "      $latest"
  case $state_now in running|unread) ;; *) echo "the run ended on its own: $state_now"; break ;; esac
  left=$(( end - $(date +%s) ))
  [ "$left" -gt 0 ] || break
  sleep $(( left < 600 ? left : 600 ))
done
if [ "$state_now" = running ] || [ "$state_now" = unread ]; then
  curl -s -m 120 -X POST "$serve/runs/$run/stop" > /dev/null || true
  for _ in $(seq 60); do
    state_now=$(status); state_now=${state_now%% *}
    [ "$state_now" = running ] || break
    sleep 10
  done
  echo "run $run $state_now after stretch $stretch"
fi

python3 "$here/host/run-summary.py" "$serve" "$run" "campaign run $run, stretch $stretch" \
  "$stretch stretches of $minutes minutes" "$workload" "$scenario" > "$here/summary.md"
[ "$state_now" = stopped ] || { echo "the run is $state_now, not stopped: the next stretch cannot resume it"; exit 1; }

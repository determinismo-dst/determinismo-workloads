#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# The host side of .github/workflows/hunt.yml: Datalevin's continuous hunt on a determinismo
# host, the only command its key may run (authorized_keys: restrict,command="<this file>"). It
# reads the asked action from SSH_ORIGINAL_COMMAND: `tick` or `status`, nothing else.
#
# tick: when the host has room, the hunt goes on: its run resumed if stopped, a new run (the next
#   seed) when it finished or when the deployed build changed. When the host has none (the
#   calibration hold file, the calibration queue or a hunt queue's unit active, another run
#   going), a hunt of ours that runs is stopped (resumed at a later tick) and nothing starts.
# status: the hunt's run and its counts.
#
# It prints counts only: the workflow's log is a public repository's.
set -euo pipefail
serve=${DETERMINISMO_SERVE:-http://127.0.0.1:7878}
tree=${DETERMINISMO_TREE:-$HOME/determinismo}
state_dir=$HOME/.determinismo-workloads
state=$state_dir/datalevin.json
mkdir -p "$state_dir"

action=${SSH_ORIGINAL_COMMAND:-${1:-}}
case $action in tick|status) ;; *) echo "refused: only tick or status"; exit 2 ;; esac

field() { python3 -c "import json,sys; d=json.load(open(sys.argv[1])); print(d.get(sys.argv[2], ''))" "$state" "$1" 2>/dev/null || true; }
run_state() { curl -s -m 20 "$serve/runs/$1" | python3 -c "import json,sys; print(json.load(sys.stdin).get('state',''))" 2>/dev/null || true; }
counts() {
  curl -s -m 60 "$serve/runs/$1/properties" | python3 -c "
import json, sys
p = json.load(sys.stdin)
failing = sum(1 for x in p if x.get('status') == 'failing')
print(f'{len(p)} properties, {failing} failing')" 2>/dev/null || echo "properties unread"
}

run=$(field run)
ours=$( [ -n "$run" ] && run_state "$run" || true )

if [ "$action" = status ]; then
  if [ -z "$run" ]; then echo "no hunt yet"; else echo "run $run: ${ours:-unknown}, $(counts "$run")"; fi
  exit 0
fi

# Room: none while the calibrations hold the host or another run goes.
busy=
[ -e "$HOME/scratch/hold-calibrations" ] && busy="calibrations hold the host"
systemctl is-active -q calibrations.service 2>/dev/null && busy="calibration queue active"
if systemctl list-units --no-legend --state=active 'hunts*.service' 2>/dev/null | grep -q .; then busy="hunt queue active"; fi
others=$(curl -s -m 20 "$serve/runs" | python3 -c "
import json, sys
mine = sys.argv[1]
runs = json.load(sys.stdin)
runs = runs if isinstance(runs, list) else runs.get('runs', [])
print(sum(1 for r in runs if r.get('state') == 'running' and str(r.get('id')) != mine))" "$run" 2>/dev/null || echo 0)
[ "${others:-0}" -gt 0 ] && busy="$others other runs going"

if [ -n "$busy" ]; then
  if [ "$ours" = running ]; then
    curl -s -m 60 -X POST "$serve/runs/$run/stop" > /dev/null
    echo "host busy: hunt stopped, to resume ($busy)"
  else
    echo "host busy: nothing started ($busy)"
  fi
  exit 0
fi

# The deployed build as serve reports it (a deployed tree has no git of its own): its commit and
# its explorer's hash, so a deploy that changes either is a new build.
build=$(curl -s -m 20 "$serve/build" | python3 -c "import json,sys; b=json.load(sys.stdin); print(b.get('commit','') + '/' + b.get('explorer',''))" 2>/dev/null || true)
[ -n "$build" ] && [ "$build" != / ] || { echo "serve did not say its build"; exit 1; }

case $ours in
  running)
    echo "run $run going, $(counts "$run")"; exit 0 ;;
  stopped|interrupted)
    if [ "$(field build)" = "$build" ]; then
      curl -s -m 120 -X POST "$serve/runs/$run/resume" > /dev/null && echo "run $run resumed" && exit 0
    fi ;;
esac

# A new run: none yet, the last one finished, or the deployed build changed. Its program built in
# the deployed tree first, as the hunt queue builds a workload before each start (no run on a
# stale binary).
(cd "$tree" && ~/opt/zig/zig build -Drelease datalevin-test > "$state_dir/build.log" 2>&1) || { echo "datalevin-test did not build"; exit 1; }
program=zig-out/bin/datalevin-test
seed=$(( $(field seed || echo 0) + 1 ))
body=$(python3 -c "
import json, sys
print(json.dumps({'program': sys.argv[1], 'scenario': 'append', 'seed': int(sys.argv[2]),
                  'time_budget': '24h', 'timeline': '600s', 'memory_mib': 10240, 'branching': 'tree'}))" "$program" "$seed")
new=$(curl -s -m 600 -X POST -d "$body" "$serve/runs" | python3 -c "import json,sys; print(json.load(sys.stdin).get('id',''))" 2>/dev/null || true)
[ -n "$new" ] || { echo "the new run was refused"; exit 1; }
python3 -c "
import json, sys
json.dump({'run': int(sys.argv[1]), 'seed': int(sys.argv[2]), 'build': sys.argv[3]}, open(sys.argv[4], 'w'))" "$new" "$seed" "$build" "$state"
echo "run $new started (seed $seed)"

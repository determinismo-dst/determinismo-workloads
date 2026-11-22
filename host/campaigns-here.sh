#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# campaigns-here.sh [minutes]: one stretch of every campaign in campaigns.json on a host of our
# own, against a campaign serve of its own (its systemd unit determinismo-campaigns: its own
# cores, memory limit, data and port), all at once, each continuing its run (host/campaign.sh),
# then each campaign's report published to this repository's Pages. Run every two hours by a
# timer (determinismo-campaigns-stretch.timer). GitHub's hosted runners cannot run hunts: our VMs'
# counter interrupts, virtualized twice, took every runner down within minutes.
#
# Layout under CAMPAIGNS (default ~/campaigns): workloads/ (this repository, pulled each stretch),
# platform/ (the platform's tree at campaigns.json's commit, built; rebuilt and the serve restarted
# when the commit changes), guest/base.cpio (its initramfs), state/<campaign>/ (each campaign's
# run: a campaign is a workload's scenario at a platform commit and a version of its files, as
# campaign.yml has it; a new one starts a new run). PAGES_KEY: a deploy key that may push to this
# repository (its gh-pages branch).
set -euo pipefail
minutes=${1:-60}
root=${CAMPAIGNS:-$HOME/campaigns}
serve=${SERVE:-http://127.0.0.1:7940}
key=${PAGES_KEY:-$HOME/.ssh/campaigns-pages}
workloads=$root/workloads
platform=$root/platform
log() { echo "$(date -u +%H:%M) $*"; }

git -C "$workloads" pull -q --ff-only
want=$(python3 -c "import json; print(json.load(open('$workloads/campaigns.json'))[0]['platform'])")
have=$(git -C "$platform" rev-parse HEAD 2>/dev/null || echo none)
if [ "$have" != "$want" ]; then
  log "platform $have -> $want: building"
  git -C "$platform" fetch -q origin && git -C "$platform" checkout -q "$want"
  (cd "$platform" && ~/opt/zig/zig build determinismo guest -Drelease -Dduckdb="$HOME/opt/duckdb" -Djdk="$HOME/opt/jdk-25")
  mkdir -p "$root/guest"
  "$platform/zig-out/bin/det-initramfs" --bin "$platform/zig-out/bin" --module "$HOME/guest/det_guest.ko" \
    --busybox /usr/bin/busybox --e2fsck /sbin/e2fsck.static --out "$root/guest/base.cpio"
  sudo systemctl restart determinismo-campaigns
  for _ in $(seq 60); do curl -fs -m 5 "$serve/runs" > /dev/null && break; sleep 2; done
fi

# Each campaign's stretch, all at once.
# (The loop in this shell, not behind a pipe: its stretches are this shell's jobs, waited for.)
while read -r workload scenario memory timeline commit; do
  files=$(cd "$workloads" && find "workloads/$workload" -type f | sort | xargs sha256sum | sha256sum | cut -c1-12)
  campaign=campaign-$workload-$scenario-$commit-$files
  mkdir -p "$root/state/$campaign" "$root/logs"
  (
    SERVE=$serve SERVE_UNIT=determinismo-campaigns PLATFORM=$platform WORKLOADS=$workloads \
      bash "$workloads/host/campaign.sh" "$root/state/$campaign" "$minutes" "$workload" "$scenario" "$memory" "$timeline" \
      > "$root/logs/$workload.log" 2>&1 || true
    run=$(cat "$root/state/$campaign/run-id" 2>/dev/null || true)
    if [ -n "$run" ]; then
      report=$root/reports/$workload
      mkdir -p "$report"
      "$platform/infra/host/report-static.sh" "$serve" "$run" "$report/index.html" >> "$root/logs/$workload.log" 2>&1 &&
        GITHUB_REPOSITORY=determinismo-dst/determinismo-workloads \
        PAGES_REMOTE=git@github.com:determinismo-dst/determinismo-workloads.git \
        GIT_SSH_COMMAND="ssh -i $key -o IdentitiesOnly=yes -o StrictHostKeyChecking=accept-new" \
        bash "$workloads/host/publish-report.sh" "$report" "campaign-$workload" \
          "$(( $(cat "$root/state/$campaign/stretches") * minutes ))" >> "$root/logs/$workload.log" 2>&1 || true
    fi
    log "$workload: $(tail -1 "$root/logs/$workload.log")"
  ) &
done < <(python3 -c "
import json
for c in json.load(open('$workloads/campaigns.json')):
    print(c['workload'], c['scenario'], c['memory_mib'], c['timeline'], c['platform'][:12])
")
wait

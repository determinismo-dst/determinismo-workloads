#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# live-mirror.sh: a hunt's page live and read only, for anyone, while it runs (the workflows').
#
#   live-mirror.sh start <dir>   the page's server (python3's, 127.0.0.1:8090, serving <dir>) and a
#                                Cloudflare quick tunnel to it (cloudflared, pinned): prints its
#                                https address. Until the first recording, a page saying the run
#                                is starting (it reloads itself).
#   live-mirror.sh record <serve-url> <run> <dir>
#                                serve's page for the run recorded (the platform's
#                                infra/host/report-static.sh, run from the job's workspace) and put
#                                in <dir> whole: an open copy of a run still going takes each newer
#                                recording within 10 s (stamp.json).
#
# Read only by construction: the page answers from its recording alone, nothing reaches serve.
set -euo pipefail
cloudflared_url=https://github.com/cloudflare/cloudflared/releases/download/2026.11.1/cloudflared-linux-amd64
cloudflared_sha256=97bb3b02d23a5980fc9c15a1a270e692da1923f103f920d5b16d4931d5ab55e7

case ${1:-} in
  start)
    dir=${2:?usage: live-mirror.sh start <dir>}
    mkdir -p "$dir"
    cat > "$dir/index.html" <<'EOF'
<!doctype html><meta charset="utf-8"><meta http-equiv="refresh" content="10">
<title>determinismo: a run starting</title>
<p style="font: 18px Georgia, serif; margin: 40px">The run is starting: its page appears here once
its first timelines are under way (this page reloads every 10 s).</p>
EOF
    nohup python3 -m http.server 8090 --bind 127.0.0.1 --directory "$dir" > "$HOME/live-http.log" 2>&1 &
    curl -fsSL -o "$HOME/cloudflared" "$cloudflared_url"
    echo "$cloudflared_sha256  $HOME/cloudflared" | sha256sum -c --status || { echo "error: cloudflared is not the pinned build" >&2; exit 1; }
    chmod +x "$HOME/cloudflared"
    nohup "$HOME/cloudflared" tunnel --no-autoupdate --url http://127.0.0.1:8090 > "$HOME/live-tunnel.log" 2>&1 &
    for _ in $(seq 90); do
      url=$(grep -oE 'https://[a-z0-9-]+\.trycloudflare\.com' "$HOME/live-tunnel.log" | head -1 || true)
      [ -n "$url" ] && { echo "$url"; exit 0; }
      sleep 1
    done
    echo "error: no tunnel address in 90 s: $(tail -3 "$HOME/live-tunnel.log")" >&2
    exit 1 ;;
  record)
    serve=${2:?usage: live-mirror.sh record <serve-url> <run> <dir>}
    run=${3:?usage: live-mirror.sh record <serve-url> <run> <dir>}
    dir=${4:?usage: live-mirror.sh record <serve-url> <run> <dir>}
    tmp="$dir.next"
    rm -rf "$tmp" && mkdir -p "$tmp"
    platform/infra/host/report-static.sh "$serve" "$run" "$tmp/index.html" > /dev/null
    # The page first, then the stamp that makes open copies take it.
    mv "$tmp/index.html" "$dir/index.html"
    mv "$tmp/stamp.json" "$dir/stamp.json" ;;
  *)
    echo "usage: live-mirror.sh start <dir> | record <serve-url> <run> <dir>" >&2
    exit 2 ;;
esac

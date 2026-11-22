#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# live-tunnel.sh <port>: serve's page live and read only for anyone, to the second: a Cloudflare
# quick tunnel (cloudflared, pinned by checksum) in front of serve's --public-listen address on
# 127.0.0.1:<port> (the platform's serve --public-listen: the page and what it reads, nothing
# that acts; DuckDB kept to the data directory). Prints the tunnel's https address. Runs where
# serve runs: a runner, or an AWS machine (the workflows, over SSH).
set -euo pipefail
port=${1:?usage: live-tunnel.sh <port>}
cloudflared_url=https://github.com/cloudflare/cloudflared/releases/download/2026.11.1/cloudflared-linux-amd64
cloudflared_sha256=97bb3b02d23a5980fc9c15a1a270e692da1923f103f920d5b16d4931d5ab55e7
binary=$HOME/cloudflared
log=$HOME/live-tunnel.log
if ! echo "$cloudflared_sha256  $binary" | sha256sum -c --status 2>/dev/null; then
  curl -fsSL -o "$binary" "$cloudflared_url"
  echo "$cloudflared_sha256  $binary" | sha256sum -c --status || { echo "error: cloudflared is not the pinned build" >&2; exit 1; }
fi
chmod +x "$binary"
: > "$log"
nohup "$binary" tunnel --no-autoupdate --url "http://127.0.0.1:$port" > "$log" 2>&1 &
for _ in $(seq 90); do
  url=$(grep -oE 'https://[a-z0-9-]+\.trycloudflare\.com' "$log" | head -1 || true)
  [ -n "$url" ] && { echo "$url"; exit 0; }
  sleep 1
done
echo "error: no tunnel address in 90 s: $(tail -3 "$log")" >&2
exit 1

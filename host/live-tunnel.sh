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
# HTTP/2 over TCP 443: its default (QUIC, over UDP) dropped within a minute or two on GitHub's
# runners, both tunnels of a trial answering Cloudflare's 1033 after (2026-11-22).
nohup "$binary" tunnel --no-autoupdate --protocol http2 --url "http://127.0.0.1:$port" > "$log" 2>&1 &
for _ in $(seq 90); do
  url=$(grep -oE 'https://[a-z0-9-]+\.trycloudflare\.com' "$log" | head -1 || true)
  registered=$(grep -m1 "Registered tunnel connection" "$log" || true)
  if [ -n "$url" ] && [ -n "$registered" ]; then
    # Where Cloudflare holds it, in the job's log (stderr): what to look at when it drops.
    echo "tunnel: $(echo "$registered" | grep -oE 'location=[a-z0-9]+|protocol=[a-z0-9]+' | tr '\n' ' ')" >&2
    echo "$url"
    exit 0
  fi
  sleep 1
done
echo "error: no tunnel address in 90 s: $(tail -3 "$log")" >&2
exit 1

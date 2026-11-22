#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# libhegel's header and prebuilt libraries from its release, each checked against the checksum the
# release publishes, into include/ and lib/<platform>/ (what the jar carries: jank-build.bb runs
# without network). Run before `lein install` or `lein deploy`.
set -euo pipefail
cd "$(dirname "$0")"
version=0.51.1
base="https://github.com/hegeldev/hegel/releases/download/libhegel%2F$version"
fetch() { # <asset> <destination>
  mkdir -p "$(dirname "$2")"
  curl -fsSL -o "$2" "$base/$1"
  local sum; sum=$(curl -fsSL "$base/$1.sha256" | cut -d' ' -f1)
  echo "$sum  $2" | sha256sum -c --quiet - 2>/dev/null || echo "$sum  $2" | shasum -a 256 -c --quiet -
}
fetch hegel.h include/hegel.h
fetch libhegel-linux-amd64.so lib/linux-amd64/libhegel.so
fetch libhegel-linux-arm64.so lib/linux-arm64/libhegel.so
fetch libhegel-darwin-arm64.dylib lib/darwin-arm64/libhegel.dylib
echo "libhegel $version: include/, lib/"

#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# push-images.sh <workload>...: each workload's node images built here, as a run would build them,
# and pushed to GitHub's container registry, so that runners pull them instead of building
# (DuckDB's engine from source takes half an hour on a free runner's 4 vCPUs). Run on a host the
# platform's infra/host/setup.sh set up (podman, ~/opt's tools), in checkouts of its own:
# WORKLOADS this repository's (default ~/determinismo-workloads), PLATFORM the platform's tree,
# built (`zig build determinismo guest`), at the commit the campaigns run (default ~/determinismo;
# on a host whose serve runs from there, give another: its workloads/ is written).
#
# For each workload: workloads/<name>/images.json says how each node's image is built (its
# Dockerfile and build arguments: the coverage set, which must match the program's profiles,
# among them); each distinct build
# is made by podman with the platform's SDK as the build context determinismo-sdk, as the
# explorer's prepare does, then pushed as ghcr.io/determinismo-dst/<workload>-<node>:<the
# workloads' commit>-<the build's hash>. Prints each image with its digest: what the test program's node names
# (`.image = "ghcr.io/...@sha256:..."`) in place of its build.
#
# REGISTRY_AUTH_FILE: a podman login to ghcr.io (a token with write:packages), kept outside the
# repository and removed after: the images pushed from here. Without it, each image is saved as
# an OCI archive in ARCHIVES (default ~/image-archives), its sha256 printed: the workflow
# push-image.yml pushes it with its own token once the archive is on the release images-staging.
# NO_PUSH=1: build only (podman's layer cache then makes a later run's builds instant).
set -euo pipefail
[ $# -gt 0 ] || { echo "usage: push-images.sh <workload>..." >&2; exit 2; }
archives=${ARCHIVES:-$HOME/image-archives}
here=${WORKLOADS:-$HOME/determinismo-workloads}
tree=${PLATFORM:-$HOME/determinismo}
commit=$(git -C "$here" rev-parse --short=12 HEAD 2>/dev/null || date -u +%Y%m%d%H%M)

cd "$here"
mkdir -p "$tree/workloads"
rsync -a --delete "$here/workloads/" "$tree/workloads/"
for workload in "$@"; do
  # The builds the test program's pinned images come from (workloads/<name>/images.json: each
  # node's Dockerfile and build arguments, its profiles' coverage set among them).
  python3 -c '
import hashlib, json, sys
for build in json.load(open(sys.argv[1])):
    key = json.dumps({k: build[k] for k in ("context", "dockerfile", "args")}, sort_keys=True)
    print(build["node"], hashlib.sha256(key.encode()).hexdigest()[:8], build["context"], build["dockerfile"],
          " ".join(build.get("args", [])))
' "workloads/$workload/images.json" | while read -r node build_key context dockerfile args; do
    image=ghcr.io/determinismo-dst/$workload-$node
    # A node built more than one way (jank-interop's profiles: JANK=coverage, JANK=package): each
    # build its own tag, the workloads' commit and its build's hash.
    tag=$commit-$build_key
    build_args=()
    for arg in $args; do build_args+=(--build-arg "$arg"); done
    (cd "$tree" && podman build --quiet --build-context determinismo-sdk="$tree/sdk" "${build_args[@]}" \
      -f "$dockerfile" -t "$image:$tag" "$context" > /dev/null)
    if [ -n "${NO_PUSH:-}" ]; then echo "$workload $node: $image:$tag built"; continue; fi
    if [ -z "${REGISTRY_AUTH_FILE:-}" ]; then
      mkdir -p "$archives"
      podman save --quiet --format oci-archive -o "$archives/$workload-$node-$tag.tar" "$image:$tag"
      echo "$workload $node: $image:$tag archived, $archives/$workload-$node-$tag.tar sha256 $(sha256sum "$archives/$workload-$node-$tag.tar" | cut -c1-64)"
      continue
    fi
    podman push --quiet --authfile "$REGISTRY_AUTH_FILE" --digestfile "/tmp/$workload-$node.digest" "$image:$tag"
    echo "$workload $node: $image@$(cat "/tmp/$workload-$node.digest")"
    rm -f "/tmp/$workload-$node.digest"
  done
done

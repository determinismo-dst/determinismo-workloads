#!/bin/bash
# usage: slot.sh <command...>  -- runs the command; with FLECS_JOB set, through that wrapper (e.g. a
# script bounding how many builds and suites run at once on the machine: FLECS_JOB="job 1800")
if [ -n "${FLECS_JOB:-}" ]; then exec $FLECS_JOB "$@"; else exec "$@"; fi

#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# run-summary.py <serve> <run> <label> <length> <workload> <scenario>: a run's report in Markdown
# (a workflow's job summary): its counts and every property, failing first. <label> names the
# run ("seed 1", "campaign run 3, hour 5"), <length> how long it ran ("60 minutes", "3 stretches of 60 minutes").
import json, sys, urllib.request
serve, run, label, minutes, workload, scenario = sys.argv[1:7]
def get(path):
    with urllib.request.urlopen(f"{serve}{path}", timeout=120) as response:
        return json.load(response)
r = get(f"/runs/{run}")
s = r.get("stats") or {}
properties = get(f"/runs/{run}/properties")
failing = [p for p in properties if p.get("status") == "failing"]
print(f"## {workload} `{scenario}`, {label}: {r.get('state', '')}")
print()
print(f"- {s.get('timelines', 0)} timelines ({minutes}), {s.get('failing_timelines', 0)} failing; "
      f"{s.get('behaviors', 0)} behaviors; {s.get('vtime_ns', 0) / 3.6e12:.1f} hours of virtual time")
print(f"- {len(properties)} properties, {len(failing)} failing")
print()
print("| Property | Kind | Status | Timelines failing | Timelines judged | First failing timeline |")
print("|---|---|---|---:|---:|---:|")
order = {"failing": 0, "passing": 1}
for p in sorted(properties, key=lambda p: (order.get(p.get("status"), 2), p.get("message", ""))):
    first = p.get("first_failing_timeline")
    print(f"| {p.get('message', '')} | {p.get('type', '')} | {p.get('status', '')} | {p.get('timelines_failing', 0)} | "
          f"{p.get('timelines_hit', 0)} | {'' if first is None else first} |")

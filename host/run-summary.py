#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# run-summary.py <serve> <run> <label> <length> <workload> <scenario>: a run's report in Markdown
# (a workflow's job summary): whether it explored, its counts and every property, failing first.
# Exit 3, the report printed whole, when a tree run never branched (no timeline from a return): a
# failed hunt, whatever it found (aws-hunt run 18: 73 timelines, all of the first generation).
# <label> names the
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
flat = (r.get("request") or {}).get("branching") == "flat"
timelines = get(f"/runs/{run}/timelines")
returned = sum(1 for t in timelines if t.get("parent") is not None)
explored = flat or returned > 0
# The run's own (the explorer's): stats.vtime_ns counts each timeline whole, a branch's inherited
# prefix again (aws-hunt run 17: 41.3 hours said where 31.8 were explored).
own = (r.get("summary") or {}).get("vtime_ns")
virtual = (f"{own / 3.6e12:.1f} hours of virtual time" if own is not None
           else f"{s.get('vtime_ns', 0) / 3.6e12:.1f} hours of virtual time, inherited prefixes counted again")
print(f"## {workload} `{scenario}`, {label}: {r.get('state', '') if explored else 'FAILED TO EXPLORE'}")
print()
if flat:
    print("- exploration: flat, as asked (no timeline returns)")
elif explored:
    generations = len({t.get("generation") for t in timelines})
    print(f"- exploration: {returned} of {len(timelines)} timelines from a return "
          f"({100 * returned / len(timelines):.0f}%), {generations} generations")
else:
    print(f"- **no exploration: 0 of {len(timelines)} timelines from a return**: the tree never branched "
          "(its budget under a few generations, or memory fitting fewer VMs than workers)")
print(f"- {s.get('timelines', 0)} timelines ({minutes}), {s.get('failing_timelines', 0)} failing; "
      f"{s.get('behaviors', 0)} behaviors; {virtual}")
print(f"- {len(properties)} properties, {len(failing)} failing")
print()
print("| Property | Kind | Status | Timelines failing | Timelines judged | First failing timeline |")
print("|---|---|---|---:|---:|---:|")
order = {"failing": 0, "passing": 1}
for p in sorted(properties, key=lambda p: (order.get(p.get("status"), 2), p.get("message", ""))):
    first = p.get("first_failing_timeline")
    print(f"| {p.get('message', '')} | {p.get('type', '')} | {p.get('status', '')} | {p.get('timelines_failing', 0)} | "
          f"{p.get('timelines_hit', 0)} | {'' if first is None else first} |")
if not explored:
    sys.exit(3)

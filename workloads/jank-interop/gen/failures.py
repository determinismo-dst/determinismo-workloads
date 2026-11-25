# SPDX-License-Identifier: MIT
# failures.py <serve URL> <run> <out.json>: a determinismo-ci run's failed jank-gen tests as
# {"<ns>::<test>": "<what the runner said>"}, the input of gen.clj's shrink and group stages.
# One query over the run's assert events, once the run has ended.
import json, sys, urllib.request

serve, run, out = sys.argv[1], sys.argv[2], sys.argv[3]
query = ("SELECT name, min(json_extract_string(event, '$.assert.details.said')) AS said FROM events "
         "WHERE kind = 'assert' AND name LIKE 'test passes: jank-gen.%' "
         "AND json_extract(event, '$.assert.condition') = false GROUP BY name ORDER BY name")
request = urllib.request.Request(f"{serve}/runs/{run}/sql", data=json.dumps({"sql": query}).encode(), method="POST")
rows = json.load(urllib.request.urlopen(request, timeout=600))
failures = {r["name"].removeprefix("test passes: "): r["said"] or "" for r in rows}
json.dump(failures, open(out, "w"), indent=1)
print(len(failures), "failed tests in", out)

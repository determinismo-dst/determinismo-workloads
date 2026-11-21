#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# publish-report.sh <report-dir> <number> <minutes>: a run's report (the platform's
# infra/host/report-static.sh: index.html and stamp.json) on this repository's GitHub Pages, at
# runs/<number>/, the index of every report made again. gh-pages is one fresh commit each time,
# force-pushed: a hunt's report is re-recorded every few minutes while it runs, and its history
# would grow by the report each time. Needs GH_TOKEN and GITHUB_REPOSITORY (a workflow's).
set -euo pipefail
dir=${1:?usage: publish-report.sh <report-dir> <number> <minutes>}
number=${2:?usage: publish-report.sh <report-dir> <number> <minutes>}
minutes=${3:?usage: publish-report.sh <report-dir> <number> <minutes>}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
remote=${PAGES_REMOTE:-"https://x-access-token:$GH_TOKEN@github.com/$GITHUB_REPOSITORY"} # PAGES_REMOTE: a test's own
git clone -q --depth 1 --branch gh-pages "$remote" "$work/pages"
mkdir -p "$work/pages/runs/$number"
cp "$dir/index.html" "$dir/stamp.json" "$work/pages/runs/$number/"

# The index: every report, newest first, each with its run's state and counts.
python3 - "$work/pages" "$number" "$minutes" <<'EOF'
import html, json, re, sys
pages, number, minutes = sys.argv[1:4]
stamp = json.load(open(f"{pages}/runs/{number}/stamp.json"))
run = stamp["run"]
page = open(f"{pages}/runs/{number}/index.html", encoding="utf-8").read()
recording = json.loads(re.search(r'id="determinismo-report">(.*?)</script>', page, re.S).group(1))
info = json.loads(recording["answers"][f"/runs/{run}"])
properties = json.loads(recording["answers"].get(f"/runs/{run}/properties", "[]"))
stats = info.get("stats") or {}
entry = {"number": int(number), "run": int(run), "date": recording["recorded"][:16].replace("T", " ") + " UTC",
         "state": info.get("state", ""), "minutes": int(minutes), "timelines": stats.get("timelines", 0),
         "failing": sum(1 for p in properties if p.get("status") == "failing"), "properties": len(properties)}
runs = [r for r in json.load(open(f"{pages}/runs.json")) if r["number"] != entry["number"]] + [entry]
runs.sort(key=lambda r: -r["number"])
json.dump(runs, open(f"{pages}/runs.json", "w"), indent=1)
items = "\n".join(
    f'<li><a href="runs/{r["number"]}/">Run {r["number"]}</a>: Datalevin <code>append</code>, {html.escape(r["date"])}, '
    f'{r["minutes"]} minutes, {r["timelines"]:,} timelines, '
    f'{"running (updating)" if r["state"] == "running" else html.escape(r["state"])}, '
    f'{r["failing"]} of {r["properties"]} properties failing</li>' for r in runs)
index = open(f"{pages}/index.html", encoding="utf-8").read()
index = re.sub(r'<ul id="runs">.*?</ul>', lambda _: f'<ul id="runs">\n{items}\n</ul>', index, flags=re.S)
open(f"{pages}/index.html", "w", encoding="utf-8").write(index)
EOF

cd "$work/pages"
git checkout -q --orphan fresh
git add -A
git -c user.name="github-actions[bot]" -c user.email="41898282+github-actions[bot]@users.noreply.github.com" \
  commit -qm "Hunt reports (run $number's, $(date -u +%H:%M) UTC)"
git push -qf origin fresh:gh-pages
echo "https://${GITHUB_REPOSITORY%%/*}.github.io/${GITHUB_REPOSITORY#*/}/runs/$number/"

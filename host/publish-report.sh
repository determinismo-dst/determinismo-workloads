#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# publish-report.sh <report-dir> <name> <minutes>: a run's report (the platform's
# infra/host/report-static.sh: index.html and stamp.json) on this repository's GitHub Pages, at
# runs/<name>/ (<workflow run>-aws, <workflow run>-runner-<try>), the index of every report made
# again. gh-pages is one fresh commit each time, force-pushed (a hunt's report is re-recorded
# while it runs; its history would grow by the report each time), and only over the commit it
# was made from: another job's publish meanwhile (the AWS and the runner hunts of one workflow
# run) and it starts again from theirs. Needs GH_TOKEN and GITHUB_REPOSITORY (a workflow's).
set -euo pipefail
dir=${1:?usage: publish-report.sh <report-dir> <name> <minutes>}
name=${2:?usage: publish-report.sh <report-dir> <name> <minutes>}
minutes=${3:?usage: publish-report.sh <report-dir> <name> <minutes>}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
remote=${PAGES_REMOTE:-"https://x-access-token:$GH_TOKEN@github.com/$GITHUB_REPOSITORY"} # PAGES_REMOTE: a test's own

for attempt in 1 2 3 4 5 6; do
  rm -rf "$work/pages"
  git clone -q --depth 1 --branch gh-pages "$remote" "$work/pages"
  base=$(git -C "$work/pages" rev-parse HEAD)
  mkdir -p "$work/pages/runs/$name"
  cp "$dir/index.html" "$dir/stamp.json" "$work/pages/runs/$name/"

  # The index: every report, newest first, each with its run's workload, state and counts.
  python3 - "$work/pages" "$name" "$minutes" <<'EOF'
import html, json, re, sys
pages, name, minutes = sys.argv[1:4]
stamp = json.load(open(f"{pages}/runs/{name}/stamp.json"))
run = stamp["run"]
page = open(f"{pages}/runs/{name}/index.html", encoding="utf-8").read()
recording = json.loads(re.search(r'id="determinismo-report">(.*?)</script>', page, re.S).group(1))
info = json.loads(recording["answers"][f"/runs/{run}"])
properties = json.loads(recording["answers"].get(f"/runs/{run}/properties", "[]"))
stats = info.get("stats") or {}
request = info.get("request") or {}
program = request.get("program_asked") or request.get("program") or ""
# A kept program's name has serve's content hash before it (<16 hex>-duckdb-test).
workload = re.sub(r"^[0-9a-f]{16}-", "", program.rsplit("/", 1)[-1]).removesuffix("-test")
entry = {"name": name, "run": int(run), "date": recording["recorded"][:16].replace("T", " ") + " UTC",
         "workload": workload, "scenario": request.get("scenario", ""),
         "state": info.get("state", ""), "minutes": int(minutes), "timelines": stats.get("timelines", 0),
         "failing": sum(1 for p in properties if p.get("status") == "failing"), "properties": len(properties)}
runs = [r for r in json.load(open(f"{pages}/runs.json")) if str(r.get("name", r.get("number"))) != name] + [entry]
runs.sort(key=lambda r: r["date"], reverse=True)
json.dump(runs, open(f"{pages}/runs.json", "w"), indent=1)
def item(r):
    key = str(r.get("name", r.get("number")))
    state = "running (updating)" if r["state"] == "running" else r["state"]
    return (f'<li><a href="runs/{html.escape(key)}/">Run {html.escape(key)}</a>: '
            f'{html.escape(r.get("workload") or "datalevin")} <code>{html.escape(r.get("scenario") or "append")}</code>, '
            f'{html.escape(r["date"])}, {r["minutes"]} minutes, {r["timelines"]:,} timelines, {html.escape(state)}, '
            f'{r["failing"]} of {r["properties"]} properties failing</li>')
items = "\n".join(item(r) for r in runs)
index = open(f"{pages}/index.html", encoding="utf-8").read()
index = re.sub(r'<ul id="runs">.*?</ul>', lambda _: f'<ul id="runs">\n{items}\n</ul>', index, flags=re.S)
open(f"{pages}/index.html", "w", encoding="utf-8").write(index)
EOF

  cd "$work/pages"
  git checkout -q --orphan fresh
  git add -A
  git -c user.name="github-actions[bot]" -c user.email="41898282+github-actions[bot]@users.noreply.github.com" \
    commit -qm "Hunt reports (run $name's, $(date -u +%H:%M) UTC)"
  if git push -q --force-with-lease="gh-pages:$base" origin fresh:gh-pages 2> "$work/push.err"; then
    echo "https://${GITHUB_REPOSITORY%%/*}.github.io/${GITHUB_REPOSITORY#*/}/runs/$name/"
    exit 0
  fi
  cd - > /dev/null
  echo "gh-pages moved meanwhile (another job's publish): again ($attempt)" >&2
  sleep $((attempt * 3))
done
echo "error: not published: $(tail -1 "$work/push.err")" >&2
exit 1

#!/bin/sh
# fetch-sources.sh: what the replica translates and what runner/elle.sh runs, all git-ignored:
# Elle at main 4e359e5 (one commit after v0.2.8) in upstream/, its Java classes compiled
# (`lein javac`: BFSPath, BitRels), and its classpath in deps/classpath.txt. Needs git, a JDK and
# Leiningen. Run it again any time: Elle already at its commit is left alone.
set -eu
cd "$(dirname "$0")"
commit=4e359e597c52938b0afebb8bc42273914d68a424
if [ -d upstream/.git ] && [ "$(git -C upstream rev-parse HEAD)" = "$commit" ]; then
  echo "upstream: at $commit"
else
  rm -rf ./upstream
  mkdir -p upstream
  git -C upstream init -q
  git -C upstream remote add origin https://github.com/jepsen-io/elle.git
  git -C upstream fetch -q --depth 1 origin "$commit"
  git -C upstream checkout -q FETCH_HEAD
  echo "upstream: fetched $commit"
fi
mkdir -p deps
(cd upstream && lein javac > /dev/null && lein classpath) > deps/classpath.txt
echo "deps/classpath.txt: $(tr ':' '\n' < deps/classpath.txt | wc -l | tr -d ' ') entries"

# service/: the Elle service round 2 replicated, the platform's checkers/elle at b8f9cc9 (Elle
# 0.2.8, before its fixes), from GitHub.
mkdir -p service
raw=https://raw.githubusercontent.com/determinismo-dst/determinismo/b8f9cc91cdf838295ae32348e78bcf8c8cc77238/checkers/elle
if curl -fsSL "$raw/src/elle_service.clj" -o service/elle_service.clj && curl -fsSL "$raw/deps.edn" -o service/deps.edn; then
  echo "service/: checkers/elle at b8f9cc9"
else
  echo "service/: not fetched" >&2
fi

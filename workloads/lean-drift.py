#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""lean-drift.py: which parts of a Lean replica a newer upstream commit touched.

A replica cites the code it copies as `file 12-34` or `file:12` (a path or its tail, and a line
or a range) at the commit its round read. This reads every citation in the replica's Lean files,
maps it through `git diff <cited commit>..<new commit>` of the upstream repository, and prints:

  changed   a hunk overlaps the cited lines: the replica may no longer be exact there;
  moved     no hunk touches them, only their line numbers changed (old -> new);
  gone      the cited file was deleted or renamed;
  ambiguous the cited tail names several files (each is checked);
  unknown   the cited tail names no file at that commit (often a dependency's: libstdc++,
            Clojure, a JDK class).

For a changed or gone file it lists the upstream commits that touched it since the cited one.

Usage:
  workloads/lean-drift.py --replica <dir> --repo <git dir> --new <commit>
                          --base <commit> [--base <lean path prefix>=<commit> ...] [--changed-only]

`--base` without a prefix is the default cited commit; with one, Lean files under that prefix
cite another (a later round's directory). The repository may be a bare, blobless clone: git
fetches the blobs a diff needs. Example, jank's replica after round 4:

  workloads/lean-drift.py --replica workloads/jank-interop/lean --repo /tmp/jank.git \\
    --base f3d82d654 --base Jank/R4/=7135b77 --new 94d32623
"""
import argparse
import collections
import os
import re
import subprocess
import sys

EXTENSIONS = "cpp|hpp|h|hh|cc|c|tcc|jank|clj|cljc|java|rs|go|py|zig"
CITATION = re.compile(
    r"(?<![\w/.-])((?:[\w.+-]+/)*[\w.+-]+\.(?:" + EXTENSIONS + r"))"
    r"(?::|,? (?:lines? )?)(\d+)(?:\s*[-–]\s*(\d+))?"
)


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], check=True, capture_output=True, text=True).stdout


def citations(replica):
    """(lean file, lean line, cited tail, first line, last line) for every citation."""
    for root, dirs, files in os.walk(replica):
        dirs[:] = [d for d in dirs if not d.startswith(".") and d not in ("upstream", "deps", "build")]
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(root, name)
            with open(path, encoding="utf-8", errors="replace") as source:
                for number, text in enumerate(source, 1):
                    for match in CITATION.finditer(text):
                        first = int(match.group(2))
                        last = int(match.group(3)) if match.group(3) else first
                        if last < first:
                            continue
                        yield os.path.relpath(path, replica), number, match.group(1), first, last


def hunks(repo, base, new, path):
    """The diff's hunks as (old start, old count, new start, new count), or None when deleted."""
    out = git(repo, "diff", "-U0", "--no-renames", base, new, "--", path)
    if re.search(r"^deleted file mode", out, re.M):
        return None
    found = []
    for match in re.finditer(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", out, re.M):
        old_start, old_count, new_start, new_count = (
            int(match.group(1)), int(match.group(2) or 1), int(match.group(3)), int(match.group(4) or 1))
        found.append((old_start, old_count, new_start, new_count))
    return found


def map_range(first, last, file_hunks):
    """'changed' when a hunk overlaps [first, last], else the range's new first line."""
    offset = 0
    for old_start, old_count, new_start, new_count in file_hunks:
        if old_count == 0:
            # An insertion after old line old_start: inside the range when within it.
            if first <= old_start < last:
                return "changed", None
            if old_start < first:
                offset += new_count
            continue
        old_end = old_start + old_count - 1
        if old_start <= last and old_end >= first:
            return "changed", None
        if old_end < first:
            offset += new_count - old_count
    return "moved", first + offset


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--replica", required=True)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--new", required=True)
    parser.add_argument("--base", action="append", required=True)
    parser.add_argument("--changed-only", action="store_true")
    arguments = parser.parse_args()

    default_base = None
    prefixed = []
    for value in arguments.base:
        if "=" in value:
            prefix, commit = value.split("=", 1)
            prefixed.append((prefix, commit))
        else:
            default_base = value
    if default_base is None:
        sys.exit("error: a --base without a prefix is the default cited commit")
    prefixed.sort(key=lambda item: -len(item[0]))

    def base_of(lean_path):
        for prefix, commit in prefixed:
            if lean_path.startswith(prefix):
                return commit
        return default_base

    trees = {}
    diffs = {}
    renamed = {}

    def tree(commit):
        if commit not in trees:
            trees[commit] = git(arguments.repo, "ls-tree", "-r", "--name-only", commit).splitlines()
        return trees[commit]

    def resolve(tail, commit):
        exact = [p for p in tree(commit) if p == tail or p.endswith("/" + tail)]
        return exact

    def changed_paths(commit):
        if commit not in renamed:
            out = git(arguments.repo, "diff", "--name-status", "-M", commit, arguments.new)
            moves = {}
            for line in out.splitlines():
                parts = line.split("\t")
                if parts[0].startswith("R") and len(parts) == 3:
                    moves[parts[1]] = parts[2]
            renamed[commit] = moves
        return renamed[commit]

    results = collections.defaultdict(list)
    counts = collections.Counter()
    for lean_path, lean_line, tail, first, last in citations(arguments.replica):
        commit = base_of(lean_path)
        paths = resolve(tail, commit)
        if not paths:
            counts["unknown"] += 1
            results["unknown"].append((lean_path, lean_line, tail, first, last, commit, ""))
            continue
        if len(paths) > 1:
            counts["ambiguous"] += 1
        for path in paths:
            key = (commit, path)
            if key not in diffs:
                diffs[key] = hunks(arguments.repo, commit, arguments.new, path)
            file_hunks = diffs[key]
            if file_hunks is None:
                moved_to = changed_paths(commit).get(path)
                state = "gone"
                detail = f"renamed to {moved_to}" if moved_to else "deleted"
            else:
                state, new_first = map_range(first, last, file_hunks)
                detail = "" if state == "changed" else f"-> {new_first}"
            counts[state] += 1
            results[state].append((lean_path, lean_line, path, first, last, commit, detail))

    total = sum(counts[s] for s in ("changed", "moved", "gone"))
    print(f"{total} citations checked against {arguments.new}: " + ", ".join(
        f"{counts[s]} {s}" for s in ("changed", "moved", "gone", "ambiguous", "unknown")))
    for state in ("changed", "gone", "unknown", "moved"):
        if arguments.changed_only and state == "moved":
            continue
        rows = results[state]
        if not rows:
            continue
        print(f"\n## {state}")
        by_file = collections.defaultdict(list)
        for row in rows:
            by_file[row[2]].append(row)
        for upstream_path in sorted(by_file):
            rows_here = sorted(by_file[upstream_path], key=lambda row: (row[3], row[0], row[1]))
            print(f"- {upstream_path} ({rows_here[0][5]})")
            if state in ("changed", "gone"):
                log = git(arguments.repo, "log", "--format=%h %s", f"{rows_here[0][5]}..{arguments.new}",
                          "--", upstream_path).splitlines()
                for entry in log[:5]:
                    print(f"  - commit {entry[:110]}")
                if len(log) > 5:
                    print(f"  - and {len(log) - 5} more commits")
            for lean_path, lean_line, _, first, last, _, detail in rows_here:
                span = f"{first}" if first == last else f"{first}-{last}"
                print(f"  - {span}{(' ' + detail) if detail else ''}, cited at {lean_path}:{lean_line}")


if __name__ == "__main__":
    main()

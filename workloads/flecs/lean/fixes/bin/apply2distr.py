#!/usr/bin/env python3
"""Apply a unified diff against flecs's src/ and include/ to the amalgamation.

usage: apply2distr.py <patch> <orig flecs root> <out distr dir>

Each hunk's old text (context and removed lines) is located in distr/flecs.c
(for src/ files) or distr/flecs.h (for include/ files). When it occurs more
than once, the block is widened with the surrounding lines of the original
source file until exactly one occurrence remains. The hunk is then replaced
by its new text. Writes the patched flecs.c/flecs.h to <out distr dir> and
prints where each hunk landed.
"""
import os
import re
import sys


def parse(patch):
    files = []
    cur = None
    lines = open(patch).read().split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    i = 0
    while i < len(lines):
        ln = lines[i]
        if ln.startswith('+++ '):
            path = ln[4:].split('\t')[0]
            if path.startswith('b/'):
                path = path[2:]
            cur = {'path': path, 'hunks': []}
            files.append(cur)
        elif ln.startswith('@@ '):
            m = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', ln)
            h = {'old_start': int(m.group(1)), 'old': [], 'new': []}
            cur['hunks'].append(h)
            i += 1
            while i < len(lines) and not lines[i].startswith('@@ ') \
                    and not lines[i].startswith('diff ') \
                    and not lines[i].startswith('--- '):
                l = lines[i]
                if l.startswith('\\'):
                    i += 1
                    continue
                tag, body = (l[0], l[1:]) if l else (' ', '')
                if tag in ' -':
                    h['old'].append(body)
                if tag in ' +':
                    h['new'].append(body)
                i += 1
            continue
        i += 1
    return files


def find_all(hay, block):
    n = len(block)
    res = []
    first = block[0] if block else None
    for k in range(len(hay) - n + 1):
        if hay[k] == first and hay[k:k + n] == block:
            res.append(k)
    return res


def main():
    patch, root, out = sys.argv[1:4]
    files = parse(patch)
    targets = {}
    for f in files:
        p = f['path']
        if p.startswith('src/'):
            t = 'flecs.c'
        elif p.startswith('include/'):
            t = 'flecs.h'
        else:
            print('skip (not src/ or include/):', p)
            continue
        targets.setdefault(t, []).append(f)
    for t, fl in targets.items():
        src_path = os.path.join(out, t)
        if not os.path.exists(src_path):
            src_path = os.path.join(root, 'distr', t)
        hay = open(src_path).read().split('\n')
        edits = []
        for f in fl:
            orig = open(os.path.join(root, f['path'])).read().split('\n')
            delta = 0
            for h in f['hunks']:
                block = h['old']
                start = h['old_start'] - 1  # 0-based start in orig
                # verify the hunk applies to the original source
                if orig[start:start + len(block)] != block:
                    print('hunk does not match original', f['path'], h['old_start'])
                    sys.exit(1)
                before, after = 0, 0
                while True:
                    blk = orig[start - before:start + len(block) + after]
                    hits = find_all(hay, blk)
                    if len(hits) == 1:
                        k = hits[0] + before
                        break
                    if len(hits) == 0:
                        print('not found in', t, 'for', f['path'], h['old_start'],
                              'widened', before, after)
                        sys.exit(1)
                    if before < start:
                        before += 1
                    if start + len(block) + after < len(orig):
                        after += 1
                    if before > 400:
                        print('ambiguous', f['path'], h['old_start'])
                        sys.exit(1)
                edits.append((k, len(block), h['new'], f['path'], h['old_start']))
        edits.sort(key=lambda e: e[0])
        for a, b in zip(edits, edits[1:]):
            if a[0] + a[1] > b[0]:
                print('overlapping hunks', a[3:], b[3:])
                sys.exit(1)
        for k, n, new, p, s in reversed(edits):
            hay[k:k + n] = new
            print('%s:%d -> %s:%d' % (p, s, t, k + 1))
        os.makedirs(out, exist_ok=True)
        open(os.path.join(out, t), 'w').write('\n'.join(hay))


main()

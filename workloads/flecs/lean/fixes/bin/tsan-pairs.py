#!/usr/bin/env python3
"""List each ThreadSanitizer data race report as 'access1 <-> access2' with the
innermost flecs function (and line) of each access."""
import re, sys
txt = open(sys.argv[1], errors='replace').read()
txt = re.sub(r'\x1b\[[0-9;]*m', '', txt)
reps = txt.split('WARNING: ThreadSanitizer: data race')[1:]
out = {}
for r in reps:
    accs = re.split(r'\n  (?=(?:Previous )?(?:[Aa]tomic )?(?:[Ww]rite|[Rr]ead) of size)', r)[1:3]
    sides = []
    for a in accs:
        kind = a.split(' of size')[0]
        frames = re.findall(r'#\d+ (\S+) (\S+?):(\d+)', a)
        fr = [f for f in frames if f[1].endswith('flecs.c')]
        f = fr[0] if fr else (frames[0] if frames else ('?', '?', '0'))
        sides.append('%s %s:%s' % (kind, f[0], f[2]))
    key = ' <-> '.join(sides)
    out[key] = out.get(key, 0) + 1
for k, v in sorted(out.items(), key=lambda x: -x[1]):
    print('%3d  %s' % (v, k))

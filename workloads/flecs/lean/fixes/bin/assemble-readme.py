#!/usr/bin/env python3
"""Assemble fixes/README.md from bin/head.md, bin/mid.md, the combined-build
results (bin/together.md), the per-finding sections and bin/tail.md."""
import os, re
R = os.environ['FLECS_FIXES_ROOT']
def rd(p):
    return open(os.path.join(R, p)).read().rstrip('\n') + '\n'
secs = sorted(os.listdir(os.path.join(R, 'build/sections')),
              key=lambda n: int(re.match(r'F(\d+)', n).group(1)))
out = [rd('bin/head.md'), rd('bin/mid.md')]
if os.path.exists(os.path.join(R, 'bin/together.md')):
    out.append(rd('bin/together.md'))
out.append('\n## Findings\n\nOne section per finding, in order. The line numbers are those of v4.2.0\'s `src/` unless a path says otherwise. F10, F15 and F24 are left to their upstream issue and PRs.\n')
for s in secs:
    out.append('\n' + rd('build/sections/' + s))
out.append(rd('bin/tail.md'))
open(os.path.join(R, 'fixes/README.md'), 'w').write(''.join(out))
print('sections:', ' '.join(x[:-3] for x in secs))

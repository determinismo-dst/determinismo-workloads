# Compares the replica's results with real Elle's, line by line by :id.
import re, sys
def load(path):
    out = {}
    for line in open(path):
        m = re.match(r'\{:id (\d+)', line)
        if not m: continue
        i = int(m.group(1))
        v = re.search(r':valid\? (true|false|:unknown)', line)
        t = re.search(r':anomaly-types \[([^\]]*)\]', line)
        e = re.search(r':error "', line)
        out[i] = ('error' if e else (v.group(1) if v else '?'),
                  tuple(re.findall(r'"([^"]+)"', t.group(1))) if t else ())
    return out
a, b = load(sys.argv[1]), load(sys.argv[2])
same = diff = 0
for i in sorted(a):
    if i not in b: continue
    if a[i] == b[i]: same += 1
    else:
        diff += 1
        if diff <= 40: print(i, 'replica', a[i], 'elle', b[i])
print('same', same, 'differ', diff)

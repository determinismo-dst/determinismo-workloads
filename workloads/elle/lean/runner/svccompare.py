# Compares the real service's answers with real Elle's (when given) and with the replica's.
# Usage: python3 runner/svccompare.py OUT.edn REPLICA.edn
import re, sys
def field(s, name):
    m = re.search(r':' + name + r' (\[[^\]]*\]|"[^"]*"|:?[\w-]+)', s)
    return m.group(1) if m else None
def norm_valid(v):
    return (v or '').strip('"').lstrip(':')
def norm_list(v):
    return tuple(sorted(re.findall(r'"([^"]+)"', v or '')))
def parse_part(s):
    if s is None: return None
    if ':error' in s: return ('error',)
    return (norm_valid(field(s, 'valid')), norm_list(field(s, 'types')), norm_list(field(s, 'not')))
out = {}
for line in open(sys.argv[1]):
    m = re.match(r'\{:id (\d+), :service (\{.*?\}), :elle (\{.*?\}|nil)\}', line.strip())
    if not m: continue
    out[int(m.group(1))] = (parse_part(m.group(2)), None if m.group(3) == 'nil' else parse_part(m.group(3)))
rep = {}
for line in open(sys.argv[2]):
    m = re.match(r'\{:id (\d+)', line)
    if m: rep[int(m.group(1))] = parse_part(line)
se_same = se_diff = sr_same = sr_diff = 0
for i in sorted(out):
    s, e = out[i]
    if e is not None:
        if s == e: se_same += 1
        else:
            se_diff += 1
            if se_diff <= 15: print('service/elle', i, s, e)
    r = rep.get(i)
    if r is not None:
        if s == r: sr_same += 1
        else:
            sr_diff += 1
            if sr_diff <= 25: print('service/replica', i, 'service', s, 'replica', r)
print('service = elle:', se_same, 'differ:', se_diff)
print('service = replica:', sr_same, 'differ:', sr_diff)

#!/usr/bin/env python3
"""Join margins (VEC file) with a structure signature (LABELS file). usage: famsig.py labels vec [top]"""
import sys, re, itertools
from fractions import Fraction as Fr
from collections import Counter
sys.path.insert(0, '.')
def load(line):
    head, info, body = line.split('|')
    meta = tuple(head.split()[1:3])
    kv = dict(x.split('=') for x in info.split())
    n, deg, K = int(kv['n']), int(kv['deg']), int(kv['K'])
    toks = body.split()
    adj = [[] for _ in range(n)]
    for i, t in enumerate(toks):
        u, l = t.split(':'); adj[i // deg].append((int(u), int(l)))
    return meta, n, deg, K, adj
def comps(n, adj, S):
    seen = [False]*n; sizes = []
    for s in range(n):
        if seen[s]: continue
        seen[s] = True; st = [s]; c = 0
        while st:
            v = st.pop(); c += 1
            for u, l in adj[v]:
                if l in S and not seen[u]: seen[u] = True; st.append(u)
        sizes.append(c)
    return sizes[0] if len(set(sizes)) == 1 else tuple(sorted(Counter(sizes).items()))
sig = {}
for line in open(sys.argv[1]):
    if not line.startswith('LABELS'): continue
    meta, n, deg, K, adj = load(line)
    d = Counter(l for u, l in adj[0])
    s = []
    for r in range(1, K):
        for S in itertools.combinations(range(K), r):
            if sum(d[x] for x in S) >= 2:
                s.append('%s:%s' % (''.join(map(str, S)), comps(n, adj, set(S))))
    sig[meta] = 'deg%s %s' % (''.join(str(d[i]) for i in range(K)), ' '.join(s))
rows = []
for line in open(sys.argv[2]):
    if not line.startswith('VEC'): continue
    parts = line.split('|')
    meta = tuple(parts[0].split()[1:3])
    n, deg, K = map(int, parts[1].split())
    sizes = list(map(int, parts[2].split()))
    status = parts[3].split()[0]
    vecs = [tuple(map(int, v.split(','))) for v in re.findall(r'\(([0-9,]+)\)', parts[4])]
    m = sum(sizes)
    if K == 1 or not vecs: continue
    fair = [Fr((n - 1) * s, m) for s in sizes]
    # depth: min over orbit-subsets S of slack of sum_{i in S} c_i from both sides (cheap proxy; exact for K=2)
    best = None; desc = ''
    for r in range(1, K):
        for S in itertools.combinations(range(K), r):
            vals = [sum(v[i] for i in S) for v in vecs]
            f = sum(fair[i] for i in S)
            for side, d in (('lo', f - min(vals)), ('hi', max(vals) - f)):
                if best is None or d < best:
                    best = d; desc = 'S=%s %s range[%d,%d] fair %.2f' % (''.join(map(str, S)), side, min(vals), max(vals), float(f))
    rows.append((best / n, best, meta, n, K, sizes, status, desc, sig.get(meta, '?')))
rows.sort()
top = int(sys.argv[3]) if len(sys.argv) > 3 else 40
for r in rows[:top]:
    print('%.4f %.2f' % (float(r[0]), float(r[1])), 'CVT[%s,%s]' % r[2], 'K=%d' % r[4], r[5], r[6], '|', r[7], '|', r[8])

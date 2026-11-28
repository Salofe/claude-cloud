#!/usr/bin/env python3
"""For cubic labelled graphs with a 2-factor of 4-cycles (union of orbits): straight circuits, parity bound, and
comparison with the exact minimum number of matching edges (VEC file). usage: c4check.py labels vecfile"""
import sys, re, itertools
from collections import Counter
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
def c4_structures(n, K, adj):
    """yield (S, blobs, mate, opp): S = orbit set forming 4-cycles; mate[v] = matching neighbour; opp[v] = opposite in blob"""
    d = Counter(l for u, l in adj[0])
    for r in range(1, K):
        for S in itertools.combinations(range(K), r):
            if sum(d[x] for x in S) != 2: continue
            S = set(S); opp = [-1]*n; ok = True
            for v in range(n):
                nb = [u for u, l in adj[v] if l in S]
                # opposite vertex: common neighbour structure of a 4-cycle
                a, b = nb
                ca = [u for u, l in adj[a] if l in S and u != v]
                cb = [u for u, l in adj[b] if l in S and u != v]
                if len(ca) != 1 or len(cb) != 1 or ca[0] != cb[0]: ok = False; break
                opp[v] = ca[0]
            if not ok: continue
            mate = [[u for u, l in adj[v] if l not in S][0] for v in range(n)]
            yield S, mate, opp
def straight_circuits(n, mate, opp):
    seen = [False]*n; lens = []
    for s in range(n):
        if seen[s]: continue
        v = s; L = 0
        while not seen[v]:
            seen[v] = True; w = opp[v]; seen[w] = True; L += 1; v = mate[w]
        lens.append(L)
    return lens
vec = {}
for line in open(sys.argv[2]):
    if not line.startswith('VEC'): continue
    parts = line.split('|'); meta = tuple(parts[0].split()[1:3])
    n, deg, K = map(int, parts[1].split()); sizes = list(map(int, parts[2].split()))
    vecs = [tuple(map(int, v.split(','))) for v in re.findall(r'\(([0-9,]+)\)', parts[4])]
    vec[meta] = (sizes, vecs)
for line in open(sys.argv[1]):
    if not line.startswith('LABELS'): continue
    meta, n, deg, K, adj = load(line)
    if deg != 3 or meta not in vec: continue
    for S, mate, opp in c4_structures(n, K, adj):
        lens = straight_circuits(n, mate, opp)
        # each straight circuit visits L blobs but the vertex walk covers 2L vertices; circuits come in pairs? count distinct
        N = n // 4
        sizes, vecs = vec[meta]
        Mset = [i for i in range(K) if i not in S]
        cmin = min(sum(v[i] for i in Mset) for v in vecs)
        tmin = cmin - (N - 1)
        cl = Counter(lens)
        nodd = sum(c for L, c in cl.items() if L % 2 == 1)
        print('CVT[%s,%s] K=%d N=%d blobs=%s straight circuits %s  odd=%d  parity bound t>=%s  exact t_min=%d  fair threshold %.2f' % (meta[0], meta[1], K, N, sorted(S), dict(cl), nodd, (nodd // 2 - 1 if nodd else 0), tmin, (N + 2) / 3))

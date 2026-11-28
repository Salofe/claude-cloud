#!/usr/bin/env python3
"""Independent verification of PASS certificates (CERT lines printed by ftc -c / ft -c).
For each certificate: recompute the edge orbits of Aut(G) by plain backtracking (no code shared with the C
checker), check that every listed path is a Hamiltonian path, and check with exact rational arithmetic that
the orbit-size vector lies in the cone of the paths' orbit-count vectors.
usage: verify_cert.py < certs.txt"""
import sys
from fractions import Fraction
sys.setrecursionlimit(100000)

def find_aut(n, adj, order, parent, a0, a1, b0, b1):
    img = [-1] * n
    used = [False] * n
    img[a0] = b0; img[a1] = b1; used[b0] = True; used[b1] = True
    assigned = [a0, a1]
    # iterative backtracking along BFS order
    idx = 2
    choices = [None] * n
    while True:
        if idx == n:
            return img
        x = order[idx]
        if choices[idx] is None:
            cand = []
            pc = img[parent[x]]
            for c in adj[pc]:
                if used[c]: continue
                ok = True
                for y in adj[x]:
                    iy = img[y]
                    if iy >= 0 and iy not in adjset[c]: ok = False; break
                if ok:
                    # non-neighbours assigned so far must map to non-neighbours: count check
                    cnt = sum(1 for y in adj[x] if img[y] >= 0)
                    cnt2 = sum(1 for z in adj[c] if used[z])
                    if cnt != cnt2: ok = False
                if ok: cand.append(c)
            choices[idx] = cand
        if choices[idx]:
            c = choices[idx].pop()
            img[x] = c; used[c] = True
            idx += 1
            if idx < n: choices[idx] = None
        else:
            choices[idx] = None
            idx -= 1
            if idx < 2: return None
            x = order[idx]
            used[img[x]] = False; img[x] = -1

def edge_orbits(n, adj):
    global adjset
    adjset = [set(a) for a in adj]
    def bfs(a0, a1):
        order = [a0, a1]; parent = {a1: a0}; seen = {a0, a1}; i = 0
        while i < len(order):
            v = order[i]; i += 1
            for u in adj[v]:
                if u not in seen: seen.add(u); parent[u] = v; order.append(u)
        return order, parent
    nb0 = adj[0]
    uf = {u: u for u in nb0}
    def find(x):
        while uf[x] != x: uf[x] = uf[uf[x]]; x = uf[x]
        return x
    arc_class = {}
    for u in nb0:
        order, parent = bfs(0, u)
        for v in range(n):
            for w in adj[v]:
                if (v, w) in arc_class: continue
                if find_aut(n, adj, order, parent, 0, u, v, w) is not None:
                    arc_class[(v, w)] = u
    for v in range(n):
        for w in adj[v]:
            if (v, w) not in arc_class: return None
    for v in range(n):
        for w in adj[v]:
            a, b = find(arc_class[(v, w)]), find(arc_class[(w, v)])
            if a != b: uf[a] = b
    ids = {}; lab = {}
    for v in range(n):
        for w in adj[v]:
            r = find(arc_class[(v, w)])
            if r not in ids: ids[r] = len(ids)
            lab[(v, w)] = ids[r]
    return len(ids), lab

def in_cone(vectors, b):
    k = len(b); N = len(vectors)
    T = [[Fraction(vectors[j][i]) for j in range(N)] + [Fraction(int(i == r)) for r in range(k)] + [Fraction(b[i])] for i in range(k)]
    basis = [N + i for i in range(k)]
    while True:
        zrow = [sum(T[r][j] for r in range(k) if basis[r] >= N) for j in range(N)]
        ent = -1
        for j in range(N):
            if zrow[j] > 0 and j not in basis: ent = j; break
        if ent < 0:
            return sum(T[r][-1] for r in range(k) if basis[r] >= N) == 0
        lv = -1; best = None
        for r in range(k):
            if T[r][ent] > 0:
                ratio = T[r][-1] / T[r][ent]
                if best is None or ratio < best or (ratio == best and basis[r] < basis[lv]): best = ratio; lv = r
        piv = T[lv][ent]
        T[lv] = [x / piv for x in T[lv]]
        for r in range(k):
            if r != lv and T[r][ent] != 0:
                f = T[r][ent]; T[r] = [x - f * y for x, y in zip(T[r], T[lv])]
        basis[lv] = ent

ok = bad = 0
for line in sys.stdin:
    if not line.startswith('CERT'): continue
    parts = line.split('|')
    meta = parts[0].split()[1:3]
    kv = dict(x.split('=') for x in parts[1].split())
    n, deg, K = int(kv['n']), int(kv['deg']), int(kv['K'])
    sizes = list(map(int, parts[2].split()[1:]))
    a = list(map(int, parts[3].split()[1:]))
    adj = [a[v*deg:(v+1)*deg] for v in range(n)]
    ptoks = parts[4].split(';')
    paths = [list(map(int, p.split())) for p in ptoks[1:]]
    res = edge_orbits(n, adj)
    if res is None: print('BAD notVT', meta); bad += 1; continue
    K2, lab = res
    sz2 = [0] * K2
    for (v, w), c in lab.items():
        if v < w: sz2[c] += 1
    problems = []
    if sorted(sz2) != sorted(sizes): problems.append('orbit sizes differ: C=%s independent=%s' % (sorted(sizes), sorted(sz2)))
    vecs = []
    for p in paths:
        if sorted(p) != list(range(n)) or any(p[i+1] not in adjset[p[i]] for i in range(n-1)):
            problems.append('invalid path'); continue
        c = [0] * K2
        for i in range(n-1): c[lab[(p[i], p[i+1])]] += 1
        vecs.append(c)
    if not problems and not in_cone(vecs, sz2): problems.append('fair vector not in cone of certificate paths')
    if problems: bad += 1; print('BAD', meta, problems)
    else: ok += 1
    sys.stderr.write("%s n=%d %s\n" % (meta, n, "BAD" if problems else "ok")); sys.stderr.flush()
    sys.stdout.flush()
print('verified ok:', ok, 'bad:', bad)

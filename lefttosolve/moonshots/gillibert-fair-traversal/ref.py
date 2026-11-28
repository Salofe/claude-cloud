#!/usr/bin/env python3
"""Independent brute-force reference for the fair traversal check (small graphs only).

usage: ref.py maxn < graphs.g6
For each connected regular graph on at most maxn vertices: edge orbits by plain backtracking
automorphism search, all Hamiltonian-path orbit-count vectors by subset DP (all start vertices),
exact rational phase-1 simplex for membership of the orbit-size vector in the cone.
Prints: idx n deg k sorted(sizes) PASS|FAIL|NOHAM [details]
"""
import sys
from fractions import Fraction


def parse_g6(s):
    data = [ord(c) - 63 for c in s.strip()]
    n = data[0]
    bits = []
    for x in data[1:]:
        for b in range(5, -1, -1):
            bits.append((x >> b) & 1)
    adj = [set() for _ in range(n)]
    t = 0
    for j in range(1, n):
        for i in range(j):
            if bits[t]:
                adj[i].add(j)
                adj[j].add(i)
            t += 1
    return n, adj


def connected(n, adj):
    seen = {0}
    st = [0]
    while st:
        v = st.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u)
                st.append(u)
    return len(seen) == n


def find_aut(n, adj, order, parent, a0, a1, b0, b1):
    """automorphism with a0->b0, a1->b1 (a1 adjacent a0), by backtracking along BFS order."""
    img = {a0: b0, a1: b1}
    used = {b0, b1}
    if (b1 in adj[b0]) != (a1 in adj[a0]):
        return None

    def rec(i):
        if i == n:
            return True
        x = order[i]
        if x in img:
            return rec(i + 1)
        for c in adj[img[parent[x]]]:
            if c in used:
                continue
            ok = True
            for y, iy in img.items():
                if (y in adj[x]) != (iy in adj[c]):
                    ok = False
                    break
            if ok:
                img[x] = c
                used.add(c)
                if rec(i + 1):
                    return True
                del img[x]
                used.discard(c)
        return False

    return dict(img) if rec(0) else None


def edge_orbits(n, adj):
    # BFS order from 0 starting with (0, u)
    labels = {}
    reps = []  # arcs (0,u) representing arc orbits
    nb0 = sorted(adj[0])
    # union-find over neighbours of 0
    uf = {u: u for u in nb0}

    def find(x):
        while uf[x] != x:
            uf[x] = uf[uf[x]]
            x = uf[x]
        return x

    def bfs(a0, a1):
        order = [a0, a1]
        parent = {a1: a0}
        seen = {a0, a1}
        i = 0
        while i < len(order):
            v = order[i]
            i += 1
            for u in sorted(adj[v]):
                if u not in seen:
                    seen.add(u)
                    parent[u] = v
                    order.append(u)
        return order, parent

    arc_class = {}
    for u in nb0:
        order, parent = bfs(0, u)
        # which arcs (v,w) is (0,u) mapped to
        for v in range(n):
            for w in adj[v]:
                if (v, w) in arc_class:
                    continue
                if find_aut(n, adj, order, parent, 0, u, v, w) is not None:
                    arc_class[(v, w)] = u
    # every arc must be classified (vertex-transitive); else not VT
    for v in range(n):
        for w in adj[v]:
            if (v, w) not in arc_class:
                return None
    # merge arc classes with reverses
    for v in range(n):
        for w in adj[v]:
            a, b = find(arc_class[(v, w)]), find(arc_class[(w, v)])
            if a != b:
                uf[a] = b
    ids = {}
    lab = {}
    for v in range(n):
        for w in adj[v]:
            r = find(arc_class[(v, w)])
            if r not in ids:
                ids[r] = len(ids)
            lab[(v, w)] = ids[r]
    return len(ids), lab


def count_vectors(n, adj, lab, k):
    full = (1 << n) - 1
    cur = {}
    for s in range(n):
        cur[(1 << s, s)] = {tuple([0] * k)}
    for step in range(n - 1):
        nxt = {}
        for (mask, last), vs in cur.items():
            for u in adj[last]:
                if mask >> u & 1:
                    continue
                j = lab[(last, u)]
                key = (mask | 1 << u, u)
                st = nxt.setdefault(key, set())
                for c in vs:
                    c2 = list(c)
                    c2[j] += 1
                    st.add(tuple(c2))
        cur = nxt
    allv = set()
    for (mask, last), vs in cur.items():
        if mask == full:
            allv |= vs
    return allv


def in_cone(vectors, b):
    """exact phase-1 simplex (Bland). returns (True, None) or (False, y) with y.v<=0 for all v, y.b>0."""
    k = len(b)
    A = [list(map(Fraction, v)) for v in vectors]
    N = len(A)
    # tableau rows: basis var index (>=N artificial), row = coefficients over N+k columns + rhs
    T = []
    for i in range(k):
        row = [A[j][i] for j in range(N)] + [Fraction(int(i == r)) for r in range(k)] + [Fraction(b[i])]
        T.append(row)
    basis = [N + i for i in range(k)]
    while True:
        # dual y: cost of artificial =1. reduced cost of column j: c_j - sum_r cB_r T[r][j]
        zrow = [sum(T[r][j] for r in range(k) if basis[r] >= N) for j in range(N + k)]
        ent = -1
        for j in range(N):
            if zrow[j] > 0 and j not in basis:
                ent = j
                break
        if ent < 0:
            obj = sum(T[r][-1] for r in range(k) if basis[r] >= N)
            if obj == 0:
                return True, None
            # y_i = sum over artificial basis rows of Binv[r][i]; Binv columns are the artificial columns
            y = [sum(T[r][N + i] for r in range(k) if basis[r] >= N) for i in range(k)]
            return False, y
        lv = -1
        best = None
        for r in range(k):
            if T[r][ent] > 0:
                ratio = T[r][-1] / T[r][ent]
                if best is None or ratio < best or (ratio == best and basis[r] < basis[lv]):
                    best = ratio
                    lv = r
        piv = T[lv][ent]
        T[lv] = [x / piv for x in T[lv]]
        for r in range(k):
            if r != lv and T[r][ent] != 0:
                f = T[r][ent]
                T[r] = [x - f * yv for x, yv in zip(T[r], T[lv])]
        basis[lv] = ent


def main():
    maxn = int(sys.argv[1])
    idx = 0
    for line in sys.stdin:
        idx += 1
        line = line.strip()
        if not line:
            continue
        n, adj = parse_g6(line)
        if n < 2 or n > maxn:
            continue
        if not connected(n, adj):
            continue
        r = edge_orbits(n, adj)
        if r is None:
            print(idx, n, 'notVT')
            continue
        k, lab = r
        deg = len(adj[0])
        sizes = [0] * k
        for (v, w), c in lab.items():
            if v < w:
                sizes[c] += 1
        vs = count_vectors(n, adj, lab, k)
        if not vs:
            print(idx, n, deg, k, sorted(sizes), 'NOHAM')
            continue
        ok, y = in_cone(sorted(vs), sizes)
        if ok:
            print(idx, n, deg, k, sorted(sizes), 'PASS', len(vs))
        else:
            print(idx, n, deg, k, sorted(sizes), 'FAIL', len(vs), 'sizes', sizes, 'y', [str(t) for t in y], 'vectors', sorted(vs), line)
        sys.stdout.flush()


main()

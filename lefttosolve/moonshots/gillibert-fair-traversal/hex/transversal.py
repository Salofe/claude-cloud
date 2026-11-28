#!/usr/bin/env python3
"""CVT[876,4]: explicit Hamiltonian cycle crossing every hexagon of the 2-factor exactly once.
Uses the Cayley structure <a,x> recovered by group.py (json): H = F xor (alternating cycle of the word (x a x^-1 a)^k).
Verifies everything from the raw adjacency list (first argument)."""
import sys, json
raw = open(sys.argv[1]).readline()
adjl = list(map(int, raw.split('|')[1].split()))
n = len(adjl) // 3
adj = [set(adjl[3*v:3*v+3]) for v in range(n)]
assert all(len(s) == 3 for s in adj) and all(v in adj[u] for v in range(n) for u in adj[v])
J = json.load(open(sys.argv[2]))
M, succ = J['M'], J['succ']
pred = [None]*n
for v in range(n): pred[succ[v]] = v
# sanity: M is a perfect matching of G, succ a permutation along edges, and the three neighbours are M, succ, pred
for v in range(n):
    assert M[M[v]] == v and adj[v] == {M[v], succ[v], pred[v]} and len({M[v], succ[v], pred[v]}) == 3
# regularity of <a,x>: orbit of the identity permutation under right multiplication has size n (checked by group.py);
# re-check here in a cheap way: build words w_v with 0.w_v = v by BFS and verify that the action is free, i.e. the
# permutation u -> u.w_v has no fixed point for v != 0 and that these n permutations are closed under a and x.
from collections import deque
perm_a = tuple(M); perm_x = tuple(succ)
def mul(p, q): return tuple(q[i] for i in p)
e = tuple(range(n)); elems = {0: e}; dq = deque([0])
while dq:
    v = dq.popleft(); p = elems[v]
    for g in (perm_a, perm_x):
        q = mul(p, g); w = q[0]
        if w not in elems: elems[w] = q; dq.append(w)
        else: assert elems[w] == q, 'not regular'
assert len(elems) == n
print('regular group of order', n, 'verified: left multiplications are automorphisms with edge orbits M (a-edges) and F (x-edges)')
Fedges = set()
for v in range(n): Fedges.add(frozenset((v, succ[v])))
Medges = set(frozenset((v, M[v])) for v in range(n))
assert len(Fedges) == n and len(Medges) == n // 2
# alternating closed walk from 0: x, a, x^-1, a, ...
rem, add = set(), set(); v = 0; steps = 0
while True:
    w = succ[v]; rem.add(frozenset((v, w))); u = M[w]; add.add(frozenset((w, u)))
    w2 = pred[u]; rem.add(frozenset((u, w2))); v2 = M[w2]; add.add(frozenset((w2, v2)))
    v = v2; steps += 1
    if v == 0: break
print('period', steps, 'removed F-edges', len(rem), 'added M-edges', len(add))
H = (Fedges - rem) | add
nb = [[] for _ in range(n)]
for ed in H:
    u, w = tuple(ed); nb[u].append(w); nb[w].append(u)
assert all(len(x) == 2 for x in nb)
cyc = [0]; p, c = 0, nb[0][0]
while c != 0:
    cyc.append(c); nx = nb[c][0] if nb[c][1] == p else nb[c][1]; p, c = c, nx
print('cycle length through 0:', len(cyc), 'Hamiltonian' if len(cyc) == n else 'NOT Hamiltonian')
assert len(cyc) == n and len(set(cyc)) == n
a_cyc = sum(1 for i in range(n) if frozenset((cyc[i], cyc[(i+1) % n])) in Medges)
print('M-edges on the Hamiltonian cycle:', a_cyc, ' F-edges:', n - a_cyc)
# path 1: delete an M-edge of the cycle
i0 = next(i for i in range(n) if frozenset((cyc[i], cyc[(i+1) % n])) in Medges)
P1 = cyc[i0+1:] + cyc[:i0+1]
def counts(P):
    assert len(P) == n and len(set(P)) == n and all(P[i+1] in adj[P[i]] for i in range(n-1))
    a = sum(1 for i in range(n-1) if frozenset((P[i], P[i+1])) in Medges)
    return a, n - 1 - a
c1 = counts(P1)
# path 2: a Hamiltonian path with many M-edges: greedy rotation-extension (Posa) preferring M-edges
import random
random.seed(1)
def posa():
    P = [0]; pos = {0: 0}
    it = 0
    while len(P) < n and it < 2000000:
        it += 1
        v = P[-1]
        cand = [u for u in adj[v] if u not in pos]
        if cand:
            u = M[v] if M[v] in cand else random.choice(cand)
            pos[u] = len(P); P.append(u); continue
        u = random.choice([u for u in adj[v] if u != P[-2]])
        i = pos[u]
        seg = P[i+1:]; seg.reverse(); P[i+1:] = seg
        for j in range(i+1, len(P)): pos[P[j]] = j
    return P if len(P) == n else None
P2 = posa()
c2 = counts(P2)
print('path counts (M,F):', c1, c2, ' orbit sizes (438, 876)')
# cone test in dimension 2: (438,876) in cone{c1,c2} iff the determinants have opposite (weak) signs
d1 = c1[0]*876 - c1[1]*438; d2 = c2[0]*876 - c2[1]*438
print('determinants', d1, d2, 'PASS' if d1 * d2 <= 0 else 'no conclusion')
json.dump({'P1': P1, 'P2': P2}, open(sys.argv[2] + '.paths.json', 'w'))

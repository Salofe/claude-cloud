"""Greedy rectangle partition of the perfect matchings of K_2k (k even): an upper bound for the number of
k-split products needed for det_2k through the Pfaffian expansion (see det_pfaffian_cover.py for the model and
for the optimal value 15 at k = 4).  The identity is verified on a random integer matrix (exact arithmetic).
usage: python3 det_pfaffian_greedy.py K"""
import itertools, math, random, sys
import numpy as np
from sympy import Matrix
k = int(sys.argv[1]); m = 2 * k
def matchings(rows):
    rows = list(rows)
    if not rows: yield (); return
    a = rows[0]
    for j in range(1, len(rows)):
        for M in matchings(rows[1:j] + rows[j + 1:]): yield ((a, rows[j]),) + M
def sgn(p):
    p = list(p); s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]: s = -s
    return s
def msgn(M): return sgn([x for e in M for x in e])
pairings = [S for S in itertools.combinations(range(m), k) if 0 in S]
blocks = []
for S in pairings:
    Sc = tuple(i for i in range(m) if i not in S)
    blocks.append((S, [tuple(sorted(M)) for M in matchings(S)], [tuple(sorted(M)) for M in matchings(Sc)]))
nb = len(blocks[0][1])
allM = {}
for M in matchings(range(m)): allM[tuple(sorted(M))] = len(allM)
ids = np.array([[[allM[tuple(sorted(a + b))] for b in MC] for a in MS] for (S, MS, MC) in blocks])   # (N, nb, nb)
unc = np.ones(len(allM), bool)
def best_rect(U):
    """large all-ones rectangle of the 0/1 matrix U (heuristic: seeded by each row and each column)"""
    best = (0, None, None)
    for T in (False, True):
        V = U.T if T else U
        for i in range(V.shape[0]):
            C = V[i]
            if not C.any(): continue
            R = V[:, C].all(axis=1)
            # also try shrinking the column set to gain rows: columns sorted by popularity
            area = R.sum() * C.sum()
            if area > best[0]: best = (area, (C, R) if T else (R, C), None)
            cols = np.where(C)[0]; order = cols[np.argsort(-V[:, cols].sum(0))]
            for t in range(1, len(order)):
                C2 = np.zeros_like(C); C2[order[:t]] = True
                R2 = V[:, C2].all(axis=1); a2 = R2.sum() * t
                if a2 > best[0]: best = (a2, (C2, R2) if T else (R2, C2), None)
    return best[0], best[1]
chosen = []
while unc.any():
    cand = (0, None, None)
    for p in range(len(blocks)):
        U = unc[ids[p]]
        if U.sum() <= cand[0]: continue
        area, rc = best_rect(U)
        if area > cand[0]: cand = (area, p, rc)
    area, p, (R, C) = cand
    chosen.append((p, np.where(R)[0], np.where(C)[0]))
    unc[ids[p][np.ix_(R, C)].ravel()] = False
print(f"k={k}: {len(allM)} perfect matchings, block size {nb}x{nb}; greedy partition into {len(chosen)} rectangles on "
      f"{len(set(c[0] for c in chosen))} pairings;  counting bound {math.ceil(len(allM) / nb**2)},  one per pairing {len(pairings)},  Laplace {math.comb(m, k)}")
W = Matrix(m, m, lambda i, j: (1 if j == i + 1 and i % 2 == 0 else (-1 if i == j + 1 and j % 2 == 0 else 0)))
random.seed(2); Rm = Matrix(m, m, lambda i, j: random.randint(-3, 3)); Gm = Rm * W * Rm.T
part = lambda Ms: sum(msgn(M) * math.prod(Gm[a, b] for a, b in M) for M in Ms)
tot = 0
for p, R, C in chosen:
    S, MS, MC = blocks[p]; Sc = [i for i in range(m) if i not in S]
    tot += sgn(list(S) + Sc) * part([MS[i] for i in R]) * part([MC[j] for j in C])
assert tot == Rm.det()
print(f"exact check passed: det_{m} = sum of {len(chosen)} {k}-split products (random integer matrix)")

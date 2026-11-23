"""det_2k as a sum of FEWER than C(2k,k)/2 k-split products, for k even, from the Pfaffian expansion.

det(R) = Pf(R W R^T) for the standard symplectic form W, i.e. with w(x,y) = x^T W y,
        det(r_0..r_{2k-1}) = sum over perfect matchings M of the rows  sgn(M) * prod_{{a,b} in M} w(r_a, r_b).
A matching M with no edge crossing the cut S | S^c is a pair (a, b) of matchings of S and S^c, and
sgn(M) prod = [sgn-part(a) prod_a] * [sgn-part(b) prod_b].  So for sets X of matchings of S and Y of matchings
of S^c,  (sum_{a in X} ...) * (sum_{b in Y} ...)  is ONE k-split product with row set S that accounts for the
matchings in the 'rectangle' X x Y.  A partition of all (2k-1)!! perfect matchings into rectangles is therefore a
decomposition of det_2k into that many k-split products.  This script finds a small partition by integer
programming and verifies the resulting identity on random integer matrices (exact arithmetic).

usage: python3 det_pfaffian_cover.py K [time_limit_seconds]
"""
import itertools, math, random, sys
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
from sympy import Matrix

k = int(sys.argv[1]); m = 2 * k; tl = float(sys.argv[2]) if len(sys.argv) > 2 else 120
assert k % 2 == 0

def matchings(rows):
    rows = list(rows)
    if not rows: yield (); return
    a = rows[0]
    for j in range(1, len(rows)):
        b = rows[j]; rest = rows[1:j] + rows[j + 1:]
        for M in matchings(rest): yield ((a, b),) + M

def sgn(p):
    p = list(p); s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]: s = -s
    return s
def msgn(M): return sgn([x for e in M for x in e])

allM = [tuple(sorted(M)) for M in matchings(range(m))]; idx = {M: i for i, M in enumerate(allM)}
pairings = [S for S in itertools.combinations(range(m), k) if 0 in S]
rects = []        # (S, X, Y) with X, Y tuples of matchings
for S in pairings:
    Sc = tuple(i for i in range(m) if i not in S)
    MS = [tuple(sorted(M)) for M in matchings(S)]; MC = [tuple(sorted(M)) for M in matchings(Sc)]
    subsS = [X for r in range(1, len(MS) + 1) for X in itertools.combinations(MS, r)]
    subsC = [Y for r in range(1, len(MC) + 1) for Y in itertools.combinations(MC, r)]
    for X in subsS:
        for Y in subsC: rects.append((S, X, Y))
print(f"k={k}: {len(allM)} perfect matchings, {len(pairings)} pairings, {len(rects)} rectangles; "
      f"counting bound ceil({len(allM)}/{len(list(matchings(range(k))))**2}) = {math.ceil(len(allM)/len(list(matchings(range(k))))**2)}", flush=True)
A = lil_matrix((len(allM), len(rects)))
for j, (S, X, Y) in enumerate(rects):
    for a in X:
        for b in Y: A[idx[tuple(sorted(a + b))], j] = 1
res = milp(np.ones(len(rects)), constraints=LinearConstraint(A.tocsr(), 1, 1), bounds=Bounds(0, 1),
           integrality=np.ones(len(rects)), options=dict(time_limit=tl, disp=False))
if res.x is None:
    print("no feasible partition found within the time limit"); sys.exit()
chosen = [rects[j] for j in np.where(res.x > 0.5)[0]]
print(f"partition of the matchings into {len(chosen)} rectangles (solver status {res.status}: "
      f"{'optimal' if res.status == 0 else 'time limit, feasible'}); pairings used: {len(set(c[0] for c in chosen))}; "
      f"Laplace needs {math.comb(m, k)}, one product per pairing needs {math.comb(m, k)//2}", flush=True)
for S, X, Y in chosen:
    print("   rows", ''.join(map(str, S)), "|", ''.join(str(i) for i in range(m) if i not in S), f"  {len(X)} x {len(Y)} matchings")

# exact verification
W = Matrix(m, m, lambda i, j: (1 if j == i + 1 and i % 2 == 0 else (-1 if i == j + 1 and j % 2 == 0 else 0)))
random.seed(1)
for trial in range(3):
    R = Matrix(m, m, lambda i, j: random.randint(-4, 4))
    Gm = R * W * R.T                      # Gm[a,b] = w(r_a, r_b)
    def part(Ms):                          # sum over matchings of sgn * product, as a function of those rows only
        return sum(msgn(M) * math.prod(Gm[a, b] for a, b in M) for M in Ms)
    total = 0
    for S, X, Y in chosen:
        Sc = [i for i in range(m) if i not in S]
        total += sgn(list(S) + Sc) * part(X) * part(Y)
    assert total == R.det(), (total, R.det())
print(f"exact check passed on 3 random integer matrices: det_{m} = sum of {len(chosen)} {k}-split products")

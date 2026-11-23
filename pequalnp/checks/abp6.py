"""Neighbouring layers of the square construction for k = 3 (6x6), lower bound by counting.
Middle layer contains ten squares X(R) X(R^c), X(R) = c q1(R) + lam q2(R) = a direct sum of two 3x3 permanent
tensors (slice rank 6, checked numerically below; it also follows from additivity of slice rank under direct sums).
Orientation: for each pairing one of R, R^c is on the source side. A layer-2 vertex u (row pair U) can only feed
source-side sets R containing U, and each X(R) needs >= 6 slices (bilinear form of a layer-2 vertex times a linear form
in the third row). Same for layer 4 with sink sides. LP relaxation of the two covering problems, all 2^10 orientations.
"""
import itertools
import numpy as np
from scipy.optimize import linprog, minimize
from scipy.linalg import null_space

# --- slice rank of P3 (+) P3: minimum of |T| on V1 x V2 x V3 over subspaces with codimensions summing to 5
T = np.zeros((6, 6, 6))
for p in itertools.permutations(range(3)):
    T[p] = 1; T[tuple(c + 3 for c in p)] = 0.7
rng = np.random.default_rng(0)
def obj(z, shape):
    i, subs = 0, []
    for n in shape:
        cov = []
        for _ in range(n):
            v = z[i:i + 6] + 1j * z[i + 6:i + 12]; i += 12
            cov.append(v / np.linalg.norm(v))
        subs.append(null_space(np.array(cov)) if cov else np.eye(6))
    return float(np.linalg.norm(np.einsum('abc,ai,bj,ck->ijk', T, *subs)))
print("P3 (+) 0.7 P3: min of the norm of the restriction to V1 x V2 x V3 (codimensions a,b,c), 12 starts each")
for shape in [(5, 0, 0), (4, 1, 0), (3, 2, 0), (3, 1, 1), (2, 2, 1), (2, 2, 2), (3, 3, 0)]:
    best = min(minimize(obj, rng.standard_normal(12 * sum(shape)), args=(shape,), method='BFGS',
                        options={'gtol': 1e-10, 'maxiter': 1500}).fun for _ in range(12))
    print(f"   codimensions {shape} (sum {sum(shape)}): min = {best:.5f}", flush=True)

# --- covering LPs
k = 3; m = 6
pairs = [R for R in itertools.combinations(range(m), k) if 0 in R]
U2 = list(itertools.combinations(range(m), k - 1))
def lp(sets, need=2 * k):
    A = np.zeros((len(sets), len(U2)))
    for i, R in enumerate(sets):
        for j, U in enumerate(U2):
            if set(U) <= set(R):
                A[i, j] = 1
    r = linprog(np.ones(len(U2)), A_ub=-A, b_ub=-need * np.ones(len(sets)), bounds=(0, None), method='highs')
    return r.fun
vals = []
for orient in itertools.product((0, 1), repeat=len(pairs)):
    src = [R if o == 0 else tuple(i for i in range(m) if i not in R) for o, R in zip(orient, pairs)]
    snk = [tuple(i for i in range(m) if i not in R) for R in src]
    vals.append((lp(src) + lp(snk), lp(src), lp(snk), orient))
vals.sort()
print("k=3: min over the 1024 orientations of LP(layer 2) + LP(layer 4):", round(vals[0][0], 3),
      " (layer 2:", round(vals[0][1], 3), ", layer 4:", round(vals[0][2], 3), ");  ordered program: 15 + 15 = 30")
print("   distribution of the sum:", sorted({round(v[0], 2) for v in vals})[:8], "...")

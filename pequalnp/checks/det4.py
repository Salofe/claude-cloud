"""Context check: the same 'difference of squares' trick for the DETERMINANT.
For k even, det_{2k} = sum over the N = C(2k,k)/2 pairings {S, S^c} of sgn(S) (d1(S) + d2(S)) (d1(S^c) + d2(S^c)),
d1/d2 = minors of the rows S on the first/second block of columns. Exact, no limit (the leftover terms are determinants
with repeated columns). Verified here for 4x4 (3 products instead of Laplace's 6) and 8x8 (35 instead of 70)."""
import itertools, numpy as np
def sgn_perm(p):
    s = 1
    p = list(p)
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]: s = -s
    return s
rng = np.random.default_rng(1)
for k in (2, 4):
    m = 2 * k
    A = rng.integers(-3, 4, size=(m, m)).astype(object)
    def minor(rows, cols):
        return sum(sgn_perm(p) * np.prod([A[rows[i], cols[p[i]]] for i in range(k)]) for p in itertools.permutations(range(k)))
    total = 0
    for S in itertools.combinations(range(m), k):
        if 0 not in S: continue
        Sc = tuple(i for i in range(m) if i not in S)
        sg = sgn_perm(S + Sc)
        c1, c2 = tuple(range(k)), tuple(range(k, m))
        total += sg * (minor(S, c1) + minor(S, c2)) * (minor(Sc, c1) + minor(Sc, c2))
    from sympy import Matrix
    print(f"k={k}: sum over {len([S for S in itertools.combinations(range(m), k) if 0 in S])} pairings = {total},  det = {Matrix(A.tolist()).det()}")

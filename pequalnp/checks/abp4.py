"""Item 6: the explicit five-term identity of FiveTerm.lean as the middle layer of an unordered
set-multilinear branching program for the 4x4 permanent: how wide must layers 1 and 3 be?

Model. Layer-1 vertices: linear forms in ONE row. Layer-3 vertices: sets of three rows; the edge to the
sink is a linear form in the remaining row. A middle vertex v has a row pair S_v; its source-side polynomial
F_v (bilinear form in rows S_v = {a,b}, matrix M) must be sum_u alpha_u(x_a) beta(x_b) + sum_u' alpha_u'(x_b) beta'(x_a)
over layer-1 vertices u reading a, u' reading b: i.e. M in L_a (x) C^4 + C^4 (x) L_b, L_r = span of the layer-1 forms
reading row r. Same for the sink-side polynomial G_v and the layer-3 forms. Necessary: dim L_a + dim L_b >= rank of
every matrix in the span of the forms that sit on the pair {a,b}.
For each of the 2^5 ways of choosing which factor of each of the five terms is on the source side, the minimum
of (layer 1 + layer 3) allowed by these rank inequalities is computed by brute force over dimensions.
"""
import itertools
import numpy as np
lam = 0.37
def E(p, q):
    M = np.zeros((4, 4)); M[p, q] = 1; return M
sym = lambda p, q: E(p, q) + E(q, p)
alt = lambda p, q: E(p, q) - E(q, p)
# five terms: (rows of first factor, matrix), (rows of second factor, matrix); coefficients are irrelevant for ranks
terms = [
    (((0, 1), sym(0, 1)), ((2, 3), sym(2, 3))),
    (((0, 1), sym(2, 3)), ((2, 3), sym(0, 1))),
    (((0, 1), alt(0, 1) / lam), ((2, 3), alt(0, 1))),
    (((0, 2), (sym(0, 1) + lam * sym(2, 3)) / lam), ((1, 3), sym(0, 1) + lam * sym(2, 3))),
    (((0, 3), -(sym(0, 1) - lam * sym(2, 3)) / lam), ((1, 2), sym(0, 1) - lam * sym(2, 3))),
]
# check the identity numerically: perm - lam * alt23(0,1) alt23(2,3) = sum of the five terms
rng = np.random.default_rng(0)
A = rng.standard_normal((4, 4))
def val(rows, M): return A[rows[0]] @ M @ A[rows[1]]
perm = sum(np.prod([A[i, s[i]] for i in range(4)]) for s in itertools.permutations(range(4)))
lhs = perm - lam * val((0, 1), alt(2, 3)) * val((2, 3), alt(2, 3))
rhs = sum(val(*f) * val(*g) for f, g in terms)
print("five-term identity holds numerically:", abs(lhs - rhs) < 1e-10)

def maxrank(mats):
    r = 0
    for _ in range(5):
        c = rng.standard_normal(len(mats))
        r = max(r, np.linalg.matrix_rank(sum(ci * M for ci, M in zip(c, mats)), tol=1e-9))
    return r

best = None
table = {}
for orient in itertools.product((0, 1), repeat=5):
    need = {1: {}, 3: {}}
    for o, t in zip(orient, terms):
        src, snk = (t[0], t[1]) if o == 0 else (t[1], t[0])
        need[1].setdefault(src[0], []).append(src[1])
        need[3].setdefault(snk[0], []).append(snk[1])
    tot = 0; detail = []
    for layer in (1, 3):
        cons = [(pair, maxrank(ms)) for pair, ms in need[layer].items()]
        m = min(sum(n) for n in itertools.product(range(5), repeat=4)
                if all(n[a] + n[b] >= r for (a, b), r in cons))
        tot += m; detail.append((m, cons))
    table[orient] = (tot, detail)
    if best is None or tot < best[0]:
        best = (tot, orient, detail)
vals = sorted({v[0] for v in table.values()})
print("lower bounds on width(layer 1) + width(layer 3) over the 32 orientations:", vals)
print("best orientation", best[1], ": layer 1 >=", best[2][0][0], ", layer 3 >=", best[2][1][0])
print("   constraints layer 1:", best[2][0][1]); print("   constraints layer 3:", best[2][1][1])
print("standard orientation (0,0,0,0,0):", table[(0,) * 5][0], [d[0] for d in table[(0,) * 5][1]])
# explicit realisation for the standard orientation: layer 1 = the four coordinate forms of row 0;
# layer 3 = forms x_t[1], x_t[3] for t = 1, 2, 3 (kernel K = span(e0, e2) for each of rows 1, 2, 3)
K = np.array([[1, 0, 0, 0], [0, 0, 1, 0]]).T
ok = all(np.allclose(K.T @ t[1][1] @ K, 0) for t in terms)
print("all five sink-side forms vanish on K x K, K = span(e0, e2) (so 6 layer-3 vertices suffice):", ok)
print("=> any unordered set-multilinear ABP with this middle layer has >= 1 + 4 + 5 + 6 + 1 = 17 vertices;"
      " the ordered (Ryser/Grenet type) one has 1 + 4 + 6 + 4 + 1 = 16.")

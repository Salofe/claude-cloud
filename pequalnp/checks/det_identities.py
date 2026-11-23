"""Exact integer checks of two determinant identities used in notes/next_steps.md (item B).

(1) For every k >= 2 (k odd included), with d1(S), d2(S) the minors of the rows S on the first / last k columns,
        det_2k = e * sum over the N = C(2k,k)/2 pairings {S, S^c} (S containing row 0) of
                 sgn(S,S^c) * (d1(S) + d2(S)) * (d1(S^c) + e * d2(S^c)),      e = (-1)^k.
    Reason: sum_{S containing 0} sgn(S,S^c) d(S) d(S^c) = ((i_{r_0} delta) ^ delta)(r_1..) = 0 for a decomposable
    k-form delta when k >= 2.  (For k = 1 it fails: det_2 is not one product.)
(2) det_5 is a sum of SIX products F(two rows) * G(the other three rows), the six row pairs being the edges of
    the complete graph on rows 1,2,3,4 (Laplace along two fixed rows needs ten):
        det_5 = sum over {A,B} disjoint pairs of rows, c the fifth row, of sgn(A,B,c) w(A) w(B) x_c[4],
        w(i,j) = r_i[0] r_j[1] - r_i[1] r_j[0] + r_i[2] r_j[3] - r_i[3] r_j[2]      (w ^ w ^ e_4 = 2 vol),
    and every summand contains a factor w(B) with B inside {1,2,3,4}; collecting by that B gives six products.
"""
import itertools, random
from sympy import Matrix

def sgn(p):
    p = list(p); s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]: s = -s
    return s

random.seed(0)
for k in (2, 3, 4, 5):
    m = 2 * k
    for trial in range(2):
        A = Matrix(m, m, lambda i, j: random.randint(-5, 5))
        c1, c2 = list(range(k)), list(range(k, m)); e = (-1) ** k; tot = 0; n = 0
        for S in itertools.combinations(range(m), k):
            if 0 not in S: continue
            Sc = [i for i in range(m) if i not in S]; n += 1
            tot += sgn(list(S) + Sc) * (A.extract(list(S), c1).det() + A.extract(list(S), c2).det()) \
                   * (A.extract(Sc, c1).det() + e * A.extract(Sc, c2).det())
        assert e * tot == A.det(), (k, trial)
    print(f"(1) k={k}: det_{m} = sum of {n} products, one for each pairing: exact on 2 random integer matrices")

def w(r, i, j):
    return r[i, 0] * r[j, 1] - r[i, 1] * r[j, 0] + r[i, 2] * r[j, 3] - r[i, 3] * r[j, 2]
for trial in range(5):
    r = Matrix(5, 5, lambda i, j: random.randint(-6, 6))
    G = {}                                    # B (edge of K4 on rows 1..4) -> value of the cofactor G_B
    for A_ in itertools.combinations(range(5), 2):
        for B_ in itertools.combinations([i for i in range(5) if i not in A_], 2):
            if A_ > B_: continue              # unordered {A, B}
            c = [i for i in range(5) if i not in A_ + B_][0]
            s = sgn(list(A_) + list(B_) + [c])
            Bk, Ak = (B_, A_) if 0 not in B_ else (A_, B_)      # Bk avoids row 0
            G[Bk] = G.get(Bk, 0) + s * w(r, *Ak) * r[c, 4]
    assert len(G) == 6 and all(0 not in B_ for B_ in G)
    total = sum(w(r, *B_) * g for B_, g in G.items())
    assert total == r.det(), (total, r.det())
print("(2) det_5 = sum of 6 products w(r_B) * G_B(other three rows), B the 6 pairs inside rows {1,2,3,4}: exact on 5 random integer matrices")
print("    (each G_B is a function of the three rows outside B only: it is a sum of terms w(two of them) * (entry of the third))")

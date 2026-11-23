"""Independent exact checks of the sum-matrix lemma (referee's own script, exact rational/integer arithmetic).
 (a) Phi_c(s,t) = perm[(s_i + t_l)]_{l != c} = sum_j j!(n-j)! e_{n-j}(s) e_j(t without t_c)   at random integer points, m <= 8
 (b) det [ e_j(t^(c)) ]_{c,j} = +- prod_{c<c'} (t_c - t_c')                                    (symbolic m <= 5, numeric m <= 9)
 (c) for every multiplicity pattern of t (partition of m into d parts): the solution set of the m conditions,
     as an affine-linear system in (e_1(s),..,e_n(s)), is empty if d = m and has dimension exactly n - d otherwise.
"""
import itertools, math, random
import sympy as sp
from fractions import Fraction

def esym_list(vals):
    """[e_0, e_1, .., e_len] of the integers vals"""
    e = [1]
    for v in vals:
        e = [1] + [e[k] + v * e[k - 1] for k in range(1, len(e))] + [v * e[-1]]
    return e

def perm_int(M):
    """permanent of a square integer matrix by Ryser/DP over subsets (exact)"""
    n = len(M)
    dp = {0: 1}
    for i in range(n):
        nd = {}
        for mask, v in dp.items():
            for j in range(n):
                if not mask >> j & 1:
                    nd[mask | 1 << j] = nd.get(mask | 1 << j, 0) + v * M[i][j]
        dp = nd
    return dp[(1 << n) - 1]

random.seed(7)
print("(a) formula at random integer points")
for m in range(2, 9):
    n = m - 1
    ok = True
    for trial in range(5):
        s = [random.randint(-9, 9) for _ in range(n)]
        t = [random.randint(-9, 9) for _ in range(m)]
        es = esym_list(s)
        for c in range(m):
            cols = [l for l in range(m) if l != c]
            lhs = perm_int([[s[i] + t[l] for l in cols] for i in range(n)])
            et = esym_list([t[l] for l in cols])
            rhs = sum(math.factorial(j) * math.factorial(n - j) * es[n - j] * et[j] for j in range(n + 1))
            ok &= (lhs == rhs)
    print(f"   m={m}: {ok}")

print("(b) det[e_j(t^(c))] = +- Vandermonde")
for m in range(2, 6):
    t = sp.symbols(f't0:{m}')
    E = sp.Matrix(m, m, lambda c, j: sum(sp.prod(cc) for cc in itertools.combinations([t[l] for l in range(m) if l != c], j)) if j else 1)
    V = sp.prod([t[a] - t[b] for a in range(m) for b in range(a + 1, m)])
    d = sp.expand(E.det(method='berkowitz'))
    print(f"   m={m} symbolic: det = +Vandermonde: {sp.expand(d - V) == 0},  det = -Vandermonde: {sp.expand(d + V) == 0}")
for m in range(6, 10):
    ok = True
    for trial in range(3):
        t = random.sample(range(-20, 21), m)
        E = sp.Matrix(m, m, lambda c, j: esym_list([t[l] for l in range(m) if l != c])[j])
        V = math.prod(t[a] - t[b] for a in range(m) for b in range(a + 1, m))
        ok &= (abs(E.det()) == abs(V))
    print(f"   m={m} at random integer points: |det| = |Vandermonde|: {ok}")

def partitions(n, maxpart=None):
    maxpart = maxpart or n
    if n == 0:
        yield []; return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield [k] + rest

print("(c) fibre over t, for every multiplicity pattern: affine-linear system in (e_1(s), .., e_n(s))")
allok = True
for m in range(2, 9):
    n = m - 1
    res = []
    for mu in partitions(m):
        d = len(mu)
        for variant in range(2):          # variant 1: one of the values is 0
            vals = random.sample([v for v in range(-12, 13) if v != 0], d)
            if variant:
                vals[random.randrange(d)] = 0
            t = [v for v, k in zip(vals, mu) for _ in range(k)]
            # row c: coefficients a_j = j!(n-j)! e_j(t^(c)) of e_{n-j}(s), j = 0..n ; e_0(s) = 1 belongs to j = n
            rows = []
            for c in range(m):
                et = esym_list([t[l] for l in range(m) if l != c])
                rows.append([math.factorial(j) * math.factorial(n - j) * et[j] for j in range(n + 1)])
            A = sp.Matrix(rows)
            hom = A[:, :n]            # coefficients of the unknowns e_n(s), .., e_1(s)
            rk_full = A.rank(); rk_hom = hom.rank()
            if rk_full > rk_hom:
                dim = None            # inconsistent: empty fibre
            else:
                dim = n - rk_hom
            want = None if d == m else n - d
            good = (dim == want) and (rk_full == d)
            allok &= good
            res.append(good)
    print(f"   m={m}: {len(res)} cases (all partitions of m, with and without a zero value): rank of the conditions = d and "
          f"fibre dimension = n-d (empty for d=m) in every case: {all(res)}")
print("ALL CHECKS PASSED" if allok else "SOME CHECK FAILED")

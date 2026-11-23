"""All rows of x but one are the all-ones vector; the last row is y.
Claim 1: M_x = (m-3)! * H(y),  H[c,d] = e1(y) - y_c - y_d (c != d), 0 on the diagonal  (Hessian of e_3).
Claim 2: with a = 2y - e1(y) 1:  H = -(1/2) * (diag(a) - (a 1^T + 1 a^T)/2) * ... check exact relation, and
         det(diag(a) - (a 1^T + 1 a^T)/2) = (1 - m/2)^2 e_m(a) - e_1(a) e_{m-1}(a)/4.
Claim 3: corank of G(a) = diag(a) - (a 1^T + 1 a^T)/2:  with Z = #{c : a_c = 0},
         corank = Z-1 if Z >= 1 and sum(a) != 0;  Z if Z >= 1 and sum(a) = 0;  0 or 1 if Z = 0."""
import itertools, math, random
import sympy as sp
def perm(M):
    n = len(M)
    return sum(sp.prod([M[i][p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
for m in (4, 5, 6):
    y = sp.symbols(f'y0:{m}')
    x = [[1] * m for _ in range(m - 3)] + [list(y)]
    e1 = sum(y)
    ok = True
    for c in range(m):
        for d in range(c + 1, m):
            cols = [l for l in range(m) if l not in (c, d)]
            ok &= sp.expand(perm([[row[l] for l in cols] for row in x]) - math.factorial(m - 3) * (e1 - y[c] - y[d])) == 0
    print(f"m={m}: M_x = (m-3)! H(y): {ok}")
    a = sp.symbols(f'a0:{m}')
    G = sp.Matrix(m, m, lambda c, d: (a[c] if c == d else 0) - sp.Rational(1, 2) * (a[c] + a[d]))
    # relation with H: a = 2y - e1 => H[c,d] = -(a_c + a_d)/2 off diagonal; G off-diagonal = -(a_c+a_d)/2, G diagonal = a_c - a_c = 0
    print("   G has zero diagonal:", all(sp.simplify(G[c, c]) == 0 for c in range(m)), " (so G = H after a = 2y - e1(y) 1)")
    es = [sum(sp.prod(s) for s in itertools.combinations(a, j)) for j in range(m + 1)]
    lhs = sp.expand(G.det())
    rhs = sp.expand(sp.Rational(1, 1) * (1 - sp.Rational(m, 2)) ** 2 * es[m] - es[1] * es[m - 1] / 4)
    print("   det G = (1-m/2)^2 e_m - e_1 e_{m-1}/4:", sp.expand(lhs - rhs) == 0)
    random.seed(m)
    good = True
    for trial in range(300):
        Z = random.randint(0, m)
        vals = [0] * Z + [random.choice([-3, -2, -1, 1, 2, 3, 5]) for _ in range(m - Z)]
        if Z < m and random.random() < 0.5 and m - Z >= 2:      # force sum = 0
            vals[-1] = -sum(vals[:-1])
            if vals[-1] == 0: continue
        random.shuffle(vals)
        Gn = G.subs(dict(zip(a, vals)))
        cork = m - Gn.rank()
        S = sum(vals)
        if Z >= 1:
            pred = Z if S == 0 else Z - 1
            good &= (cork == pred)
        else:
            good &= cork in (0, 1)
    print("   corank formula on 300 random integer points:", good)

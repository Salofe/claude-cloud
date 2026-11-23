"""Is the 4 x 4 permanent an EXACT sum of five split products?  No.  Exact checks.

P is the 4 x 4 permanent as a tensor in (K^4)^{(x)4} (one factor per ROW r0..r3):
P[j0, j1, j2, j3] = 1 when (j0..j3) is a permutation. A split product of the pairing 01|23 is
F(r0, r1) G(r2, r3), of 02|13 it is X(r0, r2) Y(r1, r3), of 03|12 it is X'(r0, r3) Y'(r1, r2).
"Pattern (a, b, c)" = a, b, c terms of the three pairings. The statements and the complete
proofs are in notes/exact_five_terms_4x4.md; this script checks every computational ingredient
exactly (sympy, rational arithmetic), one mode per claim.

Notation. B^l_u = perm(l, u, ., .): symmetric, zero diagonal, entries l_a u_b + l_b u_a at (c, d),
{a, b} the complement of {c, d}; B_u = B^1_u (l = all ones). alt_ab = E_ab - E_ba, s_ab = E_ab + E_ba
(as matrices of bilinear forms). S_{ab|cd} = span(alt_ab, s_cd). N_ab = {Phi : Phi(l, l_a e_a - l_b e_b)
= 0 for all l}.

Modes:
  python3 exact4.py lines     LEMMA L: det B_u = -4 (e1 e3 - 4 e4), and the quartic surface S = {det B_u = 0}
                              contains exactly 16 lines (6 coordinate, 6 pair, 4 star): ingredients of the
                              hand proof, and an independent Groebner computation with a completeness
                              certificate in the six charts of the Grassmannian
  python3 exact4.py types     structure lemma: for each of the 16 lines Lam the space of bilinear forms Phi
                              with Phi(l, l*p) = 0 for all l and all p in Lam; the spaces N_ab; which
                              S_{a'b'|c'd'} lie in N_ab
  python3 exact4.py frames    bookkeeping of the eight slice frames (which covectors survive when two rows
                              are fixed), on a random integer tensor of pattern (2,2,1)
  python3 exact4.py p221      pattern (2,2,1): the remaining ingredients of the hand proof (facts 1, 2 and (b),
                              the kernel on Lam_ab, Step 4 of Theorem 1)
  python3 exact4.py enum      pattern (2,2,1): independent machine proof of Theorem 1 from the structure
                              lemma alone (replaces facts (b), (c) and Steps 1-4): all 39^4 choices of
                              supports of the four doubled pencils, a combinatorial test, then Groebner
                              bases for the survivors
  python3 exact4.py referee   patterns (4,1,0), (3,2,0), (3,1,1): every ingredient of the paper proofs in
                              lower4.py, re-derived independently (LEMMA R with a certificate, the forms
                              a (x) b + b (x) a, the spaces W_t and N_t, their intersections, the final
                              contradictions)
  python3 exact4.py limit     a five-term LIMIT identity of pattern (2,2,1), exact, in closed form
  python3 exact4.py fit [restarts] [seed]
                              numerical evidence only: Levenberg-Marquardt fits of pattern (2,2,1)
                              (uses lower4.py); residual * size^2 stays bounded away from 0
  python3 exact4.py all       every exact mode (everything except fit)
"""
import itertools
import sys

import sympy as sp

M = 4
IDX = list(itertools.product(range(M), repeat=4))
PERMS = set(itertools.permutations(range(M)))
PAIRS = list(itertools.combinations(range(M), 2))


def comp(a, b):
    return tuple(i for i in range(M) if i not in (a, b))


def unit(i, j):
    Mx = sp.zeros(M, M)
    Mx[i, j] = 1
    return Mx


def alt(a, b):
    return unit(a, b) - unit(b, a)


def sym(a, b):
    return unit(a, b) + unit(b, a)


def e(i):
    return sp.Matrix([1 if k == i else 0 for k in range(M)])


def Bmat(lv, uv):
    """perm(l, u, ., .) as a matrix."""
    Bm = sp.zeros(M, M)
    for c in range(M):
        for d in range(M):
            if c != d:
                a, b = comp(c, d)
                Bm[c, d] = lv[a] * uv[b] + lv[b] * uv[a]
    return Bm


def perm_form(rows):
    """perm of four row vectors (lists of expressions)."""
    return sum(sp.prod([rows[i][p[i]] for i in range(M)]) for p in PERMS)


def span_rref(mats):
    """Canonical form of the span of a list of 4 x 4 matrices (rref of the 16-vectors)."""
    if not mats:
        return sp.zeros(0, 16)
    A = sp.Matrix([list(m) for m in mats])
    R, piv = A.rref()
    return R[:len(piv), :]


def space_of(conds, extra_vars):
    """Solutions Phi (4 x 4, symbols) of: every expression in conds vanishes identically in extra_vars."""
    f = sp.symbols('f0:16')
    Phi = sp.Matrix(M, M, f)
    eqs = []
    for expr in conds(Phi):
        eqs += sp.Poly(sp.expand(expr), *extra_vars).coeffs()
    A, _ = sp.linear_eq_to_matrix(eqs, list(f))
    return [sp.Matrix(M, M, list(v)) for v in A.nullspace()]


def certified_zero_set(eqs, variables, expected, label):
    """Proves that the common zeros of eqs over the algebraic closure are exactly the rational points
    in `expected`: (1) for each variable x, prod (x - v) over the expected values v of x lies in the
    radical of the ideal (Rabinowitsch: 1 in (eqs, 1 - z g)); (2) every point of the finite grid of
    expected coordinate values is tested by substitution."""
    z = sp.Dummy('z')
    values = []
    for k, x in enumerate(variables):
        vals = sorted({pt[k] for pt in expected})
        g = sp.prod([x - v for v in vals])
        G = sp.groebner(list(eqs) + [1 - z * g], z, *variables, order='grevlex')
        assert list(G.exprs) == [1], (label, x)
        values.append(vals)
    found = set()
    for pt in itertools.product(*values):
        sub = dict(zip(variables, pt))
        if all(sp.expand(q.subs(sub)) == 0 for q in eqs):
            found.add(tuple(pt))
    assert found == set(expected), label
    return len(found)


# ---------------------------------------------------------------------------------------------
# LEMMA L: the sixteen lines on S
# ---------------------------------------------------------------------------------------------

def sixteen_lines():
    """(name, basis vector p, basis vector q) of the 16 two-dimensional subspaces."""
    out = []
    for a, b in PAIRS:
        out.append((('coord', a, b), e(a), e(b)))
    for a, b in PAIRS:
        c, d = comp(a, b)
        out.append((('pair', a, b), e(a) + e(b), e(c) - e(d)))         # Lam_ab = {u_a = u_b, u_c + u_d = 0}
    for a in range(M):
        b, c, d = [i for i in range(M) if i != a]
        out.append((('star', a), e(b) - e(c), e(b) - e(d)))            # {u_a = 0, sum u = 0}
    return out


def lines():
    u = sp.symbols('u0:4')
    D = sp.expand(Bmat([1] * 4, u).det())
    e1 = sum(u)
    e3 = sum(sp.prod(c) for c in itertools.combinations(u, 3))
    e4 = sp.prod(u)
    sigma = sp.expand(e1 * e3 - 4 * e4)
    print("det B_u = -4 (e1 e3 - 4 e4):", sp.expand(D + 4 * sigma) == 0)
    al, be, ga = (u[0] + u[1]) * (u[2] + u[3]), (u[0] + u[2]) * (u[1] + u[3]), (u[0] + u[3]) * (u[1] + u[2])
    print("det B_u = al^2 + be^2 + ga^2 - 2 al be - 2 al ga - 2 be ga:",
          sp.expand(D - (al**2 + be**2 + ga**2 - 2 * al * be - 2 * al * ga - 2 * be * ga)) == 0)
    s, t = sp.symbols('s t')
    L16 = sixteen_lines()
    ok = all(sp.expand(sigma.subs(dict(zip(u, s * p + t * q)), simultaneous=True)) == 0 for _, p, q in L16)
    print("the 16 lines (6 coordinate, 6 pair, 4 star) lie on S:", ok)
    assert ok
    # --- ingredients of the hand proof -------------------------------------------------------
    print("hand proof, lines inside a coordinate plane: sigma restricted to u3 = 0 is",
          sp.factor(sigma.subs(u[3], 0)))
    al_, be_, ga_, de_, x, y = sp.symbols('alpha beta gamma delta x y')
    r22 = sp.Poly(sp.expand(sigma.subs(dict(zip(u, (al_ * x, be_ * x, ga_ * y, de_ * y))), simultaneous=True)), x, y)
    print("hand proof, root pattern {2,2}: sigma(alpha x, beta x, gamma y, delta y) has coefficients")
    for mon, cf in r22.terms():
        print(f"     x^{mon[0]} y^{mon[1]}: {sp.factor(cf)}")
    mid = r22.coeff_monomial(x**2 * y**2)
    print("     with beta = -alpha the middle coefficient is", sp.factor(mid.subs(be_, -al_)))
    r31 = sp.Poly(sp.expand(sigma.subs(dict(zip(u, (al_ * x, be_ * x, ga_ * x, de_ * y))), simultaneous=True)), x, y)
    print("hand proof, root pattern {3,1}: sigma(alpha x, beta x, gamma x, delta y) has coefficients")
    for mon, cf in r31.terms():
        print(f"     x^{mon[0]} y^{mon[1]}: {sp.factor(cf)}")
    c31 = r31.coeff_monomial(x**3 * y)
    print("     with gamma = -alpha-beta the x^3 y coefficient is", sp.factor(c31.subs(ga_, -al_ - be_)))
    # --- independent machine proof: the six charts of the Grassmannian -------------------------
    a, b, c, d = sp.symbols('a b c d')
    total = set()
    for piv in PAIRS:
        free = comp(*piv)
        p, q = [0] * 4, [0] * 4
        p[piv[0]], q[piv[1]] = 1, 1
        p[free[0]], p[free[1]], q[free[0]], q[free[1]] = a, b, c, d
        uv = [s * p[i] + t * q[i] for i in range(4)]
        eqs = [sp.expand(cf) for cf in sp.Poly(sp.expand(sigma.subs(dict(zip(u, uv)), simultaneous=True)), s, t).coeffs()]
        expected = set()
        for name, pv, qv in L16:
            m2 = sp.Matrix([[pv[piv[0]], pv[piv[1]]], [qv[piv[0]], qv[piv[1]]]])
            if m2.det() == 0:
                continue                           # this line is not in the chart
            red = m2.inv() * sp.Matrix([list(pv), list(qv)])     # rows: (p with pivots 1,0), (q with pivots 0,1)
            expected.add((red[0, free[0]], red[0, free[1]], red[1, free[0]], red[1, free[1]]))
            total.add(name)
        G = sp.groebner(eqs, a, b, c, d, order='grevlex')
        n = certified_zero_set(eqs, (a, b, c, d), expected, f"chart {piv}")
        print(f"chart with pivots {piv}: ideal zero-dimensional: {G.is_zero_dimensional}; "
              f"lines of S in this chart: exactly {n} (certified)", flush=True)
        assert G.is_zero_dimensional
    print(f"LEMMA L: S contains exactly {len(total)} lines (every 2-plane lies in one of the six charts);"
          " in particular S contains no plane.")
    assert len(total) == 16


# ---------------------------------------------------------------------------------------------
# structure lemma: the linear spaces attached to the lines
# ---------------------------------------------------------------------------------------------

def space_for_line(p, q):
    l = sp.symbols('l0:4')

    def conds(Phi):
        lv = sp.Matrix(l)
        return [(lv.T * Phi * sp.Matrix([l[i] * w[i] for i in range(4)]))[0] for w in (p, q)]
    return space_of(conds, l)


def node_space(a, b):
    """N_ab = {Phi : Phi(l, l_a e_a - l_b e_b) = 0 for all l}."""
    l = sp.symbols('l0:4')

    def conds(Phi):
        return [(sp.Matrix(l).T * Phi * (l[a] * e(a) - l[b] * e(b)))[0]]
    return space_of(conds, l)


def types():
    print("For a 2-plane Lam: T(Lam) = {Phi : Phi(l, l*p) = 0 for all l and all p in Lam}  (l*p = coordinatewise product)")
    for name, p, q in sixteen_lines():
        sp_ = space_for_line(p, q)
        got = span_rref(sp_)
        if name[0] == 'coord':
            a, b = name[1], name[2]
            exp = [unit(i, j) for i in range(4) for j in comp(a, b)]
            desc = f"all Phi whose columns {a},{b} vanish (dim 8)"
        elif name[0] == 'pair':
            a, b = name[1], name[2]
            c, d = comp(a, b)
            exp = [alt(a, b), sym(c, d)]
            desc = f"span(alt_{a}{b}, s_{c}{d}) = S_{{{a}{b}|{c}{d}}} (dim 2)"
        else:
            a = name[1]
            exp = [unit(i, a) for i in range(4)]
            desc = f"phi(r) (x) e_{a}: only column {a} is nonzero (dim 4), so the common zero set is a hyperplane"
        assert got == span_rref(exp), name
        print(f"   line {name}: T = {desc}")
    print("N_ab = {Phi : Phi(l, l_a e_a - l_b e_b) = 0 for all l} = {f s_ab + (columns a, b zero)}:")
    for a, b in PAIRS:
        c, d = comp(a, b)
        exp = [sym(a, b)] + [unit(i, j) for i in range(4) for j in (c, d)]
        assert span_rref(node_space(a, b)) == span_rref(exp)
    print("   checked for the six nodes e_a - e_b (dim 9)")
    ok = True
    for a, b in PAIRS:
        Nab = span_rref(node_space(a, b))
        for a2, b2 in PAIRS:
            c2, d2 = comp(a2, b2)
            inside = span_rref(node_space(a, b) + [alt(a2, b2), sym(c2, d2)]) == Nab
            ok = ok and (inside == ({a2, b2} == set(comp(a, b))))
    print("S_{a'b'|c'd'} is contained in N_ab  <=>  (a'b'|c'd') = (cd|ab):", ok)
    assert ok


# ---------------------------------------------------------------------------------------------
# pattern (2,2,1): ingredients of the hand proof
# ---------------------------------------------------------------------------------------------

def p221():
    l = sp.symbols('l0:4')
    u = sp.symbols('u0:4')
    x, y, s, t = sp.symbols('x y s t')
    chk = sp.Matrix(4, 4, lambda c, d: sum((1 if (i, j, c, d) in PERMS else 0) * l[i] * u[j]
                                           for i in range(4) for j in range(4)))
    print("B^l_u = perm(l, u, ., .) has entries l_a u_b + l_b u_a:", (chk - Bmat(l, u)).expand() == sp.zeros(4, 4))
    Dg = sp.diag(*l)
    scaled = sp.prod(l) * Dg.inv() * Bmat([1] * 4, [u[i] / l[i] for i in range(4)]) * Dg.inv()
    print("B^l_u = (prod l) D^-1 B_{u/l} D^-1, D = diag(l):", sp.simplify(scaled - Bmat(l, u)) == sp.zeros(4, 4))
    # fact (b)
    ok = True
    for a, b in PAIRS:
        lv = x * e(a) + y * e(b)
        eqs = [Bmat(list(lv), u)[c, d] for c, d in PAIRS]
        A, _ = sp.linear_eq_to_matrix(eqs, list(u))
        ns = A.nullspace()
        ok = ok and len(ns) == 1
        v = ns[0]
        ok = ok and all(sp.simplify(v[i]) == 0 for i in comp(a, b)) and sp.simplify(v[a] * y + v[b] * x) == 0
    print("fact (b): for l = x e_a + y e_b the vectors u with B^l_u = 0 are the multiples of x e_a - y e_b (dim 1):", ok)
    assert ok
    # the kernel on Lam_ab (Lemma L, Lemma S)
    ok = True
    for a2, b2 in PAIRS:
        c2, d2 = comp(a2, b2)
        p = s * (e(a2) + e(b2)) + t * (e(c2) - e(d2))
        Bp = Bmat([1] * 4, list(p))
        ok = ok and (Bp * (e(a2) - e(b2))).expand() == sp.zeros(4, 1)
        minor = sp.factor(Bp.extract([a2, c2, d2], [a2, c2, d2]).det())
        ok = ok and sp.expand(minor - 4 * s * (s**2 - t**2)) == 0
        # alt_ab(l, .) and s_cd(l, .) vanish on l * Lam_ab (which is therefore their common zero set)
        lu = [l[i] * p[i] for i in range(4)]
        ok = ok and sp.expand((sp.Matrix(l).T * alt(a2, b2) * sp.Matrix(lu))[0]) == 0
        ok = ok and sp.expand((sp.Matrix(l).T * sym(c2, d2) * sp.Matrix(lu))[0]) == 0
    print("kernel: for p = s (e_a + e_b) + t (e_c - e_d): B_p (e_a - e_b) = 0, the principal minor (a, c, d) is")
    print("        4 s (s^2 - t^2) (rank 3 for generic p), and alt_ab(l, l*p) = s_cd(l, l*p) = 0:", ok)
    assert ok
    # Step 4 of Theorem 1: with F_v in S_{ab|cd}, X_v, Y_v in S_{cd|ab}, X' in N_cd and G_v, Y' ARBITRARY, the sum of
    # the entries (a, c, b, d) and (a, d, b, c) of the five-term sum vanishes identically; for P it is 2.
    ok = True
    for a2, b2 in PAIRS:
        c2, d2 = comp(a2, b2)
        cnt = itertools.count()
        newsym = lambda: sp.Symbol(f'z{next(cnt)}')
        gen = lambda basis: sum((newsym() * m for m in basis), sp.zeros(4, 4))
        full = [unit(i, j) for i in range(4) for j in range(4)]
        F = [gen([alt(a2, b2), sym(c2, d2)]) for _ in range(2)]
        G = [gen(full) for _ in range(2)]
        X = [gen([alt(c2, d2), sym(a2, b2)]) for _ in range(2)]
        Y = [gen([alt(c2, d2), sym(a2, b2)]) for _ in range(2)]
        X1 = gen(node_space(c2, d2))
        Y1 = gen(full)

        def entry(j):
            return (sum(F[v][j[0], j[1]] * G[v][j[2], j[3]] for v in range(2))
                    + sum(X[v][j[0], j[2]] * Y[v][j[1], j[3]] for v in range(2))
                    + X1[j[0], j[3]] * Y1[j[1], j[2]])
        j1, j2 = (a2, c2, b2, d2), (a2, d2, b2, c2)
        ok = ok and j1 in PERMS and j2 in PERMS and sp.expand(entry(j1) + entry(j2)) == 0
    print("Step 4: F_v in S_{ab|cd}, X_v, Y_v in S_{cd|ab}, X' in N_cd (G_v, Y' arbitrary) force")
    print("        T[a,c,b,d] + T[a,d,b,c] = 0 for the five-term sum T, while P[a,c,b,d] + P[a,d,b,c] = 2:", ok)
    assert ok


# ---------------------------------------------------------------------------------------------
# pattern (2,2,1): independent machine proof from the structure lemma
# ---------------------------------------------------------------------------------------------

def enum():
    import numpy as np
    supports, names = [], []
    for a, b in [(0, 1), (0, 2), (0, 3)]:
        c, d = comp(a, b)
        Sm = np.zeros((4, 4), bool)
        Sm[a, b] = Sm[b, a] = Sm[c, d] = Sm[d, c] = True
        supports.append(Sm)
        names.append(('S', (a, b), (c, d)))
    for R in PAIRS:
        for C in PAIRS:
            Sm = np.zeros((4, 4), bool)
            for r in R:
                for c in C:
                    Sm[r, c] = True
            supports.append(Sm)
            names.append(('C', R, C))
    n = len(supports)
    Pt = np.zeros((4,) * 4, bool)
    for p in PERMS:
        Pt[p] = True
    fl = lambda T: np.transpose(T, (0, 3, 1, 2)).reshape(16, 16)       # rows (j0, j3), columns (j1, j2)
    SA, SB, idx = [], [], []
    for i in range(n):
        for k in range(n):
            SA.append(fl(supports[i][:, :, None, None] & supports[k][None, None, :, :]))   # F[j0,j1] G[j2,j3]
            SB.append(fl(supports[i][:, None, :, None] & supports[k][None, :, None, :]))   # X[j0,j2] Y[j1,j3]
            idx.append((i, k))
    SA, SB, Pf = np.array(SA), np.array(SB), fl(Pt)
    print(f"{n} possible supports of a doubled pencil (3 of type S: the positions of a column pairing;")
    print("36 of type C: a 2 x 2 block), so", n**4, "cases. Necessary condition for T = P - A - B to have rank <= 1 in the")
    print("flattening 03|12: with O = the ones of P outside supp A u supp B, every zero of P in rows(O) x cols(O)")
    print("must lie in supp A u supp B.")
    surv = []
    for ia in range(len(SA)):
        Mk = SA[ia][None] | SB
        O = Pf[None] & ~Mk
        rect = O.any(axis=2)[:, :, None] & O.any(axis=1)[:, None, :]
        bad = (rect & ~Pf[None] & ~Mk).any(axis=(1, 2))
        for ib in np.nonzero(~bad)[0]:
            surv.append((idx[ia], idx[int(ib)], int(O[ib].sum())))
    print("cases passing the test:", len(surv))
    for (iF, iG), (iX, iY), no in surv:
        print("   F, G, X, Y supports:", names[iF], names[iG], names[iX], names[iY], "| untouched ones of P:", no)
        assert names[iF][0] == names[iG][0] == names[iX][0] == names[iY][0] == 'S'
        assert names[iF] == names[iG] == names[iX] == names[iY]
    # survivors: all four pencils are S_{ab|cd} or S_{cd|ab} for one column pairing {ab|cd}
    a_ = sp.symbols('a0:4')
    b_ = sp.symbols('b0:4')

    def minors_for(target, F, G, X, Y):
        """2 x 2 minors, in the flattening 03|12, of target - A - B with A in span(F) (x) span(G) (rows
        01|23) and B in span(X) (x) span(Y) (rows 02|13); 8 unknown coefficients a_, b_."""
        T = {}
        for j in IDX:
            v = sp.sympify(target[j])
            k = 0
            for p in range(2):
                for q in range(2):
                    v -= a_[k] * F[p][j[0], j[1]] * G[q][j[2], j[3]]
                    v -= b_[k] * X[p][j[0], j[2]] * Y[q][j[1], j[3]]
                    k += 1
            T[j] = v
        Mx = sp.Matrix(16, 16, lambda r, cc: T[(r // 4, cc // 4, cc % 4, r % 4)])
        rows = [r for r in range(16) if any(Mx[r, cc] != 0 for cc in range(16))]
        cols = [cc for cc in range(16) if any(Mx[r, cc] != 0 for r in range(16))]
        minors = set()
        for r1, r2 in itertools.combinations(rows, 2):
            for c1, c2 in itertools.combinations(cols, 2):
                mn = sp.expand(Mx[r1, c1] * Mx[r2, c2] - Mx[r1, c2] * Mx[r2, c1])
                if mn != 0:
                    minors.add(mn)
        return minors

    Ptarget = {j: (1 if j in PERMS else 0) for j in IDX}
    # control of the pipeline: a target that IS of the form A + B + (rank one for 03|12) must NOT give {1}
    pen = (alt(0, 1), sym(2, 3))
    astar, bstar = (2, -1, 3, 5), (1, 4, -2, 7)
    Xs = sp.Matrix(4, 4, lambda i, j: (i + 2 * j) % 5 - 1)
    Ys = sp.Matrix(4, 4, lambda i, j: (3 * i + j) % 7 - 2)
    ctrl = {}
    for j in IDX:
        v, k = Xs[j[0], j[3]] * Ys[j[1], j[2]], 0
        for p in range(2):
            for q in range(2):
                v += astar[k] * pen[p][j[0], j[1]] * pen[q][j[2], j[3]] + bstar[k] * pen[p][j[0], j[2]] * pen[q][j[1], j[3]]
                k += 1
        ctrl[j] = v
    mc = minors_for(ctrl, pen, pen, pen, pen)
    sub = dict(zip(a_ + b_, astar + bstar))
    ctrl_ok = (list(sp.groebner(list(mc), *a_, *b_, order='grevlex').exprs) != [1]
               and all(m.subs(sub) == 0 for m in mc))
    print("   control (a tensor built as A + B + rank one): the ideal of minors is proper and vanishes at the"
          " planted solution:", ctrl_ok)
    assert ctrl_ok
    allunit = True
    for (iF, _), _, _ in surv:
        (a, b), (c, d) = names[iF][1], names[iF][2]
        pencils = {'+': (alt(a, b), sym(c, d)), '-': (alt(c, d), sym(a, b))}
        for oF, oG, oX, oY in itertools.product('+-', repeat=4):
            minors = minors_for(Ptarget, pencils[oF], pencils[oG], pencils[oX], pencils[oY])
            Gb = sp.groebner(list(minors), *a_, *b_, order='grevlex')
            allunit = allunit and list(Gb.exprs) == [1]
        print(f"   column pairing {a}{b}|{c}{d}: for all 16 choices of S_{{ab|cd}} / S_{{cd|ab}} for F, G, X, Y the 2 x 2 minors of",
              f"P - A - B (A in S_F (x) S_G, B in S_X (x) S_Y, 8 unknowns) generate the unit ideal: {allunit}", flush=True)
    assert allunit
    print("Hence no exact decomposition of pattern (2,2,1) (given Lemma S, the structure lemma).")


# ---------------------------------------------------------------------------------------------
# referee: ingredients of the proofs for (4,1,0), (3,2,0), (3,1,1)
# ---------------------------------------------------------------------------------------------

def node_list():
    """The ten nodes of S: (name, vector n), and for l: u = l*n, B^l_u = a b^T + b a^T."""
    out = []
    for a, b in PAIRS:
        out.append((('pair', a, b), e(a) - e(b)))
    for a in range(4):
        out.append((('star', a), sp.ones(4, 1) - 2 * e(a)))
    return out


def ab_vectors(name, l):
    if name[0] == 'pair':
        a, b = name[1], name[2]
        c, d = comp(a, b)
        return l[a] * e(b) - l[b] * e(a), l[d] * e(c) + l[c] * e(d)
    a = name[1]
    bl = sp.zeros(4, 1)
    for j in range(4):
        if j != a:
            bl[j] = 2 * sp.prod([l[i] for i in range(4) if i not in (a, j)])
    return e(a), bl


def W_space(name):
    """{Xi : Xi(l, .) in span(a_l, b_l) for all l}: all 3 x 3 minors of (Xi^T l, a_l, b_l) vanish."""
    l = sp.symbols('l0:4')
    al, bl = ab_vectors(name, l)

    def conds(Phi):
        Mx = sp.Matrix.hstack(Phi.T * sp.Matrix(l), al, bl)
        return [Mx.extract(list(r3), [0, 1, 2]).det() for r3 in itertools.combinations(range(4), 3)]
    return space_of(conds, l)


def N_space(name):
    l = sp.symbols('l0:4')
    nvec = dict(node_list())[name]

    def conds(Phi):
        return [(sp.Matrix(l).T * Phi * sp.Matrix([l[i] * nvec[i] for i in range(4)]))[0]]
    return space_of(conds, l)


def intersect(A, Bs):
    """Basis of span(A) n span(Bs) (lists of 4 x 4 matrices)."""
    if not A or not Bs:
        return []
    Mx = sp.Matrix([list(m) for m in A] + [list(m) for m in Bs]).T
    out = []
    for v in Mx.nullspace():
        w = sum((v[i] * A[i] for i in range(len(A))), sp.zeros(4, 4))
        out.append(w)
    return out


def referee():
    u = sp.symbols('u0:4')
    l = sp.symbols('l0:4')
    nodes = node_list()
    # ---- LEMMA R, independently: charts u_i = 1, Groebner certificate ---------------------------
    Bu = Bmat([1] * 4, u)
    minors3 = {sp.expand(Bu.extract(list(r3), list(k3)).det())
               for r3 in itertools.combinations(range(4), 3) for k3 in itertools.combinations(range(4), 3)}
    minors3.discard(sp.Integer(0))
    seen = set()
    for i in range(4):
        var = [u[k] for k in range(4) if k != i]
        eqs = [m.subs(u[i], 1) for m in minors3]
        expected = set()
        for name, nv in nodes:
            if nv[i] != 0:
                expected.add(tuple(nv[k] / nv[i] for k in range(4) if k != i))
                seen.add(name)
        cnt = certified_zero_set(eqs, var, expected, f"lemma R chart {i}")
        print(f"LEMMA R, chart u{i} = 1: rank B_u <= 2 exactly at {cnt} points (certified)", flush=True)
    assert len(seen) == 10
    A6, _ = sp.linear_eq_to_matrix([Bu[a, b] for a, b in PAIRS], list(u))
    print("LEMMA R: rank B_u <= 2 exactly on the ten lines e_a - e_b, 1 - 2 e_a; B_u = 0 only for u = 0:", A6.rank() == 4)
    assert all(Bu.subs(dict(zip(u, nv))).rank() == 2 for _, nv in nodes)
    # ---- the rank-two forms ----------------------------------------------------------------------
    ok = True
    for name, nv in nodes:
        al, bl = ab_vectors(name, l)
        uu = [l[i] * nv[i] for i in range(4)]
        ok = ok and (Bmat(l, uu) - al * bl.T - bl * al.T).expand() == sp.zeros(4, 4)
    print("for the ten types: B^l_{l*n} = a_l b_l^T + b_l a_l^T with (a_l, b_l) as in lower4.t3:", ok)
    assert ok
    # ---- the spaces W_t and N_t ------------------------------------------------------------------
    W, Nn = {}, {}
    for name, _ in nodes:
        W[name] = W_space(name)
        Nn[name] = N_space(name)
        if name[0] == 'pair':
            a, b = name[1], name[2]
            c, d = comp(a, b)
            assert span_rref(W[name]) == span_rref([alt(a, b), sym(c, d)])
            assert span_rref(Nn[name]) == span_rref([sym(a, b)] + [unit(i, j) for i in range(4) for j in (c, d)])
        else:
            a = name[1]
            assert span_rref(W[name]) == span_rref([unit(i, a) for i in range(4)])
    print("W_t = {Xi : Xi(l, .) in span(a_l, b_l) for all l}:  pair (a,b): span(alt_ab, s_cd);  star a: {xi (x) e_a}")
    print("N_t = {F : F(l, l*n_t) = 0 for all l}:  pair (a,b): f s_ab + (columns a, b zero)   [all checked]")
    print("   (so a single slice X(l, .) is only forced into a 2-dimensional span, resp. a multiple of one coordinate)")
    tr = lambda sp_: [m.T for m in sp_]
    # ---- (3,1,1): which types are compatible -------------------------------------------------------
    tab = {}
    for n1, _ in nodes:
        for n2, _ in nodes:
            tab[(n1, n2)] = len(intersect(W[n1], tr(W[n2])))
    pp = {v for (n1, n2), v in tab.items() if n1[0] == n2[0] == 'pair' and n1 == n2}
    pq = {v for (n1, n2), v in tab.items() if n1[0] == n2[0] == 'pair' and n1 != n2}
    ps = {v for (n1, n2), v in tab.items() if n1[0] != n2[0]}
    ss = {v for (n1, n2), v in tab.items() if n1[0] == n2[0] == 'star'}
    print("(3,1,1): dim of W_t n (W_t')^T: same pair", pp, "| different pairs", pq, "| pair and star", ps, "| two stars", ss)
    assert pp == {2} and pq == {0} and ps == {0} and ss == {1}
    print("   so X != 0 in W_t1 n W_t3^T etc. forces: all four types equal to one pair, or all four types stars;")
    print("   star, star': the intersection is spanned by one matrix unit (X is a monomial).")
    # pair case: final contradiction
    ok = True
    for a, b in PAIRS:
        c, d = comp(a, b)
        cnt = itertools.count()
        newsym = lambda: sp.Symbol(f'z{next(cnt)}')
        gen = lambda basis: sum((newsym() * m for m in basis), sp.zeros(4, 4))
        blockF = intersect(Nn[('pair', a, b)], tr(Nn[('pair', a, b)]))
        assert span_rref(blockF) == span_rref([sym(a, b)] + [unit(i, j) for i in (c, d) for j in (c, d)])
        F = [gen(blockF) for _ in range(3)]
        G = [gen(blockF) for _ in range(3)]
        X, Y, X1, Y1 = (gen([alt(a, b), sym(c, d)]) for _ in range(4))

        def entry(j):
            return (sum(F[v][j[0], j[1]] * G[v][j[2], j[3]] for v in range(3))
                    + X[j[0], j[2]] * Y[j[1], j[3]] + X1[j[0], j[3]] * Y1[j[1], j[2]])
        ok = ok and sp.expand(entry((a, c, b, d)) + entry((b, c, a, d))) == 0
    print("(3,1,1), pair type: with F_v, G_v in N_ab n N_ab^T = {f s_ab + block cd} and X, Y, X', Y' in span(alt_ab, s_cd):")
    print("   T[a,c,b,d] + T[b,c,a,d] = 0 identically, but P gives 2:", ok)
    assert ok
    # star case: P minus two monomial tensors has flattening rank >= 4
    Pm = sp.Matrix(16, 16, lambda r, cc: 1 if (r // 4, r % 4, cc // 4, cc % 4) in PERMS else 0)
    print("(3,1,1), star type: flattening rank of P for 01|23 is", Pm.rank(), "> 3 + 1 + 1")
    # ---- (3,2,0) ---------------------------------------------------------------------------------
    r1 = sp.symbols('x0:4')
    r3 = sp.symbols('y0:4')
    ok = True
    for a, b in PAIRS:
        for a2, b2 in ((a, b), (b, a)):
            c, d = comp(a2, b2)
            for c2, d2 in ((c, d), (d, c)):
                lhs = sp.expand(perm_form([list(e(c2)), list(r1), list(e(a2)), list(r3)]))
                ok = ok and sp.expand(lhs - (r1[b2] * r3[d2] + r1[d2] * r3[b2])) == 0
                # the two terms X_i Y_i vanish at r0 = e_c, r2 = e_a
                for Xb in (alt(a, b), sym(*comp(a, b))):
                    ok = ok and (e(c2).T * Xb * e(a2))[0] == 0
                # F in N_ab: F(e_c, r1) does not involve r1_a, r1_b
                for Fb in Nn[('pair', a, b)]:
                    row = e(c2).T * Fb
                    ok = ok and row[a2] == 0 and row[b2] == 0
    print("(3,2,0): perm(e_c, r1, e_a, r3) = r1_b r3_d + r1_d r3_b; alt_ab(e_c, e_a) = s_cd(e_c, e_a) = 0;")
    print("   F in N_ab has F(e_c, r1) free of r1_a, r1_b:", ok)
    assert ok
    # star type excluded in (3,2,0): W_star consists of forms xi (x) e_a, whose slices are all proportional
    # ---- (4,1,0) ---------------------------------------------------------------------------------
    rows = []
    for r0 in (sp.ones(4, 1), e(0)):
        for i in range(4):
            Bm = Bmat(list(r0), list(e(i)))
            rows.append([Bm[a, b] for a, b in PAIRS])
    print("(4,1,0): (a) the 8 forms perm(r0, e_i, ., .), r0 in {1, e_0}, span a space of dimension", sp.Matrix(rows).rank(),
          "= all zero-diagonal symmetric forms")
    assert sp.Matrix(rows).rank() == 6
    a_, b_, c_, d_ = sp.symbols('a b c d')
    bs = sp.symbols('b01 b02 b03 b12 b13 b23')
    Bs = sp.zeros(4, 4)
    for (i, j), v in zip(PAIRS, bs):
        Bs[i, j] = Bs[j, i] = v
    ok = True
    for piv in PAIRS:
        free = comp(*piv)
        m1, m2 = sp.zeros(4, 1), sp.zeros(4, 1)
        m1[piv[0]], m2[piv[1]] = 1, 1
        m1[free[0]], m1[free[1]], m2[free[0]], m2[free[1]] = a_, b_, c_, d_
        A, _ = sp.linear_eq_to_matrix(list(Bs * m1) + list(Bs * m2), list(bs))
        mins = set()
        for rr in itertools.combinations(range(8), 5):
            for cc in itertools.combinations(range(6), 5):
                mn = sp.expand(A.extract(list(rr), list(cc)).det())
                if mn != 0:
                    mins.add(mn)
        ok = ok and list(sp.groebner(list(mins), a_, b_, c_, d_, order='grevlex').exprs) == [1]
    print("(4,1,0): (b) for every plane L2 (six charts) the zero-diagonal symmetric B with B(L2, .) = 0 form a space")
    print("   of dimension <= 1 (the 5 x 5 minors of the linear system generate the unit ideal):", ok)
    assert ok
    print("   so P restricted to (L0 (x) K^4) x (L2 (x) K^4) has rank >= 6 - 1 = 5 > 4 for every plane L2.")


# ---------------------------------------------------------------------------------------------
# a five-term limit identity of pattern (2,2,1)
# ---------------------------------------------------------------------------------------------

def limit_terms(c1, c2, lam):
    """The five split products (pairing, F, G) of the identity, as matrices of bilinear forms."""
    c3 = -c1 - c2
    sI, sII, aI = sym(0, 1), sym(2, 3), alt(0, 1)
    q = lambda c: sI + (lam / c) * sII
    return [('01', c1 * q(c1), q(c1)), ('01', c2 * aI, aI),
            ('02', c2 * q(c2), q(c2)), ('02', c1 * aI, aI),
            ('03', c3 * q(c3), q(c3))], c3


def tensor_of(terms):
    T = {}
    for j in IDX:
        v = 0
        for pairing, F, G in terms:
            if pairing == '01':
                v += F[j[0], j[1]] * G[j[2], j[3]]
            elif pairing == '02':
                v += F[j[0], j[2]] * G[j[1], j[3]]
            else:
                v += F[j[0], j[3]] * G[j[1], j[2]]
        T[j] = v
    return T


def limit():
    c1, c2, lam = sp.symbols('c1 c2 lambda')
    terms, c3 = limit_terms(c1, c2, lam)
    T = tensor_of(terms)
    sII = sym(2, 3)
    W = tensor_of([('01', sII / c1, sII), ('02', sII / c2, sII), ('03', sII / c3, sII)])
    ok = all(sp.simplify(T[j] - lam * (1 if j in PERMS else 0) - lam**2 * W[j]) == 0 for j in IDX)
    print("""With s_I = s_01, s_II = s_23, alt_I = alt_01 (as bilinear forms of two rows), q_c = s_I + (lambda/c) s_II,
and c1 + c2 + c3 = 0, c1 c2 c3 != 0:
   c1 q_c1(r0,r1) q_c1(r2,r3) + c2 alt_I(r0,r1) alt_I(r2,r3)
 + c2 q_c2(r0,r2) q_c2(r1,r3) + c1 alt_I(r0,r2) alt_I(r1,r3)
 + c3 q_c3(r0,r3) q_c3(r1,r2)
 = lambda perm(r0,r1,r2,r3) + lambda^2 [ s_II(r0,r1) s_II(r2,r3)/c1 + s_II(r0,r2) s_II(r1,r3)/c2 + s_II(r0,r3) s_II(r1,r2)/c3 ]""")
    print("identity on all 256 entries, symbolic c1, c2, lambda:", ok)
    assert ok
    # the order-zero part: Gamma(c) = -c2 alt alt (01|23) - c1 alt alt (02|13)
    sI, aI = sym(0, 1), alt(0, 1)
    G0 = tensor_of([('01', c1 * sI, sI), ('02', c2 * sI, sI), ('03', c3 * sI, sI), ('01', c2 * aI, aI), ('02', c1 * aI, aI)])
    print("order zero: c1 s_I s_I (01|23) + c2 s_I s_I (02|13) + c3 s_I s_I (03|12) = -c2 alt_I alt_I (01|23) - c1 alt_I alt_I (02|13):",
          all(sp.expand(v) == 0 for v in G0.values()))
    # the special case c = (1, 1, -2), exact rational check for several lambda
    for lv in (sp.Rational(1, 10), sp.Rational(1, 1000)):
        terms, c3 = limit_terms(sp.Integer(1), sp.Integer(1), lv)
        T = tensor_of(terms)
        err2 = sum((T[j] / lv - (1 if j in PERMS else 0))**2 for j in IDX)
        size = max(sp.sqrt(sum(x**2 for x in F) * sum(x**2 for x in G)) for _, F, G in terms) / lv
        print(f"   c = (1, 1, -2), lambda = {lv}: |sum/lambda - P|^2 = {err2} = {float(err2):.3e},"
              f" largest term |F||G|/lambda = {float(size):.3e}, (|.|^2/|P|^2) * size^2 = {float(err2 / 24 * size**2):.4f}")
    print("   (so perm = lim_{lambda -> 0} (1/lambda) * (the five products): the error is lambda times a fixed tensor,")
    print("    the terms have size ~ 1/lambda; this is a LIMIT decomposition, not an exact one)")
    # ---- the general two-block family: three parameters (c3, p, q) --------------------------------
    c3, p, q = sp.symbols('c3 p q')
    terms, dd = general_limit_terms(c3, p, q, lam)
    T = tensor_of(terms)
    W = tensor_of([('01', dd[0] * sII, sII), ('02', dd[1] * sII, sII), ('03', dd[2] * sII, sII)])
    ok = all(sp.simplify(T[j] - lam * (1 if j in PERMS else 0) - lam**2 * W[j]) == 0 for j in IDX)
    print("""General family, parameters (c3, p, q) with c3 (c3^2 - p q) != 0; E_ij = r_i r'_j as a bilinear form of two rows:
   (E_01 + lambda phi1 s_II)(r0,r1) (-c3 E_01 + p E_10 + lambda s_II)(r2,r3)
 + (E_10 + lambda phi2 s_II)(r0,r1) ( q E_01 - c3 E_10 + lambda s_II)(r2,r3)
 + (E_01 + lambda psi1 s_II)(r0,r2) (-c3 E_01 - p E_10 + lambda s_II)(r1,r3)
 + (E_10 + lambda psi2 s_II)(r0,r2) (-q E_01 - c3 E_10 + lambda s_II)(r1,r3)
 + c3 (s_I + (lambda/c3) s_II)(r0,r3) (s_I + (lambda/c3) s_II)(r1,r2)
 = lambda perm + lambda^2 [ d1 s_II s_II (01|23) + d2 s_II s_II (02|13) + d3 s_II s_II (03|12) ],
   phi1 = -(c3+q)/D, phi2 = -(c3+p)/D, psi1 = (q-c3)/D, psi2 = (p-c3)/D, D = c3^2 - p q,
   d1 = phi1 + phi2, d2 = psi1 + psi2, d3 = 1/c3.""")
    print("identity on all 256 entries, symbolic c3, p, q, lambda:", ok)
    assert ok
    lv = sp.Rational(1, 1000)
    terms, dd = general_limit_terms(sp.Integer(1), sp.sqrt(3), -sp.sqrt(3), lv)
    T = tensor_of(terms)
    err2 = sp.nsimplify(sp.expand(sum((T[j] / lv - (1 if j in PERMS else 0))**2 for j in IDX)))
    size = max(sp.sqrt(sp.expand(sum(x**2 for x in F) * sum(x**2 for x in G))) for _, F, G in terms) / lv
    print(f"   member (c3, p, q) = (1, sqrt 3, -sqrt 3), lambda = {lv}: |sum/lambda - P|^2 = {err2}, largest term "
          f"{float(size):.4e}, (|.|^2/|P|^2) * size^2 = {float(err2 / 24 * size**2):.4f}")
    print("   (1/2 is the minimum of this constant over the family; the Levenberg-Marquardt fits of 'exact4.py fit'")
    print("    land in the family at p = -q = 1.669 c3 with the constant 0.520)")


def general_limit_terms(c3, p, q, lam):
    E01, E10, sI, sII = unit(0, 1), unit(1, 0), sym(0, 1), sym(2, 3)
    D = c3**2 - p * q
    phi1, phi2, psi1, psi2 = -(c3 + q) / D, -(c3 + p) / D, (q - c3) / D, (p - c3) / D
    terms = [('01', E01 + lam * phi1 * sII, -c3 * E01 + p * E10 + lam * sII),
             ('01', E10 + lam * phi2 * sII, q * E01 - c3 * E10 + lam * sII),
             ('02', E01 + lam * psi1 * sII, -c3 * E01 - p * E10 + lam * sII),
             ('02', E10 + lam * psi2 * sII, -q * E01 - c3 * E10 + lam * sII),
             ('03', c3 * (sI + lam / c3 * sII), sI + lam / c3 * sII)]
    return terms, (phi1 + phi2, psi1 + psi2, 1 / c3)


def frames(seed=5):
    """Bookkeeping of the eight slice frames, on a random integer tensor T of pattern (2,2,1) (exact)."""
    import random
    rnd = random.Random(seed)
    rmat = lambda: sp.Matrix(4, 4, lambda i, j: rnd.randint(-5, 5))
    F, G, X, Y = [rmat(), rmat()], [rmat(), rmat()], [rmat(), rmat()], [rmat(), rmat()]
    X1, Y1 = rmat(), rmat()
    T = tensor_of([('01', F[v], G[v]) for v in range(2)] + [('02', X[v], Y[v]) for v in range(2)] + [('03', X1, Y1)])
    tr = lambda ms: [m.T for m in ms]
    form = {(0, 1): F, (1, 0): tr(F), (2, 3): G, (3, 2): tr(G), (0, 2): X, (2, 0): tr(X), (1, 3): Y, (3, 1): tr(Y)}
    single = {(0, 3): X1, (3, 0): X1.T, (1, 2): Y1, (2, 1): Y1.T}
    nbrs = {0: (1, 2), 1: (0, 3), 2: (0, 3), 3: (1, 2)}          # the 4-cycle 0 - 1 - 3 - 2 - 0 of linked rows
    opp = {0: 3, 3: 0, 1: 2, 2: 1}
    print("random integer tensor T = sum of five split products of pattern (2,2,1); frame (i, j, k, m):")
    print("r_i = l, r_j = u with Phi_1(l, u) = Phi_2(l, u) = 0 (Phi = the two forms on rows i, j);")
    print("slice = T(l, u, ., .) as a matrix in (r_k, r_m); Psi = forms on (i, k), Psi' on (j, m), Omega on (i, m), Omega' on (j, k)")
    ok = True
    for (i, j) in form:
        k = [x for x in nbrs[i] if x != j][0]
        m = opp[i]
        lv = sp.Matrix([rnd.randint(1, 7) for _ in range(4)])
        Z = sp.Matrix.vstack(*[lv.T * Ph for Ph in form[(i, j)]])
        ns = Z.nullspace()
        uv = ns[0] + 2 * ns[1]
        Sl = sp.zeros(4, 4)
        for jj in IDX:
            Sl[jj[k], jj[m]] += T[jj] * lv[jj[i]] * uv[jj[j]]
        rk = Sl.rank()
        kl, kr = Sl.T.nullspace()[0], Sl.nullspace()[0]
        vals = [(lv.T * Ps * kl)[0] for Ps in form[(i, k)]] + [(uv.T * single[(j, k)] * kl)[0]] \
            + [(uv.T * Ps * kr)[0] for Ps in form[(j, m)]] + [(lv.T * single[(i, m)] * kr)[0]]
        good = rk == 3 and all(sp.simplify(v) == 0 for v in vals)
        ok = ok and good
        print(f"   frame {(i, j, k, m)}: rank of the slice = {rk}; Psi_v(l, .), Omega'(u, .) vanish on the left kernel and "
              f"Psi'_v(u, .), Omega(l, .) on the right kernel: {good}")
    assert ok


def fit(restarts=6, seed=0):
    import numpy as np
    import lower4
    rng = np.random.default_rng(seed)
    yv = lower4.perm_tensor().ravel()
    names = ['01', '01', '02', '02', '03']
    print("pattern (2,2,1), complex factors, Levenberg-Marquardt from random starts (numerical evidence only):")
    print("relative residual |sum - P|^2/|P|^2, size = max |F||G| over the terms")
    for trial in range(restarts):
        model = lower4.Split(names, rng)
        marks = {100: None, 400: None, 1000: None, 2500: None}
        loss = lower4.lm(model, yv, iters=2500, trace=marks)
        row = "  ".join(f"{k}: {v[0]:.1e} x {v[1]:.1e}^2 = {v[0] * v[1]**2:.3f}" for k, v in marks.items() if v)
        print(f"   start {trial}: final residual {loss:.2e}, size {model.size():.1e}, residual*size^2 = "
              f"{loss * model.size()**2:.3f} | {row}", flush=True)
        if loss < 1e-5:
            # compare with the closed-form family of 'limit': order-zero part on a column block {a, b}
            tens = lambda v: np.transpose(np.multiply.outer(model.F[v], model.G[v]), model.perm[v])
            A, C = tens(0) + tens(1), tens(4)
            a, b = max(itertools.combinations(range(4), 2), key=lambda ab: abs(C[ab[0], ab[0], ab[1], ab[1]]))
            c3, p, q = C[a, a, b, b], A[a, b, b, a], A[b, a, a, b]
            lead = sum(abs(A[j]) for j in [(a, b, a, b), (a, b, b, a), (b, a, a, b), (b, a, b, a)])
            print(f"      column block {{{a},{b}}}: A[abab]/c3 = {A[a, b, a, b] / c3:.4f}, A[baba]/c3 = {A[b, a, b, a] / c3:.4f} "
                  f"(family: -1, -1), p/c3 = {p / c3:.4f}, q/c3 = {q / c3:.4f}; share of these four entries in "
                  f"sum |A| = {lead / np.abs(A).sum():.6f}")


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'help'
    table = {'lines': lines, 'types': types, 'frames': frames, 'p221': p221, 'enum': enum, 'referee': referee,
             'limit': limit}
    if mode in table:
        table[mode]()
    elif mode == 'all':
        for name, fn in table.items():
            print(f"===== {name} =====")
            fn()
    elif mode == 'fit':
        fit(*(int(a) for a in sys.argv[2:]))
    else:
        print(__doc__)

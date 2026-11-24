"""Checks for notes/claim_b.md:  border R_k(perm_2k) >= 2k + 1 for every k >= 2  (no computer certificate is needed
for the proof; everything here re-checks the closed-form statements of the note by exact computation).

Objects.  m = 2k.  For y in K^m and 3 <= d <= m,  H_d(y) = Hessian of the elementary symmetric polynomial e_d at y:
        H_d(y)[c,e] = e_{d-2}(y without y_c, y_e)  (c != e),  zero diagonal.
DIAGONAL SLICE: if j rows of the (m-2) x m matrix x are equal to y and the other m-2-j rows are the all-ones vector,
        M_x = j! (m-2-j)! H_{j+2}(y)                                                    (mode 'slice').
THEOREM H (corank formula).  P(tau) = prod_c (tau - y_c),  a = m-d+1,  P = tau^a Phi + rho (deg rho < a, Phi monic of
degree d-1),  Theta = tau P' - a P,  G = gcd(P, P').  Then
        corank H_d(y) = sum over the values tau_i of y with Phi'(tau_i) = 0 of (multiplicity - 1)
                        + deg gcd(Phi', Theta / G)                                       (modes 'corank', 'corankq').
THEOREM C.  If d-1 <= t <= m-d, the set {y : corank H_d(y) >= t} has codimension >= t+1 in K^m, i.e. some linear
subspace of dimension t+1 meets it only in 0                                             (modes 'cert', 'count').

Modes (python3 claimb.py MODE ...):
  slice [MMAX]            exact: M_x on the diagonal slice equals j!(m-2-j)! H_{j+2}(y) (sympy, m <= MMAX, default 6;
                          and modulo p at random points for m = 8, 10 with the function Mx_mod of pairs.py)
  kernel [MMAX]           exact (sympy, symbolic y and v): the kernel identity (H_d v)_c = (-1)^d (ceil(P_v)(y_c) - v_c Phi'(y_c))
  corank P M [D]          exact: Theorem H for EVERY multiset y of size M over the prime field F_P (P > M), all d (or d = D)
  corankq [N] [SEED]      exact: Theorem H over Q at N random rational points with planted degeneracies, m = 4..9
  count P M               exact: number of points y in F_P^M with corank H_d(y) >= t, for all d, t (compare with P^(M-t-1))
  cert M D T [DEG] [SEED] exact certificate (Macaulay matrix in evaluation form modulo a prime, as in pairs.py): a random
                          integer subspace L of dimension T+1 of Q^M contains no nonzero y with corank H_D(y) >= T
  find M D T [SEED]       numerical: search for a point of corank >= T on a random complex subspace of dimension T+1
  hitting K               exact: every family of t <= K K-subsets of a (2K-2)-set has a hitting set of size
                          <= min(t-1, 2K-2-t)  (t >= 2)
  reduction K             exact: the only multisets of 2K pairings with every s_ij in {0..K-1} or equal to 2K are the
                          constant ones (K = 2, 3)
  linfactor [MMAX]        exact: det H_3 = (1-m/2)^2 e_m(a) - e_1(a) e_{m-1}(a)/4 (a = 2y - e_1(y) 1) is irreducible, hence has
                          no linear factor (sympy, m = 4..MMAX, default 6); and the restriction to a_c = 0
  beta                    exact: sum_i C(t,i) (-1)^i / (a-i) = (-1)^t ... the Beta-integral value used in Theorem C is nonzero
  indep [N]               exact: the 'extra condition' of Theorem C at N random rational node configurations
  all                     everything above at moderate size (about 5 minutes)
"""
import itertools, math, os, sys, time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'checks'))


# ------------------------------------------------------------------ small exact tools (generic coefficient ring)
def esym(vals, zero=0, one=1, mod=None):
    """[e_0, .., e_n] of the list vals."""
    e = [one] + [zero] * len(vals)
    for v in vals:
        for i in range(len(vals), 0, -1):
            e[i] = e[i] + v * e[i - 1]
            if mod:
                e[i] %= mod
    return e


def hessian(y, d, mod=None):
    """H_d(y) as a list of lists."""
    m = len(y)
    H = [[0] * m for _ in range(m)]
    for c in range(m):
        for e in range(c + 1, m):
            rest = [y[l] for l in range(m) if l not in (c, e)]
            H[c][e] = H[e][c] = esym(rest, mod=mod)[d - 2] if d - 2 <= m - 2 else 0
    return H


def rank_field(M, mod=None):
    """rank over Q (Fractions) or over F_mod."""
    M = [list(r) for r in M]
    n = len(M); ncol = len(M[0]) if M else 0
    r = 0
    for c in range(ncol):
        piv = next((i for i in range(r, n) if (M[i][c] % mod if mod else M[i][c]) != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], mod - 2, mod) if mod else 1 / Fraction(M[r][c])
        M[r] = [v * inv % mod if mod else v * inv for v in M[r]]
        for i in range(n):
            if i != r and (M[i][c] % mod if mod else M[i][c]) != 0:
                f = M[i][c]
                M[i] = [(a - f * b) % mod if mod else a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r


# polynomials in one variable: lists of coefficients, index = degree
def ptrim(a, mod=None):
    a = [v % mod for v in a] if mod else list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def pdivmod(a, b, mod=None):
    a = ptrim(a, mod); b = ptrim(b, mod)
    q = [0] * max(len(a) - len(b) + 1, 1)
    inv = pow(b[-1], mod - 2, mod) if mod else 1 / Fraction(b[-1])
    while len(a) >= len(b):
        f = a[-1] * inv
        if mod:
            f %= mod
        s = len(a) - len(b)
        q[s] = f
        for i, v in enumerate(b):
            a[s + i] = a[s + i] - f * v
        a = ptrim(a, mod)
    return ptrim(q, mod), a


def pgcd(a, b, mod=None):
    a = ptrim(a, mod); b = ptrim(b, mod)
    while b:
        a, b = b, pdivmod(a, b, mod)[1]
    return a


def pder(a, mod=None):
    return ptrim([i * a[i] for i in range(1, len(a))], mod)


def pmul(a, b, mod=None):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i + j] = out[i + j] + u * v
    return ptrim(out, mod)


def peval(a, x, mod=None):
    r = 0
    for v in reversed(a):
        r = r * x + v
        if mod:
            r %= mod
    return r


def corank_formula(y, d, mod=None, parts=False):
    """Right-hand side of Theorem H."""
    m = len(y); a = m - d + 1
    P = [1]
    for v in y:
        P = pmul(P, [-v, 1], mod)
    Phi = P[a:]                                         # quotient of P by tau^a (monic, degree d-1)
    dPhi = pder(Phi, mod)
    dP = pder(P, mod)
    Theta = ptrim([(dP[i - 1] if 1 <= i <= len(dP) else 0) - a * P[i] for i in range(len(P))], mod)   # tau P' - a P
    G = pgcd(P, dP, mod)
    Tred, rem = pdivmod(Theta, G, mod)
    assert not rem
    first = 0
    for tau in set(y):
        if peval(dPhi, tau, mod) == 0:
            first += list(y).count(tau) - 1
    g = len(pgcd(dPhi, Tred, mod)) - 1
    return (first, g) if parts else first + g


# ------------------------------------------------------------------ mode slice
def mode_slice(mmax=6):
    import sympy as sp
    ok_all = True
    for m in range(4, mmax + 1):
        y = sp.symbols(f'y0:{m}')
        for j in range(1, m - 1):
            x = [[1] * m for _ in range(m - 2 - j)] + [list(y) for _ in range(j)]
            ok = True
            for c in range(m):
                for e in range(c + 1, m):
                    cols = [l for l in range(m) if l not in (c, e)]
                    n = m - 2
                    dp = {0: sp.Integer(1)}
                    for row in x:                      # permanent by subsets of columns
                        nd = {}
                        for mask, v in dp.items():
                            for li, l in enumerate(cols):
                                if not mask >> li & 1:
                                    nd[mask | 1 << li] = nd.get(mask | 1 << li, 0) + v * row[l]
                        dp = nd
                    perm = sp.expand(dp[(1 << n) - 1])
                    rest = [y[l] for l in cols]
                    ej = sum(sp.prod(s) for s in itertools.combinations(rest, j))
                    ok &= sp.expand(perm - math.factorial(j) * math.factorial(m - 2 - j) * ej) == 0
            ok_all &= ok
            print(f"slice m={m} j={j}: M_x = j!(m-2-j)! Hess e_{j+2}(y) (symbolic): {ok}", flush=True)
    import numpy as np
    from pairs import Mx_mod
    p = 32003
    rng = np.random.default_rng(1)
    for m in (8, 10):
        for j in range(1, m - 1):
            Y = rng.integers(0, p, size=(3, m))
            x = np.ones((3, m - 2, m), dtype=np.int64)
            x[:, :j, :] = Y[:, None, :]
            M = Mx_mod(x, p)
            c = math.factorial(j) * math.factorial(m - 2 - j) % p
            ok = all((np.array(hessian([int(v) for v in Y[b]], j + 2, p)) * c % p == M[b]).all() for b in range(3))
            ok_all &= ok
            print(f"slice m={m} j={j}: equality modulo {p} at 3 random points (Mx_mod of pairs.py): {ok}", flush=True)
    return ok_all


# ------------------------------------------------------------------ mode kernel (the identity of Step 1 of Theorem H)
def mode_kernel(mmax=6):
    import sympy as sp
    tau = sp.symbols('tau')
    ok_all = True
    for m in range(4, mmax + 1):
        y = sp.symbols(f'y0:{m}'); v = sp.symbols(f'v0:{m}')
        P = sp.Poly(sp.prod([tau - yc for yc in y]), tau)
        Pv = sp.Poly(sum(v[e] * sp.prod([tau - y[l] for l in range(m) if l != e]) for e in range(m)), tau)
        for d in range(3, m + 1):
            a = m - d + 1
            ceil = lambda Q: sum(Q.coeff_monomial(tau ** b) * tau ** (b - a) for b in range(a, m + 1))
            Phi = ceil(P)
            ok = True
            for c in range(m):
                Hv = sum(v[e] * sum(sp.prod(s) for s in itertools.combinations([y[l] for l in range(m) if l not in (c, e)], d - 2))
                         for e in range(m) if e != c)
                rhs = (-1) ** d * (ceil(Pv).subs(tau, y[c]) - v[c] * sp.diff(Phi, tau).subs(tau, y[c]))
                ok &= sp.expand(Hv - rhs) == 0
            ok_all &= ok
            print(f"kernel m={m} d={d}: (H v)_c = (-1)^d (ceil(P_v)(y_c) - v_c Phi'(y_c)) for all c (symbolic): {ok}", flush=True)
    return ok_all


# ------------------------------------------------------------------ mode corank (Theorem H over F_p, all multisets)
def mode_corank(p, m, donly=None, verbose=True):
    assert p > m
    ok_all = True
    for d in ([donly] if donly else range(3, m + 1)):
        bad = 0; tot = 0; hist = {}
        for y in itertools.combinations_with_replacement(range(p), m):
            y = list(y)
            cr = m - rank_field(hessian(y, d, p), p)
            fo = corank_formula(y, d, p)
            tot += 1; hist[cr] = hist.get(cr, 0) + 1
            if cr != fo:
                bad += 1
                if bad <= 3:
                    print("   MISMATCH", y, d, cr, fo)
        ok_all &= bad == 0
        if verbose:
            print(f"corank p={p} m={m} d={d}: {tot} multisets, mismatches {bad}, corank histogram {dict(sorted(hist.items()))}", flush=True)
    return ok_all


def mode_corankq(N=300, seed=0):
    """Random rational points with planted structure: clusters, zeros, a cluster at a root of Phi' (the condition
    Phi'(tau_1) = 0 is affine-linear in each remaining coordinate, so one coordinate is solved for)."""
    import random
    random.seed(seed)
    bad = 0; tot = 0; seen = {}
    while tot < N:
        m = random.randint(4, 9); d = random.randint(3, m)
        kind = random.choice(['generic', 'clusters', 'zeros', 'root', 'root', 'root+zeros'])
        y = [Fraction(random.randint(-6, 6)) for _ in range(m)]
        if kind in ('clusters', 'root', 'root+zeros'):
            mu = random.randint(2, max(2, m - 2))
            for i in range(mu):
                y[i] = y[0]
        if kind in ('zeros', 'root+zeros'):
            z = random.randint(1, m - 2)
            for i in range(z):
                y[m - 1 - i] = Fraction(0)
        if kind in ('root', 'root+zeros'):
            # make Phi'(y[0]) = 0 by solving for the coordinate y[mu] (affine-linear)
            l = mu if mu < m else None
            if l is None:
                continue

            def val(t):
                yy = list(y); yy[l] = t
                P = [1]
                for v in yy:
                    P = pmul(P, [-v, 1])
                return peval(pder(P[m - d + 1:]), y[0])
            f0, f1 = val(Fraction(0)), val(Fraction(1))
            if f1 == f0:
                continue
            y[l] = -f0 / (f1 - f0)
        cr = m - rank_field(hessian(y, d))
        first, g = corank_formula(y, d, parts=True)
        tot += 1
        seen[(kind, cr)] = seen.get((kind, cr), 0) + 1
        if cr != first + g:
            bad += 1
            print("   MISMATCH", m, d, y, cr, first, g)
    print(f"corankq: {tot} rational points (m = 4..9, all d), mismatches {bad}")
    print("   (kind, corank) counts:", dict(sorted(seen.items())))
    return bad == 0


# ------------------------------------------------------------------ mode count (points over F_p)
def mode_count(p, m):
    assert p > m
    for d in range(3, m + 1):
        cnt = {}
        for y in itertools.combinations_with_replacement(range(p), m):
            mult = math.factorial(m)
            for v in set(y):
                mult //= math.factorial(y.count(v))
            cr = corank_formula(list(y), d, p)
            cnt[cr] = cnt.get(cr, 0) + mult
        line = []
        for t in range(1, m + 1):
            n = sum(v for c, v in cnt.items() if c >= t)
            if n:
                line.append(f"t={t}: {n} = p^{math.log(n) / math.log(p):.2f}")
        print(f"count p={p} m={m} d={d} (range of Theorem C: {d-1} <= t <= {m-d}; then at most about p^(m-t-1)):  " + ';  '.join(line), flush=True)


# ------------------------------------------------------------------ mode cert (exact certificate for Theorem C)
def hess_mod_batch(Y, d, p):
    import numpy as np
    B, m = Y.shape
    H = np.zeros((B, m, m), dtype=np.int64)
    for c in range(m):
        for e in range(c + 1, m):
            cols = [l for l in range(m) if l not in (c, e)]
            E = np.zeros((d - 1, B), dtype=np.int64); E[0] = 1
            for l in cols:
                for i in range(d - 2, 0, -1):
                    E[i] = (E[i] + Y[:, l] * E[i - 1]) % p
            H[:, c, e] = H[:, e, c] = E[d - 2]
    return H


def mode_cert(m, d, t, D=None, seed=0, p=32003, verbose=True, basis=None):
    """Certificate that L = row space of an integer (t+1) x m matrix contains no nonzero y with rank H_d(y) <= m-t:
    all monomials of degree D in the t+1 coordinates of L lie in the ideal of the (m-t+1)-minors (rank computation
    modulo p of the Macaulay matrix in evaluation form; rank = number of monomials is a proof over Q)."""
    import numpy as np
    import pairs
    rng = np.random.default_rng(seed)
    q = m - t + 1
    gdeg = q * (d - 2)
    if basis is None:
        basis = rng.integers(-9, 10, size=(t + 1, m))
    degs = [D] if D else range(gdeg, gdeg + 40)
    for DD in degs:
        ncols = math.comb(DD + t, t)
        if ncols > 14000:
            if verbose:
                print(f"cert m={m} d={d} t={t}: degree {DD} would need {ncols} monomials; stopped (NOT certified)")
            return False, basis
        pts = rng.integers(0, p, size=(ncols + 30, t + 1))
        Y = pts @ (basis % p) % p
        H = hess_mod_batch(Y, d, p)
        Gm, _ = pairs.minors_mod(H, q, p)
        mult = pairs.eval_monomials(list(pairs.monomials(t + 1, DD - gdeg)), pts, p)
        t0 = time.time()
        r = pairs.macaulay_rank(Gm, mult, ncols, rng, p, verbose=False)
        if verbose:
            print(f"cert m={m} d={d} t={t}: L of dimension {t+1} (seed {seed}), {Gm.shape[0]} minors of size {q} and degree {gdeg}; "
                  f"degree {DD}: {ncols} monomials, rank {r}  ({time.time()-t0:.1f} s)", flush=True)
        if r == ncols:
            if verbose:
                print(f"   CERTIFIED: no nonzero y in L with corank Hess e_{d}(y) >= {t}   (m={m}; basis rows {basis.tolist()})", flush=True)
            return True, basis
    return False, basis


def mode_find(m, d, t, seed=0, starts=30):
    import numpy as np
    from scipy.optimize import minimize
    rng = np.random.default_rng(seed)
    L = rng.normal(size=(t + 1, m)) + 1j * rng.normal(size=(t + 1, m))

    def H(y):
        M = np.zeros((m, m), dtype=complex)
        for c in range(m):
            for e in range(c + 1, m):
                E = np.zeros(d - 1, dtype=complex); E[0] = 1
                for l in range(m):
                    if l not in (c, e):
                        E[1:] = E[1:] + y[l] * E[:-1]
                M[c, e] = M[e, c] = E[d - 2]
        return M

    def yof(u):
        y = (u[:t + 1] + 1j * u[t + 1:]) @ L
        return y / np.linalg.norm(y)

    def f(u):
        sv = np.linalg.svd(H(yof(u)), compute_uv=False)
        return float(np.sum(sv[m - t:] ** 2))
    best = 1e9
    for s in range(starts):
        r = minimize(f, rng.normal(size=2 * (t + 1)), method='BFGS', options={'gtol': 1e-14, 'maxiter': 3000})
        best = min(best, r.fun)
        if r.fun < 1e-16:
            break
    print(f"find m={m} d={d} t={t}: least value of the sum of squares of the {t} smallest singular values on the unit "
          f"sphere of a random complex {t+1}-space: {best:.2e}  ({'a point of corank >= t EXISTS' if best < 1e-16 else 'no point found'})")
    return best


# ------------------------------------------------------------------ mode hitting
def mode_hitting(k):
    nR = 2 * k - 2
    subsets = [sum(1 << i for i in c) for c in itertools.combinations(range(nR), k)]
    first = subsets[0]                      # by symmetry the first set of the family is {0..k-1}
    hit_by_size = {j: [sum(1 << i for i in c) for c in itertools.combinations(range(nR), j)] for j in range(1, nR + 1)}
    ok_all = True
    for t in range(2, k + 1):
        bound = min(t - 1, 2 * k - 2 - t)
        bad = 0; tot = 0; worst = 0
        for rest in itertools.combinations(subsets, t - 1):       # distinct sets suffice (repetitions change nothing)
            fam = (first,) + rest
            tot += 1
            h = next(j for j in range(1, nR + 1) if any(all(B & A for A in fam) for B in hit_by_size[j]))
            worst = max(worst, h)
            bad += h > bound
        ok_all &= bad == 0
        print(f"hitting k={k} t={t}: {tot} families of <= {t} {k}-subsets of {nR} rows containing a fixed set; largest hitting "
              f"number {worst}; bound min(t-1, 2k-2-t) = {bound}; violations {bad}", flush=True)
    return ok_all


# ------------------------------------------------------------------ mode reduction
def mode_reduction(k):
    m = 2 * k
    pairings = [S for S in itertools.combinations(range(m), k) if 0 in S]
    sep = [[int((i in S) != (j in S)) for i in range(m) for j in range(i + 1, m)] for S in pairings]
    allowed = set(range(k)) | {m}
    tot = 0; good = []
    for ms in itertools.combinations_with_replacement(range(len(pairings)), m):
        tot += 1
        s = [sum(sep[v][q] for v in ms) for q in range(len(sep[0]))]
        if all(v in allowed for v in s):
            good.append(ms)
    const = all(len(set(ms)) == 1 for ms in good)
    print(f"reduction k={k}: {tot} multisets of {m} pairings; with every s_ij in {{0..{k-1}}} or = {m}: {len(good)}; "
          f"all of them constant (one pairing repeated): {const}")
    return const and len(good) == len(pairings)


# ------------------------------------------------------------------ mode linfactor
def mode_linfactor(mmax=6):
    import sympy as sp
    ok_all = True
    for m in range(4, mmax + 1):
        a = sp.symbols(f'a0:{m}')
        es = [sum(sp.prod(s) for s in itertools.combinations(a, j)) for j in range(m + 1)]
        G = sp.Matrix(m, m, lambda c, e: 0 if c == e else -sp.Rational(1, 2) * (a[c] + a[e]))
        closed = sp.expand((1 - sp.Rational(m, 2)) ** 2 * es[m] - es[1] * es[m - 1] / 4)
        okdet = sp.expand(G.det() - closed) == 0
        cst, fac = sp.factor_list(closed)
        irr = len(fac) == 1 and fac[0][1] == 1
        restr = sp.expand(closed.subs(a[0], 0) + sum(a[1:]) * sp.prod(a[1:]) / 4) == 0
        ok_all &= okdet and irr and restr
        print(f"linfactor m={m}: det H_3 = (1-m/2)^2 e_m(a) - e_1(a) e_(m-1)(a)/4: {okdet}; irreducible over Q: {irr}; "
              f"restriction to a_0 = 0 equals -(sum a')(prod a')/4: {restr}", flush=True)
    return ok_all


# ------------------------------------------------------------------ mode beta, indep
def mode_beta(amax=14):
    ok = True
    for a in range(2, amax + 1):
        for t in range(1, a):
            s = sum(Fraction(math.comb(t, i) * (-1) ** i, a - i) for i in range(t + 1))
            # = (-1)^t B(a-t, t+1) = (-1)^t (a-t-1)! t! / a!
            ok &= s == Fraction((-1) ** t * math.factorial(a - t - 1) * math.factorial(t), math.factorial(a))
    print(f"beta: sum_i C(t,i)(-1)^i/(a-i) = (-1)^t (a-t-1)! t!/a!  (nonzero) for all 1 <= t < a <= {amax}: {ok}")
    return ok


def mode_indep(N=200, seed=0):
    """The extra condition of Theorem C: for nodes xi_1..xi_r (rational, distinct), multiplicities c with |c| = t <= a-1,
    E = prod (tau - xi_b)^{c_b}, F = L^{-1} E (coefficient of tau^i divided by a - i).  Theorem C needs F(xi_b) != 0
    for generic nodes; here: how often it holds at random rational nodes, and the value at coinciding nodes."""
    import random
    random.seed(seed)
    zero = 0; tot = 0
    for _ in range(N):
        a = random.randint(2, 9); t = random.randint(1, a - 1)
        r = random.randint(1, t)
        xi = random.sample(range(-7, 8), r)
        c = [1] * r
        for _ in range(t - r):
            c[random.randrange(r)] += 1
        E = [Fraction(1)]
        for x, cb in zip(xi, c):
            for _ in range(cb):
                E = pmul(E, [Fraction(-x), Fraction(1)])
        F = [E[i] / (a - i) for i in range(len(E))]
        for x in xi:
            tot += 1
            zero += peval(F, Fraction(x)) == 0
    print(f"indep: (L^-1 E)(xi_b) at {tot} random rational (node configuration, node) pairs: zero in {zero} cases "
          f"(it is a nonzero polynomial in the nodes; zeros at special integer nodes are possible)")
    return True


# ------------------------------------------------------------------ main
def mode_all():
    res = {}
    res['slice'] = mode_slice(6)
    res['kernel'] = mode_kernel(6)
    res['corank F_7 m=4,5'] = mode_corank(7, 4) and mode_corank(7, 5)
    res['corank F_11 m=6'] = mode_corank(11, 6)
    res['corank F_11 m=7'] = mode_corank(11, 7)
    res['corankq'] = mode_corankq(300)
    res['linfactor'] = mode_linfactor(6)
    res['beta'] = mode_beta()
    res['indep'] = mode_indep()
    res['hitting 3'] = mode_hitting(3)
    res['hitting 4'] = mode_hitting(4)
    res['reduction 2'] = mode_reduction(2)
    res['reduction 3'] = mode_reduction(3)
    for (m, d, t) in [(6, 3, 2), (6, 3, 3), (8, 3, 2), (8, 3, 3), (8, 3, 4), (8, 4, 3)]:
        res[f'cert {m} {d} {t}'] = mode_cert(m, d, t)[0]
    print("\nSUMMARY")
    for k_, v in res.items():
        print(f"   {k_}: {'ok' if v else 'FAILED'}")
    return all(res.values())


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    mode = args[0] if args else 'help'
    ints = [int(a) for a in args[1:]]
    if mode == 'slice':
        mode_slice(*ints)
    elif mode == 'kernel':
        mode_kernel(*ints)
    elif mode == 'corank':
        mode_corank(*ints)
    elif mode == 'corankq':
        mode_corankq(*ints)
    elif mode == 'count':
        mode_count(*ints)
    elif mode == 'cert':
        prime = next((int(a.split('=')[1]) for a in sys.argv if a.startswith('--prime=')), 32003)
        m, d, t = ints[:3]
        mode_cert(m, d, t, ints[3] if len(ints) > 3 and ints[3] > 0 else None, ints[4] if len(ints) > 4 else 0, p=prime)
    elif mode == 'find':
        mode_find(*ints)
    elif mode == 'hitting':
        mode_hitting(*ints)
    elif mode == 'reduction':
        mode_reduction(*ints)
    elif mode == 'linfactor':
        mode_linfactor(*ints)
    elif mode == 'beta':
        mode_beta()
    elif mode == 'indep':
        mode_indep(*ints)
    elif mode == 'all':
        mode_all()
    else:
        print(__doc__)

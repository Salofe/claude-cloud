"""The 'two free rows' method for the balanced middle layer (notes/pairs_bound.md).

x is an (m-2) x m matrix (rows = the m-2 rows of the big matrix other than two chosen rows i, j);
M_x is the symmetric m x m matrix with zero diagonal and M_x[c,d] = perm(x without the columns c, d), so that
        perm_m(x, r_i, r_j) = r_i^T M_x r_j.
D_s = {x : rank M_x <= s}.

Modes (python3 pairs.py MODE ...):
  irred M [SEED]              exact: det M_x restricted to a random integer line, factored over Q
  cone M S C D [SEED]         exact certificate that a C-dimensional linear space Lambda of (m-2) x m matrices meets
                              D_S only in 0 (so every component of D_S has codimension >= C): the evaluation form of the
                              Macaulay matrix of the (S+1)-minors of M_x in degree D has full column rank mod p
  multi M S E D [SEED]        exact certificate in the product of projective spaces: E = e_1,..,e_{m-2} (row a ranges
                              over a random (e_a+1)-dimensional subspace), D = d_1,..,d_{m-2} the multidegree tested;
                              certifies that no x in D_S has all rows nonzero with row a in the a-th subspace
  hilb M S C DMAX [SEED]      Hilbert function of the ideal of (S+1)-minors on a random C-dimensional Lambda (mod p)
  sample M S STARTS [SEED]    numerical: points of D_S by minimisation, local (tangent) codimension, zero columns
  support K KAPPA T1 T2 ..    exact: every pattern of KAPPA non-separating terms has one of the count vectors T (e.g. 4 3,1)
  comb K [RMAX]               the pairs condition in the generic model as an integer program (least r not excluded)
  combx K R S1,S2,..          exhaustive: multisets of R pairings with all separation numbers in the given set
  theorem6                    reruns every exact ingredient of the theorem 'border R_3(perm_6) >= 8'
  theorem8                    the same for 'border R_4(perm_8) >= 9' (without the irreducibility run 'irred 8 0')
  (add --all to cone/multi to use every product generator x monomial instead of a random subset)
All 'exact' modes use integer arithmetic modulo the prime P (default 32003; --prime=) or sympy integers.
"""
import itertools, math, os, sys, time
import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'checks'))
P = 32003
for _a in sys.argv[1:]:
    if _a.startswith('--prime='):
        P = int(_a.split('=')[1])


# ------------------------------------------------------------------ M_x and its minors, exact modulo p, batched
def Mx_mod(x, p=P):
    """x: int64 array (B, n, m) with n = m-2, entries in [0, p).  Returns M (B, m, m) mod p."""
    B, n, m = x.shape
    dp = {0: np.ones(B, dtype=np.int64)}
    for j in range(n):                       # dp[mask] = perm of rows 0..j on the columns of mask (|mask| = j+1)
        nd = {}
        for mask, v in dp.items():
            for l in range(m):
                if not mask >> l & 1:
                    t = v * x[:, j, l] % p
                    k = mask | 1 << l
                    if k in nd:
                        nd[k] = (nd[k] + t) % p
                    else:
                        nd[k] = t
        dp = nd
    full = (1 << m) - 1
    M = np.zeros((B, m, m), dtype=np.int64)
    for c in range(m):
        for d in range(c + 1, m):
            M[:, c, d] = M[:, d, c] = dp[full ^ (1 << c) ^ (1 << d)]
    return M


def minors_mod(M, q, p=P, symmetric=True):
    """All q x q minors of the (B, m, m) matrices M mod p.  Returns (G (ngen, B), labels).  For symmetric M only the
    minors with row set <= column set are returned."""
    B, m, _ = M.shape
    subsets = list(itertools.combinations(range(m), q))
    out, labels = [], []
    for I in subsets:
        dp = {0: np.ones(B, dtype=np.int64)}
        for j, i in enumerate(I):
            nd = {}
            for mask, v in dp.items():
                for l in range(m):
                    if not mask >> l & 1:
                        sign = bin(mask >> (l + 1)).count('1') & 1      # elements of mask larger than l
                        t = v * M[:, i, l] % p
                        if sign:
                            t = (p - t) % p
                        k = mask | 1 << l
                        if k in nd:
                            nd[k] = (nd[k] + t) % p
                        else:
                            nd[k] = t
            dp = nd
        for J in subsets:
            if symmetric and J < I:
                continue
            out.append(dp[sum(1 << l for l in J)]); labels.append((I, J))
    return np.array(out), labels


def monomials(nv, d):
    if nv == 1:
        yield (d,); return
    for a in range(d + 1):
        for rest in monomials(nv - 1, d - a):
            yield (a,) + rest


def eval_monomials(mons, pts, p=P):
    """mons: list of exponent tuples (nv,), pts: (npts, nv) int64 -> (nmons, npts) mod p"""
    mons = np.array(mons, dtype=np.int64)
    nm, nv = mons.shape
    dmax = int(mons.max()) if nm else 0
    pw = np.ones((nv, dmax + 1, pts.shape[0]), dtype=np.int64)
    for e in range(1, dmax + 1):
        pw[:, e, :] = pw[:, e - 1, :] * pts.T % p
    out = np.ones((nm, pts.shape[0]), dtype=np.int64)
    for v in range(nv):
        out = out * pw[v, mons[:, v], :] % p
    return out


FORCE_ALL = False


def rank_mod_p(E, p=P):
    from gr_dual import echelon
    A = np.asfortranarray(E, dtype=np.float64)
    return len(echelon(A, p)[0])


def macaulay_rank(G, mult_vals, ncols, rng, p=P, oversample=1.12, extra=60, verbose=True):
    """G (ngen, npts): values of the generators; mult_vals (nmult, npts): values of the multiplier monomials.
    Rank mod p of the matrix [ mult_a(pt) g_i(pt) ] over a random subset of the pairs (a, i)."""
    ngen, npts = G.shape
    nmult = mult_vals.shape[0]
    total = ngen * nmult
    if FORCE_ALL or '--all' in sys.argv:     # use every product (needed when the generators are few)
        oversample = 1e9
    want = min(total, int(oversample * ncols) + extra)
    sel = rng.choice(total, size=want, replace=False) if want < total else np.arange(total)
    E = mult_vals[sel // ngen] * G[sel % ngen] % p
    t0 = time.time()
    r = rank_mod_p(E, p)
    if verbose:
        print(f"      matrix {E.shape[0]} x {E.shape[1]} ({want} of {total} products): rank {r}  ({time.time()-t0:.1f} s)", flush=True)
    return r


def random_basis(c, n, m, rng, lo=-9, hi=9):
    return rng.integers(lo, hi + 1, size=(c, n, m))


def cone_setup(m, s, basis, D, rng, p=P, extra_pts=30):
    """Lambda = span of basis (c, n, m) integer matrices; generators = (s+1)-minors of M_x, degree d = (s+1)(m-2)."""
    c = basis.shape[0]
    n = m - 2
    d = (s + 1) * n
    ncols = math.comb(D + c - 1, c - 1)
    pts = rng.integers(0, p, size=(ncols + extra_pts, c))
    x = np.tensordot(pts, basis % p, axes=(1, 0)) % p
    M = Mx_mod(x, p)
    G, labels = minors_mod(M, s + 1, p)
    return pts, G, d, ncols


def cone_certificate(m, s, c, D, seed=0, p=P, basis=None, verbose=True):
    rng = np.random.default_rng(seed)
    n = m - 2
    if basis is None:
        basis = random_basis(c, n, m, rng)
    pts, G, d, ncols = cone_setup(m, s, basis, D, rng, p)
    if D < d:
        return False, basis
    mult = eval_monomials(list(monomials(c, D - d)), pts, p)
    if verbose:
        print(f"   m={m} s={s}: Lambda of dimension {c} (seed {seed}), {G.shape[0]} minors of size {s+1} and degree {d}; "
              f"degree D={D}: {ncols} monomials, prime {p}", flush=True)
    r = macaulay_rank(G, mult, ncols, rng, p, verbose=verbose)
    return r == ncols, basis


def hilbert_cone(m, s, c, Dmax, seed=0, p=P):
    rng = np.random.default_rng(seed)
    n = m - 2
    basis = random_basis(c, n, m, rng)
    d = (s + 1) * n
    out = {}
    for D in range(d, Dmax + 1):
        rr = np.random.default_rng(seed + 1000 + D)
        pts, G, d, ncols = cone_setup(m, s, basis, D, rr, p)
        mult = eval_monomials(list(monomials(c, D - d)), pts, p)
        r = macaulay_rank(G, mult, ncols, rr, p, oversample=1.3, extra=200, verbose=False)
        out[D] = ncols - r
        print(f"   D={D}: {ncols} monomials, rank {r}, h_D <= {ncols - r}", flush=True)
        if r == ncols:
            break
    return out, basis


# ------------------------------------------------------------------ multiprojective certificates
def multi_setup(m, s, e, Ddeg, rng, p=P, extra_pts=30, subspaces=None):
    """Row a of x ranges over a random (e_a+1)-dimensional subspace L_a of K^m (integer basis).  Variables: the
    coordinates of row a in that basis, one group per row.  Generators: (s+1)-minors, multidegree (s+1, .., s+1)."""
    n = m - 2
    assert len(e) == n and len(Ddeg) == n
    if subspaces is None:
        subspaces = [rng.integers(-9, 10, size=(e[a] + 1, m)) for a in range(n)]
    ncols = 1
    for a in range(n):
        ncols *= math.comb(Ddeg[a] + e[a], e[a])
    npts = ncols + extra_pts
    coords = [rng.integers(0, p, size=(npts, e[a] + 1)) for a in range(n)]
    x = np.stack([coords[a] @ (subspaces[a] % p) % p for a in range(n)], axis=1)
    M = Mx_mod(x, p)
    G, labels = minors_mod(M, s + 1, p)
    return coords, G, ncols, subspaces


def multi_certificate(m, s, e, Ddeg, seed=0, p=P, verbose=True, subspaces=None):
    rng = np.random.default_rng(seed)
    n = m - 2
    coords, G, ncols, subspaces = multi_setup(m, s, e, Ddeg, rng, p, subspaces=subspaces)
    q = s + 1
    if any(Ddeg[a] < q for a in range(n)):
        return False, subspaces
    mult = np.ones((1, coords[0].shape[0]), dtype=np.int64)
    for a in range(n):
        va = eval_monomials(list(monomials(e[a] + 1, Ddeg[a] - q)), coords[a], p)
        mult = (mult[:, None, :] * va[None, :, :] % p).reshape(-1, va.shape[1])
    if verbose:
        print(f"   m={m} s={s}: rows in subspaces of dimensions {[v + 1 for v in e]} (seed {seed}), {G.shape[0]} minors of size {q}; "
              f"multidegree {tuple(Ddeg)}: {ncols} monomials, prime {p}", flush=True)
    r = macaulay_rank(G, mult, ncols, rng, p, verbose=verbose)
    return r == ncols, subspaces


# ------------------------------------------------------------------ irreducibility of det M_x (exact, sympy)
def irreducible_det(m, seed=0, verbose=True):
    import random
    import sympy as sp
    n = m - 2
    random.seed(seed)
    a = [[random.randint(-5, 5) for _ in range(m)] for _ in range(n)]
    b = [[random.randint(-5, 5) for _ in range(m)] for _ in range(n)]

    def Mint(tv):
        x = [[a[i][j] + tv * b[i][j] for j in range(m)] for i in range(n)]
        dp = {0: 1}
        for j in range(n):
            nd = {}
            for mask, v in dp.items():
                for l in range(m):
                    if not mask >> l & 1:
                        nd[mask | 1 << l] = nd.get(mask | 1 << l, 0) + v * x[j][l]
            dp = nd
        full = (1 << m) - 1
        M = sp.zeros(m, m)
        for c in range(m):
            for d in range(c + 1, m):
                M[c, d] = M[d, c] = dp[full ^ (1 << c) ^ (1 << d)]
        return M
    deg = m * n
    t = sp.symbols('t')
    pts = list(range(-(deg // 2), deg - deg // 2 + 1))
    vals = [Mint(sp.Integer(pt)).det(method='bareiss') for pt in pts]
    poly = sp.Poly(sp.interpolate(list(zip(pts, vals)), t), t)
    lead = Mint(sp.Integer(0)) if False else None
    cst, fac = sp.factor_list(poly)
    degs = [(f.degree(), e_) for f, e_ in fac]
    ok = poly.degree() == deg and len(fac) == 1 and fac[0][1] == 1
    if verbose:
        print(f"m={m} seed={seed}: det M_x on the line a + t b: degree {poly.degree()} (full degree {deg}); "
              f"factor degrees over Q: {degs};  irreducible of full degree: {ok}")
        print(f"   a = {a}\n   b = {b}")
    return ok



# ------------------------------------------------------------------ supports of the classes prod_v (sum_{a in A_v} h_a)
def has_assignment(pattern, e):
    """pattern: list of sets A_v of rows; e: dict row -> count (sum = len(pattern)).  Is there a map v -> a(v) in A_v
    with exactly e[a] forms sent to row a?  (Equivalently: is the monomial h^e in the support of prod_v sum_{a in A_v} h_a.)"""
    order = sorted(range(len(pattern)), key=lambda v: len([a for a in pattern[v] if e.get(a, 0) > 0]))
    left = dict(e)

    def rec(idx):
        if idx == len(order):
            return True
        for a in pattern[order[idx]]:
            if left.get(a, 0) > 0:
                left[a] -= 1
                if rec(idx + 1):
                    left[a] += 1
                    return True
                left[a] += 1
        return False
    return rec(0)


def support_check(k, kappa, types, verbose=True):
    """m = 2k; R = m-2 rows; a pattern is a multiset of kappa k-subsets A_v of R.  Checks that for EVERY pattern some
    placement of one of the count vectors in 'types' (tuples, padded with zeros, placed on any rows) has an assignment."""
    nR = 2 * k - 2
    subsets = [frozenset(c) for c in itertools.combinations(range(nR), k)]
    placements = set()
    for t in types:
        t = tuple(t) + (0,) * (nR - len(t))
        placements |= set(itertools.permutations(t))
    placements = [{a: c for a, c in enumerate(pl) if c} for pl in placements]
    bad = 0; total = 0; example = None
    for pat in itertools.combinations_with_replacement(range(len(subsets)), kappa):
        total += 1
        pattern = [subsets[i] for i in pat]
        if not any(has_assignment(pattern, pl) for pl in placements):
            bad += 1
            example = example or [sorted(A) for A in pattern]
    if verbose:
        print(f"k={k}: {total} patterns of {kappa} {k}-subsets of {nR} rows; patterns with NO count vector of the types "
              f"{[tuple(t) for t in types]} in the support: {bad}" + (f"  e.g. {example}" if bad else ""))
    return bad == 0


# ------------------------------------------------------------------ the pairs condition as a combinatorial problem
def pairings_of(k):
    m = 2 * k
    return [S for S in itertools.combinations(range(m), k) if 0 in S]


def sep_matrix(k):
    m = 2 * k
    prs = [(i, j) for i in range(m) for j in range(i + 1, m)]
    pa = pairings_of(k)
    return np.array([[(i in S) != (j in S) for (i, j) in prs] for S in pa], dtype=np.int64), pa, prs


def smin_generic(m, r):
    """generic model: a pair with s = m - t separating terms (t >= 1) is allowed iff r - s >= t(t+1)/2."""
    s = m
    while s > 0 and r - (s - 1) >= (m - s + 1) * (m - s + 2) // 2:
        s -= 1
    return s


def comb_exhaustive(k, r, allowed):
    """all multisets of r pairings whose separation numbers s_ij all lie in the set 'allowed'"""
    sep, pa, prs = sep_matrix(k)
    out = []
    for ms in itertools.combinations_with_replacement(range(len(pa)), r):
        sv = sep[list(ms)].sum(axis=0)
        if all(int(v) in allowed for v in sv):
            out.append((ms, sorted(int(v) for v in sv)))
    return out, pa


def comb_milp(k, r, smin):
    """is there a multiset of r pairings with every pair of rows separated at least smin times?  (integer program)"""
    from scipy.optimize import milp, LinearConstraint, Bounds
    sep, pa, prs = sep_matrix(k)
    N = len(pa)
    cons = [LinearConstraint(np.ones((1, N)), r, r), LinearConstraint(sep.T.astype(float), smin, np.inf)]
    res = milp(c=np.zeros(N), constraints=cons, integrality=np.ones(N), bounds=Bounds(0, r))
    if res.status == 0 and res.x is not None:
        n = np.rint(res.x).astype(int)
        return True, {''.join(map(str, pa[i])): int(n[i]) for i in range(N) if n[i]}
    return False, None


def comb_report(k, rmax):
    m = 2 * k
    print(f"k={k} (m={m}): generic model for the pairs condition (s = m-t allowed iff r-s >= t(t+1)/2); sum of s_ij = r k^2")
    for r in range(m, rmax + 1):
        smin = smin_generic(m, r)
        avg = r * k / (2 * k - 1)
        ok, sol = comb_milp(k, r, smin)
        print(f"   r={r}: every pair needs s >= {smin}; average s = {avg:.2f}; multiset of pairings exists: {ok}" + (f"  {sol}" if ok else ""))
        if ok:
            print(f"   => the pairs condition (generic model) excludes r <= {r-1} and not r = {r}")
            break


# ------------------------------------------------------------------ numerical sampling of D_s (not exact)
def sample(m, s, starts, seed=0, e=None):
    """Points of D_s by minimising |M_x - A A^T|^2 (complex), rows normalised; with e given, row a is restricted to a
    random subspace of dimension e_a+1.  Reports (rank M, tangent codimension of D_rank in the ambient parameter space,
    number of zero columns) for the converged starts."""
    import jax, jax.numpy as jnp
    from scipy.optimize import minimize
    jax.config.update('jax_enable_x64', True)
    n = m - 2
    perms = np.array(list(itertools.permutations(range(n))))
    prs = [(c, d) for c in range(m) for d in range(c + 1, m)]
    cols = np.array([[l for l in range(m) if l not in (c, d)] for (c, d) in prs])
    iu = (np.array([p[0] for p in prs]), np.array([p[1] for p in prs]))

    def Mx(x):
        sub = jnp.transpose(x[:, cols], (1, 0, 2))
        vals = jnp.prod(sub[:, jnp.arange(n)[None, :], perms], axis=-1).sum(axis=-1)
        M = jnp.zeros((m, m), dtype=x.dtype).at[iu].set(vals)
        return M + M.T
    rng = np.random.default_rng(seed)
    e = e or [m - 1] * n
    subs = [np.linalg.qr((rng.standard_normal((e[a] + 1, m)) + 1j * rng.standard_normal((e[a] + 1, m))).T)[0].T for a in range(n)]
    offs = np.cumsum([0] + [e[a] + 1 for a in range(n)]); nc = int(offs[-1])

    def rows_of(c):
        return jnp.stack([(c[offs[a]:offs[a + 1]] / jnp.sqrt((jnp.abs(c[offs[a]:offs[a + 1]]) ** 2).sum())) @ subs[a] for a in range(n)])

    def loss(theta):
        x = rows_of(theta[:nc] + 1j * theta[nc:2 * nc])
        rest = theta[2 * nc:]
        A = (rest[:m * s] + 1j * rest[m * s:]).reshape(m, s)
        return (jnp.abs(Mx(x) - A @ A.T) ** 2).sum()
    lg = jax.jit(jax.value_and_grad(loss))
    dM = jax.jit(jax.jacfwd(lambda cr, ci: Mx(rows_of(cr + 1j * ci))))
    found = {}
    for st in range(starts):
        th = rng.standard_normal(2 * nc + 2 * m * s)
        res = minimize(lambda t: tuple(np.asarray(v, dtype=float) for v in lg(t)), th, jac=True, method='L-BFGS-B',
                       options=dict(maxiter=20000, maxfun=40000, ftol=1e-30, gtol=1e-14))
        if res.fun > 1e-16:
            key = ('not converged',)
        else:
            cr, ci = jnp.array(res.x[:nc]), jnp.array(res.x[nc:2 * nc])
            x = np.array(rows_of(cr + 1j * ci)); M = np.array(Mx(jnp.array(x)))
            U, S, Vh = np.linalg.svd(M)
            rk = int((S > 1e-6).sum())
            Nk = Vh[rk:].conj().T
            J = np.array(dM(cr, ci)).reshape(m, m, nc)
            t = m - rk
            conds = np.array([Nk[:, a] @ J[:, :, q] @ Nk[:, b] for q in range(nc) for a in range(t) for b in range(a, t)]).reshape(nc, -1)
            cs = np.linalg.svd(conds, compute_uv=False)
            key = (rk, int((cs > 1e-6).sum()), int((np.abs(x).max(axis=0) < 1e-5).sum()))
        found[key] = found.get(key, 0) + 1
    print(f"m={m}, target rank <= {s}, row subspace dimensions {[v + 1 for v in e]}: (rank M, tangent codim, zero columns): count")
    for k_, v in sorted(found.items(), key=str):
        print("   ", k_, v)


def theorem6():
    """All exact ingredients of 'the 6 x 6 permanent is not a limit of sums of 7 balanced split products'."""
    ok = True
    print("1. supports (every pattern of kappa non-separating terms has a count vector of the listed types):")
    ok &= support_check(3, 4, [(4,), (3, 1)])
    ok &= support_check(3, 5, [(5,), (4, 1)])
    ok &= support_check(3, 6, [(5, 1)])
    ok &= support_check(3, 7, [(5, 2)])
    print("2. certificates (products of subspaces that miss D_s):")
    for s, e, D in [(3, (4, 0, 0, 0), (5, 4, 4, 4)), (3, (3, 1, 0, 0), (5, 5, 4, 4)), (3, (5, 0, 0, 0), (7, 4, 4, 4)),
                    (3, (4, 1, 0, 0), (8, 8, 4, 4)), (0, (5, 1, 0, 0), (2, 2, 1, 1)), (0, (5, 2, 0, 0), (2, 2, 1, 1))]:
        global FORCE_ALL
        FORCE_ALL = (s == 0)
        c, subs = multi_certificate(6, s, list(e), list(D), seed=0)
        print(f"   D_{s} misses a product of subspaces of dimensions {[v + 1 for v in e]}: {'CERTIFIED' if c else 'FAILED'}", flush=True)
        ok &= c
    print("3. combinatorics: multisets of 7 pairings of 6 rows with every pair separated 4, 5, 6 or 7 times:")
    sols, pa = comb_exhaustive(3, 7, {4, 5, 6, 7})
    print(f"   {len(sols)} (of {math.comb(16, 7)} multisets)")
    ok &= not sols
    print("ALL INGREDIENTS VERIFIED" if ok else "SOMETHING FAILED")
    return ok


def theorem8():
    """All exact ingredients of 'the 8 x 8 permanent is not a limit of sums of 8 balanced split products', except the
    irreducibility of det M_x (run 'irred 8 0' separately, about 5 minutes)."""
    global FORCE_ALL
    ok = True
    print("1. supports:")
    ok &= support_check(4, 2, [(2,), (1, 1)])
    ok &= support_check(4, 3, [(3,), (2, 1)])
    ok &= support_check(4, 4, [(4,), (3, 1), (2, 2)])
    ok &= support_check(4, 5, [(5,), (4, 1), (3, 2)])
    ok &= support_check(4, 6, [(6,), (5, 1), (4, 2), (3, 3)])
    ok &= support_check(4, 7, [(7,), (6, 1), (5, 2), (4, 3)])
    print("2. certificates (s, count vector, multidegree, seed, all products):", flush=True)
    z = (0, 0, 0, 0)
    items = [(6, (2, 0), (8, 7), 0, False), (6, (1, 1), (8, 8), 0, False),
             (5, (5, 0), (11, 6), 0, False), (5, (2, 1), (8, 8), 1, False),
             (4, (3, 1), (7, 7), 1, False), (4, (2, 2), (8, 8), 1, False),
             (3, (4, 1), (7, 7), 1, False), (3, (3, 2), (7, 7), 1, False),
             (2, (6, 0), (4, 3), 0, True), (2, (5, 1), (5, 5), 0, True), (2, (4, 2), (5, 5), 1, False), (2, (3, 3), (5, 5), 1, False),
             (0, (7, 0), (1, 1), 0, True), (0, (6, 1), (2, 2), 0, True), (0, (5, 2), (2, 2), 0, True), (0, (4, 3), (2, 2), 0, True)]
    for s, e2, D2, seed, use_all in items:
        FORCE_ALL = use_all
        e = list(e2) + [0, 0, 0, 0]
        D = list(D2) + [s + 1] * 4
        c, subs = multi_certificate(8, s, e, D, seed=seed, verbose=False)
        print(f"   D_{s} misses a product of subspaces of dimensions {[v + 1 for v in e]} (multidegree {D}, seed {seed}): "
              f"{'CERTIFIED' if c else 'FAILED'}", flush=True)
        ok &= c
    print("ALL INGREDIENTS VERIFIED (irreducibility of det M_x not included)" if ok else "SOMETHING FAILED")
    return ok


if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    mode = args[0] if args else ''
    if mode == 'irred':
        irreducible_det(int(args[1]), int(args[2]) if len(args) > 2 else 0)
    elif mode == 'cone':
        m, s, c, D = map(int, args[1:5]); seed = int(args[5]) if len(args) > 5 else 0
        ok, basis = cone_certificate(m, s, c, D, seed)
        print(f"m={m}: a {c}-dimensional linear space meets D_{s} only in 0, hence every component of D_{s} has "
              f"codimension >= {c}: {'CERTIFIED' if ok else 'NO CERTIFICATE at this degree'}")
        if ok:
            print("   basis of Lambda:", basis.tolist())
    elif mode == 'multi':
        m, s = int(args[1]), int(args[2])
        e = [int(v) for v in args[3].split(',')]; Dd = [int(v) for v in args[4].split(',')]
        seed = int(args[5]) if len(args) > 5 else 0
        ok, subs = multi_certificate(m, s, e, Dd, seed)
        print(f"m={m}: no x in D_{s} with all rows nonzero and row a in a fixed subspace of dimension e_a+1, e = {e}: "
              f"{'CERTIFIED' if ok else 'NO CERTIFICATE at this multidegree'}")
        if ok:
            print("   subspaces:", [sub.tolist() for sub in subs])
    elif mode == 'hilb':
        m, s, c, Dmax = map(int, args[1:5]); seed = int(args[5]) if len(args) > 5 else 0
        hilbert_cone(m, s, c, Dmax, seed)
    elif mode == 'support':
        k, kappa = int(args[1]), int(args[2])
        types = [tuple(int(v) for v in a.split(',')) for a in args[3:]]
        support_check(k, kappa, types)
    elif mode == 'comb':
        k = int(args[1]); rmax = int(args[2]) if len(args) > 2 else 4 * k
        comb_report(k, rmax)
    elif mode == 'combx':
        k, r = int(args[1]), int(args[2]); allowed = {int(v) for v in args[3].split(',')}
        sols, pa = comb_exhaustive(k, r, allowed)
        print(f"k={k} r={r}: {len(sols)} multisets of pairings with all s_ij in {sorted(allowed)}")
        for ms, sv in sols[:int(args[4]) if len(args) > 4 else 5]:
            print("   ", [''.join(map(str, pa[i])) for i in ms], sv)
    elif mode == 'sample':
        m, s, starts = int(args[1]), int(args[2]), int(args[3]); seed = int(args[4]) if len(args) > 4 else 0
        e = [int(v) for v in args[5].split(',')] if len(args) > 5 else None
        sample(m, s, starts, seed, e)
    elif mode == 'theorem6':
        theorem6()
    elif mode == 'theorem8':
        theorem8()
    else:
        print(__doc__)

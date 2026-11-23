"""The determinant at the middle layer: Pfaffian rectangles.  Companion of notes/determinant.md.

Model.  For the standard symplectic form W on K^(2k), G = R W R^T (G[a,b] = w(r_a, r_b)) and
    det(R) = Pf(G) = sum over perfect matchings M of the rows of sgn(M) prod_{{a,b} in M} G[a,b].
For k even, a set of matchings X x Y (X matchings of a k-set S, Y matchings of S^c) is ONE k-split product.

Subcommands (all identities are checked in exact integer arithmetic on random integer matrices):

  rowexp            det_2k = sum_{b=1}^{2k-1} (-1)^(b-1) w(r_0, r_b) Pf(G without rows 0, b):  2k-1 products of
                    type (2 rows | 2k-2 rows), for 2k = 4, 6, 8, 10.
  minrule K         the "first half by smallest endpoint" partition of the perfect matchings of K_2k (k even)
                    into C(3k/2, k/2) rectangles; checks that it is a partition and the determinant identity.
  count KMAX        table of N, counting bound, C(3k/2,k/2) and the weighted bound of the note.
  cover K           minimum number of pairings such that every perfect matching is uncrossed by one of them
                    (integer program; lower bound for every decomposition inside the matching model, signed or not)
  signed K n        search for real matrices g_S (one per pairing, indexed by matchings of S and of S^c) with
                    sum_S g_S(M restricted) = 1 for all M and  sum_S rank(g_S) <= n   (alternating least squares
                    over rank-one terms on a chosen multiset of pairings, with pruning)
  onesided K        integer program: partitions in which every rectangle has the form X x (all matchings of S^c)
  local K           randomised improvement of a rectangle partition (general rectangles)
"""
import itertools, math, random, sys, time
import numpy as np


def matchings(rows):
    rows = list(rows)
    if not rows:
        yield (); return
    a = rows[0]
    for j in range(1, len(rows)):
        for M in matchings(rows[1:j] + rows[j + 1:]):
            yield ((a, rows[j]),) + M


def sgn(p):
    p = list(p); s = 1
    for i in range(len(p)):
        for j in range(i + 1, len(p)):
            if p[i] > p[j]: s = -s
    return s


def msgn(M): return sgn([x for e in M for x in e])


def int_det(rows):
    """exact determinant of an integer matrix (fraction-free Bareiss elimination)"""
    A = [list(map(int, r)) for r in rows]; n = len(A); prev = 1; s = 1
    for i in range(n - 1):
        if A[i][i] == 0:
            for j in range(i + 1, n):
                if A[j][i] != 0:
                    A[i], A[j] = A[j], A[i]; s = -s; break
            else:
                return 0
        for j in range(i + 1, n):
            for l in range(i + 1, n):
                A[j][l] = (A[j][l] * A[i][i] - A[j][i] * A[i][l]) // prev
        prev = A[i][i]
    return s * A[n - 1][n - 1]


def gram(R):
    """G[a][b] = w(r_a, r_b) for the standard symplectic form (column pairs (0,1), (2,3), ...)"""
    m = len(R)
    return [[sum(R[a][2 * i] * R[b][2 * i + 1] - R[a][2 * i + 1] * R[b][2 * i] for i in range(m // 2))
             for b in range(m)] for a in range(m)]


def pf(G, rows):
    """Pfaffian of the submatrix of G on the given rows, by expansion along the first row"""
    rows = list(rows)
    if not rows: return 1
    a = rows[0]; tot = 0
    for j in range(1, len(rows)):
        if G[a][rows[j]] != 0:
            tot += (-1) ** (j - 1) * G[a][rows[j]] * pf(G, rows[1:j] + rows[j + 1:])
    return tot


def part(G, Ms):
    """sum over the matchings in Ms of sgn * product of the w's"""
    return sum(msgn(M) * math.prod(G[a][b] for a, b in M) for M in Ms)


def rand_matrix(m, rng, lo=-4, hi=4):
    return [[rng.randint(lo, hi) for _ in range(m)] for _ in range(m)]


# ------------------------------------------------------------------ row expansion: 2k - 1 products

def cmd_rowexp():
    rng = random.Random(0)
    for m in (4, 6, 8, 10):
        for trial in range(3):
            R = rand_matrix(m, rng); G = gram(R)
            assert pf(G, range(m)) == int_det(R)
            tot = sum((-1) ** (b - 1) * G[0][b] * pf(G, [i for i in range(1, m) if i != b]) for b in range(1, m))
            assert tot == int_det(R), (m, trial)
        print(f"2k={m}: det = Pf(R W R^T) and det = sum of {m - 1} products w(r_0,r_b) * Pf(other {m - 2} rows): "
              f"exact on 3 random integer matrices")


# ------------------------------------------------------------------ the min rule

def minrule(k):
    """S(M) = union of the k/2 edges of M with the smallest lower endpoints.  Returns {S: set of half matchings}."""
    m = 2 * k; fib = {}
    for M in matchings(range(m)):
        a = tuple(sorted(M)[:k // 2]); S = tuple(sorted(x for e in a for x in e))
        fib.setdefault(S, set()).add(a)
    return fib


def cmd_minrule(k):
    assert k % 2 == 0
    m = 2 * k; t0 = time.time(); fib = minrule(k)
    nm = math.prod(range(1, m, 2)); nh = math.prod(range(1, k, 2))
    # partition check: the fibre of S is X_S x (all matchings of S^c), and these sets are disjoint and exhaustive
    assert sum(len(X) for X in fib.values()) * nh == nm
    for S, X in fib.items():
        t = min(i for i in range(m) if i not in S)
        Xall = [a for a in matchings(S) if all(min(e) < t for e in a)]
        assert set(map(lambda a: tuple(sorted(a)), Xall)) == X          # X_S = "every edge has an endpoint < min(S^c)"
    assert len(fib) == math.comb(3 * k // 2, k // 2)
    sizes = {}
    for S, X in fib.items(): sizes[len(X)] = sizes.get(len(X), 0) + 1
    print(f"k={k}: min rule partitions the {nm} perfect matchings of K_{m} into {len(fib)} = C({3 * k // 2},{k // 2}) "
          f"rectangles X_S x (all {nh} matchings of S^c); |X_S| : number of S = {dict(sorted(sizes.items()))}")
    print(f"       Laplace {math.comb(m, k)}, one per pairing {math.comb(m, k) // 2}, counting bound {math.ceil(nm / nh ** 2)}")
    rng = random.Random(k)
    for trial in range(2):
        R = rand_matrix(m, rng, -3, 3); G = gram(R); tot = 0
        for S, X in fib.items():
            Sc = [i for i in range(m) if i not in S]
            tot += sgn(list(S) + Sc) * part(G, X) * pf(G, Sc)
        assert tot == int_det(R)
    print(f"       exact check: det_{m} = sum of {len(fib)} {k}-split products on 2 random integer matrices  ({time.time() - t0:.0f}s)")
    return fib


def cmd_count(kmax):
    print(" k   Laplace   N=C(2k,k)/2   counting   C(3k/2,k/2)   (27/4)^(k/2)")
    for k in range(2, kmax + 1, 2):
        nm = math.prod(range(1, 2 * k, 2)); nh = math.prod(range(1, k, 2))
        print(f"{k:2d} {math.comb(2 * k, k):9d} {math.comb(2 * k, k) // 2:12d} {math.ceil(nm / nh ** 2):10d} "
              f"{math.comb(3 * k // 2, k // 2):12d} {6.75 ** (k / 2):14.1f}")


# ------------------------------------------------------------------ the matching model for a given k

class MatchingModel:
    def __init__(self, k):
        self.k = k; self.m = m = 2 * k
        self.allM = [tuple(sorted(M)) for M in matchings(range(m))]
        self.idx = {M: i for i, M in enumerate(self.allM)}
        self.pairings = [S for S in itertools.combinations(range(m), k) if 0 in S]
        self.blocks = []
        for S in self.pairings:
            Sc = tuple(i for i in range(m) if i not in S)
            MS = [tuple(sorted(M)) for M in matchings(S)]; MC = [tuple(sorted(M)) for M in matchings(Sc)]
            ids = np.array([[self.idx[tuple(sorted(a + b))] for b in MC] for a in MS])
            self.blocks.append((S, MS, MC, ids))
        self.nb = len(self.blocks[0][1])


def cmd_cover(k, tl=300):
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import lil_matrix
    mm = MatchingModel(k)
    A = lil_matrix((len(mm.allM), len(mm.pairings)))
    for j, (S, MS, MC, ids) in enumerate(mm.blocks): A[ids.ravel(), j] = 1
    res = milp(np.ones(len(mm.pairings)), constraints=LinearConstraint(A.tocsr(), 1, np.inf), bounds=Bounds(0, 1),
               integrality=np.ones(len(mm.pairings)), options=dict(time_limit=tl))
    ch = [mm.pairings[j] for j in np.where(res.x > 0.5)[0]]
    print(f"k={k}: {len(mm.allM)} matchings, {len(mm.pairings)} pairings; minimum cover by full rectangles: {len(ch)} "
          f"(status {res.status}: {'optimal' if res.status == 0 else 'feasible, time limit'}; "
          f"dual bound {getattr(res, 'mip_dual_bound', float('nan')):.2f}); counting bound {math.ceil(len(mm.allM) / mm.nb ** 2)}")
    print("   pairings:", ' '.join(''.join(map(str, S)) for S in ch))
    return ch


def signed_fit(mm, terms, rng, iters=400, tol=1e-26):
    """terms: list of pairing indices (repetitions allowed).  Unknown rank-one matrices alpha_t beta_t^T on the
    block of pairing terms[t]; equations: for every matching M, sum of the entries that M selects = 1.
    Levenberg-Marquardt.  Returns (squared residual / number of matchings, alphas, betas)."""
    nb = mm.nb; T = len(terms); nM = len(mm.allM)
    x = rng.standard_normal((T, 2, nb)) * 0.7
    def resid(x):
        r = -np.ones(nM)
        for t, p in enumerate(terms):
            np.add.at(r, mm.blocks[p][3].ravel(), np.outer(x[t, 0], x[t, 1]).ravel())
        return r
    def jac(x):
        J = np.zeros((nM, T, 2, nb))
        for t, p in enumerate(terms):
            ids = mm.blocks[p][3]
            for a in range(nb):
                J[ids[a], t, 0, a] += x[t, 1]
                J[ids[:, a], t, 1, a] += x[t, 0]
        return J.reshape(nM, -1)
    r = resid(x); loss = r @ r; lam = 1e-2
    for it in range(iters):
        J = jac(x); H = J.T @ J; g = J.T @ r; ok = False
        for _ in range(30):
            try:
                step = np.linalg.solve(H + lam * (np.diag(np.diag(H)) + 1e-12 * np.eye(len(g))), -g)
            except np.linalg.LinAlgError:
                lam *= 10; continue
            x2 = x + step.reshape(x.shape); r2 = resid(x2); l2 = r2 @ r2
            if l2 < loss: ok = True; break
            lam *= 4
        if not ok: break
        prev = loss; x, r, loss = x2, r2, l2; lam = max(lam / 3, 1e-12)
        if loss < tol or (it > 40 and prev - loss < 1e-9 * prev): break
    return loss / nM, x


def cmd_signed(k, n, tries=200, seed=0):
    """random multisets of n pairings that cover all matchings, rank-one term on each"""
    mm = MatchingModel(k); rng = np.random.default_rng(seed); prng = random.Random(seed)
    N = len(mm.pairings); best = (np.inf, None); hits = 0; t0 = time.time()
    cov = [set(b[3].ravel().tolist()) for b in mm.blocks]
    for tr in range(tries):
        while True:                                   # random cover: greedy with random tie-breaking, then fill up
            unc = set(range(len(mm.allM))); terms = []
            while unc and len(terms) < n:
                gains = [len(c & unc) for c in cov]; g = max(gains)
                cand = [p for p in range(N) if gains[p] >= g - prng.choice([0, 0, 1, 2])]
                p = prng.choice(cand); terms.append(p); unc -= cov[p]
            if not unc: break
        while len(terms) < n: terms.append(prng.randrange(N))
        loss, x = signed_fit(mm, terms, rng)
        if loss < best[0]: best = (loss, sorted(terms))
        if loss < 1e-20:
            hits += 1
            print(f"   EXACT (to rounding) with {n} rank-one terms on pairings "
                  + ' '.join(''.join(map(str, mm.pairings[p])) for p in sorted(terms)), flush=True)
            if hits >= 3: break
    print(f"k={k}, n={n}: {hits} of {tr + 1} random covers admit a solution; best mean squared residual {best[0]:.3e} "
          f"({time.time() - t0:.0f}s)")


# ------------------------------------------------------------------ one-sided partitions (integer program)

def cmd_onesided(k, tl=600):
    """choose a set of 'half matchings' (k/2 disjoint edges) such that every perfect matching contains exactly one
    of them; a k-set S is 'used' if some chosen half matching has support S; minimise the number of used S.
    Each used S gives one rectangle X_S x (all matchings of S^c)."""
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import lil_matrix, hstack, eye, csr_matrix
    m = 2 * k; allM = [tuple(sorted(M)) for M in matchings(range(m))]
    halves = {}; rowsA = []; colsA = []
    for i, M in enumerate(allM):
        for a in itertools.combinations(M, k // 2):
            j = halves.setdefault(a, len(halves)); rowsA.append(i); colsA.append(j)
    H = list(halves); supp = {}
    hs = [supp.setdefault(tuple(sorted(x for e in a for x in e)), len(supp)) for a in H]
    nH, nS = len(H), len(supp)
    A = csr_matrix((np.ones(len(rowsA)), (rowsA, colsA)), shape=(len(allM), nH + nS))
    B = csr_matrix((np.concatenate([np.ones(nH), -np.ones(nH)]),
                    (np.concatenate([np.arange(nH), np.arange(nH)]), np.concatenate([np.arange(nH), nH + np.array(hs)]))),
                   shape=(nH, nH + nS))
    c = np.concatenate([np.zeros(nH), np.ones(nS)])
    res = milp(c, constraints=[LinearConstraint(A, 1, 1), LinearConstraint(B, -np.inf, 0)], bounds=Bounds(0, 1),
               integrality=np.ones(nH + nS), options=dict(time_limit=tl, disp=False))
    if res.x is None:
        print(f"k={k}: one-sided integer program: nothing found in {tl}s"); return
    used = int(round(res.x[nH:].sum()))
    print(f"k={k}: one-sided partitions ({nH} half matchings, {nS} supports): {used} rectangles "
          f"(status {res.status}: {'optimal' if res.status == 0 else 'feasible, time limit'}; dual bound "
          f"{getattr(res, 'mip_dual_bound', float('nan')):.2f});  min rule gives {math.comb(3 * k // 2, k // 2)}")


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'rowexp'
    if cmd == 'rowexp': cmd_rowexp()
    elif cmd == 'minrule': cmd_minrule(int(sys.argv[2]))
    elif cmd == 'count': cmd_count(int(sys.argv[2]))
    elif cmd == 'cover': cmd_cover(int(sys.argv[2]), *(float(x) for x in sys.argv[3:4]))
    elif cmd == 'signed': cmd_signed(int(sys.argv[2]), int(sys.argv[3]), *(int(x) for x in sys.argv[4:6]))
    elif cmd == 'onesided': cmd_onesided(int(sys.argv[2]), *(float(x) for x in sys.argv[3:4]))
    else: print(__doc__)

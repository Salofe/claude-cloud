"""The determinant at the middle layer: Pfaffian rectangles.  Companion of notes/determinant.md.

Model.  For the standard symplectic form W on K^(2k), G = R W R^T (G[a,b] = w(r_a, r_b)) and
    det(R) = Pf(G) = sum over perfect matchings M of the rows of sgn(M) prod_{{a,b} in M} G[a,b].
For k even, a set of matchings X x Y (X matchings of a k-set S, Y matchings of S^c) is ONE k-split product.

Subcommands (all identities are checked in exact integer arithmetic on random integer matrices; the searches
cover, coverls, covergreedy, partgreedy, onesided are combinatorial and exact about what they output; signed and
det6 are floating point):

  rowexp            det_2k = sum_{b=1}^{2k-1} (-1)^(b-1) w(r_0, r_b) Pf(G without rows 0, b):  2k-1 products of
                    type (2 rows | 2k-2 rows), for 2k = 4, 6, 8, 10.
  minrule K         the "first half by smallest endpoint" partition of the perfect matchings of K_2k (k even)
                    into C(3k/2, k/2) rectangles; checks that it is a partition and the determinant identity.
  count KMAX        table of N, counting bound and C(3k/2,k/2).
  layers M          unbalanced layers: det_M = C(M-j, j) products of type (2j rows | M-2j rows), j = 1..M/2-1.
  oddrule K         k odd: det_2k = 2k * C((3k-1)/2,(k-1)/2) k-split products (one crossing edge).
  coverx K n        exhaustive search for a cover of all perfect matchings by n pairings (exact).
  fano              the hand proof of c(4) = 15 checked: 30 affine structures AG(3,2), Fano planes, blocking sets.
  cover K           minimum number of pairings such that every perfect matching is uncrossed by one of them
                    (integer program; lower bound for every decomposition inside the matching model, signed or not)
  coverls K n [steps] [seed]   local search for a cover by n pairings (heuristic upper bound for c(K)).
  covergreedy K [runs] [seed]  randomised greedy covers with pruning (heuristic upper bound for c(K)).
  partgreedy K [runs] [seed]   randomised greedy rectangle partitions (heuristic upper bound for p(K)), verified.
  signed K n        search for real matrices g_S (one per pairing, indexed by matchings of S and of S^c) with
                    sum_S g_S(M restricted) = 1 for all M and  sum_S rank(g_S) <= n   (Levenberg-Marquardt over
                    rank-one terms on random multisets of n pairings; below the cover number none exists)
  onesided K        integer program: partitions in which every rectangle has the form X x (all matchings of S^c)
  det6 lo hi        det_6 as a sum of nine 3-split products: one splitfast.py run for each orbit lo..hi-1 of
                    multisets of nine pairings (140 orbits; numerical, slow: minutes per orbit)
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


def cmd_layers(m):
    """unbalanced layers: expanding the Pfaffian along the j smallest remaining rows gives det_m (m even) as a sum
    of C(m - j, j) products of type (2j rows | m - 2j rows)"""
    rng = random.Random(m)
    for j in range(1, m // 2):
        fib = {}
        for M in matchings(range(m)):
            a = tuple(sorted(M)[:j]); fib.setdefault(tuple(sorted(x for e in a for x in e)), set()).add(a)
        assert len(fib) == math.comb(m - j, j)
        R = rand_matrix(m, rng, -3, 3); G = gram(R); tot = 0
        for S, X in fib.items():
            Sc = [i for i in range(m) if i not in S]
            tot += sgn(list(S) + Sc) * part(G, X) * pf(G, Sc)
        assert tot == int_det(R)
        print(f"m={m}: det_{m} = sum of {len(fib)} = C({m - j},{j}) products of type ({2 * j} rows | {m - 2 * j} rows)"
              f"   [Laplace along {2 * j} rows: {math.comb(m, 2 * j)}]   exact on a random integer matrix")


def cmd_oddrule(k):
    """k odd: S(M) = union of the first (k-1)/2 edges (by lower endpoint) and the lower endpoint x of the next edge.
    The fibre of S is X_S x (all (y, b')), and the crossing edge {x, y} costs the rank 2k of w across the cut:
        det_2k = sum_S sgn(S,S^c) sum_{i<2k} [sum_{(x,a') in X_S} sgn(a',x) r_x[i] w(a')] * [sum_{y,b'} sgn(y,b') (W r_y)[i] w(b')]
    i.e. 2k * C((3k-1)/2, (k-1)/2) k-split products."""
    assert k % 2 == 1
    m = 2 * k; j = (k - 1) // 2; fib = {}
    for M in matchings(range(m)):
        E = sorted(M); a = tuple(E[:j]); x = E[j][0]
        S = tuple(sorted([v for e in a for v in e] + [x])); fib.setdefault(S, set()).add((a, x))
    assert len(fib) == math.comb((3 * k - 1) // 2, j)
    rng = random.Random(k); R = rand_matrix(m, rng, -3, 3); G = gram(R)
    WR = [[(R[y][i + 1] if i % 2 == 0 else -R[y][i - 1]) for i in range(m)] for y in range(m)]      # (W r_y)[i]
    tot = 0
    for S, X in fib.items():
        Sc = [i for i in range(m) if i not in S]
        for i in range(m):
            F = sum(sgn([v for e in a for v in e] + [x]) * R[x][i] * math.prod(G[p][q] for p, q in a) for a, x in X)
            Gv = 0
            for y in Sc:
                for b in matchings([v for v in Sc if v != y]):
                    Gv += sgn([y] + [v for e in b for v in e]) * WR[y][i] * math.prod(G[p][q] for p, q in b)
            tot += sgn(list(S) + Sc) * F * Gv
    assert tot == int_det(R)
    print(f"k={k} (odd): det_{m} = sum of {m} * {len(fib)} = {m * len(fib)} {k}-split products "
          f"(2k * C((3k-1)/2,(k-1)/2)); one per pairing: {math.comb(m, k) // 2}; exact on a random integer matrix")


def cmd_cover_exhaustive(k, size):
    """exact, independent of the integer programming solver: is there a set of `size` pairings such that every
    perfect matching is uncrossed by one of them?  Depth-first search branching on the pairings of an uncovered
    matching (each matching is uncrossed by C(k,k/2)/2 pairings)."""
    mm = MatchingModel(k); nM = len(mm.allM)
    cov = [0] * len(mm.pairings); of = [[] for _ in range(nM)]
    for p, b in enumerate(mm.blocks):
        for i in b[3].ravel().tolist(): cov[p] |= 1 << i; of[i].append(p)
    full = (1 << nM) - 1; maxc = max(bin(c).count('1') for c in cov); nodes = 0
    sys.setrecursionlimit(10000)
    def dfs(covered, left):
        nonlocal nodes; nodes += 1
        if covered == full: return True
        rem = nM - bin(covered).count('1')
        if rem > left * maxc: return False
        i = (~covered & full); i = (i & -i).bit_length() - 1              # first uncovered matching
        for p in of[i]:
            if dfs(covered | cov[p], left - 1): return True
        return False
    ok = dfs(0, size)
    print(f"k={k}: cover of the {nM} perfect matchings by {size} pairings: {'EXISTS' if ok else 'does NOT exist'} "
          f"(exhaustive search, {nodes} nodes)")


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


def cmd_coverls(k, n, steps=20000, seed=0):
    """local search (swap one pairing, tabu) for a cover of the perfect matchings by n pairings; heuristic upper
    bound for the cover number c(k).  Prints the cover when found."""
    mm = MatchingModel(k); rng = np.random.default_rng(seed); nM = len(mm.allM); N = len(mm.pairings)
    A = np.zeros((N, nM), np.float32)
    for p, b in enumerate(mm.blocks): A[p, b[3].ravel()] = 1
    of = [np.where(A[:, i] > 0)[0] for i in range(nM)]
    # greedy start, truncated or padded to n
    cnt = np.zeros(nM, np.int32); chosen = []
    while len(chosen) < n:
        gains = A @ (cnt == 0).astype(np.float32); gains[chosen] = -1
        p = int(rng.choice(np.where(gains >= gains.max() - 1)[0])); chosen.append(p); cnt += A[p].astype(np.int32)
    tabu = np.zeros(N, np.int64); best = int((cnt == 0).sum()); t0 = time.time()
    for it in range(1, steps + 1):
        unc = np.where(cnt == 0)[0]
        if len(unc) == 0:
            print(f"k={k}: COVER with {n} pairings found after {it} steps ({time.time() - t0:.0f}s): "
                  + ' '.join(''.join(format(x, 'x') for x in mm.pairings[p]) for p in sorted(chosen)))
            return sorted(chosen)
        e = int(rng.choice(unc)); u = (cnt == 0).astype(np.float32)
        cand = [p for p in of[e] if p not in chosen]
        g = np.array([A[p] @ u for p in cand]) + rng.random(len(cand)) * 2
        add = cand[int(np.argmax(g))]
        cnt2 = cnt + A[add].astype(np.int32)
        loss = A[chosen] @ (cnt2 == 1).astype(np.float32) + rng.random(len(chosen)) * 2
        loss[tabu[chosen] > it] += 1e6
        rem = chosen[int(np.argmin(loss))]
        chosen.remove(rem); chosen.append(add); cnt = cnt2 - A[rem].astype(np.int32); tabu[add] = it + 10 + rng.integers(10)
        best = min(best, int((cnt == 0).sum()))
    print(f"k={k}: no cover with {n} pairings found in {steps} steps ({time.time() - t0:.0f}s); fewest uncovered matchings {best}")
    return None


def cmd_covergreedy(k, runs=200, seed=0, slack=2.0):
    """randomised greedy covers (ties and near-ties broken at random), redundant pairings removed at the end;
    reports the smallest cover found: a heuristic upper bound for the cover number c(k)."""
    mm = MatchingModel(k); rng = np.random.default_rng(seed); nM = len(mm.allM); N = len(mm.pairings)
    A = np.zeros((N, nM), np.float32)
    for p, b in enumerate(mm.blocks): A[p, b[3].ravel()] = 1
    best = None; hist = {}; t0 = time.time()
    for r in range(runs):
        cnt = np.zeros(nM, np.int32); chosen = []
        while (cnt == 0).any():
            gains = A @ (cnt == 0).astype(np.float32)
            p = int(rng.choice(np.where(gains >= gains.max() - slack * rng.random())[0]))
            chosen.append(p); cnt += A[p].astype(np.int32)
        for p in list(rng.permutation(chosen)):                      # remove redundant pairings
            if (cnt[A[p] > 0] >= 2).all(): chosen.remove(p); cnt -= A[p].astype(np.int32)
        hist[len(chosen)] = hist.get(len(chosen), 0) + 1
        if best is None or len(chosen) < len(best): best = sorted(chosen)
    assert (A[best].sum(0) >= 1).all()
    print(f"k={k}: {runs} randomised greedy covers, sizes {dict(sorted(hist.items()))}; smallest {len(best)} "
          f"(counting bound {math.ceil(nM / mm.nb ** 2)}, min rule {math.comb(3 * k // 2, k // 2)})  ({time.time() - t0:.0f}s)")
    print("   " + ' '.join(''.join(format(x, 'x') for x in mm.pairings[p]) for p in best))
    return best


def verify_partition(mm, chosen, trials=1):
    """chosen: list of (pairing index, row indices, column indices).  Checks that the rectangles partition the
    perfect matchings and that the resulting sum of split products equals the determinant (exact integers)."""
    cnt = np.zeros(len(mm.allM), int)
    for p, R, C in chosen: cnt[mm.blocks[p][3][np.ix_(R, C)].ravel()] += 1
    assert (cnt == 1).all()
    m = mm.m; rng = random.Random(len(chosen))
    for _ in range(trials):
        Rm = rand_matrix(m, rng, -3, 3); G = gram(Rm); tot = 0
        for p, R, C in chosen:
            S, MS, MC, _ = mm.blocks[p]; Sc = [i for i in range(m) if i not in S]
            tot += sgn(list(S) + Sc) * part(G, [MS[i] for i in R]) * part(G, [MC[j] for j in C])
        assert tot == int_det(Rm)
    return True


def cmd_partgreedy(k, runs=20, seed=0, noise=0.05):
    """randomised greedy partition of the perfect matchings into rectangles: repeatedly take a (nearly) largest
    all-ones rectangle of still uncovered matchings; candidates are the maximal rectangles whose column set is the
    common neighbourhood of one or two rows (and the transposed version).  Heuristic upper bound for p(k)."""
    mm = MatchingModel(k); rng = np.random.default_rng(seed); P = len(mm.blocks); nb = mm.nb
    ids = np.array([b[3] for b in mm.blocks])                     # (P, nb, nb)
    best = None; hist = {}; t0 = time.time()
    iu, ju = np.triu_indices(nb)
    for r in range(runs):
        unc = np.ones(len(mm.allM), bool); chosen = []
        while unc.any():
            U = unc[ids]; cand = (0, None)
            for T in (False, True):
                V = U.transpose(0, 2, 1) if T else U
                C = V[:, iu, :] & V[:, ju, :]                                   # (P, pairs, nb) column sets
                Rr = (V[:, None, :, :] | ~C[:, :, None, :]).all(-1)             # (P, pairs, nb) rows containing C
                area = Rr.sum(-1) * C.sum(-1)
                score = area * (1 + noise * rng.random(area.shape))
                q = np.unravel_index(np.argmax(score), score.shape)
                if score[q] > cand[0]:
                    rows, cols = np.where(Rr[q])[0], np.where(C[q])[0]
                    cand = (score[q], (q[0], cols, rows) if T else (q[0], rows, cols))
            p, rows, cols = cand[1]; chosen.append((int(p), rows, cols)); unc[ids[p][np.ix_(rows, cols)].ravel()] = False
        hist[len(chosen)] = hist.get(len(chosen), 0) + 1
        if best is None or len(chosen) < len(best): best = chosen
    verify_partition(mm, best)
    print(f"k={k}: {runs} randomised greedy partitions, sizes {dict(sorted(hist.items()))}; smallest {len(best)} on "
          f"{len(set(c[0] for c in best))} pairings, verified exactly as a determinant identity "
          f"(min rule {math.comb(3 * k // 2, k // 2)}, counting bound {math.ceil(len(mm.allM) / nb ** 2)})  ({time.time() - t0:.0f}s)")
    return best


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
    N = len(mm.pairings); best = (np.inf, None); hits = 0; nocover = 0; t0 = time.time()
    cov = [set(b[3].ravel().tolist()) for b in mm.blocks]
    for tr in range(tries):
        for attempt in range(20):                     # random cover: greedy with random tie-breaking, then fill up
            unc = set(range(len(mm.allM))); terms = []
            while unc and len(terms) < n:
                gains = [len(c & unc) for c in cov]; g = max(gains)
                cand = [p for p in range(N) if gains[p] >= g - prng.choice([0, 0, 1, 2])]
                p = prng.choice(cand); terms.append(p); unc -= cov[p]
            if not unc: break
        nocover += bool(unc)                          # (for n below the cover number no cover exists: Prop. 4)
        while len(terms) < n: terms.append(prng.randrange(N))
        loss, x = signed_fit(mm, terms, rng)
        if loss < best[0]: best = (loss, sorted(terms))
        if loss < 1e-20:
            hits += 1
            print(f"   EXACT (to rounding) with {n} rank-one terms on pairings "
                  + ' '.join(''.join(map(str, mm.pairings[p])) for p in sorted(terms)), flush=True)
            if hits >= 3: break
    print(f"k={k}, n={n}: {hits} of {tr + 1} random multisets of pairings admit a solution ({nocover} of them do not "
          f"even cover all matchings); best mean squared residual {best[0]:.3e} ({time.time() - t0:.0f}s)")


def cmd_fano():
    """structure behind c(4) = 15: an affine structure AG(3,2) on the 8 rows has 7 parallel classes of planes
    (7 pairings) and 7 parallel classes of lines (7 perfect matchings); the matching of direction d is uncrossed
    by exactly the 3 pairings a with a.d = 0, and by no pairing outside the structure (Fano plane).  A cover must
    therefore contain a blocking set (>= 3 pairings) of each of the 30 structures, and every pairing lies in 6 of
    them: 6 |cover| >= 90."""
    pts = list(range(8)); dot = lambda a, x: bin(a & x).count('1') % 2
    base_pair = [frozenset(x for x in pts if dot(a, x) == 0) for a in range(1, 8)]
    base_match = [frozenset(frozenset((x, x ^ d)) for x in pts) for d in range(1, 8)]
    norm = lambda S, g: frozenset(g[x] for x in S)
    structs = set()
    for g in itertools.permutations(range(8)):
        if g[0] != 0: continue                       # the orbit is already reached with 0 fixed
        P = frozenset(min(norm(S, g), frozenset(pts) - norm(S, g), key=sorted) for S in base_pair)
        Mt = frozenset(frozenset(norm(e, g) for e in M) for M in base_match)
        structs.add((P, Mt))
    allpair = [frozenset(S) for S in itertools.combinations(pts, 4) if 0 in S]
    canon = lambda S: S if 0 in S else frozenset(pts) - S
    uncrossed = lambda M, S: all(e <= S or not (e & S) for e in M)
    ok = True; per_pair = {S: 0 for S in allpair}
    for P, Mt in structs:
        P = [canon(S) for S in P]
        for S in P: per_pair[S] += 1
        for M in Mt:
            inside = [S for S in P if uncrossed(M, S)]; total = [S for S in allpair if uncrossed(M, S)]
            ok &= len(inside) == 3 and len(total) == 3
        lines = [frozenset(S for S in P if uncrossed(M, S)) for M in Mt]
        # blocking sets of the 7 lines: minimum size
        best = min(r for r in range(1, 8) for B in itertools.combinations(P, r) if all(set(B) & L for L in lines))
        ok &= best == 3
    print(f"{len(structs)} affine structures on 8 points; every one has 7 pairings and 7 matchings forming a Fano plane, "
          f"minimum blocking set 3: {ok}; each pairing lies in {sorted(set(per_pair.values()))} structures; "
          f"hence |cover| >= {len(structs)} * 3 / {max(per_pair.values())} = {len(structs) * 3 // max(per_pair.values())}")


# ------------------------------------------------------------------ det_6 with nine 3-split products

def det6_orbits(n):
    """representatives (count vectors over the 10 pairings 012, 013, .., 045) of the orbits of S_6 on multisets of
    n pairings of 6 rows"""
    PAIR = [S for S in itertools.combinations(range(6), 3) if 0 in S]; pidx = {S: i for i, S in enumerate(PAIR)}
    acts = set()
    for g in itertools.permutations(range(6)):
        img = []
        for S in PAIR:
            T = tuple(sorted(g[i] for i in S))
            img.append(pidx[T if 0 in T else tuple(i for i in range(6) if i not in T)])
        acts.add(tuple(img))
    acts = np.array(sorted(acts)); seen = set(); reps = []
    def comps(n, k):
        if k == 1: yield (n,); return
        for a in range(n + 1):
            for r in comps(n - a, k - 1): yield (a,) + r
    for c in comps(n, 10):
        if c in seen: continue
        imgs = np.zeros((len(acts), 10), int); np.put_along_axis(imgs, acts, np.broadcast_to(np.array(c), acts.shape), axis=1)
        o = set(map(tuple, imgs.tolist())); seen |= o; reps.append(max(o))
    return PAIR, reps


def cmd_det6(lo, hi, n=9, iters=220):
    """exact-decomposition attempts for det_6 = sum of n 3-split products on each orbit of multisets of pairings
    (splitfast.py, one random start each), in the order: types 2 1^7, 3 1^6, 2 2 1^5, 2 2 2 1 1 1, ..."""
    import os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from splitfast import Model, lm, target
    PAIR, reps = det6_orbits(n)
    typ = lambda c: tuple(sorted([x for x in c if x], reverse=True))
    reps.sort(key=lambda c: (-len(typ(c)), typ(c), c))
    print(f"{len(reps)} orbits of multisets of {n} pairings; running {lo}..{hi}", flush=True)
    Y0 = target('det', 6)
    for j, c in enumerate(reps[lo:hi]):
        sets = [PAIR[i] for i, x in enumerate(c) for _ in range(x)]
        name = ';'.join(''.join(map(str, PAIR[i])) + (f'x{x}' if x > 1 else '') for i, x in enumerate(c) if x)
        rng = np.random.default_rng(500 + lo + j); t0 = time.time()
        mod = Model(6, sets, rng); loss, rms, its = lm(mod, Y0, iters=iters)
        print(f"{lo + j:3d} {name:44s} relative squared residual {loss:.4e}  rms of unknowns {rms:.2f}  iterations {its}  "
              f"{time.time() - t0:.0f}s", flush=True)


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
    elif cmd == 'fano': cmd_fano()
    elif cmd == 'layers': cmd_layers(int(sys.argv[2]))
    elif cmd == 'oddrule': cmd_oddrule(int(sys.argv[2]))
    elif cmd == 'coverx': cmd_cover_exhaustive(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'cover': cmd_cover(int(sys.argv[2]), *(float(x) for x in sys.argv[3:4]))
    elif cmd == 'coverls': cmd_coverls(int(sys.argv[2]), int(sys.argv[3]), *(int(x) for x in sys.argv[4:6]))
    elif cmd == 'covergreedy': cmd_covergreedy(int(sys.argv[2]), *(int(x) for x in sys.argv[3:5]))
    elif cmd == 'partgreedy': cmd_partgreedy(int(sys.argv[2]), *(int(x) for x in sys.argv[3:5]))
    elif cmd == 'det6': cmd_det6(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'signed': cmd_signed(int(sys.argv[2]), int(sys.argv[3]), *(int(x) for x in sys.argv[4:6]))
    elif cmd == 'onesided': cmd_onesided(int(sys.argv[2]), *(float(x) for x in sys.argv[3:4]))
    else: print(__doc__)

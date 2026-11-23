"""Fast solver for the "garbage" problem of the two-block model (numpy; sympy only for --syntheme).

Two-block limit decompositions of the 2k x 2k permanent (twoblock.py, garbage.py) reduce to
this. Rows 0..2k-1, columns 0..k-1 (the first block only). For a pairing pi = {R, R^c} let
q(R) be the k x k permanent tensor on the rows R and v_pi = q(R) (x) q(R^c). Find the least E
such that, for some choice of pairings for E "extra" terms,

    sum_{pi not in T} c_pi v_pi  +  sum_{pi in T} ( q(R) (x) H_pi + H'_pi (x) q(R^c) )
                                 +  sum_e F_e (x) G_e   =  0 ,        E = |T| + #e ,

with every c_pi nonzero and finite. The limit decomposition of the permanent then has N + E
split products, N = C(2k, k) / 2:

    lam * perm = sum_pi (c_pi q1(R) + lam q2(R)) (q1(R^c) + (lam / c_pi) q2(R^c))
                 + sum_e F_e G_e  -  lam^2 * sum_pi q2(R) q2(R^c) / c_pi .

  * "c-type" pairings (not in T) carry one square term, which leaves c_pi v_pi behind.
  * "tangent-type" pairings (in T) carry two terms. This is the boundary stratum c_pi -> infinity
    of "c_pi v_pi + one extra term on pi"; it belongs to the two-block model and garbage.py did
    not have it. T empty is the problem as stated in garbage.py.
  * extra terms F (x) G are arbitrary k-row tensors placed on any pairing.

RESULTS for k = 3 (6 x 6 permanent, N = 10)
  E = 6  exact, for every k: c = (1 - 2^(k-1), 1, .., 1) leaves 2^(k-1) times the T_k - 1 products
         mono_w(R_0) mono_(2..2 - w)(R_0^c), w != (1..1), all on one pairing. With all extra terms
         on one pairing 6 is optimal (the flattening has rank 6 rank(C) + rank(B) >= 6).
  E = 5  exact: C5, TERMS5 below (integers), a member of the one-parameter family family5(a, b).
         Two terms on 012|345, two on 013|245, and 12 det(024) det(135). `--verify` checks it in
         integer arithmetic together with the statement "perm_6 is a limit of 15 split products";
         `--lean` prints a Lean 4 file with the same statement.
  E <= 4 nothing found: not in the torus-fixed sub-model (all 68 configurations for E = 4, 60
         restarts each, best rel 1.0), not in the full model (all 8 configurations, 130 restarts
         each over three passes, best rel 0.99), not with tangent-type pairings (best rel 1.25).
         Exactly impossible in the matching sub-model (`--syntheme`). This is evidence, not a proof;
         the only proved general bound is E >= 2.

Method. All unknowns are complex and the residual r is holomorphic (linear in c, H, H',
bilinear in each (F_e, G_e)), so complex Levenberg-Marquardt with the exact Jacobian applies.
Minimising |r|^2 alone runs off to the trivial solutions (c supported on the pairings of the
extra terms, the other c_pi -> 0), so the objective is made scale free in c:

    mode ratio:  f = |r|^2 * sum_pi |c_pi|^-2                      (residual against the smallest |c_pi|)
    mode pen:    f = |r|^2 * sum_pi |c_pi|^-4 * sum_pi |c_pi|^2    (run-offs c_pi -> 0 are repelled)

Both are sums of squares of holomorphic functions (R[i, a] = r_i u_a(c)), vanish exactly at
solutions with all c_pi nonzero, and are invariant under c -> t c. One c is normalised to 1.
Default protocol per configuration: `pen` from random starts, then `ratio` to polish.
A run counts as SOLVED when rel = |r|^2 / (|v|^2 min|c|^2) < tol (default 1e-20) and
min|c| > max|c| / 1000. rel -> 0 slowly with min|c| -> 0 or with growing factors is a border
solution (it happens for E = 5 on other configurations, never seen for E <= 4).

Configurations (T and the multiset of pairings of the extra terms) are enumerated up to the
action of S_{2k} on the rows.

Torus-fixed sub-model (--fixed): every factor is a weight vector for the column torus, F of
weight w and G of weight (2,..,2) - w; then only the 90 (k = 3) components of weight (2,..,2)
are involved and a run takes milliseconds. Kinds: A = weight (1,..,1), B = the other weights.
Kind multisets are enumerated up to S_{2k} x S_k. The full model finds A-kind solutions from
random starts (the E = 5 identity: about one start in four) but NOT the B-kind solution with
E = 6 on one pairing (each term needs its own weight); the torus-fixed enumeration covers those.

Usage examples
  python3 garbage_fast.py 3 --verify                     exact checks of the E = 6 and E = 5 identities
  python3 garbage_fast.py 3 --syntheme                   exact: the matching sub-model needs 5
  python3 garbage_fast.py 3 --lean                       Lean 4 source of the 15-term statement
  python3 garbage_fast.py 3 4 --restarts 60              all configurations with E = 4, T empty
  python3 garbage_fast.py 3 4 --tangent 2 --restarts 20  E = 4 with |T| = 2 tangent-type pairings
  python3 garbage_fast.py 3 5 --only 0,0,1,1,5           one configuration (pairing indices)
  python3 garbage_fast.py 3 4 --fixed --restarts 60      torus-fixed sub-model, all kinds
  python3 garbage_fast.py 3 4 --fixed --tangent 1        torus-fixed, A kinds, tangent-type pairings
  python3 garbage_fast.py 2 2                            the 4 x 4 case (answer: E = 2)
  python3 garbage_fast.py 3 --list                       list pairings
"""
import argparse
import itertools
import time

import numpy as np


# ----------------------------------------------------------------------------- setup
def pairings(k):
    return [R for R in itertools.combinations(range(2 * k), k) if 0 in R]


def perm_indicator(k):
    T = np.zeros((k,) * k)
    for p in itertools.permutations(range(k)):
        T[p] = 1
    return T


class Setup:
    """Index tables. For pairing i, a tensor A (x) B with A on the rows R (the side that
    contains row 0), B on the rows R^c, written with its axes in row order and flattened, is
    np.kron(A, B)[idx[i]]."""

    def __init__(self, k):
        self.k = k
        n = 2 * k
        self.prs = pairings(k)
        self.N = len(self.prs)
        self.d = k ** k
        self.D = self.d * self.d
        self.q = perm_indicator(k).ravel()
        base = np.arange(self.D).reshape((k,) * n)
        self.idx = []
        for R in self.prs:
            Rc = tuple(i for i in range(n) if i not in R)
            self.idx.append(np.transpose(base, np.argsort(R + Rc)).ravel())
        self.V = np.stack([np.kron(self.q, self.q)[ix] for ix in self.idx])  # N x D
        self.names = [''.join(str(r) for r in R) for R in self.prs]
        self.vnorm2 = float(self.V[0] @ self.V[0])
        self.eye = np.eye(self.d)
        # weights (column multiplicities) of the d index tuples of k rows, and of the D tuples of 2k rows
        tup = np.array(list(itertools.product(range(k), repeat=k)))
        self.wt = [tuple(int((t == j).sum()) for j in range(k)) for t in tup]
        tup2 = np.array(list(itertools.product(range(k), repeat=n)))
        self.rowsW = np.array([i for i, t in enumerate(tup2) if all((t == j).sum() == 2 for j in range(k))])
        self.weights = sorted({w for w in self.wt if max(w) <= 2})          # weights that can occur in W
        self.sel = {w: np.array([i for i, x in enumerate(self.wt) if x == w]) for w in self.weights}

    def perm_table(self):
        """Action of S_{2k} on pairing indices (distinct images only)."""
        n = 2 * self.k
        ix = {frozenset(R): i for i, R in enumerate(self.prs)}
        full = frozenset(range(n))

        def image(i, p):
            R = frozenset(p[r] for r in self.prs[i])
            return ix[R] if 0 in R else ix[full - R]

        return sorted({tuple(image(i, p) for i in range(self.N)) for p in itertools.permutations(range(n))})

    def configs(self, n_extra, n_tangent):
        """(T, extra) up to row permutations: T a set of n_tangent pairings, extra a multiset
        of n_extra pairings."""
        table = self.perm_table()
        seen, out = set(), []
        for T in itertools.combinations(range(self.N), n_tangent):
            for ex in itertools.combinations_with_replacement(range(self.N), n_extra):
                key = min((tuple(sorted(t[i] for i in T)), tuple(sorted(t[i] for i in ex))) for t in table)
                if key not in seen:
                    seen.add(key)
                    out.append((T, ex))
        return out


# ----------------------------------------------------------------------------- model
class Model:
    """r(y) = sum_{pi in ctype} c_pi v_pi + sum_e place_e(F_e (x) G_e),  y = (c_free, z) complex.

    terms: list of (pairing index, Fspec, Gspec); a spec is ('free', index array) -- the
    factor is free on these coordinates and zero elsewhere -- or ('fixed', vector).
    rows: residual components kept (None = all)."""

    def __init__(self, S, terms, ctype, rows=None, cfix=None):
        self.S = S
        self.terms = terms
        self.ctype = list(ctype)
        self.cfix = cfix                      # all c fixed to these values: no c unknowns
        self.ref = self.ctype[0]
        self.free = [] if cfix is not None else self.ctype[1:]
        self.nc = len(self.free)
        self.rows = np.arange(S.D) if rows is None else np.asarray(rows)
        self.pidx = [ix[self.rows] for ix in S.idx]
        self.Vc = S.V[:, self.rows].astype(complex)
        self.Vf = self.Vc[self.free].T.copy() if self.nc else np.zeros((len(self.rows), 0), complex)
        self.slices = []
        col = self.nc
        for (_, fs, gs) in terms:
            nf = len(fs[1]) if fs[0] == 'free' else 0
            ng = len(gs[1]) if gs[0] == 'free' else 0
            self.slices.append((col, col + nf, col + nf + ng))
            col += nf + ng
        self.ny = col
        self.nz = col - self.nc

    def cvec(self, y):
        c = np.zeros(self.S.N, complex)
        if self.cfix is not None:
            c[self.ctype] = np.asarray(self.cfix)[self.ctype]
        else:
            c[self.ref] = 1.0
            c[self.free] = y[:self.nc]
        return c

    def factors(self, y):
        d = self.S.d
        out = []
        for (pi, fs, gs), (a, b, e) in zip(self.terms, self.slices):
            if fs[0] == 'free':
                F = np.zeros(d, complex)
                F[fs[1]] = y[a:b]
            else:
                F = fs[1]
            if gs[0] == 'free':
                G = np.zeros(d, complex)
                G[gs[1]] = y[b:e]
            else:
                G = gs[1]
            out.append((pi, F, G))
        return out

    def residual(self, y, jac=False):
        S = self.S
        r = self.cvec(y) @ self.Vc
        A = None
        if jac:
            A = np.empty((len(self.rows), self.ny), complex)
            A[:, :self.nc] = self.Vf
        for (pi, F, G), (_, fs, gs), (a, b, e) in zip(self.factors(y), self.terms, self.slices):
            ix = self.pidx[pi]
            r = r + np.kron(F, G)[ix]
            if jac:
                if b > a:
                    A[:, a:b] = np.kron(S.eye[:, fs[1]], G[:, None])[ix, :]
                if e > b:
                    A[:, b:e] = np.kron(F[:, None], S.eye[:, gs[1]])[ix, :]
        return (r, A) if jac else r

    def rebalance(self, y):
        """Gauge F -> tF, G -> G/t with |F| = |G| for terms with both factors free."""
        y = y.copy()
        for (_, fs, gs), (a, b, e) in zip(self.terms, self.slices):
            if b > a and e > b:
                nf, ng = np.linalg.norm(y[a:b]), np.linalg.norm(y[b:e])
                if nf > 0 and ng > 0:
                    t = np.sqrt(ng / nf)
                    y[a:b] *= t
                    y[b:e] /= t
        return y

    def random_start(self, rng, scale=0.6, cspread=0.3):
        y = (rng.standard_normal(self.ny) + 1j * rng.standard_normal(self.ny)) * scale / np.sqrt(2)
        y[:self.nc] = np.exp(rng.standard_normal(self.nc) * cspread + 1j * rng.uniform(-np.pi, np.pi, self.nc))
        return y

    # -- weights u(c) of the scale-free objectives, and W = du/dc_free
    def weight(self, y, mode):
        nc = self.nc
        if nc == 0 or mode == 'plain':
            return np.ones(1, complex), np.zeros((1, nc), complex)
        c = np.concatenate([[1.0 + 0j], y[:nc]])       # reference first
        n = nc + 1
        if mode == 'ratio':
            u = 1.0 / c
            W = np.zeros((n, nc), complex)
            W[np.arange(1, n), np.arange(nc)] = -1.0 / c[1:] ** 2
            return u, W
        if mode == 'pen':                               # u[a, b] = c_b / c_a^2, scaled by 1/n
            u = (c[None, :] / c[:, None] ** 2) / n
            W = np.zeros((n, n, nc), complex)
            for l in range(nc):
                W[:, l + 1, l] += 1.0 / c ** 2 / n                  # d/dc_b
                W[l + 1, :, l] += -2.0 * c / c[l + 1] ** 3 / n      # d/dc_a
            return u.ravel(), W.reshape(n * n, nc)
        raise ValueError(mode)

    def objective(self, y, mode):
        r = self.residual(y)
        u, _ = self.weight(y, mode)
        rr = float((r.conj() @ r).real)
        return rr * float((u.conj() @ u).real), rr


def lm(model, y, mode='ratio', iters=600, mu=1e-2, tol=1e-28, stall=50, verbose=False):
    """Complex Levenberg-Marquardt on R[i, a] = r_i(y) u_a(c). Returns y, f, |r|^2, iterations."""
    nc, ny = model.nc, model.ny
    f, rr = model.objective(y, mode)
    hist = [f]
    it = 0
    for it in range(1, iters + 1):
        r, A = model.residual(y, jac=True)
        u, W = model.weight(y, mode)
        uu = float((u.conj() @ u).real)
        rr = float((r.conj() @ r).real)
        Ar = A.conj().T @ r
        G = uu * (A.conj().T @ A)
        grad = uu * Ar
        if nc:
            uW = u.conj() @ W                      # (nc,)
            G[:, :nc] += np.outer(Ar, uW)
            G[:nc, :] += np.outer(uW.conj(), Ar.conj())
            G[:nc, :nc] += rr * (W.conj().T @ W)
            grad[:nc] += rr * uW.conj()
        dg = np.maximum(np.diag(G).real, 1e-12 * np.trace(G).real / ny)
        ok = False
        for _ in range(30):
            try:
                step = np.linalg.solve(G + mu * np.diag(dg), -grad)
            except np.linalg.LinAlgError:
                mu *= 10
                continue
            y2 = y + step
            f2, rr2 = model.objective(y2, mode)
            if np.isfinite(f2) and f2 < f:
                ok = True
                break
            mu *= 5
        if not ok:
            break
        y, f, rr = model.rebalance(y2), f2, rr2
        mu = max(mu / 3, 1e-10 if f > 1e-8 else 1e-15)
        hist.append(f)
        if verbose and it % 20 == 0:
            print(f"      it {it} f {f:.3e} |r|^2 {rr:.3e} mu {mu:.1e}", flush=True)
        if f < tol or (len(hist) > stall and hist[-stall] / f < 1.05):
            break
    return y, f, rr, it


# ----------------------------------------------------------------------------- model builders
def full_model(S, extra, tangent=(), cfix=None):
    """The problem of the header: arbitrary extra terms, tangent-type pairings T."""
    allc = np.arange(S.d)
    terms = []
    for i in tangent:
        terms.append((i, ('fixed', S.q.astype(complex)), ('free', allc)))   # q (x) H
        terms.append((i, ('free', allc), ('fixed', S.q.astype(complex))))   # H' (x) q
    for i in extra:
        terms.append((i, ('free', allc), ('free', allc)))
    ctype = [i for i in range(S.N) if i not in tangent]
    return Model(S, terms, ctype, cfix=cfix)


def fixed_model(S, kinds, tangent=(), cfix=None):
    """Torus-fixed sub-model: kinds = list of (pairing, weight w of F); G has the complementary
    weight. Only the weight-(2,..,2) components of the residual can be nonzero. Tangent-type
    pairings contribute q (x) H + H' (x) q with H, H' of weight (1,..,1)."""
    two = tuple([2] * S.k)
    wA = tuple([1] * S.k)
    terms = []
    for i in tangent:
        terms.append((i, ('fixed', S.q.astype(complex)), ('free', S.sel[wA])))
        terms.append((i, ('free', S.sel[wA]), ('fixed', S.q.astype(complex))))
    for (i, w) in kinds:
        wc = tuple(a - b for a, b in zip(two, w))
        terms.append((i, ('free', S.sel[w]), ('free', S.sel[wc])))
    return Model(S, terms, [i for i in range(S.N) if i not in tangent], rows=S.rowsW, cfix=cfix)


def run(model, S, restarts, rng, protocol=('pen', 'ratio'), iters=600, y0s=None):
    """Random restarts; each goes through the modes of `protocol` in turn. Returns a list of
    dicts sorted by rel = |r|^2 / (|v|^2 min|c|^2)."""
    out = []
    for t in range(restarts):
        y = model.random_start(rng) if y0s is None else y0s[t]
        nit = 0
        for mode in protocol:
            y, f, rr, it = lm(model, y, mode=mode, iters=iters)
            nit += it
        c = model.cvec(y)
        cc = np.abs(c[model.ctype])
        z = y[model.nc:]
        out.append(dict(rel=rr / S.vnorm2 / cc.min() ** 2, cmin=float(cc.min()), cmax=float(cc.max()), c=c, y=y, it=nit,
                        znorm=float(np.abs(z).max()) if len(z) else 0.0))
    out.sort(key=lambda u: u['rel'])
    return out


def describe(S, T, extra):
    s = "extra on [" + ' '.join(S.names[i] for i in extra) + "]"
    if T:
        s += " tangent [" + ' '.join(S.names[i] for i in T) + "]"
    return s


def matchings(elts):
    """Perfect matchings of a list of rows."""
    elts = list(elts)
    if not elts:
        yield ()
        return
    a = elts[0]
    for b in elts[1:]:
        rest = [e for e in elts if e not in (a, b)]
        for m in matchings(rest):
            yield ((a, b),) + m


def incidence(S):
    """Matchings x pairings, 1 when the pairing separates every pair of the matching.
    Gamma(c) = sum_m gamma_m w_m with gamma = A c and w_m the tensor of the matching m (sum of
    the index tuples in which the two rows of each pair of m use the same column, all columns used)."""
    ms = list(matchings(range(2 * S.k)))
    A = np.zeros((len(ms), S.N), int)
    for i, m in enumerate(ms):
        for j, R in enumerate(S.prs):
            A[i, j] = all((a in R) != (b in R) for a, b in m)
    return ms, A


def fixed_kind_configs(S, E, min_a=0, prune=True, verbose=False):
    """Torus-fixed configurations: multisets of E kinds (pairing, weight of F), up to the
    group S_{2k} (rows) x S_k (columns). Kind A = weight (1,..,1), kinds B = the other weights.

    prune (valid when the number of B terms is < k!): a matching with gamma_m != 0 needs all k!
    labellings covered, a B term covers one labelling of each matching it meets, an A term on a
    pairing that separates m covers all of them. So gamma must vanish on every matching not
    separated by an A pairing, and such a zero pattern must be compatible with all c_pi != 0."""
    k, n = S.k, 2 * S.k
    wA = tuple([1] * k)
    two = tuple([2] * k)
    W = S.weights
    widx = {w: i for i, w in enumerate(W)}
    nW = len(W)
    aid = widx[wA]
    ix = {frozenset(R): i for i, R in enumerate(S.prs)}
    full = frozenset(range(n))
    # group elements as permutations of kind ids  (pairing * nW + weight)
    gens = {}
    for g in itertools.permutations(range(n)):
        pim, swap = [], []
        for R in S.prs:
            Rg = frozenset(g[r] for r in R)
            if 0 in Rg:
                pim.append(ix[Rg]); swap.append(False)
            else:
                pim.append(ix[full - Rg]); swap.append(True)
        for h in itertools.permutations(range(k)):
            mp = []
            for i in range(S.N):
                for w in W:
                    w2 = tuple(a - b for a, b in zip(two, w)) if swap[i] else w
                    w3 = [0] * k
                    for j in range(k):
                        w3[h[j]] = w2[j]
                    mp.append(pim[i] * nW + widx[tuple(w3)])
            gens[tuple(mp)] = None
    group = [np.array(g) for g in gens]
    ms, A = incidence(S)
    fact = len(list(itertools.permutations(range(k))))
    out = []
    kindsB = [i * nW + j for i in range(S.N) for j in range(nW) if j != aid]
    for a in range(E, min_a - 1, -1):
        b = E - a
        # orbits of A multisets
        seenA, repsA = set(), []
        for pa in itertools.combinations_with_replacement(range(S.N), a):
            ka = tuple(p * nW + aid for p in pa)
            key = min(tuple(sorted(g[list(ka)])) for g in group) if a else ()
            if key not in seenA:
                seenA.add(key)
                repsA.append(ka)
        for ka in repsA:
            if prune and b < fact:
                covered = np.zeros(len(ms), bool)
                for kid in ka:
                    covered |= A[:, kid // nW].astype(bool)
                Z = np.where(~covered)[0]
                if len(Z):
                    u, s, vh = np.linalg.svd(A[Z].astype(float))
                    ker = vh[int((s > 1e-9).sum()):]
                    if ker.shape[0] == 0 or not (np.linalg.norm(ker, axis=0) > 1e-9).all():
                        continue
            stab = [g for g in group if tuple(sorted(g[list(ka)])) == tuple(sorted(ka))] if a else group
            seenB = set()
            cnt = 0
            for kb in itertools.combinations_with_replacement(kindsB, b):
                key = min(tuple(sorted(g[list(kb)])) for g in stab) if b else ()
                if key not in seenB:
                    seenB.add(key)
                    out.append(tuple((kid // nW, W[kid % nW]) for kid in ka + kb))
                    cnt += 1
            if verbose:
                print(f"   A part {[S.names[kid // nW] for kid in ka]}: |stab| {len(stab)}, {cnt} configurations", flush=True)
    return out


# ----------------------------------------------------------------------------- exact identities, k = 3
# A factor supported on permutation monomials is a "generalised matrix function" of a 3 x 3 block:
#     gmf(phi)(x_a, x_b, x_c) = sum_sigma phi(sigma) x_{a, sigma(0)} x_{b, sigma(1)} x_{c, sigma(2)} ,
# rows a < b < c, sigma in the order S3 below (permanent: phi = 1, determinant: phi = sign).
S3 = list(itertools.permutations(range(3)))


def sign(p):
    return (-1) ** sum(1 for i in range(len(p)) for j in range(i) if p[j] > p[i])


def weighted_perm(u, j):
    """phi(sigma) = u[row that uses column j]: the permanent with the entry of row i in column j
    multiplied by u[i].  sum_j weighted_perm(u, j) = (sum u) * permanent."""
    return [u[s.index(j)] for s in S3]


def std_pair(u, v):
    """For weights u on the rows of R with sum(u) = 0 and v on the rows of R^c: two split products
    whose sum is  sum over bijections m : R -> R^c of (sum_r u_r v_{m(r)}) * w_m ,
    w_m = the monomials of perm(R) perm(R^c) in which r and m(r) use the same column."""
    assert sum(u) == 0
    F = [weighted_perm(u, j) for j in range(3)]
    G = [weighted_perm(v, j) for j in range(3)]
    return [(F[0], [a - b for a, b in zip(G[0], G[2])]), (F[1], [a - b for a, b in zip(G[1], G[2])])]


# E = 5: 15 split products for the 6 x 6 permanent in the limit. Pairings in the order of
# pairings(3): 012 013 014 015 023 024 025 034 035 045.
C5 = [3, -15, 3, 9, -18, -6, 6, -18, 6, 30]
TERMS5 = ([(0, -2, F, G) for F, G in std_pair([3, -1, -2], [5, -1, -4])] +     # (pairing, scalar, phi_F, phi_G)
          [(1, -2, F, G) for F, G in std_pair([5, -7, 2], [1, 0, -1])] +
          [(5, 12, [sign(s) for s in S3], [sign(s) for s in S3])])            # 12 det(024) det(135)


def family5(a, b):
    """The one-parameter family of E = 5 identities on the same pairings (integers a, b; C5, TERMS5 is
    one third of the member a = b = 1). Every c_pi is nonzero iff a, b, a+b, 2a+b, a+2b, 2a+3b are."""
    c = [3 * a * (2 * a + b), -3 * (a + 2 * b) * (2 * a + 3 * b), 9 * a * b, 9 * b * (a + 2 * b), -9 * (a + b) * (2 * a + b),
         -9 * b * (a + b), 9 * b * (a + b), -27 * b * (a + b), 9 * b * (a + b), 9 * (a + b) * (2 * a + 3 * b)]
    terms = ([(0, -2, F, G) for F, G in std_pair([4 * a + 5 * b, -2 * a - b, -2 * a - 4 * b], [2 * a + 3 * b, -a, -a - 3 * b])] +
             [(1, 2, F, G) for F, G in std_pair([-2 * a - 3 * b, 4 * a + 3 * b, -2 * a], [2 * a + b, -a + b, -a - 2 * b])] +
             [(5, 18 * b * (a + b), [sign(s) for s in S3], [sign(s) for s in S3])])
    return c, terms


# E = 6 (all extra terms on 012|345): c = (-3, 1, ..., 1), six terms -4 * mono_w(012) * mono_{222-w}(345),
# mono_w = sum of the index tuples of weight w (polarisation of the monomial y^w).
C6 = [-3] + [1] * 9


def exact_garbage_residual(S, c, terms):
    """Integer residual of  sum_pi c_pi v_pi + sum_e scalar_e F_e (x) G_e  (terms given by full
    integer vectors of length 27)."""
    r = np.array(c, dtype=np.int64) @ S.V.astype(np.int64)
    for (pi, s, F, G) in terms:
        r = r + s * np.kron(np.array(F, dtype=np.int64), np.array(G, dtype=np.int64))[S.idx[pi]]
    return r


def gmf_vector(phi):
    v = np.zeros(27, dtype=np.int64)
    for s, x in zip(S3, phi):
        v[s[0] * 9 + s[1] * 3 + s[2]] = x
    return v


def verify_exact(verbose=True):
    """Exact checks (integers / fractions) of the E = 6 and E = 5 identities and of the statement
    that perm_6 is a limit of 15 split products. Returns True when everything holds."""
    from fractions import Fraction as Fr
    import random
    S = Setup(3)
    ok = True
    # --- E = 6
    wA = (1, 1, 1)
    terms6 = []
    for w in S.weights:
        if w == wA:
            continue
        F = np.zeros(27, dtype=np.int64)
        F[S.sel[w]] = 1
        G = np.zeros(27, dtype=np.int64)
        G[S.sel[tuple(2 - a for a in w)]] = 1
        terms6.append((0, -4, F, G))
    r6 = exact_garbage_residual(S, C6, terms6)
    ok &= not r6.any()
    if verbose:
        print(f"E = 6: sum_pi c_pi v_pi - 4 sum_w mono_w(012) mono_(222-w)(345), c = {C6}: max |residual| = {np.abs(r6).max()}")
    # --- E = 5
    terms5 = [(pi, s, gmf_vector(F), gmf_vector(G)) for (pi, s, F, G) in TERMS5]
    r5 = exact_garbage_residual(S, C5, terms5)
    ok &= not r5.any()
    if verbose:
        print(f"E = 5: sum_pi c_pi v_pi + 5 split products, c = {C5}: max |residual| = {np.abs(r5).max()}")
        for (pi, s, F, G) in TERMS5:
            print(f"    {s:3d} * gmf{F}({S.names[pi]}) * gmf{G}(complement)")
    # --- the one-parameter family
    fam_ok = True
    for (a, b) in [(1, 1), (3, -1), (1, 2), (2, 1), (1, -3), (5, 2), (-4, 7)]:
        cf, tf = family5(a, b)
        rf = exact_garbage_residual(S, cf, [(pi, s, gmf_vector(F), gmf_vector(G)) for (pi, s, F, G) in tf])
        fam_ok &= (not rf.any()) and all(x != 0 for x in cf)
    ok &= fam_ok
    if verbose:
        print(f"E = 5 family (7 integer parameter values, all c_pi nonzero): exact {fam_ok}")
    # --- the 15-term statement, coefficient by coefficient in lambda (tensors in (Z^6)^{(x)6})
    n = 6
    base = np.arange(n ** n).reshape((n,) * n)
    idx6 = []
    for R in S.prs:
        Rc = tuple(i for i in range(n) if i not in R)
        idx6.append(np.transpose(base, np.argsort(R + Rc)).ravel())

    def embed(phi, block):
        t = np.zeros((n,) * 3, dtype=np.int64)
        for s, x in zip(S3, phi):
            t[s[0] + 3 * block, s[1] + 3 * block, s[2] + 3 * block] = x
        return t.ravel()

    one = [1] * 6
    q1, q2 = embed(one, 0), embed(one, 1)
    coef0 = np.zeros(n ** n, dtype=np.int64)
    coef1 = np.zeros(n ** n, dtype=np.int64)
    for i in range(S.N):
        coef0 += C5[i] * np.kron(q1, q1)[idx6[i]]
        coef1 += (np.kron(q1, q2) + np.kron(q2, q1))[idx6[i]]
    for (pi, s, F, G) in TERMS5:
        coef0 += s * np.kron(embed(F, 0), embed(G, 0))[idx6[pi]]
    perm6 = np.zeros((n,) * n, dtype=np.int64)
    for p in itertools.permutations(range(n)):
        perm6[p] = 1
    ok &= not coef0.any()
    ok &= bool((coef1 == perm6.ravel()).all())
    if verbose:
        print(f"15 terms, lambda^0 coefficient: max |entry| = {np.abs(coef0).max()};  lambda^1 coefficient equals perm_6: "
              f"{bool((coef1 == perm6.ravel()).all())}")

    # --- the same statement evaluated at random integer matrices with exact fractions
    def gmf(phi, X, rows, block):
        return sum(x * X[rows[0]][s[0] + 3 * block] * X[rows[1]][s[1] + 3 * block] * X[rows[2]][s[2] + 3 * block]
                   for s, x in zip(S3, phi))

    rnd = random.Random(1)
    for trial in range(5):
        X = [[Fr(rnd.randint(-9, 9)) for _ in range(6)] for _ in range(6)]
        lam = Fr(1, rnd.randint(2, 50))
        permX = sum(np.prod([X[i][p[i]] for i in range(6)]) for p in itertools.permutations(range(6)))
        total, rest = Fr(0), Fr(0)
        for i, R in enumerate(S.prs):
            Rc = tuple(j for j in range(6) if j not in R)
            c = Fr(C5[i])
            total += (c * gmf(one, X, R, 0) + lam * gmf(one, X, R, 1)) * (gmf(one, X, Rc, 0) + lam / c * gmf(one, X, Rc, 1))
            rest += gmf(one, X, R, 1) * gmf(one, X, Rc, 1) / c
        for (pi, s, F, G) in TERMS5:
            R = S.prs[pi]
            Rc = tuple(j for j in range(6) if j not in R)
            total += s * gmf(F, X, R, 0) * gmf(G, X, Rc, 0)
        good = (total / lam - permX == lam * rest)
        ok &= bool(good)
        if verbose:
            print(f"    random 6 x 6 integer matrix, lambda = {lam}: (sum of 15 products) / lambda - perm_6 = lambda * rest exactly: {good}"
                  f"   (perm_6 = {permX}, error term = {float(lam * rest):.3g})")
    if verbose:
        print("ALL EXACT CHECKS PASSED" if ok else "SOME CHECK FAILED")
    return ok


def syntheme_check(verbose=True):
    """Exact (rational) analysis of the "matching" sub-model for k = 3, in which the extra terms on
    each pairing add up to a combination of the w_m (see incidence()). Then everything is a function
    on the 15 matchings: pairing pi contributes g_pi on the 6 matchings it separates,

        g_pi(m) = kappa_pi + d_pi * eps_pi(m) + sum_{r in R} C_pi[r, m(r)] ,

    kappa_pi = c_pi + (multiple of perm (x) perm), d_pi = coefficient of det(R) det(R^c), C_pi a 3 x 3
    matrix with zero row and column sums; the equations are sum_{pi separating m} g_pi(m) = 0 for
    every m. Number of extra terms (rank of the group matrix of g_pi - c_pi on S_3):

        cost = #{pi : kappa_pi = 0} + #{pi : d_pi != 0} + 2 * sum_pi rank(C_pi) .

    Shows by exact linear algebra that cost <= 4 is impossible (the identity C5 / TERMS5 has cost 5).
    Returns True when the computation confirms this."""
    import sympy as sp
    S = Setup(3)
    ms, A0 = incidence(S)
    n = 6

    def rho(pi, m):                       # the bijection R -> R^c given by m, as positions
        R = S.prs[pi]
        Rc = tuple(i for i in range(n) if i not in R)
        partner = {}
        for a, b in m:
            partner[a], partner[b] = b, a
        if any(partner[r] in R for r in R):
            return None
        return tuple(Rc.index(partner[r]) for r in R)

    A = sp.Matrix(A0.tolist())
    Ae = sp.zeros(15, 10)
    for i, m in enumerate(ms):
        for j in range(10):
            r = rho(j, m)
            if r is not None:
                Ae[i, j] = sign(r)
    basis = []                             # zero row and column sums: u (x) v, u, v in {e_a - e_2}
    for a in range(2):
        for b in range(2):
            u, v = [0, 0, 0], [0, 0, 0]
            u[a], u[2], v[b], v[2] = 1, -1, 1, -1
            basis.append([[u[i] * v[j] for j in range(3)] for i in range(3)])

    def std(pi):
        M = sp.zeros(15, 4)
        for i, m in enumerate(ms):
            r = rho(pi, m)
            if r is not None:
                for b, C in enumerate(basis):
                    M[i, b] = sum(C[p][r[p]] for p in range(3))
        return M

    ok = True
    # (a) no C at all: A kappa + Ae d = 0 forces kappa = 0
    ra, re, rae = A.rank(), Ae.rank(), A.row_join(Ae).rank()
    ok &= (ra == 10 and rae == ra + re)
    if verbose:
        print(f"(a) rank A = {ra}, rank A_eps = {re}, rank [A | A_eps] = {rae}: without C terms kappa = 0, cost >= 10")
    # (b) C on one pairing (all pairings are equivalent): rank 1 costs 2, rank 2 costs 4
    S0, S1 = std(0), std(1)
    best = None
    for nd in range(0, 3):
        for D in itertools.combinations(range(10), nd):
            M = A
            if D:
                M = M.row_join(Ae[:, list(D)])
            M = M.row_join(S0)
            ns = M.nullspace()
            if not ns:
                continue
            ok &= (len(ns) == 1)
            v = ns[0]
            kap, d, x = v[:10], v[10:10 + nd], v[10 + nd:]
            rank = 1 if x[0] * x[3] - x[1] * x[2] == 0 else 2
            cost = sum(1 for t in kap if t == 0) + sum(1 for t in d if t != 0) + 2 * rank
            best = cost if best is None else min(best, cost)
    ok &= (best is not None and best > 4)
    if verbose:
        print(f"(b) C on one pairing, d supported on at most 2 pairings: least cost {best}")
    # (c) C of rank 1 on two pairings (all pairs are equivalent), nothing else
    ns = A.row_join(S0).row_join(S1).nullspace()
    forced = [j for j in range(10) if all(v[j] == 0 for v in ns)]
    ok &= (len(forced) > 0)
    if verbose:
        print(f"(c) C on two pairings: solution space of dimension {len(ns)}, kappa vanishes identically on "
              f"{[S.names[j] for j in forced]}: cost >= {4 + len(forced)}")
        print("matching sub-model: no solution with at most 4 extra terms" if ok else "CHECK FAILED")
    return ok


def lean_source():
    """Lean 4 source (imports PvsNP.SixBySix for perm3, mk, IsSplit3, permanent_fin_six_laplace)
    stating and proving the E = 5 identity and the 15-term limit statement. Generated from C5 and
    TERMS5, the same tables that verify_exact() checks."""
    prs = pairings(3)
    L = 1
    for c in C5:
        L = L * abs(c) // np.gcd(L, abs(c))
    L = int(L)
    e = [L // c for c in C5]

    def num(x):
        return f"({x})" if x < 0 else str(x)

    def rows(R):
        return ' '.join(f"(A {r})" for r in R)

    def comp(R):
        return tuple(i for i in range(6) if i not in R)

    def gm(phi):
        return "gmf " + ' '.join(num(x) for x in phi) + " 0 1 2"

    sq, gb, rs, ex, ts = [], [], [], [], []
    for i, R in enumerate(prs):
        Rc = comp(R)
        sq.append(f"(wsq {num(C5[i])} 1 lam {rows(R)}) * (wsq {L} {num(e[i])} lam {rows(Rc)})")
        gb.append(f"{num(C5[i])} * (perm3 0 1 2 {rows(R)} * perm3 0 1 2 {rows(Rc)})")
        rs.append(f"{num(e[i])} * (perm3 3 4 5 {rows(R)} * perm3 3 4 5 {rows(Rc)})")
        ts.append(f"mk {' '.join(map(str, R + Rc))} (fun u v w => ({L} * lam)⁻¹ * wsq {num(C5[i])} 1 lam u v w) "
                  f"(fun u v w => wsq {L} {num(e[i])} lam u v w)")
    for (pi, s, F, G) in TERMS5:
        R = prs[pi]
        Rc = comp(R)
        ex.append(f"{num(s)} * ({gm(F)} {rows(R)} * {gm(G)} {rows(Rc)})")
        ts.append(f"mk {' '.join(map(str, R + Rc))} (fun u v w => lam⁻¹ * {num(s)} * {gm(F)} u v w) (fun u v w => {gm(G)} u v w)")
    nl = "\n    + "
    rc = ' | '.join(['rfl'] * 15)
    return f"""import PvsNP.SixBySix

/-!
# The middle layer of the 6 × 6 permanent: 15 split products in the limit

Generated by `python3 garbage_fast.py 3 --lean`. Rows `0, …, 5`, column blocks `{{0, 1, 2}}` and
`{{3, 4, 5}}`. Ten weighted squares, one for each splitting `R | Rᶜ` of the rows, leave behind
`∑ c_R * perm(R) * perm(Rᶜ)` in the first block, with `c = {C5}` for the splittings
`012, 013, 014, 015, 023, 024, 025, 034, 035, 045`. That combination is cancelled by five split
products: two for `012|345`, two for `013|245` and `12 * det(024) * det(135)`.
-/

namespace PvsNP

open Matrix

section Ring

variable {{R : Type*}} [CommRing R]

/-- Generalised matrix function of the row vectors `u, v, w` on columns `p, q, r`: one
coefficient for each permutation (permanent: all `1`, determinant: the signs). -/
def gmf (a b c d e f : R) (p q r : Fin 6) (u v w : Fin 6 → R) : R :=
  a * (u p * v q * w r) + b * (u p * v r * w q) + c * (u q * v p * w r)
    + d * (u q * v r * w p) + e * (u r * v p * w q) + f * (u r * v q * w p)

/-- `a` times the first-block permanent plus `lam * b` times the second-block permanent. -/
def wsq (a b lam : R) (u v w : Fin 6 → R) : R :=
  a * perm3 0 1 2 u v w + lam * (b * perm3 3 4 5 u v w)

/-- What the ten weighted squares leave behind in the first block. -/
def garbage5 (A : Matrix (Fin 6) (Fin 6) R) : R :=
  {nl.join(gb)}

/-- Five split products. -/
def extras5 (A : Matrix (Fin 6) (Fin 6) R) : R :=
  {nl.join(ex)}

/-- The ten weighted squares. -/
def wsquares (A : Matrix (Fin 6) (Fin 6) R) (lam : R) : R :=
  {nl.join(sq)}

/-- What the weighted squares leave behind in the second block. It enters with `lam ^ 2`. -/
def wrest (A : Matrix (Fin 6) (Fin 6) R) : R :=
  {nl.join(rs)}

/-- **Five split products cancel the first-block garbage.** -/
theorem garbage5_add_extras5 (A : Matrix (Fin 6) (Fin 6) R) : garbage5 A + extras5 A = 0 := by
  simp only [garbage5, extras5, gmf, perm3]
  ring

/-- **Fifteen-term identity.** -/
theorem fifteen_term_identity (A : Matrix (Fin 6) (Fin 6) R) (lam : R) :
    {L} * lam * A.permanent = wsquares A lam + {L} * extras5 A - lam ^ 2 * wrest A := by
  rw [permanent_fin_six_laplace]
  simp only [wsquares, extras5, wrest, wsq, gmf, perm3]
  ring

end Ring

section Field

variable {{K : Type*}} [Field K] [CharZero K]

/-- **Border bound for the 6 × 6 permanent.** For every nonzero `lam`, the permanent plus
`lam * wrest A / {L}` is a sum of fifteen split products. Laplace expansion uses twenty. -/
theorem permanent_sub_eq_fifteen_split (lam : K) (hlam : lam ≠ 0) :
    ∃ ts : List (Matrix (Fin 6) (Fin 6) K → K), ts.length = 15 ∧ (∀ t ∈ ts, IsSplit3 t) ∧
      ∀ A : Matrix (Fin 6) (Fin 6) K, A.permanent + lam * (wrest A / {L}) = (ts.map fun t => t A).sum := by
  refine ⟨[
      {(',' + chr(10) + '      ').join(ts)}], rfl, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with {rc} <;>
      exact isSplit3_mk _ _ _ _ _ _ (by decide) _ _
  · intro A
    have h := fifteen_term_identity A lam
    simp only [wsquares, extras5] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mk]
    have h0 : (({L} : K)) ≠ 0 := by norm_num
    field_simp
    linear_combination h

end Field

end PvsNP
"""


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('k', type=int)
    ap.add_argument('E', type=int, nargs='?', default=0)
    ap.add_argument('--tangent', type=int, default=0, help='number of tangent-type pairings (counted in E)')
    ap.add_argument('--restarts', type=int, default=10)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--protocol', default='pen,ratio', help='comma list of modes: pen, ratio, plain')
    ap.add_argument('--iters', type=int, default=600)
    ap.add_argument('--only', default='', help='comma list of pairing indices for the extra terms')
    ap.add_argument('--only-tangent', default='', help='comma list of pairing indices for T (with --only)')
    ap.add_argument('--part', default='', help='i/n: run only configurations with index = i mod n')
    ap.add_argument('--fixed', action='store_true', help='torus-fixed sub-model')
    ap.add_argument('--min-a', type=int, default=0, help='with --fixed: at least this many A-kind terms')
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--verify', action='store_true', help='exact checks of the E = 6 and E = 5 identities (k = 3)')
    ap.add_argument('--lean', action='store_true', help='print Lean 4 source for the 15-term statement')
    ap.add_argument('--syntheme', action='store_true', help='exact lower bound 5 in the matching sub-model (k = 3)')
    ap.add_argument('--count', action='store_true', help='only count configurations')
    ap.add_argument('--tol', type=float, default=1e-20, help='relative residual counted as solved')
    ap.add_argument('--quiet', action='store_true', help='print only solved configurations and the summary')
    args = ap.parse_args()

    if args.verify:
        raise SystemExit(0 if verify_exact() else 1)
    if args.lean:
        print(lean_source())
        raise SystemExit
    if args.syntheme:
        raise SystemExit(0 if syntheme_check() else 1)
    S = Setup(args.k)
    if args.list:
        for i, nm in enumerate(S.names):
            print(i, nm)
        raise SystemExit
    rng = np.random.default_rng(args.seed)
    protocol = tuple(args.protocol.split(','))
    wA = tuple([1] * args.k)
    if args.fixed and args.tangent:       # torus-fixed, A-kind terms only, with tangent-type pairings
        cfgs = [(T, tuple((i, wA) for i in ex)) for (T, ex) in S.configs(args.E - args.tangent, args.tangent)]
    elif args.fixed:
        cfgs = [((), kinds) for kinds in fixed_kind_configs(S, args.E, args.min_a, verbose=args.count)]
    elif args.only:
        cfgs = [(tuple(int(i) for i in args.only_tangent.split(',')) if args.only_tangent else (),
                 tuple(int(i) for i in args.only.split(',')))]
    else:
        cfgs = S.configs(args.E - args.tangent, args.tangent)
    if args.count:
        print(f"k={args.k} E={args.E} tangent={args.tangent} fixed={args.fixed}: {len(cfgs)} configurations")
        raise SystemExit
    if args.part:
        i0, n0 = (int(t) for t in args.part.split('/'))
        cfgs = cfgs[i0::n0]
    found, best_all = 0, np.inf
    t0 = time.time()
    for cfg in cfgs:
        if args.fixed:
            T, kinds = cfg
            model = fixed_model(S, kinds, T)
            label = ' '.join(f"{S.names[i]}:{''.join(map(str, w))}" for i, w in kinds)
            if T:
                label += " tangent [" + ' '.join(S.names[i] for i in T) + "]"
        else:
            T, extra = cfg
            model = full_model(S, extra, T)
            label = describe(S, T, extra)
        runs = run(model, S, args.restarts, rng, protocol=protocol, iters=args.iters)
        b = runs[0]
        # solved: residual at rounding level relative to the smallest |c_pi|, and no c_pi drifting to zero
        nsolved = sum(u['rel'] < args.tol and u['cmin'] > 1e-3 * u['cmax'] for u in runs)
        found += bool(nsolved)
        best_all = min(best_all, b['rel'])
        if nsolved or not args.quiet:
            tag = f"SOLVED in {nsolved}/{len(runs)} runs" if nsolved else ""
            print(f"  {label}: best rel residual {b['rel']:.2e} (min|c| {b['cmin']:.2e} max|c| {b['cmax']:.2e} "
                  f"max|factor| {b['znorm']:.1f}); all: {' '.join('%.0e' % u['rel'] for u in runs)} {tag}", flush=True)
            if nsolved and args.quiet:
                print("     c =", np.round(b['c'], 4), flush=True)
    print(f"SUMMARY k={args.k} E={args.E} tangent={args.tangent} fixed={args.fixed} protocol={protocol}: "
          f"{found} of {len(cfgs)} configurations solved; best residual {best_all:.2e}; {time.time() - t0:.0f} s", flush=True)

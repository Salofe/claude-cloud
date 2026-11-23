"""Limit decompositions of the 2k x 2k permanent by a column grading: the full model.

Give every column j an integer weight w[j]. A monomial of the tensor (one column for each
row) has weight sum_r w[column of row r]; the permanent lives in weight W = sum(w). If

    Y = sum_v F_v(rows S_v) * G_v(rows not in S_v)

has no component of weight < W and its weight-W component is the permanent, then scaling
column j by lam^w[j] and dividing by lam^W gives the permanent as lam -> 0: a limit
decomposition with as many terms as Y. Components of weight > W are free.

twoblock.py and garbage_fast.py solve the special case w = (0,..,0,1,..,1) with factors of
the form F = F1 + F2 (all rows in the first block, or all in the second). There every pairing
of the rows needs a term of its own, so N = C(2k, k) / 2 terms are forced. Here the factors are
arbitrary tensors (all mixed components allowed), so that bound does not apply: this is the
test of whether fewer terms are possible outside the two-block form.

The system "components of weight <= W match" is polynomial in the entries of F_v, G_v and is
solved by Levenberg-Marquardt with exact sparse derivatives. Real unknowns.

Usage:
  python3 fullw.py <k> <weights> <splits> [--restarts R] [--seed s] [--inj] [--exact]
     weights  comma separated, e.g. 0,0,1,1
     splits   semicolon separated list of row sets with multiplicity, e.g. "01x3;02;03"
     --inj    factors supported on injective column choices only (smaller, faster)
     --exact  match every component (an ordinary decomposition, no limit)
     --cap c  bound on the mean square of the unknowns (default 1; see lm)
"""
import argparse
import itertools
import time

import numpy as np
import scipy.linalg
import warnings

warnings.filterwarnings('ignore', category=scipy.linalg.LinAlgWarning)


def build(k, w, splits, inj, exact):
    m = 2 * k
    idx = np.array(list(itertools.product(range(m), repeat=m)), dtype=np.int64)  # (m^m, m)
    wt = np.array(w)[idx].sum(axis=1)
    W = sum(w)
    is_perm = np.array([len(set(row)) == m for row in idx])
    keep = np.ones(len(idx), dtype=bool) if exact else wt <= W
    if inj:
        # a product of injective factors never has a column used three times
        cnt = np.zeros((len(idx), m), dtype=np.int64)
        for r in range(m):
            cnt[np.arange(len(idx)), idx[:, r]] += 1
        keep &= cnt.max(axis=1) <= 2
    idx = idx[keep]
    target = is_perm[keep].astype(float)
    powers = m ** np.arange(k - 1, -1, -1)
    if inj:
        tuples = np.array(list(itertools.product(range(m), repeat=k)), dtype=np.int64)
        ok = np.array([len(set(t)) == k for t in tuples])
        compact = np.full(m ** k, -1, dtype=np.int64)
        compact[ok] = np.arange(ok.sum())
        d = int(ok.sum())
    else:
        compact = np.arange(m ** k)
        d = m ** k
    fa, ga, masks = [], [], []
    for S in splits:
        Sc = tuple(r for r in range(m) if r not in S)
        a = compact[idx[:, list(S)] @ powers]
        b = compact[idx[:, list(Sc)] @ powers]
        mk = (a >= 0) & (b >= 0)
        masks.append(mk)
        fa.append(np.where(mk, a, 0))
        ga.append(np.where(mk, b, 0))
    return dict(m=m, d=d, n=len(splits), fa=fa, ga=ga, masks=masks, target=target, neq=len(idx))


def residual(M, F, G):
    r = -M['target'].copy()
    for v in range(M['n']):
        mk = M['masks'][v]
        r[mk] += F[v][M['fa'][v][mk]] * G[v][M['ga'][v][mk]]
    return r


def normal_eqs(M, F, G, r):
    """J^T J and J^T r for the unknown order (F_0, .., F_{n-1}, G_0, .., G_{n-1})."""
    n, d = M['n'], M['d']
    N = 2 * n * d
    H = np.zeros((N, N))
    g = np.zeros(N)
    cols, vals = [], []
    for v in range(n):
        mk = M['masks'][v]
        fa, ga = M['fa'][v], M['ga'][v]
        cF = np.where(mk, fa, -1)
        vF = np.where(mk, G[v][ga], 0.0)
        cG = np.where(mk, ga, -1)
        vG = np.where(mk, F[v][fa], 0.0)
        cols.append((cF, vF))
        vals.append((cG, vG))
    blocks = [(v * d, cols[v]) for v in range(n)] + [((n + v) * d, vals[v]) for v in range(n)]
    for off, (c, x) in blocks:
        ok = c >= 0
        g[off:off + d] = np.bincount(c[ok], weights=(x * r)[ok], minlength=d)
    for i, (oi, (ci, xi)) in enumerate(blocks):
        for j in range(i, len(blocks)):
            oj, (cj, xj) = blocks[j]
            ok = (ci >= 0) & (cj >= 0)
            blk = np.bincount(ci[ok] * d + cj[ok], weights=(xi * xj)[ok], minlength=d * d).reshape(d, d)
            H[oi:oi + d, oj:oj + d] = blk
            if j > i:
                H[oj:oj + d, oi:oi + d] = blk.T
    return H, g


def lm(M, F, G, iters, cap, log=None, lam=1e-2, rho=10.0):
    """Levenberg-Marquardt with a cap on the size of the unknowns.

    The system has a scaling symmetry (the column grading itself): multiplying the weight-a
    part of every factor by s^(a - W/2) keeps the weight-W component and multiplies the
    weight-d component by s^(d - W). So from any point the lower components can be shrunk by
    running off to infinity, without ever solving the system. True solutions come in whole
    orbits and have a representative of moderate size; the penalty rho * max(0, |theta|^2 / B^2
    - 1) with B^2 = cap * (number of unknowns) blocks the escape and vanishes on them.
    """
    n, d = M['n'], M['d']
    B2 = cap * 2 * n * d

    def penalty(F, G):
        t2 = (F * F).sum() + (G * G).sum()
        return rho * max(0.0, t2 / B2 - 1.0)

    r = residual(M, F, G)
    pen = penalty(F, G)
    loss = r @ r + pen * pen
    hist = [loss]
    for it in range(iters):
        H, g = normal_eqs(M, F, G, r)
        if pen > 0:
            gp = rho * 2 * np.concatenate([F.ravel(), G.ravel()]) / B2
            H += np.outer(gp, gp)
            g += gp * pen
        dg = np.maximum(np.diag(H), 1e-12 * np.trace(H) / len(g))
        ok = False
        for _ in range(30):
            A = H.copy()
            A[np.diag_indices_from(A)] += lam * dg
            try:
                step = scipy.linalg.solve(A, -g, assume_a='pos', check_finite=False)
            except (np.linalg.LinAlgError, scipy.linalg.LinAlgError):
                lam *= 10
                continue
            F2 = F + step[:n * d].reshape(n, d)
            G2 = G + step[n * d:].reshape(n, d)
            r2 = residual(M, F2, G2)
            p2 = penalty(F2, G2)
            l2 = r2 @ r2 + p2 * p2
            if np.isfinite(l2) and l2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            break
        F, G, r, pen, loss = F2, G2, r2, p2, l2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-14)
        hist.append(loss)
        if log and (it < 5 or it % 10 == 0):
            log(f"      it {it:4d} loss {loss:.3e} rms entry {np.sqrt(((F * F).sum() + (G * G).sum()) / (2 * n * d)):.2f} lam {lam:.1e}")
        if loss < 1e-24 or (len(hist) > 60 and hist[-60] / loss < 1.05):
            break
    return F, G, loss


def parse_splits(s, k):
    out = []
    for part in s.split(';'):
        part = part.strip()
        if not part:
            continue
        if 'x' in part:
            rows, mult = part.split('x')
        else:
            rows, mult = part, '1'
        S = tuple(int(c) for c in rows)
        assert len(S) == k
        out += [S] * int(mult)
    return out


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('k', type=int)
    ap.add_argument('weights')
    ap.add_argument('splits')
    ap.add_argument('--restarts', type=int, default=4)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--iters', type=int, default=400)
    ap.add_argument('--inj', action='store_true')
    ap.add_argument('--cap', type=float, default=1.0, help='bound on the mean square of the unknowns')
    ap.add_argument('--exact', action='store_true')
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args()
    k = args.k
    w = [int(x) for x in args.weights.split(',')]
    assert len(w) == 2 * k
    splits = parse_splits(args.splits, k)
    M = build(k, w, splits, args.inj, args.exact)
    rng = np.random.default_rng(args.seed)
    norm2 = float(M['target'] @ M['target'])
    print(f"k={k} weights={w} terms={M['n']} equations={M['neq']} unknowns={2 * M['n'] * M['d']} "
          f"{'exact' if args.exact else 'limit'} model{' (injective factors)' if args.inj else ''}", flush=True)
    best, hits = np.inf, 0
    for trial in range(args.restarts):
        t0 = time.time()
        F = rng.standard_normal((M['n'], M['d'])) * 0.5
        G = rng.standard_normal((M['n'], M['d'])) * 0.5
        F, G, loss = lm(M, F, G, args.iters, args.cap, log=(lambda s: print(s, flush=True)) if args.verbose else None)
        rel = loss / norm2
        best = min(best, rel)
        hits += rel < 1e-20
        print(f"  trial {trial}: relative residual {rel:.3e}  max|factor entry| {max(np.abs(F).max(), np.abs(G).max()):.1f}"
              f"  ({time.time() - t0:.0f} s)", flush=True)
    print(f"SUMMARY k={k} w={w} splits={args.splits} terms={M['n']}: {hits}/{args.restarts} solved, "
          f"best residual {best:.3e}", flush=True)

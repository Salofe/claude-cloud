"""Searches for limit decompositions of the 2k x 2k permanent outside the two-block form.

Same graded system as fullw.py (read its docstring first): columns carry integer weights w,
the tensor Y = sum_v F_v(rows S_v) G_v(rows not in S_v) must have no component of weight
< W = sum(w) and weight-W component equal to the permanent. What is new here:

  * a sparse builder in which every factor of every term can be restricted to a set of
    "column classes" (the set of columns a monomial of the factor uses). With no restriction
    this is the full model of fullw.py; with every factor restricted to the two classes
    {first block}, {second block} it is the two-block model; in between are the sub-models
    homogeneous for a subtorus of the column torus (see CLASSES below);
  * weights on the equations (mu multiplies the squared residual of the components of weight
    < W) and several start strategies, to fight the scaling escape described in fullw.lm;
  * a term-deletion local search from a known solution.

A factor F on the rows S is stored as a vector indexed by the injective maps S -> columns
(option inj=False: all maps). Its class components are F_alpha, alpha a k-set of columns.

Usage (examples; every run prints one SUMMARY line):
  python3 fullw_search.py recover --starts 6 --strategy near2b
  python3 fullw_search.py run 0,0,0,1,1,1 "012;013;014;015;023;024;025;034;035;045;012x2;013x2;024" --starts 4
  python3 fullw_search.py delete --starts 1
"""
import argparse
import itertools
import time
import warnings

import numpy as np
import scipy.linalg
import scipy.sparse as sp

warnings.filterwarnings('ignore', category=scipy.linalg.LinAlgWarning)


class Model:
    """terms: list of (S, allowF, allowG); S a k-tuple of rows; allowF / allowG either None
    (every class) or a collection of frozensets of columns the factor may use."""

    def __init__(self, k, w, terms, exact=False, inj=True, mu=1.0):
        m = 2 * k
        self.k, self.m, self.w = k, m, list(w)
        idx = np.array(list(itertools.product(range(m), repeat=m)), dtype=np.int64)
        wt = np.array(w)[idx].sum(axis=1)
        W = sum(w)
        is_perm = np.array([len(set(row)) == m for row in idx])
        keep = np.ones(len(idx), dtype=bool) if exact else wt <= W
        if inj:
            cnt = np.zeros((len(idx), m), dtype=np.int64)
            for r in range(m):
                cnt[np.arange(len(idx)), idx[:, r]] += 1
            keep &= cnt.max(axis=1) <= 2
        idx, wt = idx[keep], wt[keep]
        target = is_perm[keep].astype(float)
        low = wt < W
        sw = np.where(low, np.sqrt(mu), 1.0)
        powers = m ** np.arange(k - 1, -1, -1)
        tuples = list(itertools.product(range(m), repeat=k))
        base_ok = np.array([(len(set(t)) == k) or not inj for t in tuples])
        tsets = [frozenset(t) for t in tuples]
        self.tuples = tuples

        def table(allow):
            ok = base_ok.copy()
            if allow is not None:
                allow = set(allow)
                ok &= np.array([s in allow for s in tsets])
            comp = np.full(len(tuples), -1, dtype=np.int64)
            comp[ok] = np.arange(ok.sum())
            return comp, int(ok.sum()), np.nonzero(ok)[0]

        self.terms = [(tuple(S), aF, aG) for S, aF, aG in terms]
        self.n = len(terms)
        self.offF, self.offG, self.codesF, self.codesG = [], [], [], []
        rows, ia, ib = [], [], []
        off = 0
        for S, aF, aG in self.terms:
            Sc = tuple(r for r in range(m) if r not in S)
            cF, dF, lF = table(aF)
            cG, dG, lG = table(aG)
            a = cF[idx[:, list(S)] @ powers]
            b = cG[idx[:, list(Sc)] @ powers]
            rw = np.nonzero((a >= 0) & (b >= 0))[0]
            self.offF.append((off, dF))
            self.offG.append((off + dF, dG))
            self.codesF.append(lF)
            self.codesG.append(lG)
            rows.append(rw)
            ia.append(a[rw] + off)
            ib.append(b[rw] + off + dF)
            off += dF + dG
        self.nu = off
        # drop the equations no term touches (their residual is constant)
        touched = np.zeros(len(idx), dtype=bool)
        for rw in rows:
            touched[rw] = True
        self.const = float((target[~touched] ** 2).sum())   # unreachable part of the permanent
        newrow = np.cumsum(touched) - 1
        self.rows = [newrow[rw] for rw in rows]
        self.ia, self.ib = ia, ib
        self.target = target[touched]
        self.sw = sw[touched]
        self.low = low[touched]
        self.neq = int(touched.sum())
        self.norm2 = float(target @ target)
        R = np.concatenate([np.concatenate([rw, rw]) for rw in self.rows])
        C = np.concatenate([np.concatenate([a, b]) for a, b in zip(ia, ib)])
        nnz = len(R)
        pat = sp.coo_matrix((np.arange(1, nnz + 1, dtype=np.float64), (R, C)), shape=(self.neq, self.nu)).tocsr()
        self._pat = pat
        self._perm = pat.data.astype(np.int64) - 1
        self._swR = self.sw[R]
        self._allrows = np.concatenate(self.rows)
        self._allia = np.concatenate(ia)
        self._allib = np.concatenate(ib)

    def raw(self, x):
        p = x[self._allia] * x[self._allib]
        if np.iscomplexobj(p):
            r = (np.bincount(self._allrows, weights=p.real, minlength=self.neq)
                 + 1j * np.bincount(self._allrows, weights=p.imag, minlength=self.neq))
        else:
            r = np.bincount(self._allrows, weights=p, minlength=self.neq)
        return r - self.target

    def residual(self, x):
        return self.raw(x) * self.sw

    def split_loss(self, x):
        """(squared residual of the weight-W equations, of the lower weights), unweighted."""
        r = np.abs(self.raw(x)) ** 2
        return float(r[~self.low].sum()) + self.const, float(r[self.low].sum())

    def jac(self, x):
        vals = []
        for a, b in zip(self.ia, self.ib):
            vals.append(x[b])
            vals.append(x[a])
        v = np.concatenate(vals) * self._swR
        return sp.csr_matrix((v[self._perm], self._pat.indices, self._pat.indptr), shape=self._pat.shape)

    def term_norms(self, x):
        out = []
        for (oF, dF), (oG, dG) in zip(self.offF, self.offG):
            out.append(np.linalg.norm(x[oF:oF + dF]) * np.linalg.norm(x[oG:oG + dG]))
        return np.array(out)

    def balance(self, x):
        """Rescale every term so that |F_v| = |G_v| (a symmetry of the system)."""
        x = x.copy()
        for (oF, dF), (oG, dG) in zip(self.offF, self.offG):
            nf, ng = np.linalg.norm(x[oF:oF + dF]), np.linalg.norm(x[oG:oG + dG])
            if nf > 0 and ng > 0:
                s = np.sqrt(ng / nf)
                x[oF:oF + dF] *= s
                x[oG:oG + dG] /= s
        return x


def lm(M, x, iters=300, cap=4.0, lam=1e-2, rho=10.0, log=None, tol=1e-24, patience=60, ridge=None):
    """Levenberg-Marquardt on M with the size cap of fullw.lm. Returns (x, weighted loss).
    ridge: optional vector of weights; adds sum_i ridge_i |x_i|^2 to the loss (used to push
    chosen terms to zero continuously: the term-deletion local search)."""
    B2 = cap * M.nu

    def penalty(x):
        return rho * max(0.0, np.vdot(x, x).real / B2 - 1.0)

    def sq(r):
        return np.vdot(r, r).real

    def rdg(x):
        return 0.0 if ridge is None else float((ridge * np.abs(x) ** 2).sum())

    r = M.residual(x)
    pen = penalty(x)
    loss = sq(r) + pen * pen + rdg(x)
    hist = [loss]
    for it in range(iters):
        J = M.jac(x)
        JH = J.conj().T.tocsr()
        H = (JH @ J).toarray()
        g = JH @ r
        if pen > 0:
            # real unknowns: exact Gauss-Newton term of the penalty; complex: exact gradient,
            # positive semidefinite approximation of its Hessian
            gp = rho * 2 * x / B2
            H += np.outer(gp, gp.conj())
            g = g + gp * pen
        if ridge is not None:
            H[np.diag_indices_from(H)] += ridge
            g = g + ridge * x
        dg = np.maximum(np.diag(H).real, 1e-12 * np.trace(H).real / len(g))
        ok = False
        for _ in range(30):
            A = H.copy()
            A[np.diag_indices_from(A)] += lam * dg
            try:
                step = scipy.linalg.solve(A, -g, assume_a='pos', check_finite=False)
            except (np.linalg.LinAlgError, scipy.linalg.LinAlgError):
                lam *= 10
                continue
            x2 = x + step
            r2 = M.residual(x2)
            p2 = penalty(x2)
            l2 = sq(r2) + p2 * p2 + rdg(x2)
            if np.isfinite(l2) and l2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            break
        x, r, pen, loss = x2, r2, p2, l2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-14)
        hist.append(loss)
        if log and (it < 3 or it % 10 == 0):
            log(f"      it {it:4d} loss {loss:.3e} rms {np.sqrt(sq(x) / M.nu):.2f} lam {lam:.1e}")
        if loss < tol or (len(hist) > patience and hist[-patience] / loss < 1.05):
            break
    return x, loss


def parse_splits(s, k):
    out = []
    for part in s.split(';'):
        part = part.strip()
        if not part:
            continue
        rows, mult = part.split('x') if 'x' in part else (part, '1')
        S = tuple(int(c) for c in rows)
        assert len(S) == k
        out += [S] * int(mult)
    return out


# ----------------------------------------------------------------------- the known 15 terms
PAIRS3 = [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5), (0, 2, 3), (0, 2, 4), (0, 2, 5), (0, 3, 4), (0, 3, 5), (0, 4, 5)]
SPLITS15 = PAIRS3 + [(0, 1, 2), (0, 1, 2), (0, 1, 3), (0, 1, 3), (0, 2, 4)]
C15 = [3, -15, 3, 9, -18, -6, 6, -18, 6, 30]
EXTRA15 = [(-2, [3, 3, -1, -2, -1, -2], [9, 6, 3, -3, -6, -9]), (-2, [-1, -2, 3, 3, -2, -1], [3, -3, 9, 6, -9, -6]),
           (-2, [5, 5, -7, 2, -7, 2], [2, 1, 1, -1, -1, -2]), (-2, [-7, 2, 5, 5, 2, -7], [1, -1, 2, 1, -2, -1]),
           (12, [1, -1, -1, 1, 1, -1], [1, -1, -1, 1, 1, -1])]


def known15(M):
    """The 15-term identity of garbage_fast.py written in the unknowns of M (a 6 x 6 model with
    weights (0,0,0,1,1,1), injective factors, terms SPLITS15, every class allowed)."""
    def gmf(codes, coef, cols):
        pos = {M.tuples[c]: i for i, c in enumerate(codes)}
        v = np.zeros(len(codes))
        p, q, r = cols
        for cf, t in zip(coef, [(p, q, r), (p, r, q), (q, p, r), (q, r, p), (r, p, q), (r, q, p)]):
            v[pos[t]] += cf
        return v
    x = np.zeros(M.nu)
    one = [1] * 6
    for v in range(15):
        (oF, dF), (oG, dG) = M.offF[v], M.offG[v]
        cF, cG = M.codesF[v], M.codesG[v]
        if v < 10:
            cc = C15[v]
            s = abs(cc) ** 0.5
            F = (cc * gmf(cF, one, (0, 1, 2)) + gmf(cF, one, (3, 4, 5))) / s
            G = (gmf(cG, one, (0, 1, 2)) + gmf(cG, one, (3, 4, 5)) / cc) * s
        else:
            co, a, b = EXTRA15[v - 10]
            fa, gb = gmf(cF, a, (0, 1, 2)), gmf(cG, b, (0, 1, 2))
            s = (np.linalg.norm(gb) / (abs(co) * np.linalg.norm(fa))) ** 0.5
            F, G = co * fa * s, gb / s
        x[oF:oF + dF] = F
        x[oG:oG + dG] = G
    return x


def two_block_classes(k):
    return [frozenset(range(k)), frozenset(range(k, 2 * k))]


def solve(M, x0, iters, cap, stages=(1.0,), log=None, ridge=None):
    """LM, optionally in stages with decreasing weight mu on the lower components.
    Returns x, relative residual (unweighted, all equations), rms entry."""
    x = x0
    for mu in stages:
        M.sw = np.where(M.low, np.sqrt(mu), 1.0)
        R = np.concatenate([np.concatenate([rw, rw]) for rw in M.rows])
        M._swR = M.sw[R]
        x, _ = lm(M, x, iters=iters, cap=cap, log=log, ridge=ridge)
    a, b = M.split_loss(x)
    return x, (a + b) / M.norm2, a / M.norm2, b / M.norm2, float(np.sqrt(np.vdot(x, x).real / M.nu))


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['run', 'recover', 'delete'])
    ap.add_argument('weights', nargs='?', default='0,0,0,1,1,1')
    ap.add_argument('splits', nargs='?', default='')
    ap.add_argument('--k', type=int, default=3)
    ap.add_argument('--starts', type=int, default=4)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--iters', type=int, default=300)
    ap.add_argument('--cap', type=float, default=4.0)
    ap.add_argument('--full', action='store_true', help='all column maps in the factors (default: injective)')
    ap.add_argument('--exact', action='store_true')
    ap.add_argument('--scale', type=float, default=0.5, help='standard deviation of the random start')
    ap.add_argument('--stages', default='1', help='comma separated weights mu on the lower components, in order')
    ap.add_argument('--strategy', default='random',
                    help='random | near2b:<eps> (random two-block point plus noise eps) | known:<eps>')
    ap.add_argument('--drop', default='', help='delete mode: comma separated term indices to delete')
    ap.add_argument('--verbose', action='store_true')
    args = ap.parse_args()
    k = args.k
    w = [int(c) for c in args.weights.split(',')]
    stages = [float(s) for s in args.stages.split(',')]
    rng = np.random.default_rng(args.seed)
    log = (lambda s: print(s, flush=True)) if args.verbose else None
    if args.mode == 'run':
        splits = parse_splits(args.splits, k)
    else:
        splits = list(SPLITS15)
    if args.mode == 'delete':
        drop = [int(c) for c in args.drop.split(',')] if args.drop else []
    M = Model(k, w, [(S, None, None) for S in splits], exact=args.exact, inj=not args.full)
    print(f"k={k} w={w} terms={M.n} equations={M.neq} unknowns={M.nu} {'exact' if args.exact else 'limit'} "
          f"{'full' if args.full else 'injective'} factors, strategy {args.strategy}, stages {stages}, cap {args.cap}", flush=True)
    kind, _, eps = args.strategy.partition(':')
    eps = float(eps) if eps else 0.1
    hits, best = 0, np.inf
    for trial in range(args.starts):
        t0 = time.time()
        if kind == 'random':
            x0 = rng.standard_normal(M.nu) * args.scale
        elif kind == 'near2b':
            # a random point of the two-block sub-model plus noise in all other components
            M2 = Model(k, w, [(S, two_block_classes(k), two_block_classes(k)) for S in splits], inj=not args.full)
            x0 = rng.standard_normal(M.nu) * eps
            for v in range(M.n):
                for (o, d), (o2, d2), cod, cod2 in ((M.offF[v], M2.offF[v], M.codesF[v], M2.codesF[v]),
                                                    (M.offG[v], M2.offG[v], M.codesG[v], M2.codesG[v])):
                    pos = {c: i for i, c in enumerate(cod)}
                    sel = np.array([pos[c] for c in cod2])
                    x0[o + sel] = rng.standard_normal(d2) * args.scale
        elif kind == 'known':
            x0 = known15(M) + eps * rng.standard_normal(M.nu)
        else:
            raise SystemExit('unknown strategy')
        x, rel, relW, rellow, rms = solve(M, x0, args.iters, args.cap, stages, log)
        best = min(best, rel)
        hits += rel < 1e-18
        print(f"  start {trial}: rel residual {rel:.3e} (weight W {relW:.1e}, lower {rellow:.1e}) rms entry {rms:.2f} "
              f"max {np.abs(x).max():.1f}  ({time.time() - t0:.0f} s)", flush=True)
    print(f"SUMMARY {args.mode} w={w} terms={M.n} splits={args.splits or 'SPLITS15'} strategy={args.strategy} stages={stages} "
          f"cap={args.cap}: {hits}/{args.starts} solved, best rel residual {best:.3e}", flush=True)

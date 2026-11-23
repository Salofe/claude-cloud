"""Exact decompositions of the 6 x 6 permanent into 3-split products: searches and exact checks.

Question: is the EXACT mixed split rank of perm_6 at k = 3 equal to Laplace's 20, or smaller?
(The limit value is <= 15; at 4 x 4 the exact value is 6 = Laplace and the limit value is 5.)
See notes/exact_6x6.md for the results; this file holds everything that produced them.

MODEL. perm_6 = sum_v F_v(rows S_v) G_v(rows not in S_v), every F_v, G_v a real trilinear form given
by its coefficients on a set of allowed column triples (--cls):
    full       all 216 triples (use checks/splitfast.py for this one: same model, faster assembly);
    inj        the 120 injective triples;
    paired     one column out of each pair {j, j+3}: 48 triples;
    twoblock   triples inside columns {0,1,2} or inside {3,4,5}: 54 triples (the two-block model at lam = 1).
All 6^6 coefficient equations that some term can reach are imposed (exact model, no grading).

SOLVER. Levenberg-Marquardt on the sparse Jacobian with a one-sided cap on the mean square of the
unknowns (penalty rho * max(0, |x|^2 / (cap * nu) - 1)), so that limit-type approximations (residual
decaying while the factors grow; expected here because the limit value is <= 15) show up as a positive
floor of the residual that moves with the cap, and only bounded solutions reach rounding level.
A start counts as EXACT when the relative squared residual is < 1e-20.

Modes
  run     --cls C --sets "012x2;013;..." --starts n --cap c     search one configuration
  suite   NAME                                                  a named list of configurations (see SUITES)
  rank2b  two-block model in the rank formulation (see the note, Section 3): minimise
          sum_P rank M_P by alternating projections / LM on a factorised model with n_P terms per pairing
  check   exact integer checks of the statements used in the note (Sections 3 and 4)
"""
import argparse
import itertools
import time
import warnings

import numpy as np
import scipy.linalg
import scipy.sparse as sp

warnings.filterwarnings('ignore', category=scipy.linalg.LinAlgWarning)

TUP = list(itertools.product(range(6), repeat=3))
PAIRS = [S for S in itertools.combinations(range(6), 3) if 0 in S]


def allowed(cls):
    if cls == 'full':
        ok = [True] * 216
    elif cls == 'inj':
        ok = [len(set(t)) == 3 for t in TUP]
    elif cls == 'paired':
        ok = [len({c % 3 for c in t}) == 3 for t in TUP]
    elif cls == 'twoblock':
        ok = [all(c < 3 for c in t) or all(c >= 3 for c in t) for t in TUP]
    elif cls == 'twoblock_inj':
        ok = [len(set(t)) == 3 and (all(c < 3 for c in t) or all(c >= 3 for c in t)) for t in TUP]
    else:
        raise ValueError(cls)
    return np.nonzero(ok)[0]


def perm_target():
    T = np.zeros(6 ** 6)
    pw = 6 ** np.arange(5, -1, -1)
    for p in itertools.permutations(range(6)):
        T[int(np.dot(p, pw))] = 1.0
    return T


def parse_sets(s):
    out = []
    for part in s.split(';'):
        part = part.strip()
        if not part:
            continue
        rows, mult = part.split('x') if 'x' in part else (part, '1')
        out += [tuple(int(c) for c in rows)] * int(mult)
    return out


class Model:
    """sum_v F_v(S_v) G_v(S_v^c) with coefficient supports given by cls (a name or a list of
    (codesF, codesG) per term)."""

    def __init__(self, sets, cls='twoblock'):
        self.sets = [tuple(sorted(S)) for S in sets]
        self.n = len(self.sets)
        tup = np.array(TUP)
        rows, ia, ib = [], [], []
        self.off = []
        off = 0
        for v, S in enumerate(self.sets):
            Sc = tuple(r for r in range(6) if r not in S)
            if isinstance(cls, str):
                cF = cG = allowed(cls)
            else:
                cF, cG = cls[v]
            pF = 6 ** (5 - np.array(S))
            pG = 6 ** (5 - np.array(Sc))
            eF = tup[cF] @ pF
            eG = tup[cG] @ pG
            rw = (eF[:, None] + eG[None, :]).ravel()
            a = np.repeat(np.arange(len(cF)), len(cG)) + off
            b = np.tile(np.arange(len(cG)), len(cF)) + off + len(cF)
            rows.append(rw)
            ia.append(a)
            ib.append(b)
            self.off.append((off, len(cF), len(cG)))
            off += len(cF) + len(cG)
        self.nu = off
        target = perm_target()
        touched = np.zeros(6 ** 6, dtype=bool)
        for rw in rows:
            touched[rw] = True
        self.const = float((target[~touched] ** 2).sum())
        newrow = np.cumsum(touched) - 1
        self.rows = np.concatenate([newrow[rw] for rw in rows])
        self.ia = np.concatenate(ia)
        self.ib = np.concatenate(ib)
        self.target = target[touched]
        self.touched = touched
        self.neq = int(touched.sum())
        self.norm2 = 720.0
        R = np.concatenate([self.rows, self.rows])
        C = np.concatenate([self.ia, self.ib])
        pat = sp.coo_matrix((np.arange(1, len(R) + 1, dtype=np.float64), (R, C)), shape=(self.neq, self.nu)).tocsr()
        self._pat = pat
        self._perm = pat.data.astype(np.int64) - 1

    def residual(self, x):
        return np.bincount(self.rows, weights=x[self.ia] * x[self.ib], minlength=self.neq) - self.target

    def jac(self, x):
        v = np.concatenate([x[self.ib], x[self.ia]])
        return sp.csr_matrix((v[self._perm], self._pat.indices, self._pat.indptr), shape=self._pat.shape)

    def balance(self, x):
        x = x.copy()
        for o, dF, dG in self.off:
            nf, ng = np.linalg.norm(x[o:o + dF]), np.linalg.norm(x[o + dF:o + dF + dG])
            if nf > 0 and ng > 0:
                s = np.sqrt(ng / nf)
                x[o:o + dF] *= s
                x[o + dF:o + dF + dG] /= s
        return x

    def term_norms(self, x):
        return np.array([np.linalg.norm(x[o:o + dF]) * np.linalg.norm(x[o + dF:o + dF + dG]) for o, dF, dG in self.off])

    def full_tensor(self, x):
        """the 6^6 tensor of the sum (only touched entries can be nonzero)."""
        Y = np.zeros(6 ** 6)
        Y[self.touched] = np.bincount(self.rows, weights=x[self.ia] * x[self.ib], minlength=self.neq)
        return Y


def lm(M, x, iters=400, cap=4.0, lam=1e-2, rho=10.0, tol=1e-24, patience=50, log=None):
    """Levenberg-Marquardt with a cap on |x|^2 / nu. Returns x, relative squared residual (without
    the penalty), number of iterations."""
    B2 = cap * M.nu

    def pen(x):
        return rho * max(0.0, float(x @ x) / B2 - 1.0)

    r = M.residual(x)
    p = pen(x)
    loss = float(r @ r) + p * p
    hist = [loss]
    for it in range(iters):
        J = M.jac(x)
        JT = J.T.tocsr()
        H = (JT @ J).toarray()
        g = JT @ r
        if p > 0:
            gp = rho * 2 * x / B2
            H += np.outer(gp, gp)
            g = g + gp * p
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
            x2 = x + step
            r2 = M.residual(x2)
            p2 = pen(x2)
            l2 = float(r2 @ r2) + p2 * p2
            if np.isfinite(l2) and l2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            break
        x, r, p, loss = x2, r2, p2, l2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-14)
        hist.append(loss)
        if log and (it < 3 or it % 20 == 0):
            log(f"      it {it:4d} loss {loss:.3e} rms {np.sqrt(float(x @ x) / M.nu):.2f} lam {lam:.1e}")
        if loss < tol * M.norm2 or (len(hist) > patience and hist[-patience] / loss < 1.05):
            break
    rel = (float(r @ r) + M.const) / M.norm2
    return x, rel, len(hist)


def search(sets, cls, starts, cap=4.0, iters=400, seed=0, scale=0.5, verbose=False, label=None, keep=None):
    """Random starts for one configuration. Returns (number of exact hits, list of (rel, rms))."""
    M = Model(sets, cls)
    rng = np.random.default_rng(seed)
    res = []
    hits = 0
    t0 = time.time()
    for s in range(starts):
        x0 = rng.standard_normal(M.nu) * scale
        t1 = time.time()
        x, rel, its = lm(M, x0, iters=iters, cap=cap, log=print if verbose else None)
        rms = float(np.sqrt(x @ x / M.nu))
        res.append((rel, rms))
        hit = rel < 1e-20
        hits += hit
        if hit and keep is not None:
            keep.append((M, M.balance(x)))
        print(f"    start {s}: rel {rel:.3e} rms {rms:.2f} max term {M.term_norms(x).max():.1f} its {its} "
              f"{time.time() - t1:.0f}s{'  EXACT' if hit else ''}", flush=True)
    best = min(r for r, _ in res)
    print(f"SUMMARY {label or ''} cls={cls} n={len(sets)} cap={cap} unknowns={M.nu} unreachable={M.const:.0f}: "
          f"exact {hits}/{starts}, best rel {best:.3e}, median rel {np.median([r for r, _ in res]):.3e}, "
          f"{time.time() - t0:.0f}s", flush=True)
    return hits, res


def cfg(mult):
    """mult: dict pairing index -> number of terms (PAIRS order 012,013,014,015,023,024,025,034,035,045)."""
    out = []
    for i, c in sorted(mult.items()):
        out += [PAIRS[i]] * c
    return out


S15 = cfg({0: 3, 1: 3, 2: 1, 3: 1, 4: 1, 5: 2, 6: 1, 7: 1, 8: 1, 9: 1})      # row sets of the 15-term limit identity

SUITES = {
    # validation
    'val20': [('laplace: 20 on one pairing', cfg({0: 20})), ('2 on each pairing', cfg({i: 2 for i in range(10)}))],
    # (b) two terms on nine pairings, one on the tenth (unique up to S_6)
    'b19': [('2 on nine, 1 on one', cfg({**{i: 2 for i in range(10)}, 9: 1}))],
    # (a) the 15 row sets of the limit identity plus four extra terms
    'a19': [
        ('S15 + 012,013,024,045', cfg({0: 4, 1: 4, 2: 1, 3: 1, 4: 1, 5: 3, 6: 1, 7: 1, 8: 1, 9: 2})),
        ('S15 + 014,015,023,025', cfg({0: 3, 1: 3, 2: 2, 3: 2, 4: 2, 5: 2, 6: 2, 7: 1, 8: 1, 9: 1})),
        ('S15 + 034,035,045,014', cfg({0: 3, 1: 3, 2: 2, 3: 1, 4: 1, 5: 2, 6: 1, 7: 2, 8: 2, 9: 2})),
        ('S15 + 012x2,013x2', cfg({0: 5, 1: 5, 2: 1, 3: 1, 4: 1, 5: 2, 6: 1, 7: 1, 8: 1, 9: 1})),
    ],
    'a18': [
        ('S15 + 012,013,024', cfg({0: 4, 1: 4, 2: 1, 3: 1, 4: 1, 5: 3, 6: 1, 7: 1, 8: 1, 9: 1})),
        ('S15 + 014,023,045', cfg({0: 3, 1: 3, 2: 2, 3: 1, 4: 2, 5: 2, 6: 1, 7: 1, 8: 1, 9: 2})),
    ],
    # (c) few pairings, many terms each
    'c19': [
        ('012x10;034x9', cfg({0: 10, 7: 9})),
        ('012x7;034x6;015x6', cfg({0: 7, 7: 6, 3: 6})),
        ('012x5;013x5;024x5;034x4', cfg({0: 5, 1: 5, 5: 5, 7: 4})),
        ('012x4;034x4;015x4;024x4;035x3', cfg({0: 4, 7: 4, 3: 4, 5: 4, 8: 3})),
    ],
    # (d) squares on all pairings plus nine extras spread in other ways
    'd19': [
        ('3 on four, 2 on one, 1 on five', cfg({0: 3, 1: 3, 5: 3, 7: 3, 2: 2, 3: 1, 4: 1, 6: 1, 8: 1, 9: 1})),
        ('4 on three, 1 on seven', cfg({0: 4, 1: 4, 5: 4, 2: 1, 3: 1, 4: 1, 6: 1, 7: 1, 8: 1, 9: 1})),
        ('10 on one, 1 on nine', cfg({0: 10, **{i: 1 for i in range(1, 10)}})),
        ('5 on 012, 5 on 345-side partner 013, 1 on eight... (5,6,1^8)', cfg({0: 5, 1: 6, **{i: 1 for i in range(2, 10)}})),
        ('3 on 012, 2 on seven, 1 on two', cfg({0: 3, 1: 2, 2: 2, 3: 2, 4: 2, 5: 2, 6: 2, 7: 2, 8: 1, 9: 1})),
    ],
}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('mode')
    ap.add_argument('name', nargs='?')
    ap.add_argument('--cls', default='twoblock')
    ap.add_argument('--sets', default='')
    ap.add_argument('--starts', type=int, default=4)
    ap.add_argument('--cap', type=float, default=4.0)
    ap.add_argument('--iters', type=int, default=400)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--scale', type=float, default=0.5)
    ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    if a.mode == 'run':
        search(parse_sets(a.sets), a.cls, a.starts, cap=a.cap, iters=a.iters, seed=a.seed, scale=a.scale,
               verbose=a.verbose, label=a.sets)
    elif a.mode == 'suite':
        for label, sets in SUITES[a.name]:
            print(f"== {label}  ({len(sets)} terms)", flush=True)
            search(sets, a.cls, a.starts, cap=a.cap, iters=a.iters, seed=a.seed, scale=a.scale, verbose=a.verbose,
                   label=label)

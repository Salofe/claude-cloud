"""Split rank of the permanent tensor: a small-case probe of a lower-bound question.

View perm_m as a tensor in (C^m)^{(x) m}: entry (j_1, .., j_m) is 1 when row r picks column j_r
and the picks form a permutation. A "k-split term" chooses a set R of k rows and is a product
F(rows in R) * G(rows not in R) of two arbitrary tensors. Laplace expansion along a fixed R
writes perm_m with C(m, k) such terms, all using the same R.

Question: can terms with *different* row sets R do it with fewer than C(m, k)?

Why it matters: layer k of any branching program for the permanent whose vertices are
multilinear in the rows (in any order, mixing orders freely) is exactly such a decomposition.
If mixing never helps, those programs need C(m, m/2) vertices in the middle layer, which is
exponential. If mixing helps, that route to a lower bound is closed.

Each configuration is fitted by Levenberg-Marquardt from random complex starts; a residual at
rounding level is a decomposition found numerically, a residual that stalls on every restart
is evidence (not proof) that none exists.
"""
import argparse
import itertools
import json

import numpy as np


def perm_tensor(m):
    T = np.zeros((m,) * m)
    for p in itertools.permutations(range(m)):
        T[p] = 1
    return T


def crandn(rng, *shape):
    return (rng.standard_normal(shape) + 1j * rng.standard_normal(shape)) / np.sqrt(2)


class Split:
    """sum_v F_v (axes R_v) * G_v (other axes)."""

    def __init__(self, m, row_sets, rng):
        self.m = m
        self.R = [tuple(sorted(r)) for r in row_sets]
        self.Rc = [tuple(i for i in range(m) if i not in r) for r in self.R]
        self.F = [crandn(rng, *(m,) * len(r)) * 0.7 for r in self.R]
        self.G = [crandn(rng, *(m,) * len(rc)) * 0.7 for rc in self.Rc]

    def get(self):
        return np.concatenate([a.ravel() for a in self.F + self.G])

    def set(self, theta):
        i = 0
        for lst in (self.F, self.G):
            for j, a in enumerate(lst):
                lst[j] = theta[i:i + a.size].reshape(a.shape)
                i += a.size

    def _place(self, r, rc, f, g):
        """Outer product f (x) g with f on axes r and g on axes rc, returned with axes in order."""
        t = np.multiply.outer(f, g)
        return np.transpose(t, np.argsort(r + rc))

    def value(self):
        out = 0
        for r, rc, f, g in zip(self.R, self.Rc, self.F, self.G):
            out = out + self._place(r, rc, f, g)
        return out.ravel()

    def jac(self):
        m, n = self.m, self.m ** self.m
        cols = []
        eye = {}
        for block in (0, 1):
            for r, rc, f, g in zip(self.R, self.Rc, self.F, self.G):
                a = f if block == 0 else g
                d = a.size
                if d not in eye:
                    eye[d] = np.eye(d).reshape((d,) + a.shape)
                E = eye[d]  # (d, *a.shape): basis of the varied factor
                if block == 0:
                    t = np.multiply.outer(E, g)  # (d, *f.shape, *g.shape)
                else:
                    t = np.moveaxis(np.multiply.outer(f, E), len(r), 0)  # (d, *f.shape, *g.shape)
                perm_axes = [0] + [1 + i for i in np.argsort(r + rc)]
                cols.append(np.transpose(t, perm_axes).reshape(d, n).T)
        return np.concatenate(cols, axis=1)


def lm(model, y, iters=400, tol=1e-26, lam=1e-2):
    ynorm = float(y @ y)
    theta = model.get()
    r = model.value() - y
    loss = np.vdot(r, r).real / ynorm
    hist = [loss]
    for it in range(iters):
        J = model.jac()
        H = J.conj().T @ J
        g = J.conj().T @ r
        dg = np.maximum(np.diag(H).real, 1e-12 * np.trace(H).real / len(g))
        ok = False
        for _ in range(30):
            try:
                step = np.linalg.solve(H + lam * np.diag(dg), -g)
            except np.linalg.LinAlgError:
                lam *= 10
                continue
            model.set(theta + step)
            r2 = model.value() - y
            loss2 = np.vdot(r2, r2).real / ynorm
            if np.isfinite(loss2) and loss2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            model.set(theta)
            break
        theta, r, loss = theta + step, r2, loss2
        lam = max(lam / 3, 1e-9 if loss > 1e-8 else 1e-13)
        hist.append(loss)
        if loss < tol or (len(hist) > 60 and hist[-60] / loss < 1.02):
            break
    return loss, float(np.linalg.norm(theta))


def run(m, row_sets, restarts, rng):
    y = perm_tensor(m).ravel()
    best, hits, norms = np.inf, 0, []
    for _ in range(restarts):
        model = Split(m, row_sets, rng)
        loss, norm = lm(model, y)
        best = min(best, loss)
        hits += loss < 1e-20
        norms.append(norm)
    return best, hits, float(np.median(norms))


def configs(m, k, terms):
    """All multisets of `terms` k-subsets of rows, up to relabelling of the rows."""
    subsets = list(itertools.combinations(range(m), k))
    seen, out = set(), []
    for combo in itertools.combinations_with_replacement(range(len(subsets)), terms):
        sets = [subsets[i] for i in combo]
        key = min(tuple(sorted(tuple(sorted(p[i] for i in s)) for s in sets))
                  for p in itertools.permutations(range(m)))
        if k * 2 == m:  # a set and its complement give the same kind of term
            key = min(key, min(tuple(sorted(min(tuple(sorted(p[i] for i in s)),
                                                     tuple(sorted(p[i] for i in range(m) if i not in s)))
                                                 for s in sets))
                               for p in itertools.permutations(range(m))))
        if key not in seen:
            seen.add(key)
            out.append(sets)
    return out


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--terms', type=int, required=True)
    ap.add_argument('--restarts', type=int, default=20)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--max-configs', type=int, default=0)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    cfgs = configs(args.m, args.k, args.terms)
    if args.max_configs and len(cfgs) > args.max_configs:
        idx = rng.choice(len(cfgs), args.max_configs, replace=False)
        cfgs = [cfgs[i] for i in sorted(idx)]
    found = 0
    overall = np.inf
    for sets in cfgs:
        best, hits, norm = run(args.m, sets, args.restarts, rng)
        overall = min(overall, best)
        found += hits > 0
        print(json.dumps(dict(rows=["".join(str(i + 1) for i in s) for s in sets], distinct=len(set(sets)),
                              best=float(f"{best:.3e}"), exact=f"{hits}/{args.restarts}",
                              median_param_norm=round(norm, 1))), flush=True)
    print(f"SUMMARY m={args.m} k={args.k} terms={args.terms}: {found} of {len(cfgs)} configurations of row sets "
          f"admit an exact decomposition; best residual over all {overall:.3e}", flush=True)

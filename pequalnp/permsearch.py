"""Numerical search for unexpectedly cheap formulas for the permanent.

The algebraic cousin of P = NP is the question whether the m x m permanent has
polynomial-size determinantal formulas / algebraic branching programs (VNP inside VBP).
The best construction known (Grenet 2011) has size 2^m - 1 and uses a layered program with
C(m, k) vertices in layer k. This script searches, at small m, for anything smaller.

Two models, both fitted on random complex sample points by Levenberg-Marquardt:

  abp    perm_m(x) = M_1(x) M_2(x) ... M_m(x), M_k a w_{k-1} x w_k matrix of linear forms
         (a homogeneous algebraic branching program with inner widths w_1..w_{m-1}; it gives a
         determinantal formula of size 1 + w_1 + ... + w_{m-1}). Grenet is w_k = C(m, k).
  det    perm_m(x) = det(Lambda + L(x)), Lambda = diag(0, 1, .., 1), L an N x N matrix of
         linear forms (the general determinantal formula of size N).

A relative residual near machine precision (about 1e-28 here) on the fitting points AND on
fresh points means a formula was found numerically; it still has to be made exact before
it is a result. A residual that stalls above zero on every restart is evidence, not proof,
that no such formula exists.
"""
import argparse
import itertools
import json
import sys
import time

import numpy as np


def perm_batch(X):
    """Permanents of a batch of m x m matrices, X of shape (S, m, m)."""
    m = X.shape[1]
    out = np.zeros(X.shape[0], dtype=X.dtype)
    cols = np.arange(m)
    for p in itertools.permutations(range(m)):
        out += np.prod(X[:, cols, list(p)], axis=1)
    return out


def crandn(rng, *shape):
    return (rng.standard_normal(shape) + 1j * rng.standard_normal(shape)) / np.sqrt(2)


class ABP:
    def __init__(self, m, widths, rng, scale=None):
        self.m, self.n = m, m * m
        self.ws = [1] + list(widths) + [1]
        assert len(self.ws) == m + 1
        self.T = []
        for k in range(m):
            s = scale if scale is not None else 1.5 / np.sqrt(self.ws[k])
            self.T.append(crandn(rng, self.n, self.ws[k], self.ws[k + 1]) * s / np.sqrt(self.n))

    def get(self):
        return np.concatenate([t.ravel() for t in self.T])

    def set(self, theta):
        i = 0
        for k in range(self.m):
            sz = self.T[k].size
            self.T[k] = theta[i:i + sz].reshape(self.T[k].shape)
            i += sz

    def _chains(self, X):
        S = X.shape[0]
        mats = [np.einsum('sv,vab->sab', X, T) for T in self.T]
        L = [np.ones((S, 1), dtype=complex)]
        for k in range(self.m):
            L.append(np.einsum('sa,sab->sb', L[-1], mats[k]))
        R = [np.ones((S, 1), dtype=complex)]
        for k in reversed(range(self.m)):
            R.append(np.einsum('sab,sb->sa', mats[k], R[-1]))
        R = R[::-1]  # R[k]: product of mats[k:], shape (S, ws[k])
        return L, R

    def value(self, X):
        L, _ = self._chains(X)
        return L[-1][:, 0]

    def value_jac(self, X):
        L, R = self._chains(X)
        S = X.shape[0]
        blocks = [np.einsum('sv,sa,sb->svab', X, L[k], R[k + 1]).reshape(S, -1) for k in range(self.m)]
        return L[-1][:, 0], np.concatenate(blocks, axis=1)


class Det:
    def __init__(self, m, N, rng, scale=0.3):
        self.m, self.n, self.N = m, m * m, N
        self.Lam = np.eye(N, dtype=complex)
        self.Lam[0, 0] = 0
        self.C = crandn(rng, N, N, self.n) * scale

    def get(self):
        return self.C.ravel().copy()

    def set(self, theta):
        self.C = theta.reshape(self.C.shape)

    def value(self, X):
        return np.linalg.det(self.Lam[None] + np.einsum('ijv,sv->sij', self.C, X))

    def value_jac(self, X):
        A = self.Lam[None] + np.einsum('ijv,sv->sij', self.C, X)
        d = np.linalg.det(A)
        cof = d[:, None, None] * np.transpose(np.linalg.inv(A), (0, 2, 1))
        J = np.einsum('sij,sv->sijv', cof, X).reshape(X.shape[0], -1)
        return d, J


def sample(rng, m, S, circle=0):
    """Random complex points with every coordinate on the unit circle. Under that measure the
    monomials are orthonormal, so the sampled loss approximates the plain l2 distance between
    coefficient vectors. With circle = c > 0 each point is repeated at c + 1 global phases,
    which weights every degree of a non-homogeneous model equally."""
    n = m * m
    if not circle:
        X = np.exp(2j * np.pi * rng.random((S, n)))
    else:
        D = max(1, S // (circle + 1))
        U = np.exp(2j * np.pi * rng.random((D, n)))
        ph = np.exp(2j * np.pi * np.arange(circle + 1) / (circle + 1))
        X = (U[:, None, :] * ph[None, :, None]).reshape(-1, n)
    return X, perm_batch(X.reshape(-1, m, m))


def lm(model, X, y, iters, tol, log=None, lam=1e-2, lam_min=1e-9, giveup=None):
    """Levenberg-Marquardt on the complex residual (holomorphic in the parameters). The damping
    never drops below lam_min: the models have gauge directions, so the normal matrix is singular."""
    ynorm = np.vdot(y, y).real
    f, J = model.value_jac(X)
    r = f - y
    loss = np.vdot(r, r).real / ynorm
    theta = model.get()
    hist = [loss]
    for it in range(iters):
        H = J.conj().T @ J
        g = J.conj().T @ r
        dg = np.maximum(np.diag(H).real, 1e-12 * np.trace(H).real / len(g))
        improved = False
        for _ in range(30):
            try:
                step = np.linalg.solve(H + lam * np.diag(dg), -g)
            except np.linalg.LinAlgError:
                lam *= 10
                continue
            model.set(theta + step)
            r2 = model.value(X) - y
            loss2 = np.vdot(r2, r2).real / ynorm
            if np.isfinite(loss2) and loss2 < loss:
                improved = True
                break
            lam *= 5
        if not improved:
            model.set(theta)
            break
        theta = theta + step
        loss = loss2
        lam = max(lam / 3, lam_min if loss > 1e-8 else 1e-13)  # near a solution, let the damping go
        hist.append(loss)
        if log and (it % log == 0):
            print(f"    it {it:4d} loss {loss:.3e} lam {lam:.1e} |theta| {np.linalg.norm(theta):.2f}", flush=True)
        if loss < tol:
            break
        if len(hist) > 80 and hist[-80] / loss < 1.02:  # stalled: under 2 percent in 80 steps
            break
        if giveup and it >= giveup[0] and loss > giveup[1]:  # a refit that is not converging
            break
        f, J = model.value_jac(X)
        r = f - y
    return loss, len(hist) - 1


def run(args):
    rng = np.random.default_rng(args.seed)
    m = args.m
    out = []
    for trial in range(args.restarts):
        if args.model == 'abp':
            model = ABP(m, args.widths, rng)
            circle = 0
        else:
            model = Det(m, args.N, rng, scale=args.scale)
            circle = args.N
        nparam = model.get().size
        S = args.samples or max(int(args.oversample * nparam), 200)
        X, y = sample(rng, m, S, circle)
        t0 = time.time()
        loss, its = lm(model, X, y, args.iters, args.tol, log=args.log)
        Xv, yv = sample(rng, m, 2000, circle)
        rv = model.value(Xv) - yv
        vloss = np.vdot(rv, rv).real / np.vdot(yv, yv).real
        norm = float(np.linalg.norm(model.get()))
        rec = dict(model=args.model, m=m, widths=args.widths, N=args.N, trial=trial, params=nparam,
                   samples=int(X.shape[0]), fit=loss, fresh=vloss, iters=its, norm=norm,
                   seconds=round(time.time() - t0, 1))
        out.append(rec)
        print(json.dumps(rec), flush=True)
        if args.save and vloss < 1e-18:
            np.save(f"{args.save}_trial{trial}.npy", model.get())
    fits = sorted(r['fresh'] for r in out)
    hits = sum(f < 1e-18 for f in fits)
    print(f"SUMMARY model={args.model} m={m} widths={args.widths} N={args.N}: {hits}/{len(out)} restarts reached zero; "
          f"best fresh residual {fits[0]:.3e}, median {fits[len(fits) // 2]:.3e}", flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('model', choices=['abp', 'det'])
    ap.add_argument('--m', type=int, required=True)
    ap.add_argument('--widths', type=int, nargs='*', default=None)
    ap.add_argument('--N', type=int, default=None)
    ap.add_argument('--restarts', type=int, default=10)
    ap.add_argument('--iters', type=int, default=400)
    ap.add_argument('--tol', type=float, default=1e-26)
    ap.add_argument('--samples', type=int, default=0)
    ap.add_argument('--oversample', type=float, default=3.0)
    ap.add_argument('--scale', type=float, default=0.3)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--log', type=int, default=0)
    ap.add_argument('--save', type=str, default='')
    run(ap.parse_args())

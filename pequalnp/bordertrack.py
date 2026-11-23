"""Does a too-narrow branching program for the m x m permanent approach it in the limit?

Fits a homogeneous branching program with the given inner widths (see permsearch.py) for many
Levenberg-Marquardt steps and prints the relative error next to the parameter norm. A border
(limit) representation shows up as an error that keeps falling like 1 / |theta|^2 while the
parameters grow; a genuine obstruction shows up as an error that levels off.

Usage: python3 bordertrack.py <m> <widths, comma separated> [restarts] [iters] [seed]
"""
import sys

import numpy as np

from permsearch import ABP, sample


def track(model, X, y, iters, lam=1e-2):
    ynorm = np.vdot(y, y).real
    theta = model.get()
    f, J = model.value_jac(X)
    r = f - y
    loss = np.vdot(r, r).real / ynorm
    marks = {int(round(10 ** e)) for e in np.arange(1.5, 6.01, 0.25)}
    rows = []
    for it in range(1, iters + 1):
        H = J.conj().T @ J
        g = J.conj().T @ r
        dg = np.maximum(np.diag(H).real, 1e-12 * np.trace(H).real / len(g))
        ok = False
        for _ in range(40):
            try:
                step = np.linalg.solve(H + lam * np.diag(dg), -g)
            except np.linalg.LinAlgError:
                lam *= 10
                continue
            model.set(theta + step)
            r2 = model.value(X) - y
            loss2 = np.vdot(r2, r2).real / ynorm
            if np.isfinite(loss2) and loss2 < loss:
                ok = True
                break
            lam *= 5
        if not ok:
            model.set(theta)
            break
        theta, loss = theta + step, loss2
        lam = max(lam / 3, 1e-13)
        if it in marks:
            rows.append((it, loss, float(np.linalg.norm(theta))))
        if loss < 1e-26:
            rows.append((it, loss, float(np.linalg.norm(theta))))
            break
        f, J = model.value_jac(X)
        r = f - y
    return rows


if __name__ == '__main__':
    m = int(sys.argv[1])
    widths = [int(w) for w in sys.argv[2].split(',')]
    restarts = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    iters = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
    rng = np.random.default_rng(int(sys.argv[5]) if len(sys.argv) > 5 else 0)
    for trial in range(restarts):
        model = ABP(m, widths, rng)
        X, y = sample(rng, m, max(3 * model.get().size, 5000 if m == 4 else 0))
        rows = track(model, X, y, iters)
        print(f"widths {widths} trial {trial}:", flush=True)
        for it, loss, norm in rows[-7:]:
            print(f"   it {it:6d}  error {loss:.3e}  |theta| {norm:9.2f}  error*|theta|^2 {loss * norm ** 2:9.3f}", flush=True)

"""Solve wide, then prune: look for small branching programs for the permanent.

A random start at the exact target widths usually lands in a bad local minimum, while a
program with a few spare vertices per layer is found almost every time. So: fit a wide
program exactly, then repeatedly try to delete one vertex. To delete a vertex of layer k the
gauge freedom of that layer is used to sort its vertices by how much they contribute, the
weakest one is squeezed by a growing penalty on its edges, removed, and the smaller program is
refitted. A deletion counts only if the refit returns to a zero residual on fresh points.
"""
import argparse
import json
import time

import numpy as np

from permsearch import ABP, lm, sample

ZERO = 1e-18    # a formula: residual at rounding level on fresh points
ACCEPT = 1e-7   # close enough to keep pruning from; the final program is polished and re-judged against ZERO


def penalised_lm(model, X, y, pen, iters, lam=1e-3, lam_min=1e-9):
    """LM on |f - y|^2 / |y|^2 + sum pen_i |theta_i|^2."""
    ynorm = np.vdot(y, y).real
    theta = model.get()
    f, J = model.value_jac(X)
    r = f - y
    obj = np.vdot(r, r).real / ynorm + float(pen @ np.abs(theta) ** 2)
    for _ in range(iters):
        H = (J.conj().T @ J) / ynorm
        g = (J.conj().T @ r) / ynorm + pen * theta
        H[np.diag_indices_from(H)] += pen
        dg = np.maximum(np.diag(H).real, 1e-12 * np.trace(H).real / len(g))
        ok = False
        for _ in range(25):
            try:
                step = np.linalg.solve(H + lam * np.diag(dg), -g)
            except np.linalg.LinAlgError:
                lam *= 10
                continue
            model.set(theta + step)
            r2 = model.value(X) - y
            obj2 = np.vdot(r2, r2).real / ynorm + float(pen @ np.abs(theta + step) ** 2)
            if np.isfinite(obj2) and obj2 < obj:
                ok = True
                break
            lam *= 5
        if not ok:
            model.set(theta)
            break
        theta = theta + step
        done = (obj - obj2) < 1e-9 * obj
        obj = obj2
        lam = max(lam / 3, lam_min)
        if done:
            break
        f, J = model.value_jac(X)
        r = f - y
    r = model.value(X) - y
    return np.vdot(r, r).real / ynorm


def sort_layer(model, k, X):
    """Gauge layer k (between T[k-1] and T[k]) so that its prefix polynomials are orthonormal on
    the sample and its suffix polynomials are orthogonal, largest first."""
    L, R = model._chains(X)
    A, B = L[k], R[k]
    _, Rm = np.linalg.qr(A)
    Bp = B @ Rm.T
    evals, V = np.linalg.eigh(Bp.conj().T @ Bp)
    V = V[:, ::-1]
    g = np.linalg.solve(Rm, V.conj())
    ginv = V.T @ Rm
    model.T[k - 1] = np.einsum('vab,bc->vac', model.T[k - 1], g)
    model.T[k] = np.einsum('ab,vbc->vac', ginv, model.T[k])
    return np.sqrt(np.maximum(evals[::-1], 0))


def balance(model, k, v):
    """Rescale vertex v of layer k so its in-edges and out-edges have equal norm."""
    a = np.linalg.norm(model.T[k - 1][:, :, v])
    b = np.linalg.norm(model.T[k][:, v, :])
    if a > 0 and b > 0:
        s = np.sqrt(b / a)
        model.T[k - 1][:, :, v] *= s
        model.T[k][:, v, :] /= s


def clone(model):
    c = ABP.__new__(ABP)
    c.m, c.n, c.ws = model.m, model.n, list(model.ws)
    c.T = [t.copy() for t in model.T]
    return c


def drop_vertex(model, k, v):
    model.T[k - 1] = np.delete(model.T[k - 1], v, axis=2)
    model.T[k] = np.delete(model.T[k], v, axis=1)
    model.ws[k] -= 1


def try_delete(model, k, X, y, Xv, yv, squeeze=True, iters=300):
    """Try to delete one vertex from layer k. Returns the smaller exact model or None."""
    cand = clone(model)
    sv = sort_layer(cand, k, X)
    v = cand.ws[k] - 1
    if squeeze:
        balance(cand, k, v)
        offs = np.cumsum([0] + [t.size for t in cand.T])
        mask = np.zeros(offs[-1])
        m1 = np.zeros(cand.T[k - 1].shape)
        m1[:, :, v] = 1
        m2 = np.zeros(cand.T[k].shape)
        m2[:, v, :] = 1
        mask[offs[k - 1]:offs[k]] = m1.ravel()
        mask[offs[k]:offs[k + 1]] = m2.ravel()
        for mu in 10.0 ** np.arange(-6, 3):
            fit = penalised_lm(cand, X, y, mu * mask, iters=60)
            edge = np.linalg.norm(cand.T[k - 1][:, :, v]) * np.linalg.norm(cand.T[k][:, v, :])
            if edge < 1e-10 or fit > 0.5:
                break
    drop_vertex(cand, k, v)
    lm(cand, X, y, iters, 1e-26, giveup=(40, 1e-3))
    rv = cand.value(Xv) - yv
    fresh = np.vdot(rv, rv).real / np.vdot(yv, yv).real
    return (cand if fresh < ACCEPT else None), fresh, float(sv[-1] / sv[0])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--m', type=int, required=True)
    ap.add_argument('--widths', type=int, nargs='+', required=True, help='starting (wide) inner widths')
    ap.add_argument('--samples', type=int, default=0)
    ap.add_argument('--restarts', type=int, default=5)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--iters', type=int, default=300)
    ap.add_argument('--save', type=str, default='')
    ap.add_argument('--squeeze', action='store_true')
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    m = args.m
    floors = []
    for trial in range(args.restarts):
        t0 = time.time()
        model = ABP(m, args.widths, rng)
        S = args.samples or 3 * model.get().size
        X, y = sample(rng, m, S)
        Xv, yv = sample(rng, m, 3000)
        lm(model, X, y, 2 * args.iters, 1e-26)
        rv = model.value(Xv) - yv
        fresh = np.vdot(rv, rv).real / np.vdot(yv, yv).real
        if fresh > ACCEPT:
            print(json.dumps(dict(trial=trial, start=args.widths, status='wide fit failed', fresh=fresh)), flush=True)
            continue
        log = []
        stuck = set()
        while True:
            layers = [k for k in range(1, m) if k not in stuck and model.ws[k] > 1]
            if not layers:
                break
            progressed = False
            # try the layer whose weakest vertex is relatively weakest first
            order = sorted(layers, key=lambda k: sort_layer(clone(model), k, X)[-1] / sort_layer(clone(model), k, X)[0])
            for k in order:
                for squeeze in ((False, True) if args.squeeze else (False,)):
                    smaller, fr, ratio = try_delete(model, k, X, y, Xv, yv, squeeze=squeeze, iters=args.iters)
                    log.append(dict(layer=k, squeeze=squeeze, to=(smaller.ws[1:-1] if smaller else None),
                                    refit=float(f"{fr:.3e}"), weakest=float(f"{ratio:.2e}")))
                    if smaller is not None:
                        model = smaller
                        stuck.clear()
                        progressed = True
                        break
                if progressed:
                    break
                stuck.add(k)
            if not progressed:
                break
        floor = model.ws[1:-1]
        lm(model, X, y, 5 * args.iters, 1e-27)
        rv = model.value(Xv) - yv
        polished = np.vdot(rv, rv).real / np.vdot(yv, yv).real
        floors.append((floor, polished))
        failed = [(e['layer'], e['refit']) for e in log if e['to'] is None]
        print(json.dumps(dict(trial=trial, start=args.widths, floor=floor, size=1 + sum(floor),
                              polished_residual=float(f"{polished:.3e}"), exact=bool(polished < ZERO),
                              failed_deletions_at_floor=failed[-2 * (m - 1):], seconds=round(time.time() - t0, 1))), flush=True)
        if args.save:
            np.save(f"{args.save}_m{m}_{'-'.join(map(str, floor))}_trial{trial}.npy", model.get())
    exact = sorted(1 + sum(f) for f, res in floors if res < ZERO)
    print(f"SUMMARY m={m} start={args.widths}: floors reached {sorted((tuple(f), float(f'{res:.1e}')) for f, res in floors)}; "
          f"smallest size with a residual at rounding level: {exact[0] if exact else None}", flush=True)


if __name__ == '__main__':
    main()
